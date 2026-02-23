(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_To_Core_Translation
  imports
    Micro_C_Syntax
    "Shallow_Micro_Rust.Core_Expression"
  keywords "micro_c_translate" :: thy_decl
begin

section \<open>C-to-Core Monad Translation Infrastructure\<close>

text \<open>
  This theory defines ML infrastructure for translating Isabelle/C's parsed C11 AST
  into AutoCorrode's core monad terms. The pipeline is:
  \begin{enumerate}
    \item Parse C source via Isabelle/C (reusing the existing @{command "C"} parser)
    \item Walk the \<open>C_Ast.cTranslationUnit\<close> AST
    \item Generate Isabelle @{command definition} commands for each C function
  \end{enumerate}

  The translation is invoked via the \<open>micro_c_translate\<close> command,
  which takes a C source string and produces definitions in the local theory.
\<close>

subsection \<open>AST Utilities\<close>

text \<open>Helper functions for extracting information from Isabelle/C's AST nodes.\<close>

ML \<open>
structure C_Ast_Utils : sig
  val abr_string_to_string : C_Ast.abr_string -> string
  val ident_name : C_Ast.ident -> string
  val declr_name : C_Ast.nodeInfo C_Ast.cDeclarator -> string
  val extract_fundefs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                        -> C_Ast.nodeInfo C_Ast.cFunctionDef list
end =
struct
  open C_Ast

  fun abr_string_to_string (SS_base (ST s)) = s
    | abr_string_to_string (SS_base (STa codes)) =
        String.implode (List.map (Char.chr o IntInf.toInt) codes)
    | abr_string_to_string (String_concatWith (sep, parts)) =
        let val sep_s = abr_string_to_string sep
        in String.concatWith sep_s (List.map abr_string_to_string parts) end

  fun ident_name (Ident0 (s, _, _)) = abr_string_to_string s

  fun declr_name (CDeclr0 (Some ident, _, _, _, _)) = ident_name ident
    | declr_name (CDeclr0 (None, _, _, _, _)) =
        error "C_Ast_Utils.declr_name: anonymous declarator"

  fun extract_fundefs (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CFDefExt0 fundef => SOME fundef | _ => NONE)
      ext_decls
end
\<close>

subsection \<open>Translation Context\<close>

text \<open>
  The translation context tracks information accumulated during AST traversal:
  variable bindings (mapping C variable names to Isabelle free variables),
  function signatures, and diagnostics.
\<close>

ML \<open>
structure C_Trans_Ctxt : sig
  type t
  val empty : t
  val add_local : string -> term -> t -> t
  val lookup_local : t -> string -> term option
end =
struct
  type t = {
    locals : term Symtab.table  (* C variable name -> Isabelle free variable *)
  }

  val empty : t = { locals = Symtab.empty }

  fun add_local name tm ({ locals } : t) : t =
    { locals = Symtab.update (name, tm) locals }

  fun lookup_local ({ locals, ... } : t) name =
    Symtab.lookup locals name
end
\<close>

subsection \<open>Term Construction\<close>

text \<open>
  Functions for building well-formed core monad terms. Each function
  constructs a term using the actual constants from @{theory "Shallow_Micro_Rust.Core_Expression"}.
\<close>

ML \<open>
structure C_Term_Build : sig
  val mk_literal_unit : term
  val mk_function_body : term -> term
  val mk_sequence : term -> term -> term
  val mk_literal_int : int -> term
  val mk_return_func : term -> term
end =
struct
  (* literal () : the "skip" operation *)
  val mk_literal_unit =
    Const (\<^const_name>\<open>literal\<close>, \<^typ>\<open>unit\<close> --> dummyT) $ HOLogic.unit

  (* FunctionBody e *)
  fun mk_function_body body =
    Const (\<^const_name>\<open>FunctionBody\<close>, dummyT --> dummyT) $ body

  (* sequence e1 e2 *)
  fun mk_sequence e1 e2 =
    Const (\<^const_name>\<open>sequence\<close>, dummyT --> dummyT --> dummyT) $ e1 $ e2

  (* literal n, where n is an integer constant *)
  fun mk_literal_int n =
    Const (\<^const_name>\<open>literal\<close>, dummyT --> dummyT)
      $ HOLogic.mk_number dummyT n

  (* return_func e : for C return statements *)
  fun mk_return_func body =
    Const (\<^const_name>\<open>return_func\<close>, dummyT --> dummyT) $ body
end
\<close>

subsection \<open>Statement and Expression Translation\<close>

text \<open>
  The core translation: C AST nodes are mapped to core monad expressions.
  Unsupported constructs produce explicit errors identifying the construct
  that could not be translated.
\<close>

ML \<open>
structure C_Translate : sig
  val translate_stmt : C_Trans_Ctxt.t -> C_Ast.nodeInfo C_Ast.cStatement -> term
  val translate_fundef : Proof.context -> C_Ast.nodeInfo C_Ast.cFunctionDef -> string * term
end =
struct
  open C_Ast

  fun unsupported construct =
    error ("micro_c_translate: unsupported C construct: " ^ construct)

  fun translate_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        C_Term_Build.mk_literal_int (IntInf.toInt n)
    | translate_expr _ (CVar0 _) =
        unsupported "variable reference (Task 1.6)"
    | translate_expr _ (CBinary0 _) =
        unsupported "binary expression (Task 1.6)"
    | translate_expr _ (CAssign0 _) =
        unsupported "assignment (Task 1.6)"
    | translate_expr _ (CCall0 _) =
        unsupported "function call (Task 1.8)"
    | translate_expr _ (CUnary0 _) =
        unsupported "unary expression"
    | translate_expr _ (CIndex0 _) =
        unsupported "array indexing (Task 1.14)"
    | translate_expr _ (CMember0 _) =
        unsupported "struct member access (Task 2.2)"
    | translate_expr _ _ =
        unsupported "expression"

  fun translate_block_item tctx (CBlockStmt0 stmt) = SOME (translate_stmt tctx stmt)
    | translate_block_item _ (CBlockDecl0 _) =
        unsupported "local declaration (Task 1.6)"
    | translate_block_item _ (CNestedFunDef0 _) =
        unsupported "nested function definition"

  and translate_stmt tctx (CCompound0 (_, items, _)) =
        (case List.mapPartial (translate_block_item tctx) items of
           [] => C_Term_Build.mk_literal_unit
         | [single] => single
         | first :: rest => List.foldl (fn (next, acc) =>
             C_Term_Build.mk_sequence acc next) first rest)
    | translate_stmt _ (CReturn0 (None, _)) =
        C_Term_Build.mk_return_func C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CReturn0 (Some expr, _)) =
        C_Term_Build.mk_return_func (translate_expr tctx expr)
    | translate_stmt tctx (CExpr0 (Some expr, _)) =
        translate_expr tctx expr
    | translate_stmt _ (CExpr0 (None, _)) =
        C_Term_Build.mk_literal_unit
    | translate_stmt _ (CIf0 _) =
        unsupported "if statement (Task 1.7)"
    | translate_stmt _ (CFor0 _) =
        unsupported "for loop (Task 1.9)"
    | translate_stmt _ (CWhile0 _) =
        unsupported "while loop (Task 1.10)"
    | translate_stmt _ (CSwitch0 _) =
        unsupported "switch statement (Task 1.10)"
    | translate_stmt _ (CGoto0 _) =
        unsupported "goto (Task 1.10)"
    | translate_stmt _ (CLabel0 _) =
        unsupported "label"
    | translate_stmt _ (CCont0 _) =
        unsupported "continue"
    | translate_stmt _ (CBreak0 _) =
        unsupported "break"
    | translate_stmt _ _ =
        unsupported "statement"

  fun translate_fundef ctxt (CFunDef0 (_, declr, _, body, _)) =
    let
      val name = C_Ast_Utils.declr_name declr
      val tctx = C_Trans_Ctxt.empty
      val body_term = translate_stmt tctx body
      val fn_term = C_Term_Build.mk_function_body body_term
      val fn_term' = Syntax.check_term ctxt fn_term
    in
      (name, fn_term')
    end
end
\<close>

subsection \<open>Definition Generation\<close>

ML \<open>
structure C_Def_Gen : sig
  val define_c_function : string -> term -> local_theory -> local_theory
  val process_translation_unit : C_Ast.nodeInfo C_Ast.cTranslationUnit
                                 -> local_theory -> local_theory
end =
struct
  fun define_c_function name term lthy =
    let
      val binding = Binding.name ("c_" ^ name)
      val ((_, (_, _)), lthy') =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, @{attributes [micro_rust_simps]}), term))
          lthy
      val _ = writeln ("Defined: c_" ^ name)
    in lthy' end

  fun process_translation_unit tu lthy =
    let
      val fundefs = C_Ast_Utils.extract_fundefs tu
      val translated = List.map (C_Translate.translate_fundef lthy) fundefs
    in
      List.foldl (fn ((name, term), lthy) =>
        define_c_function name term lthy) lthy translated
    end
end
\<close>

subsection \<open>The \<open>micro_c_translate\<close> Command\<close>

text \<open>
  The command parses inline C source via Isabelle/C's parser (reusing the
  existing infrastructure including the @{text "Root_Ast_Store"}) and
  generates @{command definition} commands for each function found.

  Usage: @{text [display] "micro_c_translate \<open>void f() { return; }\<close>"}
\<close>

ML \<open>
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>micro_c_translate\<close>
    "parse C source and generate core monad definitions"
    (Parse.embedded_input >> (fn source => fn lthy =>
      let
        (* Step 1: Parse the C source using Isabelle/C's parser.
           We use a Theory context so that Root_Ast_Store is updated at the
           theory level, where get_CTranslUnit can retrieve it. *)
        val thy = Proof_Context.theory_of lthy
        val context' = C_Module.exec_eval source (Context.Theory thy)
        val thy' = Context.theory_of context'

        (* Step 2: Retrieve the parsed AST from Root_Ast_Store *)
        val tu = get_CTranslUnit thy'

        (* Step 3: Translate and generate definitions *)
      in
        C_Def_Gen.process_translation_unit tu lthy
      end))
\<close>

subsection \<open>Smoke Test\<close>

text \<open>Verify the command works end-to-end with a trivial void function.\<close>

micro_c_translate \<open>
void f(void) {
  return;
}
\<close>

thm c_f_def

micro_c_translate \<open>
int g(void) {
  return 42;
}
\<close>

thm c_g_def

end

