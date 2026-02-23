(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)



theory C_To_Core_Translation
  imports
    Micro_C_Syntax
    "Shallow_Micro_Rust.Core_Expression"
    "Shallow_Micro_Rust.Core_Syntax"
    "Shallow_Micro_Rust.Bool_Type"
    "Shallow_Micro_Rust.Rust_Iterator"
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
  val extract_params : C_Ast.nodeInfo C_Ast.cDeclarator -> string list
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

  (* Extract parameter names from a function declarator.
     Handles void parameters (empty list) and named parameters. *)
  fun param_name (CDecl0 (_, [((Some declr, _), _)], _)) = SOME (declr_name declr)
    | param_name (CDecl0 (_, [], _)) = NONE  (* void parameter *)
    | param_name _ = NONE

  fun extract_params (CDeclr0 (_, derived, _, _, _)) =
    (case List.find (fn CFunDeclr0 _ => true | _ => false) derived of
       SOME (CFunDeclr0 (Right (params, _), _, _)) =>
         List.mapPartial param_name params
     | _ => [])

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
  datatype var_kind = Param | Local  (* Param = by-value, Local = mutable reference *)
  type t
  val make : Proof.context -> t
  val get_ctxt : t -> Proof.context
  val add_var : string -> var_kind -> term -> t -> t
  val lookup_var : t -> string -> (var_kind * term) option
end =
struct
  datatype var_kind = Param | Local
  type t = {
    ctxt : Proof.context,
    vars : (var_kind * term) Symtab.table
  }

  fun make ctxt : t = { ctxt = ctxt, vars = Symtab.empty }

  fun get_ctxt ({ ctxt, ... } : t) = ctxt

  fun add_var name kind tm ({ ctxt, vars } : t) : t =
    { ctxt = ctxt, vars = Symtab.update (name, (kind, tm)) vars }

  fun lookup_var ({ vars, ... } : t) name =
    Symtab.lookup vars name
end
\<close>

subsection \<open>Stub Constants for Unsupported C Constructs\<close>

text \<open>
  Opaque constants for C constructs that cannot be translated.
  They have no WP rules, so symbolic execution silently gets stuck
  when encountering these. The translation succeeds, and the user
  can see from the constant names which constructs need attention.
\<close>

consts c_while_stub :: "('s, 'v, 'r, 'abort, 'i, 'o) expression"
consts c_goto_stub :: "('s, 'v, 'r, 'abort, 'i, 'o) expression"
consts c_unsupported :: "('s, 'v, 'r, 'abort, 'i, 'o) expression"

subsection \<open>Term Construction\<close>

text \<open>
  Functions for building well-formed core monad terms. Each function
  constructs a term using the actual constants from @{theory "Shallow_Micro_Rust.Core_Expression"}.
\<close>

ML \<open>
structure C_Term_Build : sig
  val mk_literal_unit : term
  val mk_literal : term -> term
  val mk_function_body : term -> term
  val mk_sequence : term -> term -> term
  val mk_literal_int : int -> term
  val mk_return_func : term -> term
  val mk_bind : term -> term -> term
  val mk_var_alloc : term -> term
  val mk_var_read : term -> term
  val mk_var_write : term -> term -> term
  val mk_bindlift2 : term -> term -> term -> term
  val mk_two_armed_cond : term -> term -> term -> term
  val mk_one_armed_cond : term -> term -> term
  val mk_funcall : term -> term list -> term
  val mk_raw_for_loop : term -> term -> term
  val mk_upt_int_range : term -> term -> term
  val mk_deref : term -> term
  val mk_ptr_write : term -> term -> term
  val mk_while_stub : term
  val mk_goto_stub : term
  val mk_unsupported_stub : term
end =
struct
  (* literal v *)
  fun mk_literal v =
    Const (\<^const_name>\<open>literal\<close>, dummyT --> dummyT) $ v

  (* literal () : the "skip" operation *)
  val mk_literal_unit =
    Const (\<^const_name>\<open>literal\<close>, \<^typ>\<open>unit\<close> --> dummyT) $ HOLogic.unit

  (* FunctionBody e *)
  fun mk_function_body body =
    Const (\<^const_name>\<open>FunctionBody\<close>, dummyT --> dummyT) $ body

  (* sequence e1 e2 *)
  fun mk_sequence e1 e2 =
    Const (\<^const_name>\<open>sequence\<close>, dummyT --> dummyT --> dummyT) $ e1 $ e2

  (* literal n, where n is an integer constant (typed as int to avoid phantom TYPE params) *)
  fun mk_literal_int n =
    Const (\<^const_name>\<open>literal\<close>, \<^typ>\<open>int\<close> --> dummyT)
      $ HOLogic.mk_number \<^typ>\<open>int\<close> n

  (* return_func e : for C return statements *)
  fun mk_return_func body =
    Const (\<^const_name>\<open>return_func\<close>, dummyT --> dummyT) $ body

  (* bind e f : monadic bind *)
  fun mk_bind e f =
    Const (\<^const_name>\<open>bind\<close>, dummyT --> dummyT --> dummyT) $ e $ f

  (* Allocate a new mutable variable: funcall1 store_reference_const init_expr *)
  fun mk_var_alloc init_expr =
    Const (\<^const_name>\<open>funcall1\<close>, dummyT --> dummyT --> dummyT)
      $ Const (\<^const_name>\<open>store_reference_const\<close>, dummyT)
      $ init_expr

  (* Read a mutable variable: bind (literal ref) (deep_compose1 call store_dereference_const) *)
  fun mk_var_read ref_var =
    Const (\<^const_name>\<open>bind\<close>, dummyT --> dummyT --> dummyT)
      $ mk_literal ref_var
      $ (Const (\<^const_name>\<open>deep_compose1\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_dereference_const\<close>, dummyT))

  (* Write a mutable variable: bind2 (deep_compose2 call store_update_const) (literal ref) val_expr *)
  fun mk_var_write ref_var val_expr =
    Const (\<^const_name>\<open>bind2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ (Const (\<^const_name>\<open>deep_compose2\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_update_const\<close>, dummyT))
      $ mk_literal ref_var
      $ val_expr
  fun mk_bindlift2 f e1 e2 =
    Const (\<^const_name>\<open>bindlift2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ f $ e1 $ e2

  (* two_armed_conditional test then_br else_br *)
  fun mk_two_armed_cond test then_br else_br =
    Const (\<^const_name>\<open>two_armed_conditional\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ test $ then_br $ else_br

  (* one_armed_conditional test then_br *)
  fun mk_one_armed_cond test then_br =
    Const (\<^const_name>\<open>two_armed_conditional\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ test $ then_br $ mk_literal_unit

  (* funcallN f arg0 ... argN : call a function with N arguments *)
  local
    val funcall_names = Vector.fromList [
      \<^const_name>\<open>funcall0\<close>, \<^const_name>\<open>funcall1\<close>, \<^const_name>\<open>funcall2\<close>,
      \<^const_name>\<open>funcall3\<close>, \<^const_name>\<open>funcall4\<close>, \<^const_name>\<open>funcall5\<close>,
      \<^const_name>\<open>funcall6\<close>, \<^const_name>\<open>funcall7\<close>, \<^const_name>\<open>funcall8\<close>,
      \<^const_name>\<open>funcall9\<close>, \<^const_name>\<open>funcall10\<close>
    ]
  in
  fun mk_funcall f args =
    let val n = length args
    in if n > 10 then error "mk_funcall: more than 10 arguments not supported"
       else let val cname = Vector.sub (funcall_names, n)
                val ty = Library.foldr (fn (_, t) => dummyT --> t) (args, dummyT)
            in Library.foldl (op $) (Const (cname, dummyT --> ty), f :: args) end
    end
  end

  (* raw_for_loop range_list body_fn *)
  fun mk_raw_for_loop range body =
    Const (\<^const_name>\<open>raw_for_loop\<close>, dummyT --> dummyT --> dummyT) $ range $ body

  (* Build [start..<bound] mapped through of_nat to produce an int list:
     List.map of_nat [start..<bound] *)
  fun mk_upt_int_range start_nat bound_nat =
    Const (\<^const_name>\<open>List.map\<close>, dummyT --> dummyT --> dummyT)
      $ Const (\<^const_name>\<open>of_nat\<close>, dummyT)
      $ (Const (\<^const_name>\<open>upt\<close>, dummyT --> dummyT --> dummyT) $ start_nat $ bound_nat)

  (* Dereference a pointer expression: bind ptr_expr (deep_compose1 call store_dereference_const)
     This generalizes mk_var_read from literal variables to arbitrary expressions. *)
  fun mk_deref ptr_expr =
    Const (\<^const_name>\<open>bind\<close>, dummyT --> dummyT --> dummyT)
      $ ptr_expr
      $ (Const (\<^const_name>\<open>deep_compose1\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_dereference_const\<close>, dummyT))

  (* Write through a pointer expression: bind2 (deep_compose2 call store_update_const) ptr_expr val_expr
     This generalizes mk_var_write from literal variables to arbitrary expressions. *)
  fun mk_ptr_write ptr_expr val_expr =
    Const (\<^const_name>\<open>bind2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ (Const (\<^const_name>\<open>deep_compose2\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_update_const\<close>, dummyT))
      $ ptr_expr
      $ val_expr

  (* Stub constants for unsupported C constructs *)
  val mk_while_stub = Const (\<^const_name>\<open>c_while_stub\<close>, dummyT)
  val mk_goto_stub = Const (\<^const_name>\<open>c_goto_stub\<close>, dummyT)
  val mk_unsupported_stub = Const (\<^const_name>\<open>c_unsupported\<close>, dummyT)
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
  (* Save Isabelle term constructors before C_Ast shadows them *)
  val Isa_Const = Const
  val Isa_Free = Free
  val isa_dummyT = dummyT

  open C_Ast

  fun unsupported construct =
    error ("micro_c_translate: unsupported C construct: " ^ construct)

  (* Translate a C binary operator to a HOL function constant *)
  fun translate_binop CAddOp0 = Isa_Const (\<^const_name>\<open>plus\<close>, isa_dummyT)
    | translate_binop CSubOp0 = Isa_Const (\<^const_name>\<open>minus\<close>, isa_dummyT)
    | translate_binop CMulOp0 = Isa_Const (\<^const_name>\<open>times\<close>, isa_dummyT)
    | translate_binop CDivOp0 = Isa_Const (\<^const_name>\<open>divide\<close>, isa_dummyT)
    | translate_binop CRmdOp0 = Isa_Const (\<^const_name>\<open>modulo\<close>, isa_dummyT)
    | translate_binop CLeOp0 = Isa_Const (\<^const_name>\<open>less\<close>, isa_dummyT)
    | translate_binop CLeqOp0 = Isa_Const (\<^const_name>\<open>less_eq\<close>, isa_dummyT)
    | translate_binop CGrOp0 = Isa_Const (\<^const_name>\<open>less\<close>, isa_dummyT) (* reversed operands *)
    | translate_binop CGeqOp0 = Isa_Const (\<^const_name>\<open>less_eq\<close>, isa_dummyT) (* reversed operands *)
    | translate_binop CEqOp0 = Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
    | translate_binop CNeqOp0 = unsupported "!= operator"
    | translate_binop CLndOp0 = Isa_Const (\<^const_name>\<open>conj\<close>, isa_dummyT)
    | translate_binop CLorOp0 = Isa_Const (\<^const_name>\<open>disj\<close>, isa_dummyT)
    | translate_binop _ = unsupported "binary operator"

  fun translate_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        C_Term_Build.mk_literal_int (IntInf.toInt n)
    | translate_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, var) => C_Term_Build.mk_literal var
           | SOME (C_Trans_Ctxt.Local, var) => C_Term_Build.mk_var_read var
           | NONE => error ("micro_c_translate: undefined variable: " ^ name)
        end
    | translate_expr tctx (CBinary0 (binop, lhs, rhs, _)) =
        let val lhs' = translate_expr tctx lhs
            val rhs' = translate_expr tctx rhs
        in
          (* For > and >=, swap operands to use < and <= *)
          case binop of
            CGrOp0 => C_Term_Build.mk_bindlift2 (translate_binop binop) rhs' lhs'
          | CGeqOp0 => C_Term_Build.mk_bindlift2 (translate_binop binop) rhs' lhs'
          | _ => C_Term_Build.mk_bindlift2 (translate_binop binop) lhs' rhs'
        end
    | translate_expr tctx (CAssign0 (CAssignOp0, CVar0 (ident, _), rhs, _)) =
        let val name = C_Ast_Utils.ident_name ident
            val rhs' = translate_expr tctx rhs
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, var) => C_Term_Build.mk_var_write var rhs'
           | SOME (C_Trans_Ctxt.Param, _) =>
               error ("micro_c_translate: assignment to parameter: " ^ name)
           | NONE => error ("micro_c_translate: undefined variable: " ^ name)
        end
    | translate_expr tctx (CAssign0 (CAssignOp0, CUnary0 (CIndOp0, lhs, _), rhs, _)) =
        (* *p = v : write through pointer *)
        C_Term_Build.mk_ptr_write (translate_expr tctx lhs) (translate_expr tctx rhs)
    | translate_expr _ (CAssign0 _) =
        unsupported "compound assignment or non-variable lhs"
    | translate_expr tctx (CCall0 (CVar0 (ident, _), args, _)) =
        let val fname = C_Ast_Utils.ident_name ident
            val arg_terms = List.map (translate_expr tctx) args
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            (* Look up the fully qualified constant name, then use dummyT
               so Syntax.check_term can infer the type. *)
            val (full_name, _) = Term.dest_Const
              (Proof_Context.read_const {proper = true, strict = false} ctxt ("c_" ^ fname))
            val func_ref = Isa_Const (full_name, isa_dummyT)
        in C_Term_Build.mk_funcall func_ref arg_terms end
    | translate_expr _ (CCall0 _) =
        unsupported "indirect function call (function pointers)"
    | translate_expr tctx (CUnary0 (CIndOp0, expr, _)) =
        (* *p : dereference pointer *)
        C_Term_Build.mk_deref (translate_expr tctx expr)
    | translate_expr _ (CUnary0 _) =
        unsupported "unary expression"
    | translate_expr _ (CIndex0 _) =
        unsupported "array indexing (Task 1.14)"
    | translate_expr _ (CMember0 _) =
        unsupported "struct member access (Task 2.2)"
    | translate_expr _ _ =
        unsupported "expression"

  (* Extract variable name and initializer from a C declaration *)
  fun translate_decl tctx (CDecl0 (_, [(( Some declr, Some (CInitExpr0 (init, _))), _)], _)) =
        let val name = C_Ast_Utils.declr_name declr
            val init' = translate_expr tctx init
        in (name, init') end
    | translate_decl _ (CDecl0 (_, [((Some declr, None), _)], _)) =
        (* Uninitialized variable: default to literal 0 *)
        let val name = C_Ast_Utils.declr_name declr
        in (name, C_Term_Build.mk_literal_int 0) end
    | translate_decl _ _ = unsupported "complex declaration"

  (* Translate a compound block, right-folding declarations into nested binds *)
  fun translate_compound_items _ [] = C_Term_Build.mk_literal_unit
    | translate_compound_items tctx [CBlockStmt0 stmt] = translate_stmt tctx stmt
    | translate_compound_items tctx [CBlockDecl0 decl] =
        (* Declaration at end of block with no following statements *)
        let val (name, init_term) = translate_decl tctx decl
            val var = Isa_Free (name, isa_dummyT)
        in C_Term_Build.mk_bind (C_Term_Build.mk_var_alloc init_term)
             (Term.lambda var C_Term_Build.mk_literal_unit) end
    | translate_compound_items _ [CNestedFunDef0 _] =
        unsupported "nested function definition"
    | translate_compound_items tctx (CBlockDecl0 decl :: rest) =
        let val (name, init_term) = translate_decl tctx decl
            val var = Isa_Free (name, isa_dummyT)
            val tctx' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var tctx
            val rest_term = translate_compound_items tctx' rest
        in C_Term_Build.mk_bind (C_Term_Build.mk_var_alloc init_term)
             (Term.lambda var rest_term) end
    | translate_compound_items tctx (CBlockStmt0 stmt :: rest) =
        let val stmt_term = translate_stmt tctx stmt
            val rest_term = translate_compound_items tctx rest
        in C_Term_Build.mk_sequence stmt_term rest_term end
    | translate_compound_items _ _ = unsupported "block item"

  (* Translate a C expression to a pure nat term (for loop bounds).
     Only integer literals and parameter variables are supported. *)
  and translate_pure_nat_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        HOLogic.mk_nat (IntInf.toInt n)
    | translate_pure_nat_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, v) =>
               (* Convert parameter (int) to nat for range *)
               Isa_Const (\<^const_name>\<open>nat\<close>, isa_dummyT) $ v
           | _ => error ("micro_c_translate: loop bound must be a parameter or literal: " ^ name)
        end
    | translate_pure_nat_expr _ _ =
        error "micro_c_translate: unsupported loop bound expression"

  (* Try to recognize: for (int i = start; i < bound; i++) body
     Returns SOME (var_name, start_nat, bound_nat, body) or NONE *)
  and try_bounded_for (CFor0 (Right init_decl, Some cond, Some step, body, _)) =
        (case (init_decl, cond, step) of
           (CDecl0 (_, [((Some declr, Some (CInitExpr0 (init_expr, _))), _)], _),
            CBinary0 (CLeOp0, CVar0 (cond_var, _), bound_expr, _),
            CUnary0 (CPostIncOp0, CVar0 (step_var, _), _)) =>
             let val var_name = C_Ast_Utils.declr_name declr
                 val cond_name = C_Ast_Utils.ident_name cond_var
                 val step_name = C_Ast_Utils.ident_name step_var
             in
               if var_name = cond_name andalso var_name = step_name
               then SOME (var_name, init_expr, bound_expr, body)
               else NONE
             end
         | _ => NONE)
    | try_bounded_for _ = NONE

  and translate_stmt tctx (CCompound0 (_, items, _)) =
        translate_compound_items tctx items
    | translate_stmt _ (CReturn0 (None, _)) =
        C_Term_Build.mk_return_func C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CReturn0 (Some expr, _)) =
        C_Term_Build.mk_return_func (translate_expr tctx expr)
    | translate_stmt tctx (CExpr0 (Some expr, _)) =
        translate_expr tctx expr
    | translate_stmt _ (CExpr0 (None, _)) =
        C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CIf0 (cond, then_br, Some else_br, _)) =
        C_Term_Build.mk_two_armed_cond
          (translate_expr tctx cond) (translate_stmt tctx then_br) (translate_stmt tctx else_br)
    | translate_stmt tctx (CIf0 (cond, then_br, None, _)) =
        C_Term_Build.mk_two_armed_cond
          (translate_expr tctx cond) (translate_stmt tctx then_br) C_Term_Build.mk_literal_unit
    | translate_stmt tctx (stmt as CFor0 _) =
        (case try_bounded_for stmt of
           SOME (var_name, init_c_expr, bound_c_expr, body) =>
             let val start_nat = translate_pure_nat_expr tctx init_c_expr
                 val bound_nat = translate_pure_nat_expr tctx bound_c_expr
                 val loop_var = Isa_Free (var_name, isa_dummyT)
                 val tctx' = C_Trans_Ctxt.add_var var_name C_Trans_Ctxt.Param loop_var tctx
                 val body_term = translate_stmt tctx' body
                 val range = C_Term_Build.mk_upt_int_range start_nat bound_nat
             in C_Term_Build.mk_raw_for_loop range (Term.lambda loop_var body_term) end
         | NONE => unsupported "non-standard for loop")
    | translate_stmt _ (CWhile0 _) =
        (warning "micro_c_translate: while loop replaced with stub"; C_Term_Build.mk_while_stub)
    | translate_stmt _ (CSwitch0 _) =
        (warning "micro_c_translate: switch statement replaced with stub"; C_Term_Build.mk_unsupported_stub)
    | translate_stmt _ (CGoto0 _) =
        (warning "micro_c_translate: goto replaced with stub"; C_Term_Build.mk_goto_stub)
    | translate_stmt tctx (CLabel0 (_, stmt, _, _)) =
        (warning "micro_c_translate: label ignored, translating labeled statement";
         translate_stmt tctx stmt)
    | translate_stmt _ (CCont0 _) =
        (warning "micro_c_translate: continue replaced with stub"; C_Term_Build.mk_unsupported_stub)
    | translate_stmt _ (CBreak0 _) =
        (warning "micro_c_translate: break replaced with stub"; C_Term_Build.mk_unsupported_stub)
    | translate_stmt _ _ =
        (warning "micro_c_translate: unknown statement replaced with stub"; C_Term_Build.mk_unsupported_stub)

  fun translate_fundef ctxt (CFunDef0 (_, declr, _, body, _)) =
    let
      val name = C_Ast_Utils.declr_name declr
      val param_names = C_Ast_Utils.extract_params declr
      (* Create free variables for each parameter *)
      val param_vars = List.map (fn n => (n, Isa_Free (n, isa_dummyT))) param_names
      (* Add parameters to the translation context as Param (by-value) *)
      val tctx = List.foldl
        (fn ((n, v), ctx) => C_Trans_Ctxt.add_var n C_Trans_Ctxt.Param v ctx)
        (C_Trans_Ctxt.make ctxt) param_vars
      val body_term = translate_stmt tctx body
      val fn_term = C_Term_Build.mk_function_body body_term
      (* Wrap in lambdas for each parameter *)
      val fn_term = List.foldr
        (fn ((_, v), t) => Term.lambda v t)
        fn_term param_vars
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
    in
      (* Translate and define each function one at a time, so that later
         functions can reference earlier ones via Syntax.check_term. *)
      List.foldl (fn (fundef, lthy) =>
        let val (name, term) = C_Translate.translate_fundef lthy fundef
        in define_c_function name term lthy end) lthy fundefs
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

subsection \<open>Smoke Tests\<close>

text \<open>Verify the command works end-to-end.\<close>

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

text \<open>Test variable declaration, assignment, and arithmetic.\<close>

micro_c_translate \<open>
void h(void) {
  int x = 5;
  x = x + 1;
}
\<close>

thm c_h_def


text \<open>Test if/else translation.\<close>

micro_c_translate \<open>
int max_c(int a, int b) {
  if (a > b) {
    return a;
  } else {
    return b;
  }
}
\<close>

thm c_max_c_def
text \<open>Test function calls: a function that calls another.\<close>

micro_c_translate \<open>
int add(int a, int b) {
  return a + b;
}
\<close>

micro_c_translate \<open>
int add_three(int x, int y, int z) {
  return add(add(x, y), z);
}
\<close>

thm c_add_def c_add_three_def

text \<open>Test bounded for-loop translation.\<close>

micro_c_translate \<open>
void loop_test(int n) {
  int s = 0;
  for (int i = 0; i < n; i++) {
    s = s + i;
  }
}
\<close>

thm c_loop_test_def

micro_c_translate \<open>
void loop_literal(void) {
  int s = 0;
  for (int i = 0; i < 5; i++) {
    s = s + i;
  }
}
\<close>

thm c_loop_literal_def

text \<open>Smoke test: while loop should produce a stub constant (no error, just gets stuck).\<close>
micro_c_translate \<open>
void while_test(int n) {
  int x = 0;
  while (x < n) {
    x = x + 1;
  }
}
\<close>

thm c_while_test_def

text \<open>Smoke test: pointer dereference and assignment (swap function).\<close>
micro_c_translate \<open>
void swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}
\<close>

thm c_swap_def

end
