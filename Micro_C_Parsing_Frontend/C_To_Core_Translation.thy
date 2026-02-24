(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)



theory C_To_Core_Translation
  imports
    Micro_C_Syntax
    "Shallow_Micro_Rust.Core_Expression"
    "Shallow_Micro_Rust.Core_Syntax"
    "Shallow_Micro_Rust.Bool_Type"
    "Shallow_Micro_Rust.Rust_Iterator"
    "Shallow_Micro_C.C_Numeric_Types"
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
  datatype c_numeric_type = CInt | CUInt | CChar | CSChar
                          | CShort | CUShort | CLong | CULong | CBool
  val is_signed : c_numeric_type -> bool
  val is_bool : c_numeric_type -> bool
  val hol_type_of : c_numeric_type -> typ
  val type_name_of : c_numeric_type -> string
  val resolve_c_type : C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list -> c_numeric_type option
  val decl_type : C_Ast.nodeInfo C_Ast.cDeclaration -> c_numeric_type option
  val param_type : C_Ast.nodeInfo C_Ast.cDeclaration -> c_numeric_type option
  val is_pointer_param : C_Ast.nodeInfo C_Ast.cDeclaration -> bool
  val abr_string_to_string : C_Ast.abr_string -> string
  val ident_name : C_Ast.ident -> string
  val declr_name : C_Ast.nodeInfo C_Ast.cDeclarator -> string
  val extract_params : C_Ast.nodeInfo C_Ast.cDeclarator -> string list
  val extract_param_decls : C_Ast.nodeInfo C_Ast.cDeclarator
                            -> C_Ast.nodeInfo C_Ast.cDeclaration list
  val param_name : C_Ast.nodeInfo C_Ast.cDeclaration -> string option
  val extract_struct_type_from_decl : C_Ast.nodeInfo C_Ast.cDeclaration -> string option
  val extract_struct_defs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                            -> (string * string list) list
  val extract_enum_defs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                          -> (string * int) list
  val extract_typedefs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                         -> (string * c_numeric_type) list
  val resolve_c_type_full : c_numeric_type Symtab.table
                            -> C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list
                            -> c_numeric_type option
  val extract_fundefs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                        -> C_Ast.nodeInfo C_Ast.cFunctionDef list
end =
struct
  open C_Ast

  (* ----- Resolved C numeric type representation ----- *)

  datatype c_numeric_type = CInt | CUInt | CChar | CSChar
                          | CShort | CUShort | CLong | CULong | CBool

  fun is_signed CInt   = true
    | is_signed CSChar  = true
    | is_signed CShort  = true
    | is_signed CLong   = true
    | is_signed _       = false

  fun is_bool CBool = true
    | is_bool _     = false

  fun hol_type_of CBool   = @{typ bool}
    | hol_type_of CInt    = \<^typ>\<open>c_int\<close>
    | hol_type_of CUInt   = \<^typ>\<open>c_uint\<close>
    | hol_type_of CChar   = \<^typ>\<open>c_char\<close>
    | hol_type_of CSChar   = \<^typ>\<open>c_schar\<close>
    | hol_type_of CShort  = \<^typ>\<open>c_short\<close>
    | hol_type_of CUShort = \<^typ>\<open>c_ushort\<close>
    | hol_type_of CLong   = \<^typ>\<open>c_long\<close>
    | hol_type_of CULong  = \<^typ>\<open>c_ulong\<close>

  fun type_name_of CBool   = "_Bool"
    | type_name_of CInt    = "int"
    | type_name_of CUInt   = "unsigned int"
    | type_name_of CChar   = "char"
    | type_name_of CSChar   = "signed char"
    | type_name_of CShort  = "short"
    | type_name_of CUShort = "unsigned short"
    | type_name_of CLong   = "long"
    | type_name_of CULong  = "unsigned long"

  (* Parse a list of C declaration specifiers into a resolved numeric type.
     Returns NONE for void, struct types, and other non-numeric specifiers. *)
  fun resolve_c_type specs =
    (* _Bool is a distinct type in C — handle it before the accumulator.
       It cannot combine with signed/unsigned/short/long specifiers. *)
    if List.exists (fn CTypeSpec0 (CBoolType0 _) => true | _ => false) specs
    then SOME CBool
    else
    let
      fun accumulate (CTypeSpec0 (CSignedType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (true, us, ch, sh, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CUnsigType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, true, ch, sh, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CCharType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, true, sh, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CShortType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, ch, true, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CIntType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, ch, sh, true, lg, vd, st)
        | accumulate (CTypeSpec0 (CLongType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, ch, sh, it, true, vd, st)
        | accumulate (CTypeSpec0 (CVoidType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, ch, sh, it, lg, true, st)
        | accumulate (CTypeSpec0 (CSUType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, ch, sh, it, lg, vd, true)
        | accumulate (CTypeSpec0 (CEnumType0 _)) (sg, us, ch, sh, it, lg, vd, st) =
            (sg, us, ch, sh, true, lg, vd, st)  (* enum treated as int *)
        | accumulate _ flags = flags
      val (has_signed, has_unsigned, has_char, has_short, has_int, has_long, has_void, has_struct) =
        List.foldl (fn (spec, flags) => accumulate spec flags)
          (false, false, false, false, false, false, false, false) specs
    in
      if has_void orelse has_struct then NONE
      else if has_char then
        if has_unsigned then SOME CChar  (* unsigned char = c_char = 8 word *)
        else if has_signed then SOME CSChar
        else SOME CChar  (* plain char treated as unsigned, matching c_char = 8 word *)
      else if has_short then
        if has_unsigned then SOME CUShort
        else SOME CShort
      else if has_long then
        if has_unsigned then SOME CULong
        else SOME CLong
      else if has_unsigned then SOME CUInt
      else SOME CInt  (* int, signed, signed int, or bare specifiers *)
    end

  (* Extract numeric type from a declaration *)
  fun decl_type (CDecl0 (specs, _, _)) = resolve_c_type specs
    | decl_type _ = NONE

  (* Extract numeric type from a parameter declaration *)
  val param_type = decl_type

  (* Check if a parameter declaration has a pointer declarator (e.g. int *a, struct point *p) *)
  fun is_pointer_param (CDecl0 (_, [((Some (CDeclr0 (_, derived, _, _, _)), _), _)], _)) =
        List.exists (fn CPtrDeclr0 _ => true | _ => false) derived
    | is_pointer_param _ = false

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

  (* Extract the full parameter declarations (not just names) from a function declarator *)
  fun extract_param_decls (CDeclr0 (_, derived, _, _, _)) =
    (case List.find (fn CFunDeclr0 _ => true | _ => false) derived of
       SOME (CFunDeclr0 (Right (params, _), _, _)) => params
     | _ => [])

  (* Check if a declaration has a struct type specifier and return the struct name.
     E.g. for "struct point *p", returns SOME "point". *)
  fun extract_struct_type_from_decl (CDecl0 (specs, _, _)) =
        let fun find_struct [] = NONE
              | find_struct (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, _, _, _), _)) :: _) = SOME (ident_name ident)
              | find_struct (_ :: rest) = find_struct rest
        in find_struct specs end
    | extract_struct_type_from_decl _ = NONE

  (* Extract struct definitions (with member lists) from a top-level declaration.
     Returns SOME (struct_name, [field_name, ...]) for struct definitions. *)
  fun extract_struct_def_from_decl (CDecl0 (specs, _, _)) =
        let fun find_struct_def [] = NONE
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, Some members, _, _), _)) :: _) =
                  let val sname = ident_name ident
                      val field_names = List.mapPartial
                        (fn CDecl0 (_, [((Some declr, _), _)], _) =>
                              SOME (declr_name declr)
                          | _ => NONE)
                        members
                  in SOME (sname, field_names) end
              | find_struct_def (_ :: rest) = find_struct_def rest
        in find_struct_def specs end
    | extract_struct_def_from_decl _ = NONE

  (* Extract all struct definitions from a translation unit *)
  fun extract_struct_defs (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CDeclExt0 decl => extract_struct_def_from_decl decl | _ => NONE)
      ext_decls

  (* Extract enum constant definitions from a translation unit.
     Returns a flat list of (name, integer_value) pairs.
     Handles both explicit values and auto-incrementing. *)
  fun extract_enum_defs_from_spec (CTypeSpec0 (CEnumType0 (CEnum0 (_, Some enumerators, _, _), _))) =
        let fun process [] _ = []
              | process ((ident, Some (CConst0 (CIntConst0 (CInteger0 (n, _, _), _)))) :: rest) _ =
                  let val v = IntInf.toInt n
                  in (ident_name ident, v) :: process rest (v + 1) end
              | process ((ident, None) :: rest) next_val =
                  (ident_name ident, next_val) :: process rest (next_val + 1)
              | process (_ :: rest) next_val = process rest (next_val + 1)
        in process enumerators 0 end
    | extract_enum_defs_from_spec _ = []

  fun extract_enum_defs (CTranslUnit0 (ext_decls, _)) =
    let fun from_decl (CDeclExt0 (CDecl0 (specs, _, _))) =
              List.concat (List.map extract_enum_defs_from_spec specs)
          | from_decl _ = []
    in List.concat (List.map from_decl ext_decls) end

  (* Extract typedef mappings from a translation unit.
     A typedef declaration is CDecl0 with CStorageSpec0 (CTypedef0 _) in specifiers. *)
  fun extract_typedefs (CTranslUnit0 (ext_decls, _)) =
    let fun is_typedef_spec (CStorageSpec0 (CTypedef0 _)) = true
          | is_typedef_spec _ = false
        fun non_storage_spec (CStorageSpec0 _) = false
          | non_storage_spec _ = true
        fun extract (CDeclExt0 (CDecl0 (specs, [((Some declr, _), _)], _))) =
              if List.exists is_typedef_spec specs then
                let val name = declr_name declr
                    val type_specs = List.filter non_storage_spec specs
                in case resolve_c_type type_specs of
                     SOME cty => [(name, cty)]
                   | NONE => [] end
              else []
          | extract _ = []
    in List.concat (List.map extract ext_decls) end

  (* resolve_c_type with typedef resolution: check for CTypeDef0 first,
     then fall back to standard resolve_c_type *)
  fun resolve_c_type_full typedef_tab specs =
    case specs of
      [CTypeSpec0 (CTypeDef0 (ident, _))] =>
        (case Symtab.lookup typedef_tab (ident_name ident) of
           SOME cty => SOME cty
         | NONE => NONE)
    | _ => resolve_c_type specs

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
  val make : Proof.context -> string list Symtab.table
             -> int Symtab.table -> C_Ast_Utils.c_numeric_type Symtab.table -> t
  val get_ctxt : t -> Proof.context
  val add_var : string -> var_kind -> term -> C_Ast_Utils.c_numeric_type -> t -> t
  val lookup_var : t -> string -> (var_kind * term * C_Ast_Utils.c_numeric_type) option
  val set_struct_type : string -> string -> t -> t
  val get_struct_type : t -> string -> string option
  val get_struct_fields : t -> string -> string list option
  val lookup_enum_const : t -> string -> int option
  val add_enum_consts : (string * int) list -> t -> t
  val get_typedef_tab : t -> C_Ast_Utils.c_numeric_type Symtab.table
end =
struct
  datatype var_kind = Param | Local
  type t = {
    ctxt : Proof.context,
    vars : (var_kind * term * C_Ast_Utils.c_numeric_type) Symtab.table,
    struct_types : string Symtab.table,         (* var_name -> c_struct_name *)
    struct_fields : string list Symtab.table,   (* c_struct_name -> [field_name] *)
    enum_consts : int Symtab.table,             (* enum_name -> int_value *)
    typedef_tab : C_Ast_Utils.c_numeric_type Symtab.table  (* typedef_name -> c_numeric_type *)
  }

  fun make ctxt struct_fields enum_consts typedef_tab : t =
    { ctxt = ctxt, vars = Symtab.empty, struct_types = Symtab.empty,
      struct_fields = struct_fields, enum_consts = enum_consts,
      typedef_tab = typedef_tab }

  fun get_ctxt ({ ctxt, ... } : t) = ctxt

  fun add_var name kind tm cty ({ ctxt, vars, struct_types, struct_fields,
                                   enum_consts, typedef_tab } : t) : t =
    { ctxt = ctxt, vars = Symtab.update (name, (kind, tm, cty)) vars,
      struct_types = struct_types, struct_fields = struct_fields,
      enum_consts = enum_consts, typedef_tab = typedef_tab }

  fun lookup_var ({ vars, ... } : t) name =
    Symtab.lookup vars name

  fun set_struct_type var_name struct_name
      ({ ctxt, vars, struct_types, struct_fields, enum_consts, typedef_tab } : t) : t =
    { ctxt = ctxt, vars = vars,
      struct_types = Symtab.update (var_name, struct_name) struct_types,
      struct_fields = struct_fields, enum_consts = enum_consts,
      typedef_tab = typedef_tab }

  fun get_struct_type ({ struct_types, ... } : t) name =
    Symtab.lookup struct_types name

  fun get_struct_fields ({ struct_fields, ... } : t) name =
    Symtab.lookup struct_fields name

  fun lookup_enum_const ({ enum_consts, ... } : t) name =
    Symtab.lookup enum_consts name

  fun add_enum_consts entries ({ ctxt, vars, struct_types, struct_fields,
                                 enum_consts, typedef_tab } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields,
      enum_consts = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                      enum_consts entries,
      typedef_tab = typedef_tab }

  fun get_typedef_tab ({ typedef_tab, ... } : t) = typedef_tab
end
\<close>

subsection \<open>Array Indexing Helper\<close>

text \<open>
  The @{text unat} function from the Word library is an abbreviation, not a logical
  constant, so it cannot be referenced via @{text "\<^const_name>"} in ML.
  We define a proper constant that wraps it.
\<close>

definition c_idx_to_nat :: \<open>'a::len word \<Rightarrow> nat\<close> where
  [simp]: \<open>c_idx_to_nat w = unat w\<close>

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
  val mk_literal_num : C_Ast_Utils.c_numeric_type -> int -> term
  val mk_literal_int : int -> term
  val mk_return_func : term -> term
  val mk_bind : term -> term -> term
  val mk_var_alloc : term -> term
  val mk_var_read : term -> term
  val mk_var_write : term -> term -> term
  val mk_bindlift2 : term -> term -> term -> term
  val mk_bind2 : term -> term -> term -> term
  val mk_two_armed_cond : term -> term -> term -> term
  val mk_one_armed_cond : term -> term -> term
  val mk_funcall : term -> term list -> term
  val mk_raw_for_loop : term -> term -> term
  val mk_upt_int_range : term -> term -> term
  val mk_deref : term -> term
  val mk_ptr_write : term -> term -> term
  val mk_struct_field_read : term -> term -> term
  val mk_struct_field_write : term -> term -> term -> term
  val mk_unat : term -> term
  val mk_focus_nth : term -> term -> term
  val mk_bounded_while : term -> term -> term -> term
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

  (* literal n, typed according to the given c_numeric_type *)
  fun mk_literal_num cty n =
    let val T = C_Ast_Utils.hol_type_of cty
    in Const (\<^const_name>\<open>literal\<close>, T --> dummyT) $ HOLogic.mk_number T n end

  (* literal n, where n is a C integer constant.
     Uses dummyT so Isabelle infers the correct word type from context
     (e.g. 32 sword in signed expressions, 32 word in unsigned). *)
  fun mk_literal_int n =
    Const (\<^const_name>\<open>literal\<close>, dummyT --> dummyT) $ HOLogic.mk_number dummyT n

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

  (* bind2 f e1 e2 : evaluate e1 and e2, then apply monadic f *)
  fun mk_bind2 f e1 e2 =
    Const (\<^const_name>\<open>bind2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
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

  (* Struct field read: dereference pointer, then extract field via accessor.
     Generates: bind (deref ptr_expr) (\<lambda>v. literal (accessor v)) *)
  fun mk_struct_field_read accessor_const ptr_expr =
    let val v = Free ("v__struct", dummyT)
    in mk_bind (mk_deref ptr_expr)
         (Term.lambda v (mk_literal (accessor_const $ v)))
    end

  (* Struct field write: evaluate rhs, dereference pointer, update field, write back.
     Generates: bind val_expr (\<lambda>rhs. bind (deref ptr) (\<lambda>v. ptr_write ptr (updater (\<lambda>_. rhs) v))) *)
  fun mk_struct_field_write updater_const ptr_expr val_expr =
    let val rhs_var = Free ("v__rhs", dummyT)
        val struct_var = Free ("v__struct", dummyT)
        val dummy_var = Free ("_uu__", dummyT)
        val updated = updater_const $ (Term.lambda dummy_var rhs_var) $ struct_var
    in mk_bind val_expr (Term.lambda rhs_var
         (mk_bind (mk_deref ptr_expr) (Term.lambda struct_var
           (mk_ptr_write ptr_expr (mk_literal updated)))))
    end

  (* c_idx_to_nat idx : convert word to nat for array indexing (wraps unat) *)
  fun mk_unat idx_term =
    Const (\<^const_name>\<open>c_idx_to_nat\<close>, dummyT --> dummyT) $ idx_term

  (* focus_focused (nth_focus idx_nat) ref_term : focus reference to nth element *)
  fun mk_focus_nth idx_nat ref_term =
    Const (\<^const_name>\<open>focus_focused\<close>, dummyT --> dummyT --> dummyT)
      $ (Const (\<^const_name>\<open>nth_focus\<close>, dummyT --> dummyT) $ idx_nat)
      $ ref_term

  (* bounded_while fuel cond body *)
  fun mk_bounded_while fuel cond body =
    Const (\<^const_name>\<open>bounded_while\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ fuel $ cond $ body

  (* Stub constants for unsupported C constructs *)
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
  val translate_fundef : string list Symtab.table -> int Symtab.table
                         -> C_Ast_Utils.c_numeric_type Symtab.table
                         -> Proof.context
                         -> C_Ast.nodeInfo C_Ast.cFunctionDef -> string * term
end =
struct
  (* Save Isabelle term constructors before C_Ast shadows them *)
  val Isa_Const = Const
  val Isa_Free = Free
  val isa_dummyT = dummyT
  val Isa_add_frees = Term.add_frees

  (* Binary operator classification: monadic operators (arithmetic/comparison)
     return expressions and need bind2; pure operators (logical) return plain
     values and use bindlift2.
     NB: Must be defined before 'open C_Ast' which shadows the term type. *)
  datatype binop_kind = Monadic of term | Pure of term

  open C_Ast

  fun unsupported construct =
    error ("micro_c_translate: unsupported C construct: " ^ construct)

  (* Translate a C binary operator to a HOL function constant, dispatching
     signed vs unsigned based on the operand type.
     Arithmetic and comparison operations use the overflow-checked C operations
     from C_Numeric_Types which are monadic (they can abort).
     Logical operators remain pure and type-independent. *)
  fun translate_binop cty CAddOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
    | translate_binop cty CSubOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
    | translate_binop cty CMulOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_mul\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_mul\<close>, isa_dummyT))
    | translate_binop cty CDivOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_div\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_div\<close>, isa_dummyT))
    | translate_binop cty CRmdOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_mod\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_mod\<close>, isa_dummyT))
    | translate_binop cty CLeOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_less\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_less\<close>, isa_dummyT))
    | translate_binop cty CLeqOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_le\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_le\<close>, isa_dummyT))
    | translate_binop cty CGrOp0 =  (* reversed operands *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_less\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_less\<close>, isa_dummyT))
    | translate_binop cty CGeqOp0 =  (* reversed operands *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_le\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_le\<close>, isa_dummyT))
    | translate_binop cty CEqOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_eq\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_eq\<close>, isa_dummyT))
    | translate_binop cty CNeqOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_neq\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_neq\<close>, isa_dummyT))
    | translate_binop _ CLndOp0 = Pure (Isa_Const (\<^const_name>\<open>conj\<close>, isa_dummyT))
    | translate_binop _ CLorOp0 = Pure (Isa_Const (\<^const_name>\<open>disj\<close>, isa_dummyT))
    | translate_binop cty CAndOp0 = (* bitwise AND *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_and\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_and\<close>, isa_dummyT))
    | translate_binop cty CXorOp0 = (* bitwise XOR *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_xor\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_xor\<close>, isa_dummyT))
    | translate_binop cty COrOp0 = (* bitwise OR *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_or\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_or\<close>, isa_dummyT))
    | translate_binop cty CShlOp0 = (* left shift *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_shl\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_shl\<close>, isa_dummyT))
    | translate_binop cty CShrOp0 = (* right shift *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_shr\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_shr\<close>, isa_dummyT))
    | translate_binop _ _ = unsupported "binary operator"

  (* Determine the C struct type of a variable expression.
     Only handles simple variable references for now. *)
  fun determine_struct_type tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.get_struct_type tctx name of
             SOME sname => sname
           | NONE => error ("micro_c_translate: cannot determine struct type for: " ^ name)
        end
    | determine_struct_type _ _ =
        error "micro_c_translate: struct member access on complex expression not yet supported"

  (* Resolve a struct field accessor/updater constant by name convention.
     Convention: struct "point" field "x" -> accessor "c_point_x", updater "update_c_point_x" *)
  fun resolve_const ctxt name =
    let val (full_name, _) = Term.dest_Const
          (Proof_Context.read_const {proper = true, strict = false} ctxt name)
    in Isa_Const (full_name, isa_dummyT) end

  (* Helper for pre/post increment/decrement on local variables.
     is_inc: true for increment, false for decrement
     is_pre: true for pre (return new), false for post (return old) *)
  fun translate_inc_dec tctx is_inc is_pre (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, ref_var, cty) =>
               let val old_var = Isa_Free ("v__old", isa_dummyT)
                   val new_var = Isa_Free ("v__new", isa_dummyT)
                   val one = C_Term_Build.mk_literal_num cty 1
                   val arith_const =
                     if is_inc then
                       (if C_Ast_Utils.is_signed cty
                        then Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT)
                        else Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
                     else
                       (if C_Ast_Utils.is_signed cty
                        then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
                        else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
                   val read = C_Term_Build.mk_var_read ref_var
                   val add = C_Term_Build.mk_bind2 arith_const
                               (C_Term_Build.mk_literal old_var) one
                   val write = C_Term_Build.mk_var_write ref_var
                                 (C_Term_Build.mk_literal new_var)
                   val return_var = if is_pre then new_var else old_var
               in (C_Term_Build.mk_bind read (Term.lambda old_var
                    (C_Term_Build.mk_bind add (Term.lambda new_var
                      (C_Term_Build.mk_sequence write
                        (C_Term_Build.mk_literal return_var))))), cty) end
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               error ("micro_c_translate: cannot increment/decrement parameter: " ^ name)
           | NONE => error ("micro_c_translate: undefined variable: " ^ name)
        end
    | translate_inc_dec _ _ _ _ =
        unsupported "increment/decrement on non-variable expression"

  (* translate_expr returns (term * c_numeric_type).
     The type tracks the C type of the expression for binary operator dispatch.
     CInt is used as default when the actual type is unknown/irrelevant. *)
  fun translate_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        (C_Term_Build.mk_literal_int (IntInf.toInt n), C_Ast_Utils.CInt)
    | translate_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, var, cty) => (C_Term_Build.mk_literal var, cty)
           | SOME (C_Trans_Ctxt.Local, var, cty) => (C_Term_Build.mk_var_read var, cty)
           | NONE =>
               (* Fallback: check enum constants *)
               (case C_Trans_Ctxt.lookup_enum_const tctx name of
                  SOME value => (C_Term_Build.mk_literal_int value, C_Ast_Utils.CInt)
                | NONE => error ("micro_c_translate: undefined variable: " ^ name))
        end
    | translate_expr tctx (CBinary0 (binop, lhs, rhs, _)) =
        let val (lhs', lhs_cty) = translate_expr tctx lhs
            val (rhs', rhs_cty) = translate_expr tctx rhs
            (* C usual arithmetic conversion: if either operand is unsigned,
               use unsigned dispatch.  This handles integer literals (which
               default to CInt) mixed with unsigned variables. *)
            val cty = if lhs_cty = C_Ast_Utils.CUInt orelse rhs_cty = C_Ast_Utils.CUInt
                      then C_Ast_Utils.CUInt else lhs_cty
            (* For > and >=, swap operands to use < and <= *)
            val (l, r) = case binop of CGrOp0 => (rhs', lhs')
                                     | CGeqOp0 => (rhs', lhs')
                                     | _ => (lhs', rhs')
            (* Comparisons return CBool — they produce Isabelle bool values *)
            val result_cty = case binop of
                CLeOp0 => C_Ast_Utils.CBool | CLeqOp0 => C_Ast_Utils.CBool
              | CGrOp0 => C_Ast_Utils.CBool | CGeqOp0 => C_Ast_Utils.CBool
              | CEqOp0 => C_Ast_Utils.CBool | CNeqOp0 => C_Ast_Utils.CBool
              | _ => cty
        in case translate_binop cty binop of
             Monadic f => (C_Term_Build.mk_bind2 f l r, result_cty)
           | Pure f => (C_Term_Build.mk_bindlift2 f l r, result_cty)
        end
    (* p->field = rhs : struct field write through pointer *)
    | translate_expr tctx (CAssign0 (CAssignOp0, CMember0 (expr, field_ident, true, _), rhs, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val updater_name = "update_c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val updater_const = resolve_const ctxt updater_name
            val (ptr_expr, _) = translate_expr tctx expr
            val (rhs', _) = translate_expr tctx rhs
        in (C_Term_Build.mk_struct_field_write updater_const ptr_expr rhs', C_Ast_Utils.CInt) end
    (* arr[idx] = rhs : array element write via focus *)
    | translate_expr tctx (CAssign0 (CAssignOp0, CIndex0 (arr_expr, idx_expr, _), rhs, _)) =
        let val (arr_term, _) = translate_expr tctx arr_expr
            val (idx_term, _) = translate_expr tctx idx_expr
            val (rhs_term, _) = translate_expr tctx rhs
            val a_var = Isa_Free ("v__arr", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val v_var = Isa_Free ("v__rhs", isa_dummyT)
            val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) a_var
        in (C_Term_Build.mk_bind rhs_term (Term.lambda v_var
             (C_Term_Build.mk_bind arr_term (Term.lambda a_var
               (C_Term_Build.mk_bind idx_term (Term.lambda i_var
                 (C_Term_Build.mk_ptr_write
                   (C_Term_Build.mk_literal focused)
                   (C_Term_Build.mk_literal v_var))))))), C_Ast_Utils.CInt)
        end
    | translate_expr tctx (CAssign0 (CAssignOp0, CVar0 (ident, _), rhs, _)) =
        let val name = C_Ast_Utils.ident_name ident
            val (rhs', _) = translate_expr tctx rhs
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, var, cty) =>
               (C_Term_Build.mk_var_write var rhs', cty)
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               error ("micro_c_translate: assignment to parameter: " ^ name)
           | NONE => error ("micro_c_translate: undefined variable: " ^ name)
        end
    | translate_expr tctx (CAssign0 (CAssignOp0, CUnary0 (CIndOp0, lhs, _), rhs, _)) =
        (* *p = v : write through pointer *)
        let val (lhs', _) = translate_expr tctx lhs
            val (rhs', _) = translate_expr tctx rhs
        in (C_Term_Build.mk_ptr_write lhs' rhs', C_Ast_Utils.CInt) end
    | translate_expr tctx (CAssign0 (asgn_op, CVar0 (ident, _), rhs, _)) =
        (* Compound assignment: x op= rhs -> read x, compute (x op rhs), write x, return new *)
        let fun compound_assign_to_binop CAddAssOp0 = SOME CAddOp0
              | compound_assign_to_binop CSubAssOp0 = SOME CSubOp0
              | compound_assign_to_binop CMulAssOp0 = SOME CMulOp0
              | compound_assign_to_binop CDivAssOp0 = SOME CDivOp0
              | compound_assign_to_binop CRmdAssOp0 = SOME CRmdOp0
              | compound_assign_to_binop CShlAssOp0 = SOME CShlOp0
              | compound_assign_to_binop CShrAssOp0 = SOME CShrOp0
              | compound_assign_to_binop CAndAssOp0 = SOME CAndOp0
              | compound_assign_to_binop CXorAssOp0 = SOME CXorOp0
              | compound_assign_to_binop COrAssOp0  = SOME COrOp0
              | compound_assign_to_binop _ = NONE
        in case compound_assign_to_binop asgn_op of
             SOME binop =>
               let val name = C_Ast_Utils.ident_name ident
                   val (rhs', _) = translate_expr tctx rhs
               in case C_Trans_Ctxt.lookup_var tctx name of
                    SOME (C_Trans_Ctxt.Local, var, cty) =>
                      let val old_var = Isa_Free ("v__old", isa_dummyT)
                          val new_var = Isa_Free ("v__new", isa_dummyT)
                      in case translate_binop cty binop of
                           Monadic f =>
                             (C_Term_Build.mk_bind (C_Term_Build.mk_var_read var)
                               (Term.lambda old_var
                                 (C_Term_Build.mk_bind
                                   (C_Term_Build.mk_bind2 f
                                     (C_Term_Build.mk_literal old_var) rhs')
                                   (Term.lambda new_var
                                     (C_Term_Build.mk_sequence
                                       (C_Term_Build.mk_var_write var
                                         (C_Term_Build.mk_literal new_var))
                                       (C_Term_Build.mk_literal new_var))))), cty)
                         | _ => unsupported "pure compound assignment"
                      end
                  | _ => unsupported "compound assignment to non-local variable"
               end
           | NONE => unsupported "compound assignment or non-variable lhs"
        end
    | translate_expr _ (CAssign0 _) =
        unsupported "non-variable lhs in assignment"
    | translate_expr tctx (CCall0 (CVar0 (ident, _), args, _)) =
        let val fname = C_Ast_Utils.ident_name ident
            val arg_terms = List.map (fn a => #1 (translate_expr tctx a)) args
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            (* Look up the fully qualified constant name, then use dummyT
               so Syntax.check_term can infer the type. *)
            val (full_name, _) = Term.dest_Const
              (Proof_Context.read_const {proper = true, strict = false} ctxt ("c_" ^ fname))
            val func_ref = Isa_Const (full_name, isa_dummyT)
        in (C_Term_Build.mk_funcall func_ref arg_terms, C_Ast_Utils.CInt) end
    | translate_expr _ (CCall0 _) =
        unsupported "indirect function call (function pointers)"
    | translate_expr tctx (CUnary0 (CIndOp0, expr, _)) =
        (* *p : dereference pointer. Propagate the underlying type so that
           e.g. dereffing an unsigned int* yields CUInt for operator dispatch. *)
        let val (expr', cty) = translate_expr tctx expr
        in (C_Term_Build.mk_deref expr', cty) end
    | translate_expr tctx (CUnary0 (CCompOp0, expr, _)) =
        (* ~x : bitwise complement *)
        let val (expr', cty) = translate_expr tctx expr
            val not_const =
              if C_Ast_Utils.is_signed cty
              then Isa_Const (\<^const_name>\<open>c_signed_not\<close>, isa_dummyT)
              else Isa_Const (\<^const_name>\<open>c_unsigned_not\<close>, isa_dummyT)
            val v = Isa_Free ("v__comp", isa_dummyT)
        in (C_Term_Build.mk_bind expr' (Term.lambda v (not_const $ v)), cty) end
    | translate_expr tctx (CUnary0 (CMinOp0, expr, _)) =
        (* -x : unary minus, translate as 0 - x *)
        let val (expr', cty) = translate_expr tctx expr
            val zero = C_Term_Build.mk_literal_num cty 0
            val sub_const =
              if C_Ast_Utils.is_signed cty
              then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
              else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT)
        in (C_Term_Build.mk_bind2 sub_const zero expr', cty) end
    | translate_expr tctx (CUnary0 (CPreIncOp0, expr, _)) =
        translate_inc_dec tctx true true expr
    | translate_expr tctx (CUnary0 (CPostIncOp0, expr, _)) =
        translate_inc_dec tctx true false expr
    | translate_expr tctx (CUnary0 (CPreDecOp0, expr, _)) =
        translate_inc_dec tctx false true expr
    | translate_expr tctx (CUnary0 (CPostDecOp0, expr, _)) =
        translate_inc_dec tctx false false expr
    | translate_expr tctx (CUnary0 (CPlusOp0, expr, _)) =
        (* +x : unary plus is identity in C *)
        translate_expr tctx expr
    | translate_expr tctx (CUnary0 (CNegOp0, expr, _)) =
        (* !x : logical NOT *)
        let val (expr', cty) = translate_expr tctx expr
        in if C_Ast_Utils.is_bool cty then
             (* Bool: bind expr (\<lambda>v. literal (Not v)) *)
             let val v = Isa_Free ("v__neg", isa_dummyT)
             in (C_Term_Build.mk_bind expr'
                   (Term.lambda v
                     (C_Term_Build.mk_literal
                       (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT) $ v))),
                 C_Ast_Utils.CBool) end
           else
             (* Word: translate as x == 0 *)
             let val zero = C_Term_Build.mk_literal_num cty 0
                 val eq_const =
                   if C_Ast_Utils.is_signed cty
                   then Isa_Const (\<^const_name>\<open>c_signed_eq\<close>, isa_dummyT)
                   else Isa_Const (\<^const_name>\<open>c_unsigned_eq\<close>, isa_dummyT)
             in (C_Term_Build.mk_bind2 eq_const expr' zero, C_Ast_Utils.CBool) end
        end
    | translate_expr _ (CUnary0 _) =
        unsupported "unary expression"
    (* arr[idx] : deref whole list, then index with nth.
       We resolve dereference_fun from the locale context instead of using
       store_dereference_const, which has ambiguous adhoc overloading
       (dereference_fun vs ro_dereference_fun) for read-only references. *)
    | translate_expr tctx (CIndex0 (arr_expr, idx_expr, _)) =
        let val (arr_term, _) = translate_expr tctx arr_expr
            val (idx_term, _) = translate_expr tctx idx_expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            (* Resolve dereference_fun from locale context to avoid adhoc
               overloading ambiguity; fall back to store_dereference_const
               when outside a reference locale (e.g. smoke tests). *)
            val deref_const =
              resolve_const ctxt "dereference_fun"
              handle ERROR _ =>
                Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
            val a_var = Isa_Free ("v__arr", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val list_var = Isa_Free ("v__list", isa_dummyT)
            val nth_term = Isa_Const (\<^const_name>\<open>nth\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                             $ list_var $ (C_Term_Build.mk_unat i_var)
            (* bind (literal a) (deep_compose1 call dereference_fun) — same structure
               as mk_deref but with the resolved constant *)
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ a_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
        in (C_Term_Build.mk_bind arr_term (Term.lambda a_var
             (C_Term_Build.mk_bind idx_term (Term.lambda i_var
               (C_Term_Build.mk_bind deref_expr
                 (Term.lambda list_var
                   (C_Term_Build.mk_literal nth_term)))))), C_Ast_Utils.CInt)
        end
    (* p->field : struct field read through pointer *)
    | translate_expr tctx (CMember0 (expr, field_ident, true, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_const ctxt accessor_name
            val (ptr_expr, _) = translate_expr tctx expr
        in (C_Term_Build.mk_struct_field_read accessor_const ptr_expr, C_Ast_Utils.CInt) end
    (* s.field : direct struct member access via value *)
    | translate_expr tctx (CMember0 (expr, field_ident, false, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_const ctxt accessor_name
            val (struct_expr, _) = translate_expr tctx expr
            val v = Isa_Free ("v__struct", isa_dummyT)
        in (C_Term_Build.mk_bind struct_expr
              (Term.lambda v (C_Term_Build.mk_literal (accessor_const $ v))),
            C_Ast_Utils.CInt) end
    | translate_expr tctx (CCond0 (cond, Some then_expr, else_expr, _)) =
        (* x ? y : z — ternary conditional *)
        let val (then', then_cty) = translate_expr tctx then_expr
            val (else', _) = translate_expr tctx else_expr
        in (C_Term_Build.mk_two_armed_cond (ensure_bool_cond tctx cond) then' else', then_cty) end
    | translate_expr tctx (CCond0 (cond, None, else_expr, _)) =
        (* GNU extension: x ?: y means x ? x : y *)
        let val cond_bool = ensure_bool_cond tctx cond
            val (else', _) = translate_expr tctx else_expr
        in (C_Term_Build.mk_two_armed_cond cond_bool cond_bool else',
            C_Ast_Utils.CBool) end
    | translate_expr _ (CConst0 (CCharConst0 (CChar0 (c, _), _))) =
        (* Character literal — convert to ASCII ordinal *)
        (C_Term_Build.mk_literal_num C_Ast_Utils.CChar (IntInf.toInt (integer_of_char c)),
         C_Ast_Utils.CChar)
    | translate_expr tctx (CComma0 ([], _)) =
        (C_Term_Build.mk_literal_unit, C_Ast_Utils.CInt)
    | translate_expr tctx (CComma0 (exprs, _)) =
        let val translated = List.map (translate_expr tctx) exprs
            fun fold_comma [] = error "micro_c_translate: empty comma expression"
              | fold_comma [(e, ty)] = (e, ty)
              | fold_comma ((e, _) :: rest) =
                  let val (rest_e, rest_ty) = fold_comma rest
                  in (C_Term_Build.mk_sequence e rest_e, rest_ty) end
        in fold_comma translated end
    (* (target_type)expr : type cast *)
    | translate_expr tctx (CCast0 (target_decl, source_expr, _)) =
        let val (source_term, source_cty) = translate_expr tctx source_expr
            val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val target_cty = case C_Ast_Utils.resolve_c_type_full typedef_tab
                                    (case target_decl of CDecl0 (specs, _, _) => specs
                                                        | _ => []) of
                               SOME ct => ct | NONE => unsupported "cast to non-numeric type"
        in if source_cty = target_cty
           then (source_term, target_cty)
           else let val cast_const =
                      if C_Ast_Utils.is_signed source_cty
                      then Isa_Const (\<^const_name>\<open>c_scast\<close>, isa_dummyT)
                      else Isa_Const (\<^const_name>\<open>c_ucast\<close>, isa_dummyT)
                    val v = Isa_Free ("v__cast", isa_dummyT)
                in (C_Term_Build.mk_bind source_term
                      (Term.lambda v (cast_const $ v)), target_cty) end
        end
    | translate_expr _ _ =
        unsupported "expression"

  (* Convenience: extract just the term from translate_expr *)
  and expr_term tctx e = #1 (translate_expr tctx e)

  (* Ensure a C expression produces a bool condition.
     In C, any scalar value in a condition position is implicitly converted
     to bool via != 0. If the expression already produces CBool (from a
     comparison or _Bool variable), use it directly. Otherwise, wrap with
     bind expr (\<lambda>v. literal (v \<noteq> 0)). *)
  and ensure_bool_cond tctx cond_expr =
    let val (cond_term, cond_cty) = translate_expr tctx cond_expr
    in if C_Ast_Utils.is_bool cond_cty then cond_term
       else
         let val v = Isa_Free ("v__cond", isa_dummyT)
             val zero = Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT)
             val neq_term = Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                            $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT) $ v $ zero)
         in C_Term_Build.mk_bind cond_term
              (Term.lambda v (C_Term_Build.mk_literal neq_term))
         end
    end

  (* Extract variable declarations as a list of (name, init_term, cty) triples.
     Handles multiple declarators in a single CDecl0. *)
  fun translate_decl tctx (CDecl0 (specs, declarators, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val cty = (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                         SOME t => t | NONE => C_Ast_Utils.CInt)
            fun process_one ((Some declr, Some (CInitExpr0 (init, _))), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val (init', _) = translate_expr tctx init
                  in (name, init', cty) end
              | process_one ((Some declr, None), _) =
                  let val name = C_Ast_Utils.declr_name declr
                  in (name, C_Term_Build.mk_literal_num cty 0, cty) end
              | process_one _ = unsupported "complex declarator"
        in List.map process_one declarators end
    | translate_decl _ _ = unsupported "complex declaration"

  (* Translate a compound block, right-folding declarations into nested binds *)
  fun translate_compound_items _ [] = C_Term_Build.mk_literal_unit
    | translate_compound_items tctx [CBlockStmt0 stmt] = translate_stmt tctx stmt
    | translate_compound_items _ [CNestedFunDef0 _] =
        unsupported "nested function definition"
    | translate_compound_items tctx (CBlockDecl0 decl :: rest) =
        let val decls = translate_decl tctx decl
            fun fold_decls [] tctx' = translate_compound_items tctx' rest
              | fold_decls ((name, init_term, cty) :: ds) tctx' =
                  let val var = Isa_Free (name, isa_dummyT)
                      val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var cty tctx'
                  in C_Term_Build.mk_bind (C_Term_Build.mk_var_alloc init_term)
                       (Term.lambda var (fold_decls ds tctx'')) end
        in fold_decls decls tctx end
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
             SOME (C_Trans_Ctxt.Param, v, _) =>
               (* Convert parameter (word) to nat for range *)
               C_Term_Build.mk_unat v
           | _ => error ("micro_c_translate: loop bound must be a parameter or literal: " ^ name)
        end
    | translate_pure_nat_expr _ _ =
        error "micro_c_translate: unsupported loop bound expression"

  (* Try to recognize: for (int i = start; i < bound; i++) body
     Returns SOME (var_name, start_nat, bound_nat, body) or NONE *)
  and try_bounded_for (CFor0 (Right init_decl, Some cond, Some step, body, _)) =
        let fun step_var_name (CUnary0 (CPostIncOp0, CVar0 (v, _), _)) =
                  SOME (C_Ast_Utils.ident_name v)
              | step_var_name (CUnary0 (CPreIncOp0, CVar0 (v, _), _)) =
                  SOME (C_Ast_Utils.ident_name v)
              | step_var_name _ = NONE
        in case (init_decl, cond, step_var_name step) of
             (CDecl0 (_, [((Some declr, Some (CInitExpr0 (init_expr, _))), _)], _),
              CBinary0 (CLeOp0, CVar0 (cond_var, _), bound_expr, _),
              SOME step_name) =>
               let val var_name = C_Ast_Utils.declr_name declr
                   val cond_name = C_Ast_Utils.ident_name cond_var
               in
                 if var_name = cond_name andalso var_name = step_name
                 then SOME (var_name, init_expr, bound_expr, body)
                 else NONE
               end
           | _ => NONE
        end
    | try_bounded_for _ = NONE

  and translate_stmt tctx (CCompound0 (_, items, _)) =
        translate_compound_items tctx items
    | translate_stmt _ (CReturn0 (None, _)) =
        C_Term_Build.mk_return_func C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CReturn0 (Some expr, _)) =
        C_Term_Build.mk_return_func (expr_term tctx expr)
    | translate_stmt tctx (CExpr0 (Some expr, _)) =
        (* Expression statements are evaluated for side effects only.
           Discard the return value by sequencing with unit. *)
        C_Term_Build.mk_sequence (expr_term tctx expr) C_Term_Build.mk_literal_unit
    | translate_stmt _ (CExpr0 (None, _)) =
        C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CIf0 (cond, then_br, Some else_br, _)) =
        C_Term_Build.mk_two_armed_cond
          (ensure_bool_cond tctx cond) (translate_stmt tctx then_br) (translate_stmt tctx else_br)
    | translate_stmt tctx (CIf0 (cond, then_br, None, _)) =
        C_Term_Build.mk_two_armed_cond
          (ensure_bool_cond tctx cond) (translate_stmt tctx then_br) C_Term_Build.mk_literal_unit
    | translate_stmt tctx (stmt as CFor0 _) =
        (case try_bounded_for stmt of
           SOME (var_name, init_c_expr, bound_c_expr, body) =>
             let val start_nat = translate_pure_nat_expr tctx init_c_expr
                 val bound_nat = translate_pure_nat_expr tctx bound_c_expr
                 val loop_var = Isa_Free (var_name, isa_dummyT)
                 val tctx' = C_Trans_Ctxt.add_var var_name C_Trans_Ctxt.Param
                               loop_var C_Ast_Utils.CInt tctx
                 val body_term = translate_stmt tctx' body
                 val range = C_Term_Build.mk_upt_int_range start_nat bound_nat
             in C_Term_Build.mk_raw_for_loop range (Term.lambda loop_var body_term) end
         | NONE =>
             (* General for-loop: for(init; cond; step) body
                \<rightarrow> init; bounded_while fuel cond (sequence body step) *)
             let val CFor0 (init_part, cond_opt, step_opt, body, _) = stmt
                 val fuel_var = Isa_Free ("while_fuel", @{typ nat})
                 fun build_while tctx' =
                   let val cond_term = case cond_opt of
                             Some c => ensure_bool_cond tctx' c
                           | None => C_Term_Build.mk_literal (Isa_Const (\<^const_name>\<open>HOL.True\<close>, @{typ bool}))
                       val step_term = case step_opt of
                             Some s => C_Term_Build.mk_sequence
                                         (expr_term tctx' s) C_Term_Build.mk_literal_unit
                           | None => C_Term_Build.mk_literal_unit
                       val body_term = C_Term_Build.mk_sequence
                             (translate_stmt tctx' body) step_term
                   in C_Term_Build.mk_bounded_while fuel_var cond_term body_term end
             in case init_part of
                  Left init_expr_opt =>
                    let val init_term = case init_expr_opt of
                              Some e => expr_term tctx e
                            | None => C_Term_Build.mk_literal_unit
                    in C_Term_Build.mk_sequence init_term (build_while tctx) end
                | Right init_decl =>
                    let val decls = translate_decl tctx init_decl
                        fun fold_decls [] tctx' = build_while tctx'
                          | fold_decls ((name, init, cty) :: ds) tctx' =
                              let val var = Isa_Free (name, isa_dummyT)
                                  val tctx'' = C_Trans_Ctxt.add_var name
                                                 C_Trans_Ctxt.Local var cty tctx'
                              in C_Term_Build.mk_bind
                                   (C_Term_Build.mk_var_alloc init)
                                   (Term.lambda var (fold_decls ds tctx'')) end
                    in fold_decls decls tctx end
             end)
    | translate_stmt tctx (CWhile0 (cond, body, is_do_while, _)) =
        let val cond_term = ensure_bool_cond tctx cond
            val body_term = translate_stmt tctx body
            val fuel_var = Isa_Free ("while_fuel", @{typ nat})
            val while_term = C_Term_Build.mk_bounded_while fuel_var cond_term body_term
        in if is_do_while
           then C_Term_Build.mk_sequence body_term while_term
           else while_term
        end
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

  fun translate_fundef struct_tab enum_tab typedef_tab ctxt (CFunDef0 (specs, declr, _, body, _)) =
    let
      val name = C_Ast_Utils.declr_name declr
      val param_names = C_Ast_Utils.extract_params declr
      val param_decls = C_Ast_Utils.extract_param_decls declr
      (* Extract parameter types and pointer-ness from declarations.
         Use resolve_c_type_full so that typedef'd types (e.g. uint32) resolve
         correctly to their underlying C type for signed/unsigned dispatch. *)
      val param_info = List.map (fn pdecl =>
        let val cty = case pdecl of
                        CDecl0 (specs, _, _) =>
                          (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                             SOME t => t | NONE => C_Ast_Utils.CInt)
                      | _ => C_Ast_Utils.CInt
            val is_ptr = C_Ast_Utils.is_pointer_param pdecl
        in (cty, is_ptr) end) param_decls
      (* Pair names with type info; fall back to (CInt, false) if lengths differ *)
      val param_name_info = ListPair.zipEq (param_names, param_info)
        handle ListPair.UnequalLengths =>
          List.map (fn n => (n, (C_Ast_Utils.CInt, false))) param_names
      (* Create free variables for each parameter.
         Pointer params use dummyT (Isabelle infers reference types).
         Non-pointer params get explicit types for signed/unsigned dispatch. *)
      val param_vars = List.map (fn (n, (cty, is_ptr)) =>
        let val hol_ty = if is_ptr then isa_dummyT else C_Ast_Utils.hol_type_of cty
        in (n, Isa_Free (n, hol_ty), cty) end) param_name_info
      (* Add parameters to the translation context as Param (by-value) *)
      val tctx = List.foldl
        (fn ((n, v, cty), ctx) => C_Trans_Ctxt.add_var n C_Trans_Ctxt.Param v cty ctx)
        (C_Trans_Ctxt.make ctxt struct_tab enum_tab typedef_tab) param_vars
      (* Annotate struct pointer parameters with their struct type *)
      val tctx = List.foldl (fn (pdecl, ctx) =>
        case (C_Ast_Utils.param_name pdecl,
              C_Ast_Utils.extract_struct_type_from_decl pdecl) of
          (SOME n, SOME sn) => C_Trans_Ctxt.set_struct_type n sn ctx
        | _ => ctx) tctx param_decls
      val body_term = translate_stmt tctx body
      val fn_term = C_Term_Build.mk_function_body body_term
      (* Wrap in lambdas for each parameter *)
      val fn_term = List.foldr
        (fn ((_, v, _), t) => Term.lambda v t)
        fn_term param_vars
      (* Abstract while-loop fuel variables as additional parameters *)
      val fuel_frees = Isa_add_frees fn_term []
        |> List.filter (fn (n, _) => String.isPrefix "while_fuel" n)
        |> List.map (fn (n, ty) => Isa_Free (n, ty))
      val fn_term = List.foldr (fn (v, t) => Term.lambda v t) fn_term fuel_frees
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
      (* Extract struct definitions to build the struct field registry *)
      val struct_defs = C_Ast_Utils.extract_struct_defs tu
      val struct_tab = Symtab.make struct_defs
      val _ = List.app (fn (sname, fields) =>
        writeln ("Registered struct: " ^ sname ^ " with fields: " ^
                 String.concatWith ", " fields)) struct_defs
      (* Extract enum constant definitions *)
      val enum_defs = C_Ast_Utils.extract_enum_defs tu
      val enum_tab = Symtab.make enum_defs
      val _ = if null enum_defs then () else
        List.app (fn (name, value) =>
          writeln ("Registered enum constant: " ^ name ^ " = " ^
                   Int.toString value)) enum_defs
      (* Extract typedef mappings *)
      val typedef_defs = C_Ast_Utils.extract_typedefs tu
      val typedef_tab = Symtab.make typedef_defs
      val _ = if null typedef_defs then () else
        List.app (fn (name, _) =>
          writeln ("Registered typedef: " ^ name)) typedef_defs
      val fundefs = C_Ast_Utils.extract_fundefs tu
    in
      (* Translate and define each function one at a time, so that later
         functions can reference earlier ones via Syntax.check_term. *)
      List.foldl (fn (fundef, lthy) =>
        let val (name, term) = C_Translate.translate_fundef
              struct_tab enum_tab typedef_tab lthy fundef
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

text \<open>Smoke test: struct field access and assignment.\<close>
datatype_record c_point =
  c_point_x :: c_int
  c_point_y :: c_int

micro_c_translate \<open>
struct point {
  int x;
  int y;
};
void swap_fields(struct point *p) {
  int t = p->x;
  p->x = p->y;
  p->y = t;
}
\<close>

thm c_swap_fields_def

text \<open>Smoke test: array indexing read and write via focus.\<close>
micro_c_translate \<open>
int read_at(int *arr, int idx) {
  return arr[idx];
}
\<close>

thm c_read_at_def

micro_c_translate \<open>
void write_at(int *arr, int idx, int val) {
  arr[idx] = val;
}
\<close>

thm c_write_at_def

text \<open>Smoke test: unsigned int arithmetic uses @{const c_unsigned_add}.\<close>
micro_c_translate \<open>
unsigned int u_add(unsigned int a, unsigned int b) {
  return a + b;
}
\<close>

thm c_u_add_def

text \<open>Smoke test: long (64-bit signed) arithmetic uses @{const c_signed_add} at 64-bit type.\<close>
micro_c_translate \<open>
long l_add(long a, long b) {
  return a + b;
}
\<close>

thm c_l_add_def

text \<open>Smoke test: char identity function.\<close>
micro_c_translate \<open>
char identity_char(char c) {
  return c;
}
\<close>

thm c_identity_char_def

text \<open>Smoke test: unsigned comparison uses @{const c_unsigned_less}.\<close>
micro_c_translate \<open>
unsigned int u_max(unsigned int a, unsigned int b) {
  if (a > b) return a;
  else return b;
}
\<close>

thm c_u_max_def

text \<open>Smoke test: comma operator.\<close>
micro_c_translate \<open>
unsigned int comma_smoke(unsigned int a, unsigned int b) {
    unsigned int x = (a, b);
    return x;
}
\<close>

thm c_comma_smoke_def

text \<open>Smoke test: multiple declarations per statement.\<close>
micro_c_translate \<open>
unsigned int multi_decl_smoke(unsigned int a, unsigned int b) {
    unsigned int x = a, y = b;
    return x;
}
\<close>

thm c_multi_decl_smoke_def

text \<open>Smoke test: pre-increment.\<close>
micro_c_translate \<open>
void pre_inc_smoke(void) {
    unsigned int x = 0;
    unsigned int r = ++x;
}
\<close>

thm c_pre_inc_smoke_def

text \<open>Smoke test: post-increment.\<close>
micro_c_translate \<open>
void post_inc_smoke(void) {
    unsigned int x = 0;
    unsigned int r = x++;
}
\<close>

thm c_post_inc_smoke_def

text \<open>Smoke test: post-decrement.\<close>
micro_c_translate \<open>
void post_dec_smoke(void) {
    unsigned int x = 5;
    unsigned int r = x--;
}
\<close>

thm c_post_dec_smoke_def

text \<open>Smoke test: for loop with pre-increment (++i).\<close>
micro_c_translate \<open>
void loop_pre_inc(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    s = s + i;
  }
}
\<close>

thm c_loop_pre_inc_def

text \<open>Smoke test: not-equal operator.\<close>
micro_c_translate \<open>
unsigned int neq_test(unsigned int a, unsigned int b) {
  return a != b;
}
\<close>

thm c_neq_test_def

text \<open>Smoke test: logical NOT.\<close>
micro_c_translate \<open>
unsigned int not_test(unsigned int x) {
  if (!x) return 1; else return 0;
}
\<close>

thm c_not_test_def

text \<open>Smoke test: unary plus.\<close>
micro_c_translate \<open>
unsigned int uplus_test(unsigned int x) {
  return +x;
}
\<close>

thm c_uplus_test_def

text \<open>Smoke test: ternary conditional.\<close>
micro_c_translate \<open>
unsigned int ternary_test(unsigned int a, unsigned int b) {
  return (a > b) ? a : b;
}
\<close>

thm c_ternary_test_def

text \<open>Smoke test: character literal.\<close>
micro_c_translate \<open>
char char_test(char c) {
  return 'A';
}
\<close>

thm c_char_test_def

text \<open>Smoke test: compound add-assign.\<close>
micro_c_translate \<open>
unsigned int add_assign_test(unsigned int a, unsigned int b) {
  unsigned int x = a;
  x += b;
  return x;
}
\<close>

thm c_add_assign_test_def

text \<open>Smoke test: compound sub-assign.\<close>
micro_c_translate \<open>
unsigned int sub_assign_test(unsigned int a, unsigned int b) {
  unsigned int x = a;
  x -= b;
  return x;
}
\<close>

thm c_sub_assign_test_def

text \<open>Smoke test: compound mul-assign.\<close>
micro_c_translate \<open>
unsigned int mul_assign_test(unsigned int a) {
  unsigned int x = a;
  x *= 2;
  return x;
}
\<close>

thm c_mul_assign_test_def

text \<open>Smoke test: _Bool type (mapped to Isabelle bool).\<close>
micro_c_translate \<open>
_Bool bool_test(_Bool a, _Bool b) {
  if (a) return b;
  else return !a;
}
\<close>

thm c_bool_test_def

text \<open>Smoke test: type cast (unsigned to signed).\<close>
micro_c_translate \<open>
int cast_test(unsigned int x) {
  return (int)x;
}
\<close>

thm c_cast_test_def

text \<open>Smoke test: do-while loop.\<close>
micro_c_translate \<open>
unsigned int do_while_test(unsigned int n) {
  unsigned int i = 0;
  do {
    i += 1;
  } while (i < n);
  return i;
}
\<close>

thm c_do_while_test_def

text \<open>Smoke test: general for-loop (countdown with decrement).\<close>
micro_c_translate \<open>
unsigned int countdown(unsigned int n) {
  unsigned int r = 0;
  for (unsigned int i = n; i > 0; i--) {
    r += i;
  }
  return r;
}
\<close>

thm c_countdown_def

text \<open>Smoke test: direct struct member access (s.field read).\<close>
micro_c_translate \<open>
struct point {
  int x;
  int y;
};
int get_x(struct point *p) {
  int t = p->x;
  return t;
}
\<close>

thm c_get_x_def

text \<open>Smoke test: enum type.\<close>
micro_c_translate \<open>
enum color { RED = 0, GREEN = 1, BLUE = 2 };
unsigned int enum_test(void) {
  return GREEN;
}
\<close>

thm c_enum_test_def

text \<open>Smoke test: typedef.\<close>
micro_c_translate \<open>
typedef unsigned int uint32;
uint32 typedef_test(uint32 a, uint32 b) {
  return a + b;
}
\<close>

thm c_typedef_test_def

end
