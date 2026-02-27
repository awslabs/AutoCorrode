theory C_To_Core_Translation
  imports
    Micro_C_Syntax
    "Shallow_Micro_Rust.Core_Expression"
    "Shallow_Micro_Rust.Core_Syntax"
    "Shallow_Micro_Rust.Bool_Type"
    "Shallow_Micro_Rust.Rust_Iterator"
    "Shallow_Micro_C.C_Numeric_Types"
    "Shallow_Micro_C.C_Sizeof"
  keywords "micro_c_translate" :: thy_decl
       and "micro_c_file" :: thy_load
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
                          | CPtr of c_numeric_type | CVoid
                          | CStruct of string
  val is_signed : c_numeric_type -> bool
  val is_bool : c_numeric_type -> bool
  val is_ptr : c_numeric_type -> bool
  val is_unsigned_int : c_numeric_type -> bool
  val hol_type_of : c_numeric_type -> typ
  val type_name_of : c_numeric_type -> string
  val resolve_c_type : C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list -> c_numeric_type option
  val decl_type : C_Ast.nodeInfo C_Ast.cDeclaration -> c_numeric_type option
  val param_type : C_Ast.nodeInfo C_Ast.cDeclaration -> c_numeric_type option
  val is_pointer_param : C_Ast.nodeInfo C_Ast.cDeclaration -> bool
  val pointer_depth_of_declr : C_Ast.nodeInfo C_Ast.cDeclarator -> int
  val pointer_depth_of_decl : C_Ast.nodeInfo C_Ast.cDeclaration -> int
  val apply_ptr_depth : c_numeric_type -> int -> c_numeric_type
  val abr_string_to_string : C_Ast.abr_string -> string
  val ident_name : C_Ast.ident -> string
  val declr_name : C_Ast.nodeInfo C_Ast.cDeclarator -> string
  val extract_params : C_Ast.nodeInfo C_Ast.cDeclarator -> string list
  val extract_param_decls : C_Ast.nodeInfo C_Ast.cDeclarator
                            -> C_Ast.nodeInfo C_Ast.cDeclaration list
  val declr_is_variadic : C_Ast.nodeInfo C_Ast.cDeclarator -> bool
  val param_name : C_Ast.nodeInfo C_Ast.cDeclaration -> string option
  val extract_struct_type_from_decl : C_Ast.nodeInfo C_Ast.cDeclaration -> string option
  val extract_struct_type_from_decl_full : string list
                                           -> C_Ast.nodeInfo C_Ast.cDeclaration -> string option
  val extract_struct_type_from_specs_full : string list
                                            -> C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list
                                            -> string option
  val extract_struct_defs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                            -> (string * string list) list
  val extract_enum_defs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                          -> (string * int) list
  val extract_typedefs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                         -> (string * c_numeric_type) list
  val resolve_c_type_full : c_numeric_type Symtab.table
                            -> C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list
                            -> c_numeric_type option
  val int_literal_type : 'a C_Ast.flags -> c_numeric_type
  val find_assigned_vars : C_Ast.nodeInfo C_Ast.cStatement -> string list
  val find_goto_targets : C_Ast.nodeInfo C_Ast.cStatement -> string list

  val extract_struct_defs_with_types : c_numeric_type Symtab.table
                                       -> C_Ast.nodeInfo C_Ast.cTranslationUnit
                                       -> (string * (string * c_numeric_type) list) list
  val extract_fundefs : C_Ast.nodeInfo C_Ast.cTranslationUnit
                        -> C_Ast.nodeInfo C_Ast.cFunctionDef list
  val type_rank : c_numeric_type -> int
  val integer_promote : c_numeric_type -> c_numeric_type
  val usual_arith_conv : c_numeric_type * c_numeric_type -> c_numeric_type
end =
struct
  open C_Ast

  (* ----- Resolved C numeric type representation ----- *)

  datatype c_numeric_type = CInt | CUInt | CChar | CSChar
                          | CShort | CUShort | CLong | CULong | CBool
                          | CPtr of c_numeric_type | CVoid
                          | CStruct of string

  fun is_signed CInt   = true
    | is_signed CSChar  = true
    | is_signed CShort  = true
    | is_signed CLong   = true
    | is_signed (CPtr _) = false
    | is_signed CVoid   = false
    | is_signed (CStruct _) = false
    | is_signed _       = false

  fun is_bool CBool = true
    | is_bool _     = false

  fun is_ptr (CPtr _) = true
    | is_ptr _        = false

  fun is_unsigned_int cty = not (is_signed cty) andalso not (is_bool cty)
                            andalso not (is_ptr cty) andalso cty <> CVoid
                            andalso (case cty of CStruct _ => false | _ => true)

  fun hol_type_of CBool   = @{typ bool}
    | hol_type_of CInt    = \<^typ>\<open>c_int\<close>
    | hol_type_of CUInt   = \<^typ>\<open>c_uint\<close>
    | hol_type_of CChar   = \<^typ>\<open>c_char\<close>
    | hol_type_of CSChar   = \<^typ>\<open>c_schar\<close>
    | hol_type_of CShort  = \<^typ>\<open>c_short\<close>
    | hol_type_of CUShort = \<^typ>\<open>c_ushort\<close>
    | hol_type_of CLong   = \<^typ>\<open>c_long\<close>
    | hol_type_of CULong  = \<^typ>\<open>c_ulong\<close>
    | hol_type_of (CPtr _) = dummyT  (* pointer types use type inference *)
    | hol_type_of CVoid   = @{typ unit}
    | hol_type_of (CStruct _) = dummyT

  fun type_name_of CBool   = "_Bool"
    | type_name_of CInt    = "int"
    | type_name_of CUInt   = "unsigned int"
    | type_name_of CChar   = "char"
    | type_name_of CSChar   = "signed char"
    | type_name_of CShort  = "short"
    | type_name_of CUShort = "unsigned short"
    | type_name_of CLong   = "long"
    | type_name_of CULong  = "unsigned long"
    | type_name_of (CPtr cty) = type_name_of cty ^ " *"
    | type_name_of CVoid   = "void"
    | type_name_of (CStruct s) = "struct " ^ s

  (* Determine C numeric type from integer literal suffix flags.
     Flags0 of int is a bitfield: bit 0 = unsigned, bit 1 = long, bit 2 = long long. *)
  fun int_literal_type (Flags0 bits) =
    let val is_unsigned = IntInf.andb (bits, 1) <> 0
        val is_long = IntInf.andb (bits, 2) <> 0
        val is_long_long = IntInf.andb (bits, 4) <> 0
    in if is_long_long then
         error "micro_c_translate: long long integer literals are not supported; use explicit-sized constants"
       else if is_unsigned andalso is_long then CULong
       else if is_long then CLong
       else if is_unsigned then CUInt
       else CInt
    end

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
        | accumulate (CTypeSpec0 (CFloatType0 _)) _ =
            error "micro_c_translate: float type not supported"
        | accumulate (CTypeSpec0 (CDoubleType0 _)) _ =
            error "micro_c_translate: double type not supported"
        | accumulate (CTypeSpec0 (CInt128Type0 _)) _ =
            error "micro_c_translate: __int128 type not supported"
        | accumulate (CTypeSpec0 (CComplexType0 _)) _ =
            error "micro_c_translate: _Complex type not supported"
        | accumulate (CTypeSpec0 (CTypeDef0 _)) flags = flags
        | accumulate (CTypeSpec0 _) _ =
            error "micro_c_translate: unsupported type specifier"
        | accumulate _ flags = flags
      val (has_signed, has_unsigned, has_char, has_short, has_int, has_long, has_void, has_struct) =
        List.foldl (fn (spec, flags) => accumulate spec flags)
          (false, false, false, false, false, false, false, false) specs
    in
      if has_void then SOME CVoid
      else if has_struct then NONE
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

  (* Check if a parameter declaration has a pointer or array declarator
     (e.g. int *a, struct point *p, int arr[]) *)
  fun pointer_depth_of_derived derived =
    List.foldl
      (fn (d, acc) =>
        (case d of
           CPtrDeclr0 _ => acc + 1
         | CArrDeclr0 _ => acc + 1
         | _ => acc))
      0 derived

  fun pointer_depth_of_declr (CDeclr0 (_, derived, _, _, _)) =
        pointer_depth_of_derived derived
    | pointer_depth_of_declr _ = 0

  fun pointer_depth_of_decl (CDecl0 (_, [((Some declr, _), _)], _)) =
        pointer_depth_of_declr declr
    | pointer_depth_of_decl _ = 0

  fun apply_ptr_depth base 0 = base
    | apply_ptr_depth base n = apply_ptr_depth (CPtr base) (n - 1)

  fun is_pointer_param decl =
        pointer_depth_of_decl decl > 0

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

  fun declr_is_variadic (CDeclr0 (_, derived, _, _, _)) =
    (case List.find (fn CFunDeclr0 _ => true | _ => false) derived of
       SOME (CFunDeclr0 (Right (_, has_varargs), _, _)) => has_varargs
     | SOME (CFunDeclr0 _) => true
     | _ => false)
    | declr_is_variadic _ = false

  (* Check if a declaration has a struct type specifier and return the struct name.
     E.g. for "struct point *p", returns SOME "point". *)
  fun extract_struct_type_from_decl (CDecl0 (specs, _, _)) =
        let fun find_struct [] = NONE
              | find_struct (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, _, _, _), _)) :: _) = SOME (ident_name ident)
              | find_struct (_ :: rest) = find_struct rest
        in find_struct specs end
    | extract_struct_type_from_decl _ = NONE

  (* Like extract_struct_type_from_decl, but also recognizes typedef names
     that refer to structs.  E.g. for "mlk_poly *r" where mlk_poly was
     typedef'd from an anonymous struct, returns SOME "mlk_poly". *)
  fun extract_struct_type_from_decl_full struct_names (CDecl0 (specs, _, _)) =
        let fun find_struct [] = NONE
              | find_struct (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, _, _, _), _)) :: _) = SOME (ident_name ident)
              | find_struct (CTypeSpec0 (CTypeDef0 (ident, _)) :: _) =
                    let val n = ident_name ident
                    in if List.exists (fn s => s = n) struct_names
                       then SOME n else NONE end
              | find_struct (_ :: rest) = find_struct rest
        in find_struct specs end
    | extract_struct_type_from_decl_full _ _ = NONE

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
        let
            fun intinf_to_int_checked what n =
              let
                val ge_min =
                  (case Int.minInt of
                     SOME lo => n >= IntInf.fromInt lo
                   | NONE => true)
                val le_max =
                  (case Int.maxInt of
                     SOME hi => n <= IntInf.fromInt hi
                   | NONE => true)
              in
                if ge_min andalso le_max then IntInf.toInt n
                else error ("micro_c_translate: " ^ what ^ " out of ML-int range: " ^ IntInf.toString n)
              end
            fun process [] _ = []
              | process ((ident, Some (CConst0 (CIntConst0 (CInteger0 (n, _, _), _)))) :: rest) _ =
                  let val v = intinf_to_int_checked "enum constant" n
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
                    val base_cty =
                      (case resolve_c_type type_specs of
                         SOME cty => SOME cty
                       | NONE =>
                           (case List.find (fn CTypeSpec0 (CSUType0 _) => true | _ => false) type_specs of
                              SOME (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0, Some ident, _, _, _), _))) =>
                                SOME (CStruct (ident_name ident))
                            | _ => NONE))
                    val ptr_depth = pointer_depth_of_declr declr
                in case base_cty of
                     SOME cty => [(name, apply_ptr_depth cty ptr_depth)]
                   | NONE => []
                end
              else []
          | extract _ = []
    in List.concat (List.map extract ext_decls) end

  (* resolve_c_type with typedef resolution: check for CTypeDef0 first,
     then fall back to standard resolve_c_type.
     We strip type qualifiers (const, volatile) and storage specifiers
     (static, extern) before matching, so that e.g. "const int32_t" still
     resolves the typedef correctly. *)
  fun resolve_c_type_full typedef_tab specs =
    let val type_specs = List.filter
          (fn CTypeQual0 _ => false | CStorageSpec0 _ => false | _ => true) specs
    in case type_specs of
        [CTypeSpec0 (CTypeDef0 (ident, _))] =>
          (case Symtab.lookup typedef_tab (ident_name ident) of
             SOME cty => SOME cty
           | NONE => NONE)
      | _ => resolve_c_type specs
    end

  (* Walk the C AST and collect variable names that appear on the LHS of
     assignments or as operands of pre/post increment/decrement.
     Used to identify parameters that need promotion to local variables. *)
  local
    fun fae (CAssign0 (_, CVar0 (ident, _), rhs, _)) acc =
          fae rhs (ident_name ident :: acc)
      | fae (CAssign0 (_, lhs, rhs, _)) acc = fae rhs (fae lhs acc)
      | fae (CUnary0 (CPreIncOp0, CVar0 (ident, _), _)) acc = ident_name ident :: acc
      | fae (CUnary0 (CPostIncOp0, CVar0 (ident, _), _)) acc = ident_name ident :: acc
      | fae (CUnary0 (CPreDecOp0, CVar0 (ident, _), _)) acc = ident_name ident :: acc
      | fae (CUnary0 (CPostDecOp0, CVar0 (ident, _), _)) acc = ident_name ident :: acc
      | fae (CBinary0 (_, l, r, _)) acc = fae r (fae l acc)
      | fae (CUnary0 (CAdrOp0, CVar0 (ident, _), _)) acc = ident_name ident :: acc
      | fae (CUnary0 (_, e, _)) acc = fae e acc
      | fae (CCall0 (f, args, _)) acc =
          List.foldl (fn (a, ac) => fae a ac) (fae f acc) args
      | fae (CIndex0 (a, i, _)) acc = fae i (fae a acc)
      | fae (CMember0 (e, _, _, _)) acc = fae e acc
      | fae (CCast0 (_, e, _)) acc = fae e acc
      | fae (CComma0 (es, _)) acc = List.foldl (fn (e, ac) => fae e ac) acc es
      | fae (CCond0 (c, t, e, _)) acc =
          fae e ((case t of Some te => fae te | None => I) (fae c acc))
      | fae _ acc = acc
    and fas (CCompound0 (_, items, _)) acc =
          List.foldl (fn (CBlockStmt0 s, ac) => fas s ac | (_, ac) => ac) acc items
      | fas (CExpr0 (Some e, _)) acc = fae e acc
      | fas (CIf0 (c, t, e_opt, _)) acc =
          (case e_opt of Some e => fas e | None => I) (fas t (fae c acc))
      | fas (CWhile0 (c, b, _, _)) acc = fas b (fae c acc)
      | fas (CFor0 (Left (Some i), c, s, b, _)) acc =
          fas b (opt s (opt c (fae i acc)))
      | fas (CFor0 (_, c, s, b, _)) acc =
          fas b (opt s (opt c acc))
      | fas (CReturn0 (Some e, _)) acc = fae e acc
      | fas (CLabel0 (_, s, _, _)) acc = fas s acc
      | fas (CSwitch0 (e, s, _)) acc = fas s (fae e acc)
      | fas _ acc = acc
    and opt (Some e) acc = fae e acc
      | opt None acc = acc
  in
    fun find_assigned_vars stmt = distinct (op =) (fas stmt [])
  end

  (* Walk the C AST and collect label names targeted by goto statements.
     Used to allocate goto flag references for forward-only goto support. *)
  local
    fun fgt (CGoto0 (ident, _)) acc = ident_name ident :: acc
      | fgt (CCompound0 (_, items, _)) acc =
          List.foldl (fn (CBlockStmt0 s, ac) => fgt s ac | (_, ac) => ac) acc items
      | fgt (CIf0 (_, t, e_opt, _)) acc =
          (case e_opt of Some e => fgt e | None => I) (fgt t acc)
      | fgt (CWhile0 (_, b, _, _)) acc = fgt b acc
      | fgt (CFor0 (_, _, _, b, _)) acc = fgt b acc
      | fgt (CSwitch0 (_, s, _)) acc = fgt s acc
      | fgt (CLabel0 (_, s, _, _)) acc = fgt s acc
      | fgt _ acc = acc
  in
    fun find_goto_targets stmt = distinct (op =) (fgt stmt [])
  end


  (* Extract struct definitions with field types from a top-level declaration.
     Returns SOME (struct_name, [(field_name, field_type)]) for struct definitions.
     Falls back to CInt for fields whose type cannot be resolved. *)
  (* Extract struct type name from declaration specifiers (for struct-typed fields) *)
  fun extract_struct_type_from_specs specs =
    case List.find (fn CTypeSpec0 (CSUType0 _) => true | _ => false) specs of
      SOME (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0, Some ident, _, _, _), _))) =>
        SOME (ident_name ident)
    | _ => NONE

  (* Like extract_struct_type_from_specs, but also recognizes typedef names
     that refer to known structs. *)
  fun extract_struct_type_from_specs_full struct_names specs =
    case extract_struct_type_from_specs specs of
      SOME sn => SOME sn
    | NONE =>
        let val type_specs = List.filter
              (fn CTypeQual0 _ => false | CStorageSpec0 _ => false | _ => true) specs
        in case type_specs of
            [CTypeSpec0 (CTypeDef0 (ident, _))] =>
              let val n = ident_name ident
              in if List.exists (fn s => s = n) struct_names
                 then SOME n else NONE end
          | _ => NONE
        end

  fun extract_member_field_info typedef_tab members =
        List.mapPartial
          (fn CDecl0 (field_specs, [((Some (CDeclr0 (Some ident_node, derived, _, _, _)), _), _)], _) =>
                let val fname = ident_name ident_node
                    val base_fty = case resolve_c_type_full typedef_tab field_specs of
                                     SOME CVoid => CInt
                                   | SOME ct => ct
                                   | NONE =>
                                       (case extract_struct_type_from_specs field_specs of
                                          SOME sn => CStruct sn
                                        | NONE => CInt)
                    val ptr_depth = pointer_depth_of_derived derived
                    val fty = apply_ptr_depth base_fty ptr_depth
                in SOME (fname, fty) end
            | _ => NONE)
          members

  fun extract_struct_def_with_types_from_decl typedef_tab (CDecl0 (specs, declrs, _)) =
        let fun find_struct_def [] = NONE
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, Some members, _, _), _)) :: _) =
                  SOME (ident_name ident, extract_member_field_info typedef_tab members)
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    None, Some members, _, _), _)) :: _) =
                  (* Anonymous struct in typedef: get name from declarator *)
                  if List.exists (fn CStorageSpec0 (CTypedef0 _) => true | _ => false) specs
                  then (case declrs of
                      [((Some (CDeclr0 (Some td_ident, _, _, _, _)), _), _)] =>
                        SOME (ident_name td_ident,
                              extract_member_field_info typedef_tab members)
                    | _ => NONE)
                  else NONE
              | find_struct_def (_ :: rest) = find_struct_def rest
        in find_struct_def specs end
    | extract_struct_def_with_types_from_decl _ _ = NONE

  fun extract_struct_defs_with_types typedef_tab (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CDeclExt0 decl => extract_struct_def_with_types_from_decl typedef_tab decl
        | _ => NONE)
      ext_decls

  fun extract_fundefs (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CFDefExt0 fundef => SOME fundef | _ => NONE)
      ext_decls

  (* C11 integer conversion rank (\<section>6.3.1.1) *)
  fun type_rank CBool   = 0
    | type_rank CChar   = 1
    | type_rank CSChar  = 1
    | type_rank CShort  = 2
    | type_rank CUShort = 2
    | type_rank CInt    = 3
    | type_rank CUInt   = 3
    | type_rank CLong   = 4
    | type_rank CULong  = 4
    | type_rank _       = 3  (* default: int rank *)

  (* C11 \<section>6.3.1.1: integer promotion — sub-int types promote to int *)
  fun integer_promote cty =
    if type_rank cty < type_rank CInt then CInt else cty

  (* C11 \<section>6.3.1.8: usual arithmetic conversions for binary ops *)
  fun usual_arith_conv (lty, rty) =
    let val lp = integer_promote lty
        val rp = integer_promote rty
    in if lp = rp then lp
       else if is_signed lp = is_signed rp then
         (if type_rank lp >= type_rank rp then lp else rp)
       else
         let val (_, u) = if is_signed lp then (lp, rp) else (rp, lp)
         in if type_rank u >= type_rank lp andalso type_rank u >= type_rank rp
            then u  (* unsigned wins when rank >= signed *)
            else if is_signed lp then lp else rp  (* signed can represent all unsigned values *)
         end
    end
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
  val make : Proof.context -> (string * C_Ast_Utils.c_numeric_type) list Symtab.table
             -> int Symtab.table -> C_Ast_Utils.c_numeric_type Symtab.table
             -> C_Ast_Utils.c_numeric_type Symtab.table Unsynchronized.ref
             -> C_Ast_Utils.c_numeric_type list Symtab.table Unsynchronized.ref -> t
  val get_ctxt : t -> Proof.context
  val add_var : string -> var_kind -> term -> C_Ast_Utils.c_numeric_type -> t -> t
  val lookup_var : t -> string -> (var_kind * term * C_Ast_Utils.c_numeric_type) option
  val get_struct_names : t -> string list
  val set_struct_type : string -> string -> t -> t
  val get_struct_type : t -> string -> string option
  val get_struct_fields : t -> string -> (string * C_Ast_Utils.c_numeric_type) list option
  val lookup_struct_field_type : t -> string -> string -> C_Ast_Utils.c_numeric_type option
  val set_array_decl : string -> C_Ast_Utils.c_numeric_type -> int -> t -> t
  val lookup_array_decl : t -> string -> (C_Ast_Utils.c_numeric_type * int) option
  val lookup_enum_const : t -> string -> int option
  val add_enum_consts : (string * int) list -> t -> t
  val get_typedef_tab : t -> C_Ast_Utils.c_numeric_type Symtab.table
  val register_func_return_type : string -> C_Ast_Utils.c_numeric_type -> t -> unit
  val lookup_func_return_type : t -> string -> C_Ast_Utils.c_numeric_type option
  val register_func_param_types : string -> C_Ast_Utils.c_numeric_type list -> t -> unit
  val lookup_func_param_types : t -> string -> C_Ast_Utils.c_numeric_type list option
  val get_break_ref : t -> term option
  val get_continue_ref : t -> term option
  val set_break_ref : term -> t -> t
  val set_continue_ref : term -> t -> t
  val clear_break_ref : t -> t
  val get_goto_refs : t -> (string * term) list
  val set_goto_refs : (string * term) list -> t -> t
  val lookup_goto_ref : t -> string -> term option
  val get_active_goto_labels : t -> string list
  val set_active_goto_labels : string list -> t -> t
end =
struct
  datatype var_kind = Param | Local
  type t = {
    ctxt : Proof.context,
    vars : (var_kind * term * C_Ast_Utils.c_numeric_type) Symtab.table,
    struct_types : string Symtab.table,         (* var_name -> c_struct_name *)
    struct_fields : (string * C_Ast_Utils.c_numeric_type) list Symtab.table,
    array_decls : (C_Ast_Utils.c_numeric_type * int) Symtab.table,  (* var_name -> (elem_cty, size) *)
    enum_consts : int Symtab.table,             (* enum_name -> int_value *)
    typedef_tab : C_Ast_Utils.c_numeric_type Symtab.table,
    func_ret_types : C_Ast_Utils.c_numeric_type Symtab.table Unsynchronized.ref,
    func_param_types : C_Ast_Utils.c_numeric_type list Symtab.table Unsynchronized.ref,
    break_ref : term option,
    continue_ref : term option,
    goto_refs : (string * term) list,           (* label_name -> flag ref variable *)
    active_goto_labels : string list             (* labels that are valid forward goto targets from here *)
  }

  fun make ctxt struct_fields enum_consts typedef_tab func_ret_types func_param_types : t =
    { ctxt = ctxt, vars = Symtab.empty, struct_types = Symtab.empty,
      struct_fields = struct_fields, array_decls = Symtab.empty,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = NONE, continue_ref = NONE,
      goto_refs = [], active_goto_labels = [] }

  fun get_ctxt ({ ctxt, ... } : t) = ctxt

  fun add_var name kind tm cty ({ ctxt, vars, struct_types, struct_fields,
                                   array_decls, enum_consts, typedef_tab, func_ret_types,
                                   func_param_types, break_ref, continue_ref, goto_refs,
                                   active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = Symtab.update (name, (kind, tm, cty)) vars,
      struct_types = struct_types, struct_fields = struct_fields,
      array_decls = array_decls,
      enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun lookup_var ({ vars, ... } : t) name =
    Symtab.lookup vars name

  fun get_struct_names ({ struct_fields, ... } : t) =
    Symtab.keys struct_fields

  fun set_struct_type var_name struct_name
      ({ ctxt, vars, struct_types, struct_fields, array_decls, enum_consts, typedef_tab,
         func_ret_types, func_param_types, break_ref, continue_ref, goto_refs,
         active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars,
      struct_types = Symtab.update (var_name, struct_name) struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun get_struct_type ({ struct_types, ... } : t) name =
    Symtab.lookup struct_types name

  fun get_struct_fields ({ struct_fields, ... } : t) name =
    Symtab.lookup struct_fields name

  fun lookup_struct_field_type tctx struct_name field_name =
    case get_struct_fields tctx struct_name of
      SOME fields => (case List.find (fn (n, _) => n = field_name) fields of
                        SOME (_, cty) => SOME cty | NONE => NONE)
    | NONE => NONE

  fun set_array_decl var_name elem_cty size
      ({ ctxt, vars, struct_types, struct_fields, array_decls, enum_consts,
         typedef_tab, func_ret_types, func_param_types, break_ref, continue_ref,
         goto_refs, active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields,
      array_decls = Symtab.update (var_name, (elem_cty, size)) array_decls,
      enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types, func_param_types = func_param_types,
      break_ref = break_ref, continue_ref = continue_ref, goto_refs = goto_refs,
      active_goto_labels = active_goto_labels }

  fun lookup_array_decl ({ array_decls, ... } : t) name =
    Symtab.lookup array_decls name

  fun lookup_enum_const ({ enum_consts, ... } : t) name =
    Symtab.lookup enum_consts name

  fun add_enum_consts entries ({ ctxt, vars, struct_types, struct_fields,
                                 array_decls, enum_consts, typedef_tab, func_ret_types,
                                 func_param_types, break_ref, continue_ref, goto_refs,
                                 active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields,
      array_decls = array_decls,
      enum_consts = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                      enum_consts entries,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun get_typedef_tab ({ typedef_tab, ... } : t) = typedef_tab

  fun register_func_return_type name cty ({ func_ret_types, ... } : t) =
    func_ret_types := Symtab.update (name, cty) (! func_ret_types)

  fun lookup_func_return_type ({ func_ret_types, ... } : t) name =
    Symtab.lookup (! func_ret_types) name

  fun register_func_param_types name ctys ({ func_param_types, ... } : t) =
    func_param_types := Symtab.update (name, ctys) (! func_param_types)

  fun lookup_func_param_types ({ func_param_types, ... } : t) name =
    Symtab.lookup (! func_param_types) name

  fun get_break_ref ({ break_ref, ... } : t) = break_ref
  fun get_continue_ref ({ continue_ref, ... } : t) = continue_ref

  fun set_break_ref ref_term ({ ctxt, vars, struct_types, struct_fields,
                                 array_decls, enum_consts, typedef_tab, func_ret_types,
                                 func_param_types, break_ref = _, continue_ref,
                                 goto_refs, active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = SOME ref_term,
      continue_ref = continue_ref, goto_refs = goto_refs,
      active_goto_labels = active_goto_labels }

  fun set_continue_ref ref_term ({ ctxt, vars, struct_types, struct_fields,
                                    array_decls, enum_consts, typedef_tab, func_ret_types,
                                    func_param_types, break_ref, continue_ref = _,
                                    goto_refs, active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = break_ref,
      continue_ref = SOME ref_term, goto_refs = goto_refs,
      active_goto_labels = active_goto_labels }

  fun clear_break_ref ({ ctxt, vars, struct_types, struct_fields,
                          array_decls, enum_consts, typedef_tab, func_ret_types,
                          func_param_types, break_ref = _, continue_ref, goto_refs,
                          active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = NONE, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun get_goto_refs ({ goto_refs, ... } : t) = goto_refs

  fun set_goto_refs refs ({ ctxt, vars, struct_types, struct_fields,
                             array_decls, enum_consts, typedef_tab, func_ret_types,
                             func_param_types, break_ref, continue_ref, goto_refs = _,
                             active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types,
      break_ref = break_ref,
      continue_ref = continue_ref, goto_refs = refs,
      active_goto_labels = active_goto_labels }

  fun lookup_goto_ref ({ goto_refs, ... } : t) name =
    case List.find (fn (n, _) => n = name) goto_refs of
      SOME (_, ref_term) => SOME ref_term
    | NONE => NONE

  fun get_active_goto_labels ({ active_goto_labels, ... } : t) =
    active_goto_labels

  fun set_active_goto_labels labels ({ ctxt, vars, struct_types, struct_fields,
                                       array_decls, enum_consts, typedef_tab, func_ret_types,
                                       func_param_types, break_ref, continue_ref, goto_refs,
                                       active_goto_labels = _ } : t) : t =
    { ctxt = ctxt, vars = vars, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types, func_param_types = func_param_types,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = distinct (op =) labels }
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
consts c_uninitialized :: "'a"

definition c_bounds_abort :: "('s, 'v, 'r, 'abort, 'i, 'o) expression" where [simp]:
  "c_bounds_abort \<equiv> abort undefined"

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
  val mk_var_alloc_typed : typ -> term -> term
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

  (* Type-annotated variant: constrains the value type of store_reference_const
     so adhoc overloading can resolve when multiple word-type prisms exist. *)
  fun mk_var_alloc_typed val_hol_type init_expr =
    if val_hol_type = dummyT then mk_var_alloc init_expr
    else
      Const (\<^const_name>\<open>funcall1\<close>, dummyT --> dummyT --> dummyT)
        $ Const (\<^const_name>\<open>store_reference_const\<close>, val_hol_type --> dummyT)
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
  val translate_fundef : (string * C_Ast_Utils.c_numeric_type) list Symtab.table
                         -> int Symtab.table
                         -> C_Ast_Utils.c_numeric_type Symtab.table
                         -> C_Ast_Utils.c_numeric_type Symtab.table Unsynchronized.ref
                         -> C_Ast_Utils.c_numeric_type list Symtab.table Unsynchronized.ref
                         -> Proof.context
                         -> C_Ast.nodeInfo C_Ast.cFunctionDef -> string * term
end =
struct
  (* Save Isabelle term constructors before C_Ast shadows them *)
  val Isa_Const = Const
  val Isa_Free = Free
  val isa_dummyT = dummyT
  val Isa_add_frees = Term.add_frees
  val Isa_Type = Type

  (* Generate a fresh variable name not occurring free in the given terms *)
  fun fresh_var terms stem typ =
    let val used = List.foldl (fn (t, acc) => Isa_add_frees t acc) [] terms
                   |> List.map fst
        val (name, _) = Name.variant stem (Name.make_context used)
    in Isa_Free (name, typ) end

  fun expr_value_type tm =
    (case fastype_of tm of
       Type (_, _ :: vty :: _) => vty
     | _ => isa_dummyT)

  (* Binary operator classification: arithmetic/comparison/bitwise operators are
     monadic and compose via bind2.
     NB: Must be defined before 'open C_Ast' which shadows the term type. *)
  datatype binop_kind = Monadic of term

  (* C11 implicit integer promotion cast.
     Inserts c_scast or c_ucast when from_cty <> to_cty.
     Cast direction: signed source \<rightarrow> c_scast (sign-extend), unsigned \<rightarrow> c_ucast (zero-extend).
     Both c_scast/c_ucast are fully polymorphic: 'a word \<rightarrow> ('s, 'b word, ...) expression.
     Must be defined before 'open C_Ast' to use Const/Free/dummyT. *)
  fun mk_implicit_cast (tm, from_cty, to_cty) =
    if from_cty = to_cty then tm
    else if C_Ast_Utils.is_bool to_cty then
      (* scalar -> _Bool : compare against zero *)
      if C_Ast_Utils.is_ptr from_cty then
        let val v = Isa_Free ("v__promo", isa_dummyT)
            val addr_term =
              Isa_Const (\<^const_name>\<open>address\<close>, isa_dummyT --> isa_dummyT) $ v
            val neq_zero =
              Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool})
                $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool})
                     $ addr_term
                     $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
        in C_Term_Build.mk_bind tm (Term.lambda v (C_Term_Build.mk_literal neq_zero)) end
      else
        let val from_ty = if C_Ast_Utils.is_bool from_cty
                          then @{typ bool}
                          else C_Ast_Utils.hol_type_of from_cty
            val v = Isa_Free ("v__promo", from_ty)
            val truthy_expr =
              if C_Ast_Utils.is_bool from_cty then
                C_Term_Build.mk_literal v
              else if C_Ast_Utils.is_signed from_cty then
                Const (\<^const_name>\<open>c_signed_truthy\<close>, isa_dummyT) $ v
              else
                Const (\<^const_name>\<open>c_unsigned_truthy\<close>, isa_dummyT) $ v
        in C_Term_Build.mk_bind tm (Term.lambda v truthy_expr) end
    else if C_Ast_Utils.is_bool from_cty then
      (* Bool \<rightarrow> integer: if b then 1 else 0 *)
      let val v = Isa_Free ("v__promo", @{typ bool})
          val one = C_Term_Build.mk_literal_num to_cty 1
          val zero = C_Term_Build.mk_literal_num to_cty 0
      in C_Term_Build.mk_bind tm
           (Term.lambda v (C_Term_Build.mk_two_armed_cond
              (C_Term_Build.mk_literal v) one zero)) end
    else if C_Ast_Utils.is_ptr from_cty andalso C_Ast_Utils.is_ptr to_cty then
      tm
    else if C_Ast_Utils.is_ptr from_cty orelse C_Ast_Utils.is_ptr to_cty then
      error "micro_c_translate: non-pointer/pointer cast not supported"
    else let val cast_const =
               if C_Ast_Utils.is_signed from_cty
               then Const (\<^const_name>\<open>c_scast\<close>, isa_dummyT)
               else Const (\<^const_name>\<open>c_ucast\<close>, isa_dummyT)
             (* Type-annotate the lambda variable with the source HOL type
                so c_scast/c_ucast input type is fully determined. *)
             val from_ty = C_Ast_Utils.hol_type_of from_cty
             val v = Isa_Free ("v__promo", from_ty)
         in C_Term_Build.mk_bind tm (Term.lambda v (cast_const $ v)) end

  (* Current function's return type, set by translate_fundef before translating
     the function body. Used by CReturn0 to insert narrowing casts. *)
  val current_ret_cty : C_Ast_Utils.c_numeric_type option Unsynchronized.ref =
    Unsynchronized.ref NONE

  open C_Ast

  fun unsupported construct =
    error ("micro_c_translate: unsupported C construct: " ^ construct)

  (* Translate a C binary operator to a HOL function constant, dispatching
     signed vs unsigned based on the operand type.
     Arithmetic, comparison and bitwise operations use the overflow-checked
     C operations from C_Numeric_Types which are monadic (they can abort). *)
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
    | translate_binop _ _ = unsupported "unsupported binary operator"

  (* Determine the C struct type of a variable expression.
     Handles simple variable references and chained member access (p->vec[i].coeffs). *)
  fun determine_struct_type tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.get_struct_type tctx name of
             SOME sname => sname
           | NONE => error ("micro_c_translate: cannot determine struct type for: " ^ name)
        end
    | determine_struct_type tctx (CMember0 (inner_expr, field_ident, _, _)) =
        let val inner_struct = determine_struct_type tctx inner_expr
            val field_name = C_Ast_Utils.ident_name field_ident
        in case C_Trans_Ctxt.lookup_struct_field_type tctx inner_struct field_name of
             SOME (C_Ast_Utils.CStruct sname) => sname
           | SOME (C_Ast_Utils.CPtr (C_Ast_Utils.CStruct sname)) => sname
           | _ => error ("micro_c_translate: field " ^ field_name ^ " of " ^
                         inner_struct ^ " is not a struct type")
        end
    | determine_struct_type tctx (CIndex0 (inner_expr, _, _)) =
        (* arr[i] where arr is a struct field — the struct type comes from the array expression *)
        determine_struct_type tctx inner_expr
    | determine_struct_type _ _ =
        error "micro_c_translate: struct member access on complex expression not yet supported"

  (* Resolve a struct field accessor/updater constant by name convention.
     Convention: struct "point" field "x" -> accessor "c_point_x", updater "update_c_point_x" *)
  fun resolve_const ctxt name =
    let val (full_name, _) = Term.dest_Const
          (Proof_Context.read_const {proper = true, strict = false} ctxt name)
    in Isa_Const (full_name, isa_dummyT) end

  fun mk_resolved_var_alloc_typed ctxt val_hol_type init_expr =
    let val ref_const =
          (resolve_const ctxt "store_reference_const"
           handle ERROR _ =>
             if val_hol_type = isa_dummyT
             then Isa_Const (\<^const_name>\<open>store_reference_const\<close>, isa_dummyT)
             else Isa_Const (\<^const_name>\<open>store_reference_const\<close>, val_hol_type --> isa_dummyT))
        val ref_const =
          if val_hol_type = isa_dummyT then ref_const
          else
            let val (full_name, _) = Term.dest_Const ref_const
            in Isa_Const (full_name, val_hol_type --> isa_dummyT) end
    in C_Term_Build.mk_funcall ref_const [init_expr] end

  fun mk_resolved_var_alloc ctxt init_expr =
    mk_resolved_var_alloc_typed ctxt isa_dummyT init_expr

  (* Variable read with locale-resolved dereference_fun.
     Avoids store_dereference_const adhoc overloading issues when type context
     is insufficient (e.g. guard reads in goto, return after guards). *)
  fun mk_resolved_var_read ctxt ref_var =
    let val deref_const =
          resolve_const ctxt "dereference_fun"
          handle ERROR _ =>
            Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
        val deref_fn =
          Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
            $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
            $ deref_const
    in Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
         $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ref_var)
         $ deref_fn
    end

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

  (* Map compound assignment operators to their binary operator equivalents *)
  fun compound_assign_to_binop CAddAssOp0 = SOME CAddOp0
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

  fun intinf_to_int_checked what n =
    let
      val ge_min =
        (case Int.minInt of
           SOME lo => n >= IntInf.fromInt lo
         | NONE => true)
      val le_max =
        (case Int.maxInt of
           SOME hi => n <= IntInf.fromInt hi
         | NONE => true)
    in
      if ge_min andalso le_max then IntInf.toInt n
      else error ("micro_c_translate: " ^ what ^ " out of ML-int range: " ^ IntInf.toString n)
    end

  fun cty_bit_width C_Ast_Utils.CChar = SOME 8
    | cty_bit_width C_Ast_Utils.CSChar = SOME 8
    | cty_bit_width C_Ast_Utils.CShort = SOME 16
    | cty_bit_width C_Ast_Utils.CUShort = SOME 16
    | cty_bit_width C_Ast_Utils.CInt = SOME 32
    | cty_bit_width C_Ast_Utils.CUInt = SOME 32
    | cty_bit_width C_Ast_Utils.CLong = SOME 64
    | cty_bit_width C_Ast_Utils.CULong = SOME 64
    | cty_bit_width _ = NONE

  fun fits_int_literal_cty cty n =
    case cty_bit_width cty of
      NONE => false
    | SOME bits =>
        let val two_pow = IntInf.pow (2, bits)
        in
          if C_Ast_Utils.is_signed cty then
            let
              val maxp1 = IntInf.pow (2, bits - 1)
              val lo = ~ maxp1
              val hi = maxp1 - 1
            in lo <= n andalso n <= hi end
          else
            0 <= n andalso n < two_pow
        end

  fun choose_int_literal_type n flags =
    let
      val unsuffixed =
        (case flags of
           Flags0 bits => IntInf.andb (bits, 7) = 0)
    in
      (case C_Ast_Utils.int_literal_type flags of
         C_Ast_Utils.CInt =>
           if fits_int_literal_cty C_Ast_Utils.CInt n then C_Ast_Utils.CInt
           else if unsuffixed then
             unsupported "unsuffixed integer literal beyond int range is not supported; add an explicit U/L suffix"
           else if fits_int_literal_cty C_Ast_Utils.CLong n then C_Ast_Utils.CLong
           else unsupported "integer literal out of supported signed range"
       | C_Ast_Utils.CUInt =>
           if fits_int_literal_cty C_Ast_Utils.CUInt n then C_Ast_Utils.CUInt
           else if fits_int_literal_cty C_Ast_Utils.CULong n then C_Ast_Utils.CULong
           else unsupported "integer literal out of supported unsigned range"
       | C_Ast_Utils.CLong =>
           if fits_int_literal_cty C_Ast_Utils.CLong n then C_Ast_Utils.CLong
           else unsupported "integer literal out of supported long range"
       | C_Ast_Utils.CULong =>
           if fits_int_literal_cty C_Ast_Utils.CULong n then C_Ast_Utils.CULong
           else unsupported "integer literal out of supported unsigned long range"
       | cty => cty)
    end

  fun mk_index_guard idx_p_cty i_var list_tm body_term =
    let
      val idx_nat = C_Term_Build.mk_unat i_var
      val len_tm =
        Isa_Const (\<^const_name>\<open>size\<close>, isa_dummyT --> @{typ nat}) $ list_tm
      val in_bounds =
        Isa_Const (\<^const_name>\<open>Orderings.less\<close>, @{typ nat} --> @{typ nat} --> @{typ bool})
          $ idx_nat $ len_tm
      val overflow = Isa_Const (\<^const_name>\<open>c_bounds_abort\<close>, isa_dummyT)
      val guarded_upper =
        C_Term_Build.mk_two_armed_cond (C_Term_Build.mk_literal in_bounds) body_term overflow
    in
      if C_Ast_Utils.is_signed idx_p_cty then
        let
          val lt_zero =
            C_Term_Build.mk_bind2
              (Isa_Const (\<^const_name>\<open>c_signed_less\<close>, isa_dummyT))
              (C_Term_Build.mk_literal i_var)
              (C_Term_Build.mk_literal_num idx_p_cty 0)
        in
          C_Term_Build.mk_two_armed_cond lt_zero overflow guarded_upper
        end
      else guarded_upper
    end

  (* --- Switch statement helpers --- *)

  (* Unwrap nested case/default labels from the C AST.
     CCase0(1, CCase0(2, stmt)) becomes labels=[SOME 1, SOME 2], stmt *)
  fun unwrap_case_labels (CCase0 (expr, inner, _)) labels =
        unwrap_case_labels inner (SOME expr :: labels)
    | unwrap_case_labels (CDefault0 (inner, _)) labels =
        unwrap_case_labels inner (NONE :: labels)
    | unwrap_case_labels stmt labels = (rev labels, stmt)

  (* Extract case groups from flat switch body items.
     Returns list of {labels, body, has_break}. *)
  fun extract_switch_groups items =
    let
      fun close_group labels body has_break acc =
        if null labels then acc
        else {labels = rev labels, body = rev body, has_break = has_break} :: acc
      fun walk [] labels body acc = rev (close_group labels body false acc)
        | walk (CBlockStmt0 (stmt as CCase0 _) :: rest) labels body acc =
            let val acc' = close_group labels body false acc
                val (new_labels, first_stmt) = unwrap_case_labels stmt []
            in walk rest new_labels [CBlockStmt0 first_stmt] acc' end
        | walk (CBlockStmt0 (stmt as CDefault0 _) :: rest) labels body acc =
            let val acc' = close_group labels body false acc
                val (new_labels, first_stmt) = unwrap_case_labels stmt []
            in walk rest new_labels [CBlockStmt0 first_stmt] acc' end
        | walk (CBlockStmt0 (CBreak0 _) :: rest) labels body acc =
            let val acc' = close_group labels body true acc
            in walk rest [] [] acc' end
        | walk (item :: rest) labels body acc =
            walk rest labels (item :: body) acc
    in walk items [] [] [] end

  (* Translate a case label expression to a pure HOL value *)
  fun case_label_value switch_cty tctx (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        HOLogic.mk_number (C_Ast_Utils.hol_type_of switch_cty)
          (intinf_to_int_checked "switch case label" n)
    | case_label_value switch_cty tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_enum_const tctx name of
             SOME v => HOLogic.mk_number (C_Ast_Utils.hol_type_of switch_cty) v
           | NONE => error ("micro_c_translate: unsupported case label: " ^ name)
        end
    | case_label_value _ _ _ = error "micro_c_translate: unsupported case label expression"

  (* Build condition for a case group: switch_var = label1 OR ... OR labelN.
     Default labels map to default_cond, which should be ~(any explicit case matched). *)
  fun make_switch_cond switch_var switch_cty tctx default_cond labels =
    let fun one_label (SOME e) =
              HOLogic.mk_eq (switch_var, case_label_value switch_cty tctx e)
          | one_label NONE = default_cond
        fun combine [] = Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})
          | combine [c] = c
          | combine (c :: cs) =
              Isa_Const (\<^const_name>\<open>HOL.disj\<close>,
                @{typ bool} --> @{typ bool} --> @{typ bool}) $ c $ (combine cs)
    in combine (List.map one_label labels) end

  (* Build a condition that says whether switch_var matches any explicit case label. *)
  fun make_any_case_match switch_var switch_cty tctx groups =
    let val labels = List.concat (List.map #labels groups)
                    |> List.mapPartial I
        fun one_label e = HOLogic.mk_eq (switch_var, case_label_value switch_cty tctx e)
        fun combine [] = Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})
          | combine [c] = c
          | combine (c :: cs) =
              Isa_Const (\<^const_name>\<open>HOL.disj\<close>,
                @{typ bool} --> @{typ bool} --> @{typ bool}) $ c $ (combine cs)
    in combine (List.map one_label labels) end

  (* --- Break/continue AST scanners --- *)

  fun contains_break (CBreak0 _) = true
    | contains_break (CCompound0 (_, items, _)) = List.exists block_has_break items
    | contains_break (CIf0 (_, t_br, e_opt, _)) =
        contains_break t_br orelse
        (case e_opt of Some e => contains_break e | None => false)
    | contains_break (CSwitch0 _) = false  (* break in switch exits switch, not loop *)
    | contains_break (CFor0 _) = false     (* break in nested loop is local *)
    | contains_break (CWhile0 _) = false
    | contains_break _ = false
  and block_has_break (CBlockStmt0 s) = contains_break s
    | block_has_break _ = false

  fun contains_continue (CCont0 _) = true
    | contains_continue (CCompound0 (_, items, _)) = List.exists block_has_continue items
    | contains_continue (CIf0 (_, t_br, e_opt, _)) =
        contains_continue t_br orelse
        (case e_opt of Some e => contains_continue e | None => false)
    | contains_continue (CFor0 _) = false
    | contains_continue (CWhile0 _) = false
    | contains_continue _ = false
  and block_has_continue (CBlockStmt0 s) = contains_continue s
    | block_has_continue _ = false

  fun struct_name_of_cty (C_Ast_Utils.CStruct sname) = SOME sname
    | struct_name_of_cty (C_Ast_Utils.CPtr (C_Ast_Utils.CStruct sname)) = SOME sname
    | struct_name_of_cty _ = NONE

  fun is_zero_int_const (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) = (n = 0)
    | is_zero_int_const (CCast0 (_, e, _)) = is_zero_int_const e
    | is_zero_int_const _ = false

  fun mk_ptr_is_null ptr_term =
    let val p = Isa_Free ("v__ptrcmp", isa_dummyT)
        val is_null =
          Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool})
            $ (Isa_Const (\<^const_name>\<open>address\<close>, isa_dummyT --> isa_dummyT) $ p)
            $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT)
    in C_Term_Build.mk_bind ptr_term (Term.lambda p (C_Term_Build.mk_literal is_null)) end

  (* translate_expr returns (term * c_numeric_type).
     The type tracks the C type of the expression for binary operator dispatch.
     CInt is used as default when the actual type is unknown/irrelevant. *)
  fun translate_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, flags), _))) =
        let val cty = choose_int_literal_type n flags
            val n_int = intinf_to_int_checked "integer literal" n
        in (C_Term_Build.mk_literal_num cty n_int, cty)
        end
    | translate_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, var, cty) => (C_Term_Build.mk_literal var, cty)
           | SOME (C_Trans_Ctxt.Local, var, cty) =>
               (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx) var, cty)
           | NONE =>
               (* Fallback: check enum constants *)
               (case C_Trans_Ctxt.lookup_enum_const tctx name of
                  SOME value => (C_Term_Build.mk_literal_int value, C_Ast_Utils.CInt)
                | NONE => error ("micro_c_translate: undefined variable: " ^ name))
        end
    | translate_expr tctx (CBinary0 (binop, lhs, rhs, _)) =
        let val (lhs', lhs_cty) = translate_expr tctx lhs
            val (rhs', rhs_cty) = translate_expr tctx rhs
            fun to_bool (tm, cty) = mk_implicit_cast (tm, cty, C_Ast_Utils.CBool)
            fun mk_ptr_add ptr_term idx_term idx_cty elem_cty =
              let val p_var = Isa_Free ("v__ptr", isa_dummyT)
                  val i_var = Isa_Free ("v__idx", isa_dummyT)
                  val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
                  val idx_p_term = mk_implicit_cast (idx_term, idx_cty, idx_p_cty)
                  val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) p_var
                  val focused_lit = C_Term_Build.mk_literal focused
                  val guarded = mk_index_guard idx_p_cty i_var p_var focused_lit
              in (C_Term_Build.mk_bind ptr_term (Term.lambda p_var
                    (C_Term_Build.mk_bind idx_p_term (Term.lambda i_var guarded))),
                  C_Ast_Utils.CPtr elem_cty)
              end
        in
        case binop of
          (* C logical operators short-circuit and return _Bool *)
          CLndOp0 =>
            let val lhs_bool = to_bool (lhs', lhs_cty)
                val rhs_bool = to_bool (rhs', rhs_cty)
                val v = Isa_Free ("v__lhsb", @{typ bool})
            in (C_Term_Build.mk_bind lhs_bool (Term.lambda v
                  (C_Term_Build.mk_two_armed_cond
                    (C_Term_Build.mk_literal v)
                    rhs_bool
                    (C_Term_Build.mk_literal (Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool}))))),
                C_Ast_Utils.CBool)
            end
        | CLorOp0 =>
            let val lhs_bool = to_bool (lhs', lhs_cty)
                val rhs_bool = to_bool (rhs', rhs_cty)
                val v = Isa_Free ("v__lhsb", @{typ bool})
            in (C_Term_Build.mk_bind lhs_bool (Term.lambda v
                  (C_Term_Build.mk_two_armed_cond
                    (C_Term_Build.mk_literal v)
                    (C_Term_Build.mk_literal (Isa_Const (\<^const_name>\<open>HOL.True\<close>, @{typ bool})))
                    rhs_bool)),
                C_Ast_Utils.CBool)
            end
        | _ =>
            (* Pointer arithmetic: p + n or n + p via focus_nth *)
            (case (binop, lhs_cty, rhs_cty) of
              (CEqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                let val l = Isa_Free ("v__lptr", isa_dummyT)
                    val r = Isa_Free ("v__rptr", isa_dummyT)
                    val eq_t = Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool}) $ l $ r
                in (C_Term_Build.mk_bind lhs' (Term.lambda l
                      (C_Term_Build.mk_bind rhs' (Term.lambda r
                        (C_Term_Build.mk_literal eq_t)))),
                    C_Ast_Utils.CBool)
                end
            | (CNeqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                let val l = Isa_Free ("v__lptr", isa_dummyT)
                    val r = Isa_Free ("v__rptr", isa_dummyT)
                    val neq_t =
                      Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool})
                        $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool}) $ l $ r)
                in (C_Term_Build.mk_bind lhs' (Term.lambda l
                      (C_Term_Build.mk_bind rhs' (Term.lambda r
                        (C_Term_Build.mk_literal neq_t)))),
                    C_Ast_Utils.CBool)
                end
            | (CEqOp0, C_Ast_Utils.CPtr _, _) =>
                if is_zero_int_const rhs then
                  (mk_ptr_is_null lhs', C_Ast_Utils.CBool)
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CEqOp0, _, C_Ast_Utils.CPtr _) =>
                if is_zero_int_const lhs then
                  (mk_ptr_is_null rhs', C_Ast_Utils.CBool)
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CNeqOp0, C_Ast_Utils.CPtr _, _) =>
                if is_zero_int_const rhs then
                  let val b = Isa_Free ("v__isnull", @{typ bool})
                  in (C_Term_Build.mk_bind (mk_ptr_is_null lhs') (Term.lambda b
                        (C_Term_Build.mk_literal
                          (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ b))),
                      C_Ast_Utils.CBool)
                  end
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CNeqOp0, _, C_Ast_Utils.CPtr _) =>
                if is_zero_int_const lhs then
                  let val b = Isa_Free ("v__isnull", @{typ bool})
                  in (C_Term_Build.mk_bind (mk_ptr_is_null rhs') (Term.lambda b
                        (C_Term_Build.mk_literal
                          (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ b))),
                      C_Ast_Utils.CBool)
                  end
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CLeOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison"
            | (CLeqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison"
            | (CGrOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison"
            | (CGeqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison"
            | (CLeOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CLeOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CLeqOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CLeqOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGrOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGrOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGeqOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGeqOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CAddOp0, C_Ast_Utils.CPtr elem_cty, _) =>
                mk_ptr_add lhs' rhs' rhs_cty elem_cty
            | (CAddOp0, _, C_Ast_Utils.CPtr elem_cty) =>
                (* n + p = p + n *)
                mk_ptr_add rhs' lhs' lhs_cty elem_cty
            | (CSubOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer subtraction"
            | _ =>
                let
                  (* C11 integer promotion and usual arithmetic conversions.
                     Shifts: each operand independently promoted, result = promoted LHS.
                     Other ops: usual_arith_conv determines common type. *)
                  val is_shift = case binop of CShlOp0 => true | CShrOp0 => true | _ => false
                  val (cty, lhs_p, rhs_p) =
                    if is_shift then
                      let val lp_cty = C_Ast_Utils.integer_promote lhs_cty
                          val rp_cty = C_Ast_Utils.integer_promote rhs_cty
                      in (lp_cty,
                          mk_implicit_cast (lhs', lhs_cty, lp_cty),
                          mk_implicit_cast
                            (mk_implicit_cast (rhs', rhs_cty, rp_cty), rp_cty, lp_cty)) end
                    else
                      let val conv_cty = C_Ast_Utils.usual_arith_conv (lhs_cty, rhs_cty)
                      in (conv_cty,
                          mk_implicit_cast (lhs', lhs_cty, conv_cty),
                          mk_implicit_cast (rhs', rhs_cty, conv_cty)) end
                  (* For > and >=, swap operands to use < and <= *)
                  val (l, r) = case binop of CGrOp0 => (rhs_p, lhs_p)
                                           | CGeqOp0 => (rhs_p, lhs_p)
                                           | _ => (lhs_p, rhs_p)
                  (* Comparisons return CBool — they produce Isabelle bool values *)
                  val result_cty = case binop of
                      CLeOp0 => C_Ast_Utils.CBool | CLeqOp0 => C_Ast_Utils.CBool
                    | CGrOp0 => C_Ast_Utils.CBool | CGeqOp0 => C_Ast_Utils.CBool
                    | CEqOp0 => C_Ast_Utils.CBool | CNeqOp0 => C_Ast_Utils.CBool
                    | _ => cty
                in case translate_binop cty binop of
                     Monadic f => (C_Term_Build.mk_bind2 f l r, result_cty)
                end)
        end
    (* p->field = rhs : struct field write through pointer *)
    | translate_expr tctx (CAssign0 (CAssignOp0, CMember0 (expr, field_ident, true, _), rhs, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val updater_name = "update_c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val updater_const = resolve_const ctxt updater_name
            val (ptr_expr, _) = translate_expr tctx expr
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME cty => cty
                             | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val rhs_cast = mk_implicit_cast (rhs', rhs_cty, field_cty)
            val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
        in (C_Term_Build.mk_bind rhs_cast (Term.lambda rhs_var
              (C_Term_Build.mk_sequence
                (C_Term_Build.mk_struct_field_write updater_const ptr_expr
                  (C_Term_Build.mk_literal rhs_var))
                (C_Term_Build.mk_literal rhs_var))),
            field_cty)
        end
    (* p->field op= rhs : compound struct field write through pointer *)
    | translate_expr tctx (CAssign0 (asgn_op, CMember0 (expr, field_ident, true, _), rhs, _)) =
        (case compound_assign_to_binop asgn_op of
           SOME binop =>
             let val field_name = C_Ast_Utils.ident_name field_ident
                 val struct_name = determine_struct_type tctx expr
                 val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
                 val updater_name = "update_c_" ^ struct_name ^ "_" ^ field_name
                 val ctxt = C_Trans_Ctxt.get_ctxt tctx
                 val accessor_const = resolve_const ctxt accessor_name
                 val updater_const = resolve_const ctxt updater_name
                 val (ptr_term, _) = translate_expr tctx expr
                 val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
                 val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
                 val struct_var = Isa_Free ("v__struct", isa_dummyT)
                 val new_var = Isa_Free ("v__new", isa_dummyT)
                 val old_val = accessor_const $ struct_var
                 val updated_struct = updater_const
                       $ Term.lambda (Isa_Free ("_uu", isa_dummyT)) new_var
                       $ struct_var
                 val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                                    SOME cty => cty
                                  | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
                 val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, field_cty)
             in case translate_binop field_cty binop of
                  Monadic f =>
                    (C_Term_Build.mk_bind ptr_term (Term.lambda ptr_var
                      (C_Term_Build.mk_bind
                        (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                        (Term.lambda struct_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_bind2 f
                              (C_Term_Build.mk_literal old_val)
                              rhs_term)
                            (Term.lambda new_var
                              (C_Term_Build.mk_sequence
                                (C_Term_Build.mk_ptr_write
                                  (C_Term_Build.mk_literal ptr_var)
                                  (C_Term_Build.mk_literal updated_struct))
                                (C_Term_Build.mk_literal new_var))))))), field_cty)
                | _ => unsupported "pure compound assignment on struct field"
             end
         | NONE => unsupported "unsupported compound operator on struct field")
    (* p->field[idx] = rhs : struct field array write through pointer.
       Uses resolved dereference_fun to avoid store_dereference_const adhoc overloading. *)
    | translate_expr tctx (CAssign0 (CAssignOp0,
          CIndex0 (CMember0 (expr, field_ident, true, _), idx_expr, _), rhs, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
            val updater_name = "update_c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_const ctxt accessor_name
            val updater_const = resolve_const ctxt updater_name
            val deref_const =
              resolve_const ctxt "dereference_fun"
              handle ERROR _ =>
                Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
            val (ptr_expr, _) = translate_expr tctx expr
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val struct_var = Isa_Free ("v__struct", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val v_var = Isa_Free ("v__rhs", isa_dummyT)
            val old_list = accessor_const $ struct_var
            val new_list = Isa_Const (\<^const_name>\<open>list_update\<close>,
                             isa_dummyT --> isa_dummyT --> isa_dummyT --> isa_dummyT)
                             $ old_list $ (C_Term_Build.mk_unat i_var) $ v_var
            val dummy_var = Isa_Free ("_uu__", isa_dummyT)
            val new_struct = updater_const $ (Term.lambda dummy_var new_list) $ struct_var
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ptr_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME (C_Ast_Utils.CPtr inner) => inner
                             | _ => unsupported "indexing non-array struct field")
            val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, field_cty)
            val write_term =
              C_Term_Build.mk_ptr_write
                (C_Term_Build.mk_literal ptr_var)
                (C_Term_Build.mk_literal new_struct)
            val write_term = mk_index_guard idx_p_cty i_var old_list write_term
            val assign_term =
              C_Term_Build.mk_bind rhs_term
                (Term.lambda v_var
                  (C_Term_Build.mk_bind ptr_expr
                    (Term.lambda ptr_var
                      (C_Term_Build.mk_bind deref_expr
                        (Term.lambda struct_var
                          (C_Term_Build.mk_bind idx_term
                            (Term.lambda i_var
                              (C_Term_Build.mk_sequence
                                write_term
                                (C_Term_Build.mk_literal v_var)))))))))
        in (assign_term, field_cty)
        end
    (* arr[idx] = rhs : array element write via focus *)
    | translate_expr tctx (CAssign0 (CAssignOp0, CIndex0 (arr_expr, idx_expr, _), rhs, _)) =
        let val (arr_term, arr_cty) = translate_expr tctx arr_expr
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
            val a_var = Isa_Free ("v__arr", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val v_var = Isa_Free ("v__rhs", isa_dummyT)
            val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) a_var
            val elem_cty = (case arr_cty of
                              C_Ast_Utils.CPtr inner => inner
                            | _ => unsupported "indexing non-array expression")
            val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, elem_cty)
            val write_term =
              C_Term_Build.mk_ptr_write
                (C_Term_Build.mk_literal focused)
                (C_Term_Build.mk_literal v_var)
            val write_term = mk_index_guard idx_p_cty i_var a_var write_term
            val assign_term =
              C_Term_Build.mk_bind rhs_term
                (Term.lambda v_var
                  (C_Term_Build.mk_bind arr_term
                    (Term.lambda a_var
                      (C_Term_Build.mk_bind idx_term
                        (Term.lambda i_var
                          (C_Term_Build.mk_sequence
                            write_term
                            (C_Term_Build.mk_literal v_var)))))))
        in (assign_term, elem_cty)
        end
    (* arr[idx] op= rhs : compound array element write *)
    | translate_expr tctx (CAssign0 (asgn_op, CIndex0 (arr_expr, idx_expr, _), rhs, _)) =
        (case compound_assign_to_binop asgn_op of
           SOME binop =>
             let val (arr_term, arr_cty) = translate_expr tctx arr_expr
                 val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
                 val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
                 val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
                 val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
                 val ctxt = C_Trans_Ctxt.get_ctxt tctx
                 val deref_const =
                   resolve_const ctxt "dereference_fun"
                   handle ERROR _ =>
                     Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
                 val a_var = Isa_Free ("v__arr", isa_dummyT)
                 val i_var = Isa_Free ("v__idx", isa_dummyT)
                 val list_var = Isa_Free ("v__list", isa_dummyT)
                 val new_var = Isa_Free ("v__new", isa_dummyT)
                 val nth_term = Isa_Const (\<^const_name>\<open>nth\<close>,
                                  isa_dummyT --> isa_dummyT --> isa_dummyT)
                                  $ list_var $ (C_Term_Build.mk_unat i_var)
                 val deref_expr =
                   Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>,
                     isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>,
                          isa_dummyT --> isa_dummyT) $ a_var)
                     $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>,
                          isa_dummyT --> isa_dummyT --> isa_dummyT)
                          $ Isa_Const (\<^const_name>\<open>call\<close>,
                              isa_dummyT --> isa_dummyT)
                          $ deref_const)
                 val focused = C_Term_Build.mk_focus_nth
                                 (C_Term_Build.mk_unat i_var) a_var
                 val elem_cty = (case arr_cty of
                                   C_Ast_Utils.CPtr inner => inner
                                 | _ => unsupported "indexing non-array expression")
                 val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, elem_cty)
                 val write_term =
                   C_Term_Build.mk_ptr_write
                     (C_Term_Build.mk_literal focused)
                     (C_Term_Build.mk_literal new_var)
                 val write_term = mk_index_guard idx_p_cty i_var list_var write_term
             in case translate_binop elem_cty binop of
                  Monadic f =>
                    (C_Term_Build.mk_bind arr_term (Term.lambda a_var
                      (C_Term_Build.mk_bind idx_term (Term.lambda i_var
                        (C_Term_Build.mk_bind deref_expr (Term.lambda list_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_bind2 f
                              (C_Term_Build.mk_literal nth_term)
                              rhs_term)
                            (Term.lambda new_var
                              (C_Term_Build.mk_sequence
                                write_term
                                (C_Term_Build.mk_literal new_var))))))))),
                     elem_cty)
                | _ => unsupported "pure compound assignment on array element"
             end
         | NONE => unsupported "unsupported compound operator on array element")
    | translate_expr tctx (CAssign0 (CAssignOp0, CVar0 (ident, _), rhs, _)) =
        let val name = C_Ast_Utils.ident_name ident
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, var, cty) =>
               let val rhs_cast = mk_implicit_cast (rhs', rhs_cty, cty)
               in (C_Term_Build.mk_bind rhs_cast (Term.lambda rhs_var
                     (C_Term_Build.mk_sequence
                       (C_Term_Build.mk_var_write var (C_Term_Build.mk_literal rhs_var))
                       (C_Term_Build.mk_literal rhs_var))),
                   cty)
               end
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               error ("micro_c_translate: assignment to parameter: " ^ name)
           | NONE => error ("micro_c_translate: undefined variable: " ^ name)
        end
    | translate_expr tctx (CAssign0 (CAssignOp0, CUnary0 (CIndOp0, lhs, _), rhs, _)) =
        (* *p = v : write through pointer *)
        let val (lhs', lhs_cty) = translate_expr tctx lhs
            val pointee_cty = (case lhs_cty of
                                 C_Ast_Utils.CPtr inner => inner
                               | _ => unsupported "dereference assignment on non-pointer expression")
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val rhs_cast = mk_implicit_cast (rhs', rhs_cty, pointee_cty)
            val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
        in (C_Term_Build.mk_bind rhs_cast (Term.lambda rhs_var
              (C_Term_Build.mk_sequence
                (C_Term_Build.mk_ptr_write lhs' (C_Term_Build.mk_literal rhs_var))
                (C_Term_Build.mk_literal rhs_var))),
            pointee_cty)
        end
    (* *p op= rhs : compound assignment through pointer dereference *)
    | translate_expr tctx (CAssign0 (asgn_op, CUnary0 (CIndOp0, ptr_expr, _), rhs, _)) =
        (case compound_assign_to_binop asgn_op of
           SOME binop =>
             let val (ptr_term, cty) = translate_expr tctx ptr_expr
                 val pointee_cty = (case cty of
                                      C_Ast_Utils.CPtr inner => inner
                                    | _ => unsupported "compound dereference assignment on non-pointer expression")
                 val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
                 val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, pointee_cty)
                 val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
                 val old_var = Isa_Free ("v__old", isa_dummyT)
                 val new_var = Isa_Free ("v__new", isa_dummyT)
             in case translate_binop pointee_cty binop of
                  Monadic f =>
                    (C_Term_Build.mk_bind ptr_term (Term.lambda ptr_var
                      (C_Term_Build.mk_bind
                        (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                        (Term.lambda old_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_bind2 f
                              (C_Term_Build.mk_literal old_var) rhs_term)
                            (Term.lambda new_var
                              (C_Term_Build.mk_sequence
                                (C_Term_Build.mk_ptr_write
                                  (C_Term_Build.mk_literal ptr_var)
                                  (C_Term_Build.mk_literal new_var))
                                (C_Term_Build.mk_literal new_var))))))), pointee_cty)
                | _ => unsupported "pure compound assignment on dereferenced pointer"
             end
         | NONE => unsupported "unsupported operator on dereferenced pointer")
    | translate_expr tctx (CAssign0 (asgn_op, CVar0 (ident, _), rhs, _)) =
        (* Compound assignment: x op= rhs -> read x, compute (x op rhs), write x, return new *)
        (case compound_assign_to_binop asgn_op of
             SOME binop =>
               let val name = C_Ast_Utils.ident_name ident
                   val (rhs_raw, rhs_cty) = translate_expr tctx rhs
               in case C_Trans_Ctxt.lookup_var tctx name of
                    SOME (C_Trans_Ctxt.Local, var, cty) =>
                      let val old_var = Isa_Free ("v__old", isa_dummyT)
                          val new_var = Isa_Free ("v__new", isa_dummyT)
                          val rhs' = mk_implicit_cast (rhs_raw, rhs_cty, cty)
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
           | NONE => unsupported "compound assignment or non-variable lhs")
    | translate_expr _ (CAssign0 _) =
        unsupported "non-variable lhs in assignment"
    | translate_expr tctx (CCall0 (CVar0 (ident, _), args, _)) =
        let val fname = C_Ast_Utils.ident_name ident
            val arg_terms_typed = List.map (translate_expr tctx) args
            val param_ctys = C_Trans_Ctxt.lookup_func_param_types tctx fname
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val func_ref =
              let val (full_name, _) = Term.dest_Const
                    (Proof_Context.read_const {proper = true, strict = false} ctxt ("c_" ^ fname))
              in SOME (Isa_Const (full_name, isa_dummyT)) end
              handle ERROR _ => NONE
            val _ =
              (case param_ctys of
                 SOME tys =>
                   if List.length arg_terms_typed = List.length tys then ()
                   else unsupported
                     ("function call arity mismatch for " ^ fname ^ ": expected " ^
                      Int.toString (List.length tys) ^ ", got " ^ Int.toString (List.length arg_terms_typed))
               | NONE =>
                   (case func_ref of
                      SOME _ => ()
                    | NONE => unsupported ("call to undeclared function: " ^ fname)))
            fun cast_args [] _ = []
              | cast_args ((arg_tm, _) :: rest) [] = arg_tm :: cast_args rest []
              | cast_args ((arg_tm, arg_cty) :: rest) (p_cty :: p_rest) =
                  mk_implicit_cast (arg_tm, arg_cty, p_cty) :: cast_args rest p_rest
            val arg_terms =
              (case param_ctys of
                 SOME tys => cast_args arg_terms_typed tys
               | NONE => List.map #1 arg_terms_typed)
            (* Use registered return type if available, fall back to CInt *)
            val ret_cty =
              (case C_Trans_Ctxt.lookup_func_return_type tctx fname of
                 SOME cty => cty
               | NONE => C_Ast_Utils.CInt)
        in
          (case func_ref of
             SOME fref => (C_Term_Build.mk_funcall fref arg_terms, ret_cty)
           | NONE => unsupported ("call to undeclared function: " ^ fname))
        end
    | translate_expr _ (CCall0 _) =
        unsupported "indirect function call (function pointers)"
    | translate_expr tctx (CUnary0 (CAdrOp0, CVar0 (ident, _), _)) =
        (* &x : address-of local variable. Local variables are already refs,
           so &x simply returns the ref variable as a literal value. *)
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, ref_var, cty) =>
               (C_Term_Build.mk_literal ref_var, C_Ast_Utils.CPtr cty)
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               unsupported ("address-of by-value parameter: " ^ name)
           | NONE => error ("micro_c_translate: undefined variable: " ^ name)
        end
    | translate_expr _ (CUnary0 (CAdrOp0, _, _)) =
        unsupported "address-of complex expression"
    | translate_expr tctx (CUnary0 (CIndOp0, expr, _)) =
        (* *p : dereference pointer. Resolve dereference_fun from locale context
           to avoid adhoc overloading ambiguity (same as CIndex0 reads).
           If the inner expression has CPtr ty, unwrap to ty. *)
        let val (expr', cty) = translate_expr tctx expr
            val result_cty = (case cty of
                                C_Ast_Utils.CPtr inner => inner
                              | _ => unsupported "dereference on non-pointer expression")
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val deref_const =
              resolve_const ctxt "dereference_fun"
              handle ERROR _ =>
                Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
            val deref_fn =
              Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                $ deref_const
        in (Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
              $ expr' $ deref_fn,
            result_cty) end
    | translate_expr tctx (CUnary0 (CCompOp0, expr, _)) =
        (* ~x : bitwise complement — C11: operand undergoes integer promotion *)
        let val (expr', cty) = translate_expr tctx expr
            val pcty = C_Ast_Utils.integer_promote cty
            val promoted = mk_implicit_cast (expr', cty, pcty)
            val not_const =
              if C_Ast_Utils.is_signed pcty
              then Isa_Const (\<^const_name>\<open>c_signed_not\<close>, isa_dummyT)
              else Isa_Const (\<^const_name>\<open>c_unsigned_not\<close>, isa_dummyT)
            val v = Isa_Free ("v__comp", isa_dummyT)
        in (C_Term_Build.mk_bind promoted (Term.lambda v (not_const $ v)), pcty) end
    | translate_expr tctx (CUnary0 (CMinOp0, expr, _)) =
        (* -x : unary minus, translate as 0 - x — C11: operand undergoes integer promotion *)
        let val (expr', cty) = translate_expr tctx expr
            val pcty = C_Ast_Utils.integer_promote cty
            val promoted = mk_implicit_cast (expr', cty, pcty)
            val zero = C_Term_Build.mk_literal_num pcty 0
            val sub_const =
              if C_Ast_Utils.is_signed pcty
              then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
              else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT)
        in (C_Term_Build.mk_bind2 sub_const zero promoted, pcty) end
    | translate_expr tctx (CUnary0 (CPreIncOp0, expr, _)) =
        translate_inc_dec tctx true true expr
    | translate_expr tctx (CUnary0 (CPostIncOp0, expr, _)) =
        translate_inc_dec tctx true false expr
    | translate_expr tctx (CUnary0 (CPreDecOp0, expr, _)) =
        translate_inc_dec tctx false true expr
    | translate_expr tctx (CUnary0 (CPostDecOp0, expr, _)) =
        translate_inc_dec tctx false false expr
    | translate_expr tctx (CUnary0 (CPlusOp0, expr, _)) =
        (* +x : unary plus — C11: operand undergoes integer promotion *)
        let val (expr', cty) = translate_expr tctx expr
            val pcty = C_Ast_Utils.integer_promote cty
        in (mk_implicit_cast (expr', cty, pcty), pcty) end
    | translate_expr tctx (CUnary0 (CNegOp0, expr, _)) =
        (* !x : logical NOT *)
        let val (expr', cty) = translate_expr tctx expr
            val b = mk_implicit_cast (expr', cty, C_Ast_Utils.CBool)
            val v = Isa_Free ("v__neg", @{typ bool})
        in (C_Term_Build.mk_bind b
              (Term.lambda v
                (C_Term_Build.mk_literal
                  (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ v))),
            C_Ast_Utils.CBool)
        end
    | translate_expr _ (CUnary0 _) =
        unsupported "unary expression"
    (* p->field[idx] : struct field (list) read via pointer, then index with nth.
       AST: CIndex0(CMember0(expr, field, true, _), idx, _)
       Uses resolved dereference_fun to avoid store_dereference_const adhoc overloading. *)
    | translate_expr tctx (CIndex0 (CMember0 (expr, field_ident, true, _), idx_expr, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_const ctxt accessor_name
            val deref_const =
              resolve_const ctxt "dereference_fun"
              handle ERROR _ =>
                Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
            val (ptr_expr, _) = translate_expr tctx expr
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val struct_var = Isa_Free ("v__struct", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val list_val = accessor_const $ struct_var
            val nth_term = Isa_Const (\<^const_name>\<open>nth\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                             $ list_val $ (C_Term_Build.mk_unat i_var)
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ptr_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val elem_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                              SOME (C_Ast_Utils.CPtr inner) => inner
                            | _ => unsupported "indexing non-array struct field")
            val value_term = C_Term_Build.mk_literal nth_term
            val value_term = mk_index_guard idx_p_cty i_var list_val value_term
        in (C_Term_Build.mk_bind ptr_expr (Term.lambda ptr_var
             (C_Term_Build.mk_bind deref_expr (Term.lambda struct_var
               (C_Term_Build.mk_bind idx_term (Term.lambda i_var
                 value_term))))), elem_cty)
        end
    (* arr[idx] : deref whole list, then index with nth.
       We resolve dereference_fun from the locale context instead of using
       store_dereference_const, which has ambiguous adhoc overloading
       (dereference_fun vs ro_dereference_fun) for read-only references. *)
    | translate_expr tctx (CIndex0 (arr_expr, idx_expr, _)) =
        let val (arr_term, arr_cty) = translate_expr tctx arr_expr
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
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
            val value_term = C_Term_Build.mk_literal nth_term
            val value_term = mk_index_guard idx_p_cty i_var list_var value_term
        in (C_Term_Build.mk_bind arr_term (Term.lambda a_var
             (C_Term_Build.mk_bind idx_term (Term.lambda i_var
               (C_Term_Build.mk_bind deref_expr
                 (Term.lambda list_var
                   value_term))))),
            (case arr_cty of
               C_Ast_Utils.CPtr inner => inner
             | _ => unsupported "indexing non-array expression"))
        end
    (* p->field : struct field read through pointer *)
    | translate_expr tctx (CMember0 (expr, field_ident, true, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_const ctxt accessor_name
            val (ptr_expr, _) = translate_expr tctx expr
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME cty => cty
                             | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
        in (C_Term_Build.mk_struct_field_read accessor_const ptr_expr, field_cty) end
    (* s.field : direct struct member access via value *)
    | translate_expr tctx (CMember0 (expr, field_ident, false, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val accessor_name = "c_" ^ struct_name ^ "_" ^ field_name
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_const ctxt accessor_name
            val (struct_expr, _) = translate_expr tctx expr
            val v = Isa_Free ("v__struct", isa_dummyT)
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME cty => cty
                             | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
        in (C_Term_Build.mk_bind struct_expr
              (Term.lambda v (C_Term_Build.mk_literal (accessor_const $ v))),
            field_cty) end
    | translate_expr tctx (CCond0 (cond, Some then_expr, else_expr, _)) =
        (* x ? y : z — ternary conditional *)
        let val (then', then_cty) = translate_expr tctx then_expr
            val (else', else_cty) = translate_expr tctx else_expr
            val result_cty =
              if then_cty = else_cty then then_cty
              else if C_Ast_Utils.is_ptr then_cty orelse C_Ast_Utils.is_ptr else_cty
              then unsupported "ternary with pointer operands"
              else C_Ast_Utils.usual_arith_conv (then_cty, else_cty)
            val then_cast = mk_implicit_cast (then', then_cty, result_cty)
            val else_cast = mk_implicit_cast (else', else_cty, result_cty)
        in (C_Term_Build.mk_two_armed_cond (ensure_bool_cond tctx cond) then_cast else_cast, result_cty) end
    | translate_expr tctx (CCond0 (cond, None, else_expr, _)) =
        (* GNU extension: x ?: y means x ? x : y *)
        let val (cond_term, cond_cty) = translate_expr tctx cond
            val (else', else_cty) = translate_expr tctx else_expr
            val result_cty =
              if cond_cty = else_cty then cond_cty
              else if C_Ast_Utils.is_ptr cond_cty orelse C_Ast_Utils.is_ptr else_cty
              then unsupported "GNU ?: with pointer operands"
              else C_Ast_Utils.usual_arith_conv (cond_cty, else_cty)
            val cond_v = Isa_Free ("v__condv", isa_dummyT)
            val cond_bool = mk_implicit_cast (C_Term_Build.mk_literal cond_v, cond_cty, C_Ast_Utils.CBool)
            val then_cast = mk_implicit_cast (C_Term_Build.mk_literal cond_v, cond_cty, result_cty)
            val else_cast = mk_implicit_cast (else', else_cty, result_cty)
        in (C_Term_Build.mk_bind cond_term
              (Term.lambda cond_v
                (C_Term_Build.mk_two_armed_cond cond_bool then_cast else_cast)),
            result_cty)
        end
    | translate_expr _ (CConst0 (CCharConst0 (CChar0 (c, _), _))) =
        (* Character literal — convert to ASCII ordinal *)
        (C_Term_Build.mk_literal_num C_Ast_Utils.CChar
           (intinf_to_int_checked "character literal" (integer_of_char c)),
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
            val target_cty =
              (case target_decl of
                 CDecl0 (specs, declrs, _) =>
                   let val struct_names = C_Trans_Ctxt.get_struct_names tctx
                       val base_cty =
                         (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME ct => SOME ct
                          | NONE =>
                              (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                                 SOME sn => SOME (C_Ast_Utils.CStruct sn)
                               | NONE => NONE))
                       val ptr_depth =
                         List.mapPartial
                           (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                             | _ => NONE) declrs
                         |> (fn d :: _ => d | [] => 0)
                   in case base_cty of
                        SOME ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth
                      | NONE => unsupported "cast to non-numeric type"
                   end
               | _ => unsupported "cast to non-numeric type")
        in (mk_implicit_cast (source_term, source_cty, target_cty), target_cty)
        end
    (* sizeof(type) *)
    | translate_expr tctx (CSizeofType0 (decl, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val cty =
              (case decl of
                 CDecl0 (specs, declrs, _) =>
                   let val struct_names = C_Trans_Ctxt.get_struct_names tctx
                       val base_cty =
                         (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME ct => SOME ct
                          | NONE =>
                              (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                                 SOME sn => SOME (C_Ast_Utils.CStruct sn)
                               | NONE => NONE))
                       val ptr_depth =
                         List.mapPartial
                           (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                             | _ => NONE) declrs
                         |> (fn d :: _ => d | [] => 0)
                   in case base_cty of
                        SOME ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth
                      | NONE => unsupported "sizeof non-numeric type"
                   end
               | _ => unsupported "sizeof non-numeric type")
            val isa_ty = C_Ast_Utils.hol_type_of cty
            val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
            val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
            val sizeof_nat = Isa_Const (\<^const_name>\<open>c_sizeof\<close>,
                                itself_ty --> @{typ nat}) $ type_term
            (* Wrap in of_nat to produce a word matching CULong *)
            val word_ty = C_Ast_Utils.hol_type_of C_Ast_Utils.CULong
            val sizeof_term = Isa_Const (\<^const_name>\<open>of_nat\<close>,
                                @{typ nat} --> word_ty) $ sizeof_nat
        in (C_Term_Build.mk_literal sizeof_term, C_Ast_Utils.CULong) end
    (* sizeof(expr) *)
    | translate_expr tctx (CSizeofExpr0 (expr, _)) =
        let fun sizeof_nat_term cty =
                  let val isa_ty = C_Ast_Utils.hol_type_of cty
                      val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
                      val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
                  in Isa_Const (\<^const_name>\<open>c_sizeof\<close>, itself_ty --> @{typ nat}) $ type_term end
            val sizeof_nat =
              (case expr of
                 CVar0 (ident, _) =>
                   let val name = C_Ast_Utils.ident_name ident
                   in case C_Trans_Ctxt.lookup_array_decl tctx name of
                        SOME (elem_cty, n) =>
                          Isa_Const (\<^const_name>\<open>Groups.times_class.times\<close>, @{typ nat} --> @{typ nat} --> @{typ nat})
                            $ HOLogic.mk_nat n
                            $ sizeof_nat_term elem_cty
                      | NONE =>
                          let val (_, cty) = translate_expr tctx expr
                          in sizeof_nat_term cty end
                   end
               | _ =>
                   let val (_, cty) = translate_expr tctx expr
                   in sizeof_nat_term cty end)
            val word_ty = C_Ast_Utils.hol_type_of C_Ast_Utils.CULong
            val sizeof_term = Isa_Const (\<^const_name>\<open>of_nat\<close>,
                                @{typ nat} --> word_ty) $ sizeof_nat
        in (C_Term_Build.mk_literal sizeof_term, C_Ast_Utils.CULong) end
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
    in mk_implicit_cast (cond_term, cond_cty, C_Ast_Utils.CBool)
    end

  (* Extract variable declarations as a list of (name, init_term, cty, array_meta) tuples.
     Handles multiple declarators in a single CDecl0.
     For pointer declarators (e.g. int *p = &x), the returned cty is CPtr base_cty. *)
  fun translate_decl tctx (CDecl0 (specs, declarators, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val struct_names = C_Trans_Ctxt.get_struct_names tctx
            val cty =
              (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                 SOME C_Ast_Utils.CVoid => C_Ast_Utils.CInt
               | SOME t => t
               | NONE =>
                   (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                      SOME sn => C_Ast_Utils.CStruct sn
                    | NONE => C_Ast_Utils.CInt))
            fun pointer_depth_of_declr declr = C_Ast_Utils.pointer_depth_of_declr declr
            fun has_array_declr (CDeclr0 (_, derived, _, _, _)) =
                  List.exists (fn CArrDeclr0 _ => true | _ => false) derived
            fun array_decl_size (CDeclr0 (_, derived, _, _, _)) =
                  List.mapPartial
                    (fn CArrDeclr0 (_, CArrSize0 (_, CConst0 (CIntConst0 (CInteger0 (n, _, _), _))), _) =>
                          if n < 0 then
                            error "micro_c_translate: negative array bound not supported"
                          else
                            SOME (intinf_to_int_checked "array bound" n)
                      | _ => NONE) derived
                  |> (fn n :: _ => SOME n | [] => NONE)
              | array_decl_size _ = NONE
            fun init_scalar_const_term target_cty (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
                  HOLogic.mk_number (C_Ast_Utils.hol_type_of target_cty)
                    (intinf_to_int_checked "array initializer literal" n)
              | init_scalar_const_term target_cty (CConst0 (CCharConst0 (CChar0 (c, _), _))) =
                  HOLogic.mk_number (C_Ast_Utils.hol_type_of target_cty)
                    (intinf_to_int_checked "array initializer char literal" (integer_of_char c))
              | init_scalar_const_term target_cty (CVar0 (ident, _)) =
                  let val name = C_Ast_Utils.ident_name ident
                  in case C_Trans_Ctxt.lookup_enum_const tctx name of
                       SOME value =>
                         HOLogic.mk_number (C_Ast_Utils.hol_type_of target_cty) value
                     | NONE =>
                         unsupported ("unsupported array initializer element: " ^ name)
                  end
              | init_scalar_const_term _ _ =
                  unsupported "non-constant array initializer element"
            fun process_one ((Some declr, Some (CInitExpr0 (init, _))), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val ptr_depth = pointer_depth_of_declr declr
                      val actual_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
                      val (init_raw, init_cty) = translate_expr tctx init
                      val init_term = mk_implicit_cast (init_raw, init_cty, actual_cty)
                      val arr_meta =
                        (case array_decl_size declr of
                           SOME n =>
                             if ptr_depth > 0
                             then SOME (C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1), n)
                             else NONE
                         | NONE => NONE)
                  in (name, init_term, actual_cty, arr_meta) end
              | process_one ((Some declr, Some (CInitList0 (init_list, _))), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val _ =
                        if has_array_declr declr then ()
                        else unsupported "initializer list for non-array declaration"
                      val ptr_depth = pointer_depth_of_declr declr
                      val actual_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
                      val elem_cty =
                        if ptr_depth > 0 then C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1) else cty
                      val elem_values = List.map
                        (fn ([], CInitExpr0 (e, _)) => init_scalar_const_term elem_cty e
                          | _ => unsupported "complex array initializer element") init_list
                      val declared_size = array_decl_size declr
                      val zero_value = HOLogic.mk_number (C_Ast_Utils.hol_type_of elem_cty) 0
                      val padded_values =
                        case declared_size of
                          SOME n =>
                            if List.length elem_values > n
                            then error "micro_c_translate: too many initializers for array"
                            else elem_values @ List.tabulate (n - List.length elem_values, fn _ => zero_value)
                        | NONE => elem_values
                      val list_term = HOLogic.mk_list (C_Ast_Utils.hol_type_of elem_cty) padded_values
                      val arr_meta =
                        (case declared_size of
                           SOME n => SOME (elem_cty, n)
                         | NONE => NONE)
                  in (name, C_Term_Build.mk_literal list_term, actual_cty, arr_meta) end
              | process_one ((Some declr, None), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val ptr_depth = pointer_depth_of_declr declr
                      val actual_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
                      val uninit = Isa_Const (\<^const_name>\<open>c_uninitialized\<close>, isa_dummyT)
                      val arr_meta =
                        (case array_decl_size declr of
                           SOME n =>
                             if ptr_depth > 0
                             then SOME (C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1), n)
                             else NONE
                         | NONE => NONE)
                  in (name, C_Term_Build.mk_literal uninit, actual_cty, arr_meta) end
              | process_one _ = unsupported "complex declarator"
        in List.map process_one declarators end
    | translate_decl _ _ = unsupported "complex declaration"

  (* Find label names nested in statements/items, preserving first-seen order. *)
  fun find_stmt_labels (CLabel0 (ident, inner, _, _)) =
        C_Ast_Utils.ident_name ident :: find_stmt_labels inner
    | find_stmt_labels (CCompound0 (_, items, _)) = find_block_labels items
    | find_stmt_labels (CIf0 (_, thn, Some els, _)) =
        find_stmt_labels thn @ find_stmt_labels els
    | find_stmt_labels (CIf0 (_, thn, None, _)) = find_stmt_labels thn
    | find_stmt_labels (CWhile0 (_, body, _, _)) = find_stmt_labels body
    | find_stmt_labels (CFor0 (_, _, _, body, _)) = find_stmt_labels body
    | find_stmt_labels (CSwitch0 (_, body, _)) = find_stmt_labels body
    | find_stmt_labels _ = []
  and find_block_labels [] = []
    | find_block_labels (CBlockStmt0 stmt :: rest) =
        find_stmt_labels stmt @ find_block_labels rest
    | find_block_labels (_ :: rest) = find_block_labels rest

  (* Translate a compound block, right-folding declarations into nested binds.
     Goto support: when goto_refs is non-empty, each statement is guarded to be
     skipped if any active goto flag is set. At a label site, the corresponding
     goto flag is reset (written to 0) and removed from the active list. *)
  fun translate_compound_items _ [] = C_Term_Build.mk_literal_unit
    | translate_compound_items tctx [CBlockStmt0 stmt] =
        (* Last item: if it's a label, handle goto flag reset *)
        (case stmt of
           CLabel0 (ident, inner_stmt, _, _) =>
             let val label_name = C_Ast_Utils.ident_name ident
                 val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
                 val active' = List.filter (fn n => n <> label_name)
                                   (C_Trans_Ctxt.get_active_goto_labels tctx)
                 val tctx' = C_Trans_Ctxt.set_active_goto_labels active' tctx
             in case C_Trans_Ctxt.lookup_goto_ref tctx label_name of
                  SOME goto_ref =>
                    C_Term_Build.mk_sequence
                      (C_Term_Build.mk_var_write goto_ref false_lit)
                      (translate_stmt tctx' inner_stmt)
                | NONE => translate_stmt tctx' stmt
             end
         | _ => translate_stmt tctx stmt)
    | translate_compound_items _ [CNestedFunDef0 _] =
        unsupported "nested function definition"
    | translate_compound_items tctx (CBlockDecl0 decl :: rest) =
        let val decls = translate_decl tctx decl
            fun fold_decls [] tctx' = translate_compound_items tctx' rest
              | fold_decls ((name, init_term, cty, arr_meta) :: ds) tctx' =
                  let val val_type =
                        let val ty = C_Ast_Utils.hol_type_of cty
                        in if ty = isa_dummyT then expr_value_type init_term else ty end
                      val alloc_expr =
                        mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt tctx') val_type init_term
                      val var = Isa_Free (name, expr_value_type alloc_expr)
                      val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var cty tctx'
                      val tctx'' = (case struct_name_of_cty cty of
                                      SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                    | NONE => tctx'')
                      val tctx'' = (case arr_meta of
                                      SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                    | NONE => tctx'')
                  in C_Term_Build.mk_bind alloc_expr
                       (Term.lambda var (fold_decls ds tctx'')) 
                  end
        in fold_decls decls tctx end
    | translate_compound_items tctx (CBlockStmt0 (CLabel0 (ident, inner_stmt, _, _)) :: rest) =
        (* Label site: reset this label's goto flag, translate the labeled statement,
           then continue with the rest of the block *)
        let val label_name = C_Ast_Utils.ident_name ident
            val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
            val active' = List.filter (fn n => n <> label_name)
                              (C_Trans_Ctxt.get_active_goto_labels tctx)
            val tctx' = C_Trans_Ctxt.set_active_goto_labels active' tctx
            val stmt_term = translate_stmt tctx' inner_stmt
            val rest_term = translate_compound_items tctx' rest
        in case C_Trans_Ctxt.lookup_goto_ref tctx label_name of
             SOME goto_ref =>
               C_Term_Build.mk_sequence
                 (C_Term_Build.mk_var_write goto_ref false_lit)
                 (C_Term_Build.mk_sequence stmt_term rest_term)
           | NONE =>
               (* Label not targeted by any goto — just translate normally *)
               C_Term_Build.mk_sequence stmt_term rest_term
        end
    | translate_compound_items tctx (CBlockStmt0 stmt :: rest) =
        let val inherited_labels = C_Trans_Ctxt.get_active_goto_labels tctx
            val goto_refs = C_Trans_Ctxt.get_goto_refs tctx
            (* Determine which goto labels appear later in this block.
               Only those need guarding at this point. *)
            val later_labels = find_block_labels rest
            val active_labels = distinct (op =) (inherited_labels @ later_labels)
            val tctx_stmt = C_Trans_Ctxt.set_active_goto_labels active_labels tctx
            val stmt_term = translate_stmt tctx_stmt stmt
            val active_goto_refs = List.filter
              (fn (name, _) => List.exists (fn l => l = name) active_labels) goto_refs
        in case (C_Trans_Ctxt.get_break_ref tctx,
                 C_Trans_Ctxt.get_continue_ref tctx,
                 active_goto_refs) of
             (NONE, NONE, []) =>
               C_Term_Build.mk_sequence stmt_term
                 (translate_compound_items tctx rest)
           | _ =>
               let val guard_var = Isa_Free ("v__guard", isa_dummyT)
                   val guard_nonzero =
                     Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                     $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                        $ guard_var
                        $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                   (* Resolve dereference_fun from locale context to avoid
                      store_dereference_const adhoc overloading issues *)
                   val ctxt = C_Trans_Ctxt.get_ctxt tctx
                   val deref_const =
                     resolve_const ctxt "dereference_fun"
                     handle ERROR _ =>
                       Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT)
                   val deref_fn =
                     Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                       $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                       $ deref_const
                   fun mk_guard_read ref_var =
                     Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                       $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ref_var)
                       $ deref_fn
                   fun wrap_guard NONE inner = inner
                     | wrap_guard (SOME ref_var) inner =
                         C_Term_Build.mk_bind (mk_guard_read ref_var)
                           (Term.lambda guard_var
                             (C_Term_Build.mk_two_armed_cond
                               (C_Term_Build.mk_literal guard_nonzero)
                               C_Term_Build.mk_literal_unit inner))
                   fun wrap_goto_guards [] inner = inner
                     | wrap_goto_guards ((_, ref_var) :: refs) inner =
                         wrap_guard (SOME ref_var) (wrap_goto_guards refs inner)
                   (* Split rest into guarded prefix (before first active label)
                      and unguarded suffix (label + remaining items).
                      The label code must be outside the guard so that the return type
                      from return statements at/after the label doesn't clash with
                      the guard's then-branch (literal unit). *)
                   fun split_at_active_label [] = ([], [])
                     | split_at_active_label (all as (CBlockStmt0 (CLabel0 (ident, _, _, _)) :: _)) =
                         let val lname = C_Ast_Utils.ident_name ident
                         in if List.exists (fn (n, _) => n = lname) active_goto_refs
                            then ([], all)
                            else let val (pre, post) = split_at_active_label (tl all)
                                 in (hd all :: pre, post) end
                         end
                     | split_at_active_label (item :: items) =
                         let val (pre, post) = split_at_active_label items
                         in (item :: pre, post) end
                   val (guarded_items, label_suffix) = split_at_active_label rest
                   val guarded_term = translate_compound_items tctx_stmt guarded_items
                   val label_term = translate_compound_items tctx label_suffix
                   val guarded_part =
                     wrap_guard (C_Trans_Ctxt.get_break_ref tctx)
                       (wrap_guard (C_Trans_Ctxt.get_continue_ref tctx)
                         (wrap_goto_guards active_goto_refs guarded_term))
               in C_Term_Build.mk_sequence stmt_term
                    (C_Term_Build.mk_sequence guarded_part label_term)
               end
        end
    | translate_compound_items _ _ = unsupported "block item"

  (* Translate a C expression to a pure nat term (for loop bounds).
     Only integer literals and parameter variables are supported. *)
  and translate_pure_nat_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        if n < 0
        then error "micro_c_translate: negative literal loop bound not supported in bounded-for lowering"
        else HOLogic.mk_nat (intinf_to_int_checked "for-loop bound literal" n)
    | translate_pure_nat_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, v, cty) =>
               if C_Ast_Utils.is_signed cty orelse C_Ast_Utils.is_bool cty orelse C_Ast_Utils.is_ptr cty
               then error ("micro_c_translate: loop bound parameter must be unsigned integer: " ^ name)
               else
               (* Convert parameter (word) to nat for range *)
               C_Term_Build.mk_unat v
           | _ => error ("micro_c_translate: loop bound must be a parameter or literal: " ^ name)
        end
    | translate_pure_nat_expr _ _ =
        error "micro_c_translate: unsupported loop bound expression"

  and try_translate_pure_nat_expr tctx e =
        SOME (translate_pure_nat_expr tctx e)
        handle ERROR _ => NONE

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
        let val (term, expr_cty) = translate_expr tctx expr
            val ret_term = case !current_ret_cty of
                SOME ret_cty => mk_implicit_cast (term, expr_cty, ret_cty)
              | NONE => term
        in C_Term_Build.mk_return_func ret_term end
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
        let
          fun translate_general_for () =
            let
              val CFor0 (init_part, cond_opt, step_opt, body, _) = stmt
              fun cond_term_of tctx' =
                    (case cond_opt of
                       Some c => ensure_bool_cond tctx' c
                     | None => C_Term_Build.mk_literal
                                 (Isa_Const (\<^const_name>\<open>HOL.True\<close>, @{typ bool})))
              fun step_term_of tctx' =
                    (case step_opt of
                       Some s => C_Term_Build.mk_sequence (expr_term tctx' s) C_Term_Build.mk_literal_unit
                     | None => C_Term_Build.mk_literal_unit)
              fun build_while tctx' =
                let val has_brk = contains_break body
                    val has_cont = contains_continue body
                    val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
                in if not has_brk andalso not has_cont then
                     let val cond_term = cond_term_of tctx'
                         val body_term =
                           C_Term_Build.mk_sequence (translate_stmt tctx' body) (step_term_of tctx')
                         val fuel_var = fresh_var [cond_term, body_term] "while_fuel" @{typ nat}
                     in C_Term_Build.mk_bounded_while fuel_var cond_term body_term end
                   else
                     let
                       val dummy_tctx = (if has_brk
                         then C_Trans_Ctxt.set_break_ref (Isa_Free ("__dummy_brk", isa_dummyT)) tctx'
                         else tctx')
                       val dummy_tctx = (if has_cont
                         then C_Trans_Ctxt.set_continue_ref (Isa_Free ("__dummy_cont", isa_dummyT)) dummy_tctx
                         else dummy_tctx)
                       val cond_raw = cond_term_of dummy_tctx
                       val body_raw = translate_stmt dummy_tctx body
                       val step_raw = step_term_of dummy_tctx
                       val break_ref = if has_brk
                         then SOME (fresh_var [cond_raw, body_raw, step_raw] "v__for_break" isa_dummyT)
                         else NONE
                       val continue_ref = if has_cont
                         then SOME (fresh_var [cond_raw, body_raw, step_raw] "v__for_cont" isa_dummyT)
                         else NONE
                       val tctx_loop = case break_ref of
                           SOME b => C_Trans_Ctxt.set_break_ref b tctx'
                         | NONE => tctx'
                       val tctx_loop = case continue_ref of
                           SOME c => C_Trans_Ctxt.set_continue_ref c tctx_loop
                         | NONE => tctx_loop
                       val body_term = translate_stmt tctx_loop body
                       val step_term = step_term_of tctx_loop
                       val step_term =
                         (case break_ref of
                            SOME br =>
                              let val bf = Isa_Free ("v__for_bf", isa_dummyT)
                                  val bf_nonzero =
                                    Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                                    $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                                       $ bf
                                       $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                              in C_Term_Build.mk_bind
                                   (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx_loop) br)
                                   (Term.lambda bf
                                     (C_Term_Build.mk_two_armed_cond
                                       (C_Term_Build.mk_literal bf_nonzero)
                                       C_Term_Build.mk_literal_unit
                                       step_term))
                              end
                          | NONE => step_term)
                       val cond_term = cond_term_of tctx_loop
                       val cond_term =
                         (case break_ref of
                            SOME br =>
                              let val bf = Isa_Free ("v__for_bfc", isa_dummyT)
                                  val bf_nonzero =
                                    Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                                    $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                                       $ bf
                                       $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                              in C_Term_Build.mk_bind
                                   (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx_loop) br)
                                   (Term.lambda bf
                                     (C_Term_Build.mk_two_armed_cond
                                       (C_Term_Build.mk_literal bf_nonzero)
                                       (C_Term_Build.mk_literal
                                         (Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})))
                                       cond_term))
                              end
                          | NONE => cond_term)
                       val body_with_resets =
                         (case continue_ref of
                            SOME cr =>
                              C_Term_Build.mk_sequence
                                (C_Term_Build.mk_var_write cr false_lit)
                                (C_Term_Build.mk_sequence body_term step_term)
                          | NONE => C_Term_Build.mk_sequence body_term step_term)
                       val fuel_var = fresh_var [cond_term, body_with_resets] "while_fuel" @{typ nat}
                       val loop_term = C_Term_Build.mk_bounded_while fuel_var cond_term body_with_resets
                       fun wrap_ref NONE t = t
                         | wrap_ref (SOME ref_var) t =
                             C_Term_Build.mk_bind
                               (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx') false_lit)
                               (Term.lambda ref_var t)
                     in wrap_ref break_ref (wrap_ref continue_ref loop_term) end
                end
            in
              case init_part of
                Left init_expr_opt =>
                  let val init_term = case init_expr_opt of
                            Some e => expr_term tctx e
                          | None => C_Term_Build.mk_literal_unit
                  in C_Term_Build.mk_sequence init_term (build_while tctx) end
              | Right init_decl =>
                  let val decls = translate_decl tctx init_decl
                      fun fold_decls [] tctx' = build_while tctx'
                        | fold_decls ((name, init, cty, arr_meta) :: ds) tctx' =
                            let val val_type =
                                  let val ty = C_Ast_Utils.hol_type_of cty
                                  in if ty = isa_dummyT then expr_value_type init else ty end
                                val alloc_expr =
                                  mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt tctx') val_type init
                                val var = Isa_Free (name, expr_value_type alloc_expr)
                                val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var cty tctx'
                                val tctx'' = (case struct_name_of_cty cty of
                                                SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                              | NONE => tctx'')
                                val tctx'' = (case arr_meta of
                                                SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                              | NONE => tctx'')
                            in C_Term_Build.mk_bind alloc_expr
                                 (Term.lambda var (fold_decls ds tctx'')) end
                  in fold_decls decls tctx end
            end
        in
          case try_bounded_for stmt of
            SOME (var_name, init_c_expr, bound_c_expr, body) =>
              if contains_break body orelse contains_continue body then
                translate_general_for ()
              else
                (case (try_translate_pure_nat_expr tctx init_c_expr,
                       try_translate_pure_nat_expr tctx bound_c_expr) of
                   (SOME start_nat, SOME bound_nat) =>
                     let val loop_cty =
                           (case stmt of
                              CFor0 (Right (CDecl0 (specs, [((Some declr, _), _)], _)), _, _, _, _) =>
                                let val base_cty = (case C_Ast_Utils.resolve_c_type_full
                                                          (C_Trans_Ctxt.get_typedef_tab tctx) specs of
                                                      SOME C_Ast_Utils.CVoid => C_Ast_Utils.CInt
                                                    | SOME t => t
                                                    | NONE => C_Ast_Utils.CInt)
                                in C_Ast_Utils.apply_ptr_depth base_cty
                                     (C_Ast_Utils.pointer_depth_of_declr declr)
                                end
                            | _ => C_Ast_Utils.CInt)
                         val loop_hol_ty = C_Ast_Utils.hol_type_of loop_cty
                         val loop_var = Isa_Free (var_name, loop_hol_ty)
                         val tctx' = C_Trans_Ctxt.add_var var_name C_Trans_Ctxt.Param loop_var loop_cty tctx
                         val body_term = translate_stmt tctx' body
                         val range = C_Term_Build.mk_upt_int_range start_nat bound_nat
                     in C_Term_Build.mk_raw_for_loop range (Term.lambda loop_var body_term) end
                 | _ => translate_general_for ())
          | NONE => translate_general_for ()
        end
    | translate_stmt tctx (CWhile0 (cond, body_stmt, is_do_while, _)) =
        let val has_brk = contains_break body_stmt
            val has_cont = contains_continue body_stmt
            val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
            val true_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1
        in if not has_brk andalso not has_cont then
             (* Simple case: no break/continue *)
             let val cond_term = ensure_bool_cond tctx cond
                 val body_term = translate_stmt tctx body_stmt
                 val fuel_var = fresh_var [cond_term, body_term] "while_fuel" @{typ nat}
                 val while_term = C_Term_Build.mk_bounded_while fuel_var cond_term body_term
             in if is_do_while
                then C_Term_Build.mk_sequence body_term while_term
                else while_term
             end
           else
             (* Allocate break/continue flag refs *)
             let (* Pre-set dummy refs so first-pass translation doesn't warn *)
                 val dummy_tctx = (if has_brk
                   then C_Trans_Ctxt.set_break_ref (Isa_Free ("__dummy_brk", isa_dummyT)) tctx
                   else tctx)
                 val dummy_tctx = (if has_cont
                   then C_Trans_Ctxt.set_continue_ref (Isa_Free ("__dummy_cont", isa_dummyT)) dummy_tctx
                   else dummy_tctx)
                 val cond_term_raw = ensure_bool_cond dummy_tctx cond
                 val body_raw = translate_stmt dummy_tctx body_stmt
                 val break_ref = if has_brk
                   then SOME (fresh_var [cond_term_raw, body_raw] "v__break" isa_dummyT)
                   else NONE
                 val continue_ref = if has_cont
                   then SOME (fresh_var [cond_term_raw, body_raw] "v__cont" isa_dummyT)
                   else NONE
                 (* Update context *)
                 val tctx' = case break_ref of
                     SOME b => C_Trans_Ctxt.set_break_ref b tctx | NONE => tctx
                 val tctx' = case continue_ref of
                     SOME c => C_Trans_Ctxt.set_continue_ref c tctx' | NONE => tctx'
                 (* Re-translate body with updated context (guards will be inserted) *)
                 val body_term = translate_stmt tctx' body_stmt
                 val cond_term = ensure_bool_cond tctx' cond
                 (* Augment condition: if break_flag then False else original_cond *)
                 val augmented_cond = case break_ref of
                     SOME br =>
                       let val bf = Isa_Free ("v__bf", isa_dummyT)
                           val bf_nonzero =
                             Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                             $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                                $ bf
                                $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                       in C_Term_Build.mk_bind (C_Term_Build.mk_var_read br)
                            (Term.lambda bf
                              (C_Term_Build.mk_two_armed_cond
                                (C_Term_Build.mk_literal bf_nonzero)
                                (C_Term_Build.mk_literal
                                  (Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})))
                                cond_term))
                       end
                   | NONE => cond_term
                 (* For continue: reset flag at start of each iteration *)
                 val body_with_resets = case continue_ref of
                     SOME cr =>
                       C_Term_Build.mk_sequence
                         (C_Term_Build.mk_var_write cr false_lit) body_term
                   | NONE => body_term
                 val fuel_var = fresh_var [augmented_cond, body_with_resets]
                                  "while_fuel" @{typ nat}
                 val while_term = C_Term_Build.mk_bounded_while
                                    fuel_var augmented_cond body_with_resets
                 val loop_term = if is_do_while
                   then C_Term_Build.mk_sequence body_with_resets while_term
                   else while_term
                 (* Wrap in Ref::new for break/continue refs *)
                 fun wrap_ref NONE t = t
                   | wrap_ref (SOME ref_var) t =
                       C_Term_Build.mk_bind
                         (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx) false_lit)
                         (Term.lambda ref_var t)
             in wrap_ref break_ref (wrap_ref continue_ref loop_term) end
        end
    | translate_stmt tctx (CSwitch0 (switch_expr, body, _)) =
        let val (switch_term_raw, switch_cty_raw) = translate_expr tctx switch_expr
            val switch_cty = C_Ast_Utils.integer_promote switch_cty_raw
            val switch_term = mk_implicit_cast (switch_term_raw, switch_cty_raw, switch_cty)
            val switch_var = fresh_var [switch_term] "v__switch" isa_dummyT
            val items = case body of
                          CCompound0 (_, items, _) => items
                        | _ => [CBlockStmt0 body]
            val groups = extract_switch_groups items
            val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
            val true_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1
            val switch_break_ref = fresh_var [switch_term] "v__switch_break" isa_dummyT
            (* break inside switch exits this switch, not any enclosing loop *)
            val tctx_sw = C_Trans_Ctxt.set_break_ref switch_break_ref
                            (C_Trans_Ctxt.clear_break_ref tctx)
            val all_have_break = List.all #has_break groups
                                 orelse List.length groups <= 1
            val any_case_match = make_any_case_match switch_var switch_cty tctx groups
            val default_cond = Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ any_case_match
            val brk = Isa_Free ("v__sw_break", isa_dummyT)
            val break_nonzero =
              Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
              $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                 $ brk
                 $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
            fun guard_break inner =
              C_Term_Build.mk_bind
                (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx_sw) switch_break_ref)
                (Term.lambda brk
                  (C_Term_Build.mk_two_armed_cond
                    (C_Term_Build.mk_literal break_nonzero)
                    C_Term_Build.mk_literal_unit
                    inner))
        in C_Term_Build.mk_bind
             (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx) false_lit)
             (Term.lambda switch_break_ref
               (if all_have_break then
                  (* Simple if-else chain: no fall-through *)
                  let fun build_chain [] = C_Term_Build.mk_literal_unit
                        | build_chain ({labels, body, ...} :: rest) =
                            let val body_term = translate_compound_items tctx_sw body
                                val rest_term = build_chain rest
                                val cond = C_Term_Build.mk_literal
                                             (make_switch_cond switch_var switch_cty tctx default_cond labels)
                            in C_Term_Build.mk_two_armed_cond cond body_term rest_term end
                  in C_Term_Build.mk_bind switch_term
                       (Term.lambda switch_var (build_chain groups))
                  end
                else
                  (* Fall-through: use matched_ref *)
                  let val matched_ref = fresh_var [switch_term] "v__matched" isa_dummyT
                      val matched_var = Isa_Free ("v__m", isa_dummyT)
                      val matched_nonzero =
                        Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                        $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                           $ matched_var
                           $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                      fun build_groups [] = C_Term_Build.mk_literal_unit
                        | build_groups ({labels, body, has_break} :: rest) =
                            let val body_term = translate_compound_items tctx_sw body
                                val label_cond =
                                  make_switch_cond switch_var switch_cty tctx default_cond labels
                                val full_cond =
                                  Isa_Const (\<^const_name>\<open>HOL.disj\<close>,
                                    @{typ bool} --> @{typ bool} --> @{typ bool})
                                  $ matched_nonzero $ label_cond
                                val group_action =
                                  C_Term_Build.mk_sequence body_term
                                    (if has_break
                                     then C_Term_Build.mk_var_write matched_ref false_lit
                                     else C_Term_Build.mk_var_write matched_ref true_lit)
                                val group_term =
                                  C_Term_Build.mk_bind (C_Term_Build.mk_var_read matched_ref)
                                    (Term.lambda matched_var
                                      (C_Term_Build.mk_two_armed_cond
                                        (C_Term_Build.mk_literal full_cond)
                                        group_action C_Term_Build.mk_literal_unit))
                            in guard_break (C_Term_Build.mk_sequence group_term (build_groups rest)) end
                  in C_Term_Build.mk_bind switch_term
                       (Term.lambda switch_var
                         (C_Term_Build.mk_bind
                         (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx) false_lit)
                         (Term.lambda matched_ref (build_groups groups))))
                  end))
        end
    | translate_stmt tctx (CGoto0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
            val is_forward_target =
              List.exists (fn n => n = name) (C_Trans_Ctxt.get_active_goto_labels tctx)
        in case C_Trans_Ctxt.lookup_goto_ref tctx name of
             SOME goto_ref =>
               if is_forward_target then
                 C_Term_Build.mk_var_write goto_ref
                   (C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1)
               else
                 unsupported ("non-forward goto not supported: " ^ name)
           | NONE => unsupported ("goto target not found: " ^ name)
        end
    | translate_stmt tctx (CLabel0 (_, stmt, _, _)) =
        (* Labels as standalone statements (not in compound block context):
           just translate the labeled statement. The label flag reset is handled
           by translate_compound_items when the label appears in a block. *)
        translate_stmt tctx stmt
    | translate_stmt tctx (CCont0 _) =
        (case C_Trans_Ctxt.get_continue_ref tctx of
           SOME cont_ref =>
             C_Term_Build.mk_var_write cont_ref
               (C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1)
         | NONE => unsupported "continue outside loop")
    | translate_stmt tctx (CBreak0 _) =
        (case C_Trans_Ctxt.get_break_ref tctx of
           SOME break_ref =>
             C_Term_Build.mk_var_write break_ref
               (C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1)
         | NONE => unsupported "break outside loop/switch")
    | translate_stmt _ _ =
        unsupported "statement"

  fun translate_fundef struct_tab enum_tab typedef_tab func_ret_types func_param_types ctxt
      (CFunDef0 (specs, declr, _, body, _)) =
    let
      val name = C_Ast_Utils.declr_name declr
      val _ =
        if C_Ast_Utils.declr_is_variadic declr then
          unsupported ("variadic functions are not supported: " ^ name)
        else ()
      (* Register the function's return type for cross-function call type tracking *)
      val ret_base_cty = (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME C_Ast_Utils.CVoid => C_Ast_Utils.CVoid
                          | SOME t => t | NONE => C_Ast_Utils.CInt)
      val ret_cty = C_Ast_Utils.apply_ptr_depth ret_base_cty
                      (C_Ast_Utils.pointer_depth_of_declr declr)
      val _ = func_ret_types := Symtab.update (name, ret_cty) (! func_ret_types)
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
            val ptr_depth = C_Ast_Utils.pointer_depth_of_decl pdecl
            val reg_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
        in reg_cty end) param_decls
      (* Pair names with type info; fall back to (CInt, false) if lengths differ *)
      val param_name_info = ListPair.zipEq (param_names, param_info)
        handle ListPair.UnequalLengths =>
          List.map (fn n => (n, C_Ast_Utils.CInt)) param_names
      (* Create free variables for each parameter.
         Pointer params use dummyT (Isabelle infers reference types).
         Non-pointer params get explicit types for signed/unsigned dispatch. *)
      val param_vars = List.map (fn (n, cty) =>
        let val hol_ty = if C_Ast_Utils.is_ptr cty then isa_dummyT else C_Ast_Utils.hol_type_of cty
        in (n, Isa_Free (n, hol_ty), cty) end) param_name_info
      (* Add parameters to the translation context as Param (by-value) *)
      val tctx = List.foldl
        (fn ((n, v, cty), ctx) => C_Trans_Ctxt.add_var n C_Trans_Ctxt.Param v cty ctx)
        (C_Trans_Ctxt.make ctxt struct_tab enum_tab typedef_tab func_ret_types func_param_types) param_vars
      (* Annotate struct pointer parameters with their struct type.
         Uses _full variant to also recognize typedef'd struct names. *)
      val struct_names = Symtab.keys struct_tab
      val tctx = List.foldl (fn (pdecl, ctx) =>
        case (C_Ast_Utils.param_name pdecl,
              C_Ast_Utils.extract_struct_type_from_decl_full struct_names pdecl) of
          (SOME n, SOME sn) => C_Trans_Ctxt.set_struct_type n sn ctx
        | _ => ctx) tctx param_decls
      (* Promote parameters that are assigned in the body to local variables.
         For each promoted parameter, wrap the body with Ref::new(literal param)
         and register the ref as a Local in the context (shadowing the Param). *)
      val assigned_names = C_Ast_Utils.find_assigned_vars body
      val promoted_params = List.filter (fn (n, _, _) =>
        List.exists (fn a => a = n) assigned_names) param_vars
      val (tctx, promoted_bindings) = List.foldl
        (fn ((n, orig_var, cty), (ctx, binds)) =>
          let val ref_var = Isa_Free (n ^ "_ref", isa_dummyT)
              val ctx' = C_Trans_Ctxt.add_var n C_Trans_Ctxt.Local ref_var cty ctx
          in (ctx', binds @ [(ref_var, orig_var)]) end)
        (tctx, []) promoted_params
      (* Allocate goto flag references for forward-only goto support.
         Each label targeted by a goto gets a flag ref initialized to 0. *)
      val goto_labels = C_Ast_Utils.find_goto_targets body
      val goto_refs = List.map (fn label_name =>
        (label_name, Isa_Free ("v__goto_" ^ label_name, isa_dummyT))) goto_labels
      val tctx = C_Trans_Ctxt.set_goto_refs goto_refs tctx
      (* Set current return type for implicit narrowing in CReturn0 *)
      val _ = current_ret_cty := SOME ret_cty
      val body_term = translate_stmt tctx body
      (* Wrap body with Ref::new for each promoted parameter *)
      val body_term = List.foldr
        (fn ((ref_var, orig_var), b) =>
          C_Term_Build.mk_bind
            (mk_resolved_var_alloc ctxt (C_Term_Build.mk_literal orig_var))
            (Term.lambda ref_var b))
        body_term promoted_bindings
      (* Wrap body with Ref::new(0) for each goto flag ref *)
      val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
      val body_term = List.foldr
        (fn ((_, ref_var), b) =>
          C_Term_Build.mk_bind
            (mk_resolved_var_alloc ctxt false_lit)
            (Term.lambda ref_var b))
        body_term goto_refs
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
      val builtin_typedefs = [
        ("uint8_t",  C_Ast_Utils.CChar),
        ("int8_t",   C_Ast_Utils.CSChar),
        ("uint16_t", C_Ast_Utils.CUShort),
        ("int16_t",  C_Ast_Utils.CShort),
        ("uint32_t", C_Ast_Utils.CUInt),
        ("int32_t",  C_Ast_Utils.CInt),
        ("uint64_t", C_Ast_Utils.CULong),
        ("int64_t",  C_Ast_Utils.CLong),
        ("size_t",   C_Ast_Utils.CULong)
      ]
      (* Extract struct definitions to build the struct field registry.
         Use fold/update to allow user typedefs to override builtins. *)
      val typedef_defs_early = builtin_typedefs @ C_Ast_Utils.extract_typedefs tu
      val typedef_tab_early = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                                Symtab.empty typedef_defs_early
      val struct_defs = C_Ast_Utils.extract_struct_defs_with_types typedef_tab_early tu
      val struct_tab = Symtab.make struct_defs
      val _ = List.app (fn (sname, fields) =>
        writeln ("Registered struct: " ^ sname ^ " with fields: " ^
                 String.concatWith ", " (List.map #1 fields))) struct_defs
      (* Extract enum constant definitions *)
      val enum_defs = C_Ast_Utils.extract_enum_defs tu
      val enum_tab = Symtab.make enum_defs
      val _ = if null enum_defs then () else
        List.app (fn (name, value) =>
          writeln ("Registered enum constant: " ^ name ^ " = " ^
                   Int.toString value)) enum_defs
      (* Extract typedef mappings *)
      val typedef_defs = builtin_typedefs @ C_Ast_Utils.extract_typedefs tu
      val typedef_tab = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                          Symtab.empty typedef_defs
      val _ = if null typedef_defs then () else
        List.app (fn (name, _) =>
          writeln ("Registered typedef: " ^ name)) typedef_defs
      val fundefs = C_Ast_Utils.extract_fundefs tu
      val _ = List.app (fn C_Ast.CFunDef0 (_, declr, _, _, _) =>
                  let val name = C_Ast_Utils.declr_name declr
                  in if C_Ast_Utils.declr_is_variadic declr then
                       error ("micro_c_translate: unsupported C construct: variadic function definition: " ^ name)
                     else ()
                  end) fundefs
      (* Pre-register all function signatures so calls to later-defined
         functions are translated with the correct result and argument types. *)
      fun param_cty_of_decl pdecl =
            (case pdecl of
               C_Ast.CDecl0 (specs, _, _) =>
                 let
                   val base = (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                                 SOME t => t
                               | NONE => C_Ast_Utils.CInt)
                   val depth = C_Ast_Utils.pointer_depth_of_decl pdecl
                 in C_Ast_Utils.apply_ptr_depth base depth end
             | _ => C_Ast_Utils.CInt)
      fun signature_of_declr specs declr =
            let val fname = C_Ast_Utils.declr_name declr
                val _ =
                  if C_Ast_Utils.declr_is_variadic declr then
                    error ("micro_c_translate: unsupported C construct: variadic function declaration: " ^ fname)
                  else ()
                val rty_base = (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                                  SOME C_Ast_Utils.CVoid => C_Ast_Utils.CVoid
                                | SOME t => t | NONE => C_Ast_Utils.CInt)
                val rty = C_Ast_Utils.apply_ptr_depth rty_base
                            (C_Ast_Utils.pointer_depth_of_declr declr)
                val ptys = List.map param_cty_of_decl (C_Ast_Utils.extract_param_decls declr)
            in (fname, (rty, ptys)) end
      fun declr_is_function (C_Ast.CDeclr0 (_, derived, _, _, _)) =
            List.exists (fn C_Ast.CFunDeclr0 _ => true | _ => false) derived
        | declr_is_function _ = false
      fun signatures_from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CDecl0 (specs, declarators, _))) =
            List.mapPartial
              (fn ((C_Ast.Some declr, _), _) =>
                    if declr_is_function declr then SOME (signature_of_declr specs declr) else NONE
                | _ => NONE)
              declarators
        | signatures_from_ext_decl _ = []
      val C_Ast.CTranslUnit0 (ext_decls, _) = tu
      fun fundef_signature (C_Ast.CFunDef0 (specs, declr, _, _, _)) =
            signature_of_declr specs declr
      val decl_signatures = List.concat (List.map signatures_from_ext_decl ext_decls)
      val signatures = decl_signatures @ List.map fundef_signature fundefs
      val func_ret_table = List.foldl
        (fn ((n, (rty, _)), tab) => Symtab.update (n, rty) tab)
        Symtab.empty signatures
      val func_ret_types = Unsynchronized.ref func_ret_table
      val func_param_table = List.foldl
        (fn ((n, (_, ptys)), tab) => Symtab.update (n, ptys) tab)
        Symtab.empty signatures
      val func_param_types = Unsynchronized.ref func_param_table
    in
      (* Translate and define each function one at a time, so that later
         functions can reference earlier ones via Syntax.check_term. *)
      List.foldl (fn (fundef, lthy) =>
        let val (name, term) = C_Translate.translate_fundef
              struct_tab enum_tab typedef_tab func_ret_types func_param_types lthy fundef
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

text \<open>
  The @{text "micro_c_file"} command loads C source from an external file,
  parses it using Isabelle/C, and generates core monad definitions.
  This enables keeping verified C code in separate @{text ".c"} files,
  identical to upstream sources.

  Usage: @{text [display] "micro_c_file \<open>path/to/file.c\<close>"}
\<close>

ML \<open>
local
  val semi = Scan.option \<^keyword>\<open>;\<close>;
in
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>micro_c_file\<close>
    "load C file and generate core monad definitions"
    (Resources.parse_file --| semi >> (fn get_file => fn lthy =>
      let
        val thy = Proof_Context.theory_of lthy
        val {src_path, lines, digest, pos} : Token.file = get_file thy

        (* Step 1: Parse the C file using Isabelle/C's parser *)
        val source = Input.source true (cat_lines lines) (pos, pos)
        val context' = C_Module.exec_eval source (Context.Theory thy)
        val thy' = Context.theory_of context'

        (* Step 2: Register file dependency so Isabelle rebuilds if file changes *)
        val lthy = Local_Theory.background_theory
                     (Resources.provide (src_path, digest)) lthy

        (* Step 3: Retrieve parsed AST and translate *)
        val tu = get_CTranslUnit thy'
      in
        C_Def_Gen.process_translation_unit tu lthy
      end))
end
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

text \<open>Smoke test: static function qualifier (silently ignored).\<close>
micro_c_translate \<open>
static unsigned int static_test(unsigned int x) { return x + 1; }
\<close>

thm c_static_test_def

text \<open>Smoke test: fixed-width integer types via built-in typedefs.
     Note: the C parser requires explicit typedef declarations in the source
     since it does not know about stdint.h types natively.\<close>
micro_c_translate \<open>
typedef unsigned short uint16_t;
uint16_t u16_add(uint16_t a, uint16_t b) { return a + b; }
\<close>

thm c_u16_add_def

micro_c_translate \<open>
typedef int int32_t;
int32_t i32_negate(int32_t x) { return 0 - x; }
\<close>

thm c_i32_negate_def

micro_c_translate \<open>
typedef unsigned long size_t;
size_t size_add(size_t a, size_t b) { return a + b; }
\<close>

thm c_size_add_def

text \<open>Smoke test: void return type.\<close>
micro_c_translate \<open>
void void_noop(void) { return; }
\<close>

thm c_void_noop_def

text \<open>Smoke test: uint8_t pointer arithmetic (byte buffer).\<close>
micro_c_translate \<open>
typedef unsigned char uint8_t;
uint8_t read_byte(uint8_t *buf, unsigned int idx) { return *(buf + idx); }
\<close>

thm c_read_byte_def

text \<open>Smoke test: array parameter syntax (int arr[]).\<close>
micro_c_translate \<open>
unsigned int arr_param_test(unsigned int arr[], unsigned int i) {
  return arr[i];
}
\<close>

thm c_arr_param_test_def

text \<open>Smoke test: local array initializer.\<close>
micro_c_translate \<open>
void local_arr_test(void) {
  unsigned int arr[] = {1, 2, 3};
  unsigned int x = arr[1];
}
\<close>

thm c_local_arr_test_def

text \<open>Smoke test: function call return type tracking.
     helper returns int16_t (signed short), caller uses result in arithmetic.
     The addition should use c_signed_add (not c_unsigned_add).\<close>
micro_c_translate \<open>
typedef short int16_t;
int16_t ret_type_helper(int16_t x) { return x; }
int16_t ret_type_caller(int16_t a, int16_t b) {
  return ret_type_helper(a) + ret_type_helper(b);
}
\<close>

thm c_ret_type_helper_def c_ret_type_caller_def

text \<open>Smoke test: zero-initialized array with declared size.\<close>
micro_c_translate \<open>
typedef unsigned char uint8_t;
void zero_init_test(void) {
  uint8_t t[4] = {0};
  uint8_t x = t[2];
}
\<close>

thm c_zero_init_test_def

end
