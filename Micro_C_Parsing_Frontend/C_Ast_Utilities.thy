theory C_Ast_Utilities
  imports
    C_ABI_And_Compiler
    "Shallow_Micro_C.C_Numeric_Types"
    "Shallow_Micro_C.C_Sizeof"
    "Shallow_Micro_C.C_Memory_Operations"
    "Shallow_Micro_C.C_Void_Pointer"
begin

subsection \<open>AST Utilities\<close>

text \<open>
  C11 standard sections implemented in this module:

  \<^item> \<^bold>\<open>\<section>6.2.5\<close> (Types): @{text is_signed}, @{text is_unsigned_int}, @{text is_bool}, @{text is_ptr}
    classify C numeric types by signedness, boolean, and pointer status.
  \<^item> \<^bold>\<open>\<section>5.2.4.2.1\<close> (Sizes of integer types): @{text bit_width_of} returns the bit width
    of each integer type, parameterized by the ABI profile for @{text long}/@{text pointer}.
  \<^item> \<^bold>\<open>\<section>6.3.1.1p1\<close> (Integer conversion rank): @{text type_rank} assigns conversion ranks.
  \<^item> \<^bold>\<open>\<section>6.3.1.1p2\<close> (Integer promotion): @{text integer_promote} promotes sub-int types to int.
  \<^item> \<^bold>\<open>\<section>6.3.1.8\<close> (Usual arithmetic conversions): @{text usual_arith_conv} determines the
    common type for binary arithmetic operations.
  \<^item> \<^bold>\<open>\<section>6.4.4.1p5\<close> (Integer constant types): @{text int_literal_type} determines the C type
    of an integer constant from its suffix flags.
  \<^item> \<^bold>\<open>\<section>6.7.2\<close> (Type specifiers): @{text resolve_c_type} resolves a list of C declaration
    specifiers into a @{text c_numeric_type}.
  \<^item> \<^bold>\<open>\<section>7.20\<close> (Integer types \<open><stdint.h>\<close>), \<^bold>\<open>\<section>7.19\<close> (\<open><stddef.h>\<close>):
    @{text builtin_typedefs} maps fixed-width type names to their @{text c_numeric_type}.
\<close>

text \<open>Helper functions for extracting information from Isabelle/C's AST nodes.\<close>

ML \<open>
structure C_Ast_Utils : sig
  datatype c_numeric_type = CInt | CUInt | CChar | CSChar
                          | CShort | CUShort | CLong | CULong
                          | CLongLong | CULongLong
                          | CInt128 | CUInt128 | CBool
                          | CPtr of c_numeric_type | CVoid
                          | CStruct of string
                          | CUnion of string

  val is_signed : c_numeric_type -> bool
  val is_bool : c_numeric_type -> bool
  val is_ptr : c_numeric_type -> bool
  val is_unsigned_int : c_numeric_type -> bool
  val set_abi_profile : C_ABI.profile -> unit
  val set_ref_universe_types : typ -> typ -> unit
  val set_parametric_struct_names : string list -> unit
  val set_pure_function_names : string list -> unit
  val get_abi_profile : unit -> C_ABI.profile
  val current_abi_name : unit -> string
  val pointer_uint_cty : unit -> c_numeric_type
  val pointer_int_cty : unit -> c_numeric_type
  val bit_width_of : c_numeric_type -> int option
  val sizeof_c_type : c_numeric_type -> int
  val alignof_c_type : c_numeric_type -> int
  val intinf_to_int_checked : string -> IntInf.int -> int
  val struct_name_of_cty : c_numeric_type -> string option
  val builtin_typedefs : unit -> (string * c_numeric_type) list
  val hol_type_of : c_numeric_type -> typ
  val cty_to_record_typ : string -> c_numeric_type -> typ option
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
  val extract_union_type_from_specs : C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list
                                      -> string option
  val extract_union_type_from_specs_full : string list
                                           -> C_Ast.nodeInfo C_Ast.cDeclarationSpecifier list
                                           -> string option
  val extract_union_type_from_decl_full : string list
                                          -> C_Ast.nodeInfo C_Ast.cDeclaration -> string option
  val extract_union_defs_with_types : c_numeric_type Symtab.table
                                      -> C_Ast.nodeInfo C_Ast.cTranslationUnit
                                      -> (string * (string * c_numeric_type) list) list
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
  val expr_has_side_effect : C_Ast.nodeInfo C_Ast.cExpression -> bool
  val expr_has_unsequenced_ub_risk :
      C_Ast.nodeInfo C_Ast.cExpression -> C_Ast.nodeInfo C_Ast.cExpression -> bool
  val find_assigned_vars : C_Ast.nodeInfo C_Ast.cStatement -> string list
  val find_goto_targets : C_Ast.nodeInfo C_Ast.cStatement -> string list
  val find_called_functions : C_Ast.nodeInfo C_Ast.cFunctionDef -> string list
  val find_list_backed_aliases : (string * c_numeric_type) list Symtab.table
                                 -> string list Symtab.table
                                 -> C_Ast.nodeInfo C_Ast.cFunctionDef -> string list
  val find_indexed_base_vars : C_Ast.nodeInfo C_Ast.cFunctionDef -> string list
  val find_named_calls_with_args :
      C_Ast.nodeInfo C_Ast.cFunctionDef
      -> (string * C_Ast.nodeInfo C_Ast.cExpression list) list
  val fundef_is_pure_with : unit Symtab.table -> C_Ast.nodeInfo C_Ast.cFunctionDef -> bool
  val extract_string_literal : C_Ast.nodeInfo C_Ast.cStringLiteral -> string
  val eval_const_int_expr : (C_Ast.nodeInfo C_Ast.cDeclaration -> c_numeric_type option)
                            -> C_Ast.nodeInfo C_Ast.cExpression -> IntInf.int

  val extract_struct_defs_with_types : c_numeric_type Symtab.table
                                       -> C_Ast.nodeInfo C_Ast.cTranslationUnit
                                       -> (string * (string * c_numeric_type) list) list
  val derive_parametric_struct_names : (string * (string * c_numeric_type) list) list
                                       -> string list
  val extract_struct_record_defs : string -> c_numeric_type Symtab.table
                                   -> C_Ast.nodeInfo C_Ast.cTranslationUnit
                                   -> (string * (string * typ option) list) list
  val extract_struct_array_fields : C_Ast.nodeInfo C_Ast.cTranslationUnit
                                    -> (string * string list) list
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
                          | CShort | CUShort | CLong | CULong
                          | CLongLong | CULongLong
                          | CInt128 | CUInt128 | CBool
                          | CPtr of c_numeric_type | CVoid
                          | CStruct of string
                          | CUnion of string

  val current_abi_profile : C_ABI.profile Unsynchronized.ref =
    Unsynchronized.ref C_ABI.LP64_LE

  val current_ref_addr_ty : Term.typ Unsynchronized.ref =
    Unsynchronized.ref (Term.TFree ("'addr", []))
  val current_ref_gv_ty : Term.typ Unsynchronized.ref =
    Unsynchronized.ref (Term.TFree ("'gv", []))
  val current_parametric_struct_names : unit Symtab.table Unsynchronized.ref =
    Unsynchronized.ref Symtab.empty
  val current_pure_function_names : unit Symtab.table Unsynchronized.ref =
    Unsynchronized.ref Symtab.empty

  fun set_abi_profile abi = (current_abi_profile := abi)
  fun set_ref_universe_types (addr_ty: Term.typ) (gv_ty: Term.typ) =
    (current_ref_addr_ty := addr_ty; current_ref_gv_ty := gv_ty)
  fun set_parametric_struct_names names =
    current_parametric_struct_names :=
      List.foldl (fn (n, tab) => Symtab.update (n, ()) tab) Symtab.empty names
  fun set_pure_function_names names =
    current_pure_function_names :=
      List.foldl (fn (n, tab) => Symtab.update (n, ()) tab) Symtab.empty names
  fun get_abi_profile () = !current_abi_profile
  fun current_abi_name () = C_ABI.profile_name (get_abi_profile ())
  fun pointer_uint_cty () =
    if C_ABI.pointer_bits (get_abi_profile ()) = 64 then CULong else CUInt
  fun pointer_int_cty () =
    if C_ABI.pointer_bits (get_abi_profile ()) = 64 then CLong else CInt

  (* C11 \<section>6.2.5p4-6: signed integer types are signed char, short int, int, long int,
     long long int, and the extended signed types (__int128).
     \<section>6.2.5p6: unsigned types are the corresponding unsigned variants.
     \<section>6.2.5p2: _Bool is a separate unsigned integer type.
     \<section>6.2.5p20: pointer types are derived types, not integer types. *)
  fun is_signed CInt   = true
    | is_signed CSChar  = true
    | is_signed CShort  = true
    | is_signed CLong   = true
    | is_signed CLongLong = true
    | is_signed CInt128  = true
    | is_signed (CPtr _) = false
    | is_signed CVoid   = false
    | is_signed (CStruct _) = false
    | is_signed (CUnion _) = false
    | is_signed _       = false

  fun is_bool CBool = true
    | is_bool _     = false

  fun is_ptr (CPtr _) = true
    | is_ptr _        = false

  fun is_unsigned_int cty = not (is_signed cty) andalso not (is_bool cty)
                            andalso not (is_ptr cty) andalso cty <> CVoid
                            andalso (case cty of CStruct _ => false | CUnion _ => false | _ => true)

  (* C11 \<section>5.2.4.2.1: minimum widths from <limits.h>.
     We use exact widths matching standard ABI conventions:
     char=8, short=16, int=32, long long=64. long and pointer widths
     are ABI-dependent (queried from the current ABI profile). *)
  fun bit_width_of CChar = SOME 8
    | bit_width_of CSChar = SOME 8
    | bit_width_of CShort = SOME 16
    | bit_width_of CUShort = SOME 16
    | bit_width_of CInt = SOME 32
    | bit_width_of CUInt = SOME 32
    | bit_width_of CLong = SOME (C_ABI.long_bits (get_abi_profile ()))
    | bit_width_of CULong = SOME (C_ABI.long_bits (get_abi_profile ()))
    | bit_width_of CLongLong = SOME 64
    | bit_width_of CULongLong = SOME 64
    | bit_width_of CInt128 = SOME 128
    | bit_width_of CUInt128 = SOME 128
    | bit_width_of (CPtr _) = SOME (C_ABI.pointer_bits (get_abi_profile ()))
    | bit_width_of _ = NONE

  fun sizeof_c_type cty =
    (case bit_width_of cty of
       SOME bits => bits div 8
     | NONE => error "micro_c_translate: sizeof: unsupported type")

  fun alignof_c_type CInt128 = 16
    | alignof_c_type CUInt128 = 16
    | alignof_c_type cty = Int.min (sizeof_c_type cty, 8)

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

  fun struct_name_of_cty (CStruct sname) = SOME sname
    | struct_name_of_cty (CPtr (CStruct sname)) = SOME sname
    | struct_name_of_cty (CUnion sname) = SOME sname
    | struct_name_of_cty (CPtr (CUnion sname)) = SOME sname
    | struct_name_of_cty _ = NONE

  (* C11 \<section>7.20 <stdint.h>: exact-width integer types (uint8_t, int32_t, etc.)
     C11 \<section>7.19 <stddef.h>: size_t
     C11 \<section>7.20.1.4: uintptr_t/intptr_t -- integer types capable of holding a pointer.
     Mappings are ABI-dependent for pointer-width types (size_t, uintptr_t, intptr_t). *)
  fun builtin_typedefs () =
    let
      val uintptr_cty = pointer_uint_cty ()
      val intptr_cty = pointer_int_cty ()
    in
      [ ("uint8_t", CChar), ("int8_t", CSChar),
        ("uint16_t", CUShort), ("int16_t", CShort),
        ("uint32_t", CUInt), ("int32_t", CInt),
        ("uint64_t", CULongLong), ("int64_t", CLongLong),
        ("size_t", uintptr_cty), ("uintptr_t", uintptr_cty), ("intptr_t", intptr_cty),
        ("__int128_t", CInt128), ("__uint128_t", CUInt128) ]
    end

  fun hol_type_of CBool   = @{typ bool}
    | hol_type_of CInt    = \<^typ>\<open>c_int\<close>
    | hol_type_of CUInt   = \<^typ>\<open>c_uint\<close>
    | hol_type_of CChar   = \<^typ>\<open>c_char\<close>
    | hol_type_of CSChar   = \<^typ>\<open>c_schar\<close>
    | hol_type_of CShort  = \<^typ>\<open>c_short\<close>
    | hol_type_of CUShort = \<^typ>\<open>c_ushort\<close>
    | hol_type_of CLong   =
        if C_ABI.long_bits (get_abi_profile ()) = 32 then \<^typ>\<open>c_int\<close> else \<^typ>\<open>c_long\<close>
    | hol_type_of CULong  =
        if C_ABI.long_bits (get_abi_profile ()) = 32 then \<^typ>\<open>c_uint\<close> else \<^typ>\<open>c_ulong\<close>
    | hol_type_of CLongLong = \<^typ>\<open>c_long\<close>
    | hol_type_of CULongLong = \<^typ>\<open>c_ulong\<close>
    | hol_type_of CInt128   = \<^typ>\<open>c_int128\<close>
    | hol_type_of CUInt128  = \<^typ>\<open>c_uint128\<close>
    | hol_type_of (CPtr _) = dummyT  (* pointer types use type inference *)
    | hol_type_of CVoid   = @{typ unit}
    | hol_type_of (CStruct _) = dummyT
    | hol_type_of (CUnion _) = dummyT

  fun type_name_of CBool   = "_Bool"
    | type_name_of CInt    = "int"
    | type_name_of CUInt   = "unsigned int"
    | type_name_of CChar   = "char"
    | type_name_of CSChar   = "signed char"
    | type_name_of CShort  = "short"
    | type_name_of CUShort = "unsigned short"
    | type_name_of CLong   = "long"
    | type_name_of CULong  = "unsigned long"
    | type_name_of CLongLong = "long long"
    | type_name_of CULongLong = "unsigned long long"
    | type_name_of CInt128   = "__int128"
    | type_name_of CUInt128  = "unsigned __int128"
    | type_name_of (CPtr cty) = type_name_of cty ^ " *"
    | type_name_of CVoid   = "void"
    | type_name_of (CStruct s) = "struct " ^ s
    | type_name_of (CUnion s) = "union " ^ s

  (* C11 \<section>6.4.4.1p5: integer constant type from suffix flags.
     Flags0 of int is a bitfield: bit 0 = unsigned (U suffix),
     bit 1 = long (L suffix), bit 2 = long long (LL suffix).
     This simplified version returns the base type from the suffix without
     considering the constant's value; see choose_int_literal_type in
     C_Translation_Engine for the full Table 5 lookup. *)
  fun int_literal_type (Flags0 bits) =
    let val is_unsigned = IntInf.andb (bits, 1) <> 0
        val is_long = IntInf.andb (bits, 2) <> 0
        val is_long_long = IntInf.andb (bits, 4) <> 0
    in if is_long_long andalso is_unsigned then CULongLong
       else if is_long_long then CLongLong
       else if is_unsigned andalso is_long then CULong
       else if is_long then CLong
       else if is_unsigned then CUInt
       else CInt
    end

  (* C11 \<section>6.7.2 (Type specifiers): resolve a list of C declaration specifiers
     into a c_numeric_type.  Specifier combinations follow \<section>6.7.2p2.
     \<section>6.2.5p15: plain char signedness is implementation-defined (compiler profile).
     \<section>6.7.2.2: enum specifiers treated as int.
     Returns NONE for void, struct types, and other non-numeric specifiers. *)
  fun resolve_c_type specs =
    (* _Bool is a distinct type in C — handle it before the accumulator.
       It cannot combine with signed/unsigned/short/long specifiers. *)
    if List.exists (fn CTypeSpec0 (CBoolType0 _) => true | _ => false) specs
    then SOME CBool
    else
    let
      fun accumulate (CTypeSpec0 (CSignedType0 _)) (_, us, ch, sh, it, lg, vd, st) =
            (true, us, ch, sh, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CUnsigType0 _)) (sg, _, ch, sh, it, lg, vd, st) =
            (sg, true, ch, sh, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CCharType0 _)) (sg, us, _, sh, it, lg, vd, st) =
            (sg, us, true, sh, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CShortType0 _)) (sg, us, ch, _, it, lg, vd, st) =
            (sg, us, ch, true, it, lg, vd, st)
        | accumulate (CTypeSpec0 (CIntType0 _)) (sg, us, ch, sh, _, lg, vd, st) =
            (sg, us, ch, sh, true, lg, vd, st)
        | accumulate (CTypeSpec0 (CLongType0 _)) (sg, us, ch, sh, it, lc, vd, st) =
            (sg, us, ch, sh, it, lc + 1, vd, st)  (* count long occurrences *)
        | accumulate (CTypeSpec0 (CVoidType0 _)) (sg, us, ch, sh, it, lc, _, st) =
            (sg, us, ch, sh, it, lc, true, st)
        | accumulate (CTypeSpec0 (CSUType0 _)) (sg, us, ch, sh, it, lc, vd, _) =
            (sg, us, ch, sh, it, lc, vd, true)
        | accumulate (CTypeSpec0 (CEnumType0 _)) (sg, us, ch, sh, _, lc, vd, st) =
            (sg, us, ch, sh, true, lc, vd, st)  (* enum treated as int *)
        | accumulate (CTypeSpec0 (CFloatType0 _)) _ =
            error "micro_c_translate: float type not supported"
        | accumulate (CTypeSpec0 (CDoubleType0 _)) _ =
            error "micro_c_translate: double type not supported"
        | accumulate (CTypeSpec0 (CInt128Type0 _)) (sg, us, ch, sh, it, _, vd, st) =
            (sg, us, ch, sh, it, 128, vd, st)  (* __int128: use long_count=128 as sentinel *)
        | accumulate (CTypeSpec0 (CComplexType0 _)) _ =
            error "micro_c_translate: _Complex type not supported"
        | accumulate (CTypeSpec0 (CTypeDef0 _)) flags = flags
        | accumulate (CTypeSpec0 _) _ =
            error "micro_c_translate: unsupported type specifier"
        (* C11 \<section>6.7.5: _Alignas affects memory layout alignment but not computation
           semantics. Our translation does not model byte-level local variable layout,
           so alignment is safely irrelevant. Verified example: C_Misc_Examples.thy. *)
        | accumulate (CAlignSpec0 _) flags = flags
        | accumulate (CFunSpec0 _) flags = flags    (* inline/_Noreturn: silently ignored *)
        | accumulate (CTypeQual0 (CVolatQual0 _)) _ =
            error "micro_c_translate: volatile qualifier not supported"
        | accumulate (CTypeQual0 (CAtomicQual0 _)) _ =
            error "micro_c_translate: _Atomic qualifier not supported (atomic semantics not modeled)"
        | accumulate (CTypeQual0 (CRestrQual0 _)) flags = flags  (* C11 \<section>6.7.3.1: restrict is optimization hint *)
        | accumulate (CTypeQual0 (CConstQual0 _)) flags = flags  (* C11 \<section>6.7.3: const has no runtime effect *)
        | accumulate (CTypeQual0 _) flags = flags
        | accumulate (CStorageSpec0 (CExtern0 _)) flags = flags  (* extern: linkage only, safe to ignore *)
        | accumulate (CStorageSpec0 _) flags = flags  (* static/register/typedef: safe to ignore *)
        | accumulate _ flags = flags
      val (has_signed, has_unsigned, has_char, has_short, _, long_count, has_void, has_struct) =
        List.foldl (fn (spec, flags) => accumulate spec flags)
          (false, false, false, false, false, 0, false, false) specs
    in
      if has_void then SOME CVoid
      else if has_struct then NONE
      else if has_char then
        if has_unsigned then SOME CChar  (* unsigned char = c_char = 8 word *)
        else if has_signed then SOME CSChar
        else if #char_is_signed (C_Compiler.get_compiler_profile ()) then SOME CSChar else SOME CChar  (* compiler: option controls plain-char signedness *)

      else if has_short then
        if has_unsigned then SOME CUShort
        else SOME CShort
      else if long_count = 128 then  (* __int128 *)
        if has_unsigned then SOME CUInt128
        else SOME CInt128
      else if long_count >= 2 then  (* long long *)
        if has_unsigned then SOME CULongLong
        else SOME CLongLong
      else if long_count = 1 then
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

  (* Like extract_struct_type_from_decl_full, but for unions. *)
  fun extract_union_type_from_decl_full union_names (CDecl0 (specs, _, _)) =
        let fun find_union [] = NONE
              | find_union (CTypeSpec0 (CSUType0 (CStruct0 (CUnionTag0,
                    Some ident, _, _, _), _)) :: _) = SOME (ident_name ident)
              | find_union (CTypeSpec0 (CTypeDef0 (ident, _)) :: _) =
                    let val n = ident_name ident
                    in if List.exists (fn s => s = n) union_names
                       then SOME n else NONE end
              | find_union (_ :: rest) = find_union rest
        in find_union specs end
    | extract_union_type_from_decl_full _ _ = NONE

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
    let
      fun is_typedef_spec (CStorageSpec0 (CTypedef0 _)) = true
        | is_typedef_spec _ = false
      fun non_storage_spec (CStorageSpec0 _) = false
        | non_storage_spec _ = true

      fun resolve_with_typedefs typedef_tab specs =
        let
          val type_specs = List.filter (fn CTypeSpec0 _ => true | _ => false) specs
        in
          case type_specs of
            [CTypeSpec0 (CTypeDef0 (ident, _))] =>
              Symtab.lookup typedef_tab (ident_name ident)
          | _ => resolve_c_type specs
        end

      fun resolve_typedef_decl typedef_tab specs declr =
        let
          val type_specs = List.filter non_storage_spec specs
          val base_cty =
            (case resolve_with_typedefs typedef_tab type_specs of
               SOME cty => SOME cty
             | NONE =>
                 (case List.find (fn CTypeSpec0 (CSUType0 _) => true | _ => false) type_specs of
                    SOME (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0, Some ident, _, _, _), _))) =>
                      SOME (CStruct (ident_name ident))
                  | _ =>
                      (case List.find (fn CTypeSpec0 (CSUType0 _) => true | _ => false) type_specs of
                         SOME (CTypeSpec0 (CSUType0 (CStruct0 (CUnionTag0, Some ident, _, _, _), _))) =>
                           SOME (CUnion (ident_name ident))
                       | _ => NONE)))
          val ptr_depth = pointer_depth_of_declr declr
        in
          Option.map (fn cty => apply_ptr_depth cty ptr_depth) base_cty
        end

      fun step (decl, (typedef_tab, acc)) =
        (case decl of
           CDeclExt0 (CDecl0 (specs, [((Some declr, _), _)], _)) =>
             if List.exists is_typedef_spec specs then
               let
                 val name = declr_name declr
               in
                 (case resolve_typedef_decl typedef_tab specs declr of
                    SOME cty =>
                      let val tab' = Symtab.update (name, cty) typedef_tab
                      in (tab', acc @ [(name, cty)]) end
                  | NONE => (typedef_tab, acc))
               end
             else (typedef_tab, acc)
         | _ => (typedef_tab, acc))

      val init_tab = Symtab.make (builtin_typedefs ())
      val (_, typedefs) = List.foldl step (init_tab, []) ext_decls
    in
      typedefs
    end

  (* resolve_c_type with typedef resolution: check for CTypeDef0 first,
     then fall back to standard resolve_c_type.
     We strip type qualifiers (const, volatile) and storage specifiers
     (static, extern) before matching, so that e.g. "const int32_t" still
     resolves the typedef correctly. *)
  fun resolve_c_type_full typedef_tab specs =
    let val type_specs = List.filter
          (fn CTypeSpec0 _ => true | _ => false) specs
    in case type_specs of
        [CTypeSpec0 (CTypeDef0 (ident, _))] =>
          (case Symtab.lookup typedef_tab (ident_name ident) of
             SOME cty => SOME cty
           | NONE => NONE)
      | _ => resolve_c_type specs
    end

  (* Extract the string from a C string literal node *)
  fun extract_string_literal (CStrLit0 (CString0 (abr_str, _), _)) =
        abr_string_to_string abr_str

  (* Evaluate a constant integer expression at translation time.
     Used for _Static_assert conditions and similar compile-time checks.
     resolve_decl_type resolves CDecl0 to a c_numeric_type (for sizeof). *)
  fun eval_const_int_expr resolve_decl_type expr =
    let fun eval (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) = n
          | eval (CConst0 (CCharConst0 (CChar0 (c, _), _))) = integer_of_char c
          | eval (CSizeofType0 (decl, _)) =
              (case resolve_decl_type decl of
                 SOME cty => IntInf.fromInt (sizeof_c_type cty)
               | NONE => error "micro_c_translate: _Static_assert: sizeof unsupported type")
          | eval (CAlignofType0 (decl, _)) =
              (case resolve_decl_type decl of
                 SOME cty => IntInf.fromInt (alignof_c_type cty)
               | NONE => error "micro_c_translate: _Static_assert: _Alignof unsupported type")
          | eval (CUnary0 (CMinOp0, e, _)) = IntInf.~ (eval e)
          | eval (CUnary0 (CPlusOp0, e, _)) = eval e
          | eval (CUnary0 (CNegOp0, e, _)) =
              if eval e = 0 then 1 else 0
          | eval (CBinary0 (op_, lhs, rhs, _)) =
              let val l = eval lhs val r = eval rhs
              in case op_ of
                   CEqOp0 => if l = r then 1 else 0
                 | CNeqOp0 => if l <> r then 1 else 0
                 | CLeOp0 => if l < r then 1 else 0
                 | CGrOp0 => if l > r then 1 else 0
                 | CLeqOp0 => if l <= r then 1 else 0
                 | CGeqOp0 => if l >= r then 1 else 0
                 | CAddOp0 => l + r
                 | CSubOp0 => l - r
                 | CMulOp0 => l * r
                 | CLndOp0 => if l <> 0 andalso r <> 0 then 1 else 0
                 | CLorOp0 => if l <> 0 orelse r <> 0 then 1 else 0
                 | _ => error "micro_c_translate: _Static_assert: unsupported binary operator"
              end
          | eval _ = error "micro_c_translate: _Static_assert: unsupported expression in condition"
    in eval expr end

  (* Conservative side-effect analysis for expression-order soundness checks.
     Calls and mutating operators are treated as side-effecting. *)
  fun named_call_is_pure pure_tab (CVar0 (ident, _)) =
        Symtab.defined pure_tab (ident_name ident)
    | named_call_is_pure _ _ = false

  fun expr_has_side_effect_with pure_tab (CAssign0 _) = true
    | expr_has_side_effect_with pure_tab (CUnary0 (CPreIncOp0, _, _)) = true
    | expr_has_side_effect_with pure_tab (CUnary0 (CPostIncOp0, _, _)) = true
    | expr_has_side_effect_with pure_tab (CUnary0 (CPreDecOp0, _, _)) = true
    | expr_has_side_effect_with pure_tab (CUnary0 (CPostDecOp0, _, _)) = true
    | expr_has_side_effect_with pure_tab (CCall0 (f, args, _)) =
        let
          val sub_effects =
            expr_has_side_effect_with pure_tab f orelse
            List.exists (expr_has_side_effect_with pure_tab) args
        in
          if named_call_is_pure pure_tab f then sub_effects else true
        end
    | expr_has_side_effect_with pure_tab (CBinary0 (_, l, r, _)) =
        expr_has_side_effect_with pure_tab l orelse expr_has_side_effect_with pure_tab r
    | expr_has_side_effect_with pure_tab (CUnary0 (_, e, _)) = expr_has_side_effect_with pure_tab e
    | expr_has_side_effect_with pure_tab (CIndex0 (a, i, _)) =
        expr_has_side_effect_with pure_tab a orelse expr_has_side_effect_with pure_tab i
    | expr_has_side_effect_with pure_tab (CMember0 (e, _, _, _)) = expr_has_side_effect_with pure_tab e
    | expr_has_side_effect_with pure_tab (CCast0 (_, e, _)) = expr_has_side_effect_with pure_tab e
    | expr_has_side_effect_with pure_tab (CComma0 (es, _)) = List.exists (expr_has_side_effect_with pure_tab) es
    | expr_has_side_effect_with pure_tab (CCond0 (c, t, e, _)) =
        expr_has_side_effect_with pure_tab c orelse
          (case t of Some te => expr_has_side_effect_with pure_tab te | None => false) orelse
          expr_has_side_effect_with pure_tab e
    | expr_has_side_effect_with _ _ = false

  fun expr_has_side_effect expr =
    expr_has_side_effect_with (!current_pure_function_names) expr

  fun init_has_side_effect_with pure_tab (CInitExpr0 (e, _)) =
        expr_has_side_effect_with pure_tab e
    | init_has_side_effect_with pure_tab (CInitList0 (inits, _)) =
        List.exists (fn (_, init) => init_has_side_effect_with pure_tab init) inits

  fun decl_has_side_effect_with pure_tab (CDecl0 (_, declarators, _)) =
        List.exists
          (fn ((_, Some init), _) => init_has_side_effect_with pure_tab init
            | _ => false)
          declarators
    | decl_has_side_effect_with _ _ = true

  fun stmt_has_side_effect_with pure_tab (CCompound0 (_, items, _)) =
        List.exists (item_has_side_effect_with pure_tab) items
    | stmt_has_side_effect_with pure_tab (CExpr0 (Some e, _)) = expr_has_side_effect_with pure_tab e
    | stmt_has_side_effect_with _ (CExpr0 (None, _)) = false
    | stmt_has_side_effect_with pure_tab (CReturn0 (Some e, _)) = expr_has_side_effect_with pure_tab e
    | stmt_has_side_effect_with _ (CReturn0 (None, _)) = false
    | stmt_has_side_effect_with pure_tab (CIf0 (c, t, e_opt, _)) =
        expr_has_side_effect_with pure_tab c orelse
          stmt_has_side_effect_with pure_tab t orelse
          (case e_opt of Some e => stmt_has_side_effect_with pure_tab e | None => false)
    | stmt_has_side_effect_with pure_tab (CWhile0 (c, b, _, _)) =
        expr_has_side_effect_with pure_tab c orelse stmt_has_side_effect_with pure_tab b
    | stmt_has_side_effect_with pure_tab (CFor0 (Left init_opt, cond_opt, step_opt, body, _)) =
        (case init_opt of Some e => expr_has_side_effect_with pure_tab e | None => false) orelse
        (case cond_opt of Some e => expr_has_side_effect_with pure_tab e | None => false) orelse
        (case step_opt of Some e => expr_has_side_effect_with pure_tab e | None => false) orelse
        stmt_has_side_effect_with pure_tab body
    | stmt_has_side_effect_with pure_tab (CFor0 (Right decl, cond_opt, step_opt, body, _)) =
        decl_has_side_effect_with pure_tab decl orelse
        (case cond_opt of Some e => expr_has_side_effect_with pure_tab e | None => false) orelse
        (case step_opt of Some e => expr_has_side_effect_with pure_tab e | None => false) orelse
        stmt_has_side_effect_with pure_tab body
    | stmt_has_side_effect_with pure_tab (CSwitch0 (e, s, _)) =
        expr_has_side_effect_with pure_tab e orelse stmt_has_side_effect_with pure_tab s
    | stmt_has_side_effect_with pure_tab (CCase0 (e, s, _)) =
        expr_has_side_effect_with pure_tab e orelse stmt_has_side_effect_with pure_tab s
    | stmt_has_side_effect_with pure_tab (CCases0 (e1, e2, s, _)) =
        expr_has_side_effect_with pure_tab e1 orelse
        expr_has_side_effect_with pure_tab e2 orelse
        stmt_has_side_effect_with pure_tab s
    | stmt_has_side_effect_with pure_tab (CDefault0 (s, _)) = stmt_has_side_effect_with pure_tab s
    | stmt_has_side_effect_with pure_tab (CLabel0 (_, s, _, _)) = stmt_has_side_effect_with pure_tab s
    | stmt_has_side_effect_with _ (CBreak0 _) = false
    | stmt_has_side_effect_with _ (CCont0 _) = false
    | stmt_has_side_effect_with _ (CGoto0 _) = true
    | stmt_has_side_effect_with _ (CGotoPtr0 _) = true
    | stmt_has_side_effect_with _ (CAsm0 _) = true

  and item_has_side_effect_with pure_tab (CBlockStmt0 s) = stmt_has_side_effect_with pure_tab s
    | item_has_side_effect_with pure_tab (CBlockDecl0 d) = decl_has_side_effect_with pure_tab d
    | item_has_side_effect_with _ (CNestedFunDef0 _) = true

  fun fundef_is_pure_with pure_tab (CFunDef0 (_, _, _, body, _)) =
    not (stmt_has_side_effect_with pure_tab body)

  (* ----- Generic C AST fold -----
     Post-order fold over C expression/statement trees.
     The handler f receives each node AFTER its children have been accumulated.
     This eliminates the need for repetitive per-walker AST traversal code. *)
  fun fold_c_expr f expr acc =
    f expr (case expr of
      CAssign0 (_, lhs, rhs, _) => fold_c_expr f rhs (fold_c_expr f lhs acc)
    | CBinary0 (_, l, r, _) => fold_c_expr f r (fold_c_expr f l acc)
    | CUnary0 (_, e, _) => fold_c_expr f e acc
    | CIndex0 (a, i, _) => fold_c_expr f i (fold_c_expr f a acc)
    | CMember0 (e, _, _, _) => fold_c_expr f e acc
    | CCast0 (_, e, _) => fold_c_expr f e acc
    | CCall0 (callee, args, _) =>
        List.foldl (fn (a, ac) => fold_c_expr f a ac)
          (fold_c_expr f callee acc) args
    | CComma0 (es, _) =>
        List.foldl (fn (e, ac) => fold_c_expr f e ac) acc es
    | CCond0 (c, t, e, _) =>
        fold_c_expr f e
          ((case t of Some te => fold_c_expr f te | None => I)
            (fold_c_expr f c acc))
    | CCompoundLit0 (_, inits, _) =>
        List.foldl (fn ((_, CInitExpr0 (e, _)), ac) => fold_c_expr f e ac
                     | (_, ac) => ac) acc inits
    | CGenericSelection0 (ctrl, assocs, _) =>
        List.foldl (fn ((_, e), ac) => fold_c_expr f e ac)
          (fold_c_expr f ctrl acc) assocs
    | _ => acc)

  fun fold_c_init fe init acc =
    (case init of
       CInitExpr0 (e, _) => fe e acc
     | CInitList0 (inits, _) =>
         List.foldl (fn ((_, i), ac) => fold_c_init fe i ac) acc inits)

  fun fold_c_stmt fe fs stmt acc =
    let
      val oe = fn (Some e) => fe e | None => I
      fun fi (CBlockStmt0 s) acc = fold_c_stmt fe fs s acc
        | fi (CBlockDecl0 (CDecl0 (_, declarators, _))) acc =
            List.foldl
              (fn (((_, Some init), _), ac) => fold_c_init fe init ac
                | (_, ac) => ac)
              acc declarators
        | fi _ acc = acc
    in
      fs stmt (case stmt of
        CCompound0 (_, items, _) =>
          List.foldl (fn (item, ac) => fi item ac) acc items
      | CExpr0 (Some e, _) => fe e acc
      | CExpr0 (None, _) => acc
      | CReturn0 (Some e, _) => fe e acc
      | CReturn0 (None, _) => acc
      | CIf0 (c, t, e_opt, _) =>
          (case e_opt of Some e => fold_c_stmt fe fs e | None => I)
            (fold_c_stmt fe fs t (fe c acc))
      | CWhile0 (c, b, _, _) =>
          fold_c_stmt fe fs b (fe c acc)
      | CFor0 (Left (Some i), c, s, b, _) =>
          fold_c_stmt fe fs b (oe s (oe c (fe i acc)))
      | CFor0 (Left None, c, s, b, _) =>
          fold_c_stmt fe fs b (oe s (oe c acc))
      | CFor0 (Right d, c, s, b, _) =>
          fold_c_stmt fe fs b (oe s (oe c (fi (CBlockDecl0 d) acc)))
      | CSwitch0 (e, s, _) =>
          fold_c_stmt fe fs s (fe e acc)
      | CCase0 (e, s, _) =>
          fold_c_stmt fe fs s (fe e acc)
      | CCases0 (e1, e2, s, _) =>
          fold_c_stmt fe fs s (fe e2 (fe e1 acc))
      | CDefault0 (s, _) =>
          fold_c_stmt fe fs s acc
      | CLabel0 (_, s, _, _) =>
          fold_c_stmt fe fs s acc
      | _ => acc)
    end

  fun expr_reads_vars expr =
    fold_c_expr
      (fn CVar0 (ident, _) => (fn acc => ident_name ident :: acc)
        | _ => I) expr []

  fun expr_written_vars expr =
    fold_c_expr
      (fn CAssign0 (_, CVar0 (ident, _), _, _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPreIncOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPostIncOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPreDecOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPostDecOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | _ => I) expr []

  fun list_intersects xs ys =
    List.exists (fn x => List.exists (fn y => x = y) ys) xs

  (* C11 \<section>6.5p2: detect unsequenced conflicting accesses to the same
     scalar object between two operands. *)
  fun expr_has_unsequenced_ub_risk e0 e1 =
    let
      val r0 = distinct (op =) (expr_reads_vars e0)
      val r1 = distinct (op =) (expr_reads_vars e1)
      val w0 = distinct (op =) (expr_written_vars e0)
      val w1 = distinct (op =) (expr_written_vars e1)
      val writes_conflict =
        list_intersects w0 (r1 @ w1) orelse list_intersects w1 (r0 @ w0)
    in
      (* Only reject when we can identify a concrete scalar object conflict.
         Opaque/unknown side effects (e.g., function calls) are not treated as UB
         by themselves, to avoid rejecting common valid C expressions. *)
      writes_conflict
    end

  (* Walk the C AST and collect variable names that appear on the LHS of
     assignments or as operands of pre/post increment/decrement or address-of.
     Used to identify parameters that need promotion to local variables. *)
  fun find_assigned_vars stmt =
    distinct (op =) (fold_c_stmt (fold_c_expr
      (fn CAssign0 (_, CVar0 (ident, _), _, _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPreIncOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPostIncOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPreDecOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CPostDecOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CAdrOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | _ => I)) (fn _ => I) stmt [])

  (* Walk the C AST and collect label names targeted by goto statements.
     Used to allocate goto flag references for forward-only goto support. *)
  fun find_goto_targets stmt =
    distinct (op =) (fold_c_stmt (fn _ => I)
      (fn CGoto0 (ident, _) => (fn acc => ident_name ident :: acc)
        | _ => I) stmt [])

  (* Collect direct function-call targets used in a function body.
     Only named calls (CCall0 (CVar0 ...)) are collected. *)
  fun find_called_functions (CFunDef0 (_, _, _, body, _)) =
    distinct (op =) (fold_c_stmt (fold_c_expr
      (fn CCall0 (CVar0 (ident, _), _, _) => (fn acc => ident_name ident :: acc)
        | _ => I)) (fn _ => I) body [])

  local
    fun declr_has_array (CDeclr0 (_, derived, _, _, _)) =
      List.exists (fn CArrDeclr0 _ => true | _ => false) derived

    fun declr_of_decl (CDecl0 (_, declarators, _)) =
          (case declarators of
             ((Some declr, _), _) :: _ => SOME declr
           | _ => NONE)
      | declr_of_decl _ = NONE

    fun struct_name_of_decl struct_names decl =
      extract_struct_type_from_decl_full struct_names decl

    fun env_contains env name = Option.isSome (Symtab.lookup env name)
    fun env_insert name env = Symtab.update (name, ()) env

    fun expr_struct_name struct_env (CVar0 (ident, _)) =
          Symtab.lookup struct_env (ident_name ident)
      | expr_struct_name struct_env (CCast0 (_, e, _)) =
          expr_struct_name struct_env e
      | expr_struct_name _ _ = NONE

    fun struct_field_is_array_backed array_field_tab struct_name field_name =
      List.exists (fn fname => fname = field_name)
        (the_default [] (Symtab.lookup array_field_tab struct_name))

    fun expr_is_list_backed_in_env struct_tab array_field_tab env struct_env (CVar0 (ident, _)) =
          env_contains env (ident_name ident)
      | expr_is_list_backed_in_env struct_tab array_field_tab env struct_env (CCast0 (_, e, _)) =
          expr_is_list_backed_in_env struct_tab array_field_tab env struct_env e
      | expr_is_list_backed_in_env struct_tab array_field_tab env struct_env (CMember0 (base, field_ident, _, _)) =
          (case expr_struct_name struct_env base of
             SOME struct_name =>
               struct_field_is_array_backed array_field_tab struct_name (ident_name field_ident)
           | NONE => false)
      | expr_is_list_backed_in_env _ _ _ _ _ = false

    fun add_decl_struct_bindings struct_names decl struct_env =
      (case (declr_of_decl decl, struct_name_of_decl struct_names decl) of
         (SOME declr, SOME sname) =>
           Symtab.update (declr_name declr, sname) struct_env
       | _ => struct_env)

    fun add_decl_array_bindings decl env =
      (case declr_of_decl decl of
         SOME declr =>
           if declr_has_array declr then env_insert (declr_name declr) env else env
       | NONE => env)

    fun alias_names_from_expr struct_tab array_field_tab env struct_env (CAssign0 (_, CVar0 (ident, _), rhs, _)) acc =
          let
            val acc' = alias_names_from_expr struct_tab array_field_tab env struct_env rhs acc
          in
            if expr_is_list_backed_in_env struct_tab array_field_tab env struct_env rhs then
              ident_name ident :: acc'
            else
              acc'
          end
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CAssign0 (_, lhs, rhs, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env rhs
            (alias_names_from_expr struct_tab array_field_tab env struct_env lhs acc)
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CBinary0 (_, l, r, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env r
            (alias_names_from_expr struct_tab array_field_tab env struct_env l acc)
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CUnary0 (_, e, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e acc
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CIndex0 (a, i, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env i
            (alias_names_from_expr struct_tab array_field_tab env struct_env a acc)
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CMember0 (e, _, _, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e acc
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CCast0 (_, e, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e acc
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CCall0 (f, args, _)) acc =
          List.foldl (fn (a, ac) => alias_names_from_expr struct_tab array_field_tab env struct_env a ac)
            (alias_names_from_expr struct_tab array_field_tab env struct_env f acc) args
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CComma0 (es, _)) acc =
          List.foldl (fn (e, ac) => alias_names_from_expr struct_tab array_field_tab env struct_env e ac) acc es
      | alias_names_from_expr struct_tab array_field_tab env struct_env (CCond0 (c, t, e, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e
            ((case t of Some te => alias_names_from_expr struct_tab array_field_tab env struct_env te | None => I)
              (alias_names_from_expr struct_tab array_field_tab env struct_env c acc))
      | alias_names_from_expr _ _ _ _ _ acc = acc

    fun alias_names_from_decl struct_tab array_field_tab env struct_env (CDecl0 (_, declarators, _)) acc =
          List.foldl
            (fn (((Some declr, Some (CInitExpr0 (init, _))), _), ac) =>
                  if expr_is_list_backed_in_env struct_tab array_field_tab env struct_env init then
                    declr_name declr :: ac
                  else
                    ac
              | (_, ac) => ac)
            acc declarators
      | alias_names_from_decl _ _ _ _ _ acc = acc

    fun alias_names_from_item struct_tab array_field_tab env struct_env (CBlockStmt0 stmt) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env stmt acc
      | alias_names_from_item struct_tab array_field_tab env struct_env (CBlockDecl0 decl) acc =
          alias_names_from_decl struct_tab array_field_tab env struct_env decl acc
      | alias_names_from_item _ _ _ _ _ acc = acc

    and alias_names_from_stmt struct_tab array_field_tab env struct_env (CCompound0 (_, items, _)) acc =
          List.foldl (fn (item, ac) => alias_names_from_item struct_tab array_field_tab env struct_env item ac) acc items
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CExpr0 (Some e, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e acc
      | alias_names_from_stmt _ _ _ _ (CExpr0 (None, _)) acc = acc
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CReturn0 (Some e, _)) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e acc
      | alias_names_from_stmt _ _ _ _ (CReturn0 (None, _)) acc = acc
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CIf0 (c, t, e_opt, _)) acc =
          (case e_opt of
             Some e => alias_names_from_stmt struct_tab array_field_tab env struct_env e
           | None => I)
            (alias_names_from_stmt struct_tab array_field_tab env struct_env t
              (alias_names_from_expr struct_tab array_field_tab env struct_env c acc))
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CWhile0 (c, b, _, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env b
            (alias_names_from_expr struct_tab array_field_tab env struct_env c acc)
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CFor0 (Left (Some i), c, s, b, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env b
            (opt_alias_expr struct_tab array_field_tab env struct_env s
              (opt_alias_expr struct_tab array_field_tab env struct_env c
                (alias_names_from_expr struct_tab array_field_tab env struct_env i acc)))
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CFor0 (Left None, c, s, b, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env b
            (opt_alias_expr struct_tab array_field_tab env struct_env s
              (opt_alias_expr struct_tab array_field_tab env struct_env c acc))
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CFor0 (Right d, c, s, b, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env b
            (opt_alias_expr struct_tab array_field_tab env struct_env s
              (opt_alias_expr struct_tab array_field_tab env struct_env c
                (alias_names_from_decl struct_tab array_field_tab env struct_env d acc)))
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CSwitch0 (e, s, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env s
            (alias_names_from_expr struct_tab array_field_tab env struct_env e acc)
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CCase0 (e, s, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env s
            (alias_names_from_expr struct_tab array_field_tab env struct_env e acc)
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CDefault0 (s, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env s acc
      | alias_names_from_stmt struct_tab array_field_tab env struct_env (CLabel0 (_, s, _, _)) acc =
          alias_names_from_stmt struct_tab array_field_tab env struct_env s acc
      | alias_names_from_stmt _ _ _ _ _ acc = acc

    and opt_alias_expr struct_tab array_field_tab env struct_env (Some e) acc =
          alias_names_from_expr struct_tab array_field_tab env struct_env e acc
      | opt_alias_expr _ _ _ _ None acc = acc

  in
    fun find_list_backed_aliases struct_tab array_field_tab (CFunDef0 (_, declr, _, body, _)) =
      let
        val struct_names = Symtab.keys struct_tab
        val param_decls = extract_param_decls declr
        val struct_env =
          List.foldl (fn (pdecl, env) =>
            case (declr_of_decl pdecl, struct_name_of_decl struct_names pdecl) of
              (SOME pdeclr, SOME sname) =>
                Symtab.update (declr_name pdeclr, sname) env
            | _ => env) Symtab.empty param_decls
        val env0 =
          List.foldl (fn (pdecl, env) =>
            case declr_of_decl pdecl of
              SOME pdeclr =>
                if declr_has_array pdeclr then env_insert (declr_name pdeclr) env else env
            | NONE => env) Symtab.empty param_decls
        fun add_local_arrays_stmt (CCompound0 (_, items, _)) env =
              List.foldl
                (fn (CBlockStmt0 stmt, ea) => add_local_arrays_stmt stmt ea
                  | (CBlockDecl0 decl, ea) => add_decl_array_bindings decl ea
                  | (_, ea) => ea)
                env items
          | add_local_arrays_stmt (CIf0 (_, t, e_opt, _)) env =
              (case e_opt of Some e => add_local_arrays_stmt e | None => I) (add_local_arrays_stmt t env)
          | add_local_arrays_stmt (CWhile0 (_, b, _, _)) env = add_local_arrays_stmt b env
          | add_local_arrays_stmt (CFor0 (Right d, _, _, b, _)) env =
              add_local_arrays_stmt b (add_decl_array_bindings d env)
          | add_local_arrays_stmt (CFor0 (_, _, _, b, _)) env = add_local_arrays_stmt b env
          | add_local_arrays_stmt (CSwitch0 (_, s, _)) env = add_local_arrays_stmt s env
          | add_local_arrays_stmt (CCase0 (_, s, _)) env = add_local_arrays_stmt s env
          | add_local_arrays_stmt (CDefault0 (s, _)) env = add_local_arrays_stmt s env
          | add_local_arrays_stmt (CLabel0 (_, s, _, _)) env = add_local_arrays_stmt s env
          | add_local_arrays_stmt _ env = env
        val env0 = add_local_arrays_stmt body env0
        fun iterate env =
          let
            val added =
              distinct (op =) (alias_names_from_stmt struct_tab array_field_tab env struct_env body [])
            val env' = List.foldl (fn (name, ea) => env_insert name ea) env added
          in
            if Symtab.dest env' = Symtab.dest env then env else iterate env'
          end
      in
        Symtab.keys (iterate env0)
      end

  end

  fun find_indexed_base_vars (CFunDef0 (_, _, _, body, _)) =
    distinct (op =) (fold_c_stmt (fold_c_expr
      (fn CIndex0 (CVar0 (ident, _), _, _) => (fn acc => ident_name ident :: acc)
        | CUnary0 (CIndOp0, CVar0 (ident, _), _) => (fn acc => ident_name ident :: acc)
        | _ => I)) (fn _ => I) body [])

  fun find_named_calls_with_args (CFunDef0 (_, _, _, body, _)) =
    fold_c_stmt (fold_c_expr
      (fn CCall0 (CVar0 (ident, _), args, _) => (fn acc => (ident_name ident, args) :: acc)
        | _ => I)) (fn _ => I) body []


  (* Extract struct definitions with field types from a top-level declaration.
     Returns SOME (struct_name, [(field_name, field_type)]) for struct definitions.
     Falls back to CInt for fields whose type cannot be resolved. *)
  (* Extract struct type name from declaration specifiers (for struct-typed fields) *)
  fun extract_struct_type_from_specs specs =
    case List.find (fn CTypeSpec0 (CSUType0 _) => true | _ => false) specs of
      SOME (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0, Some ident, _, _, _), _))) =>
        SOME (ident_name ident)
    | _ => NONE

  (* Extract union type name from declaration specifiers *)
  fun extract_union_type_from_specs specs =
    case List.find (fn CTypeSpec0 (CSUType0 _) => true | _ => false) specs of
      SOME (CTypeSpec0 (CSUType0 (CStruct0 (CUnionTag0, Some ident, _, _, _), _))) =>
        SOME (ident_name ident)
    | _ => NONE

  (* Like extract_struct_type_from_specs, but also recognizes typedef names
     that refer to known structs. *)
  fun extract_struct_type_from_specs_full struct_names specs =
    case extract_struct_type_from_specs specs of
      SOME sn => SOME sn
    | NONE =>
        let val type_specs = List.filter
              (fn CTypeSpec0 _ => true | _ => false) specs
        in case type_specs of
            [CTypeSpec0 (CTypeDef0 (ident, _))] =>
              let val n = ident_name ident
              in if List.exists (fn s => s = n) struct_names
                 then SOME n else NONE end
          | _ => NONE
        end

  (* Like extract_union_type_from_specs, but also recognizes typedef names
     that refer to known unions. *)
  fun extract_union_type_from_specs_full union_names specs =
    case extract_union_type_from_specs specs of
      SOME un => SOME un
    | NONE =>
        let val type_specs = List.filter
              (fn CTypeQual0 _ => false | CStorageSpec0 _ => false | _ => true) specs
        in case type_specs of
            [CTypeSpec0 (CTypeDef0 (ident, _))] =>
              let val n = ident_name ident
              in if List.exists (fn s => s = n) union_names
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
                                        | NONE =>
                                            (case extract_union_type_from_specs field_specs of
                                               SOME un => CUnion un
                                             | NONE => CInt))
                    val ptr_depth = pointer_depth_of_derived derived
                    val fty = apply_ptr_depth base_fty ptr_depth
                in SOME (fname, fty) end
            | _ => NONE)
          members

  fun raw_gref_typ () =
    Term.Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])

  fun focused_ref_typ pointee_ty =
    Term.Type (\<^type_name>\<open>focused\<close>, [raw_gref_typ (), !current_ref_gv_ty, pointee_ty])

  fun struct_record_typ prefix sname =
    if Symtab.defined (!current_parametric_struct_names) sname
    then Term.Type (prefix ^ sname, [!current_ref_addr_ty, !current_ref_gv_ty])
    else Term.Type (prefix ^ sname, [])

  fun cty_to_record_typ _ CBool = SOME @{typ bool}
    | cty_to_record_typ _ CInt = SOME \<^typ>\<open>c_int\<close>
    | cty_to_record_typ _ CUInt = SOME \<^typ>\<open>c_uint\<close>
    | cty_to_record_typ _ CChar = SOME \<^typ>\<open>c_char\<close>
    | cty_to_record_typ _ CSChar = SOME \<^typ>\<open>c_schar\<close>
    | cty_to_record_typ _ CShort = SOME \<^typ>\<open>c_short\<close>
    | cty_to_record_typ _ CUShort = SOME \<^typ>\<open>c_ushort\<close>
    | cty_to_record_typ _ CLong =
        if C_ABI.long_bits (get_abi_profile ()) = 32 then SOME \<^typ>\<open>c_int\<close> else SOME \<^typ>\<open>c_long\<close>
    | cty_to_record_typ _ CULong =
        if C_ABI.long_bits (get_abi_profile ()) = 32 then SOME \<^typ>\<open>c_uint\<close> else SOME \<^typ>\<open>c_ulong\<close>
    | cty_to_record_typ _ CLongLong = SOME \<^typ>\<open>c_long\<close>
    | cty_to_record_typ _ CULongLong = SOME \<^typ>\<open>c_ulong\<close>
    | cty_to_record_typ _ CInt128 = SOME \<^typ>\<open>c_int128\<close>
    | cty_to_record_typ _ CUInt128 = SOME \<^typ>\<open>c_uint128\<close>
    | cty_to_record_typ prefix (CStruct sname) = SOME (struct_record_typ prefix sname)
    | cty_to_record_typ _ (CPtr CChar) = SOME (HOLogic.listT \<^typ>\<open>c_char\<close>)
    | cty_to_record_typ _ (CPtr CVoid) = SOME (raw_gref_typ ())
    | cty_to_record_typ _ (CPtr (CUnion _)) = SOME (raw_gref_typ ())
    | cty_to_record_typ prefix (CPtr cty) =
        (case cty_to_record_typ prefix cty of
           SOME inner => SOME (focused_ref_typ inner)
         | NONE => SOME (raw_gref_typ ()))
    | cty_to_record_typ _ CVoid = NONE
    | cty_to_record_typ _ (CUnion _) = NONE

  fun ptr_depth_only derived =
    List.foldl
      (fn (d, acc) =>
        (case d of
           CPtrDeclr0 _ => acc + 1
         | _ => acc))
      0 derived

  fun has_array_derived derived =
    List.exists (fn CArrDeclr0 _ => true | _ => false) derived

  fun member_record_field_typ prefix base_fty derived =
    if has_array_derived derived then
      Option.map HOLogic.listT (cty_to_record_typ prefix base_fty)
    else if ptr_depth_only derived > 0 then
      cty_to_record_typ prefix (apply_ptr_depth base_fty (ptr_depth_only derived))
    else
      cty_to_record_typ prefix base_fty

  fun extract_member_record_field_info prefix typedef_tab members =
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
                in SOME (fname, member_record_field_typ prefix base_fty derived) end
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

  fun cty_needs_parametric_struct parametric_structs (CPtr _) = true
    | cty_needs_parametric_struct parametric_structs (CStruct sname) =
        Symtab.defined parametric_structs sname
    | cty_needs_parametric_struct parametric_structs (CUnion sname) =
        Symtab.defined parametric_structs sname
    | cty_needs_parametric_struct _ _ = false

  fun derive_parametric_struct_names struct_defs =
    let
      fun step acc =
        List.foldl
          (fn ((sname, fields), tab) =>
            if List.exists (fn (_, fty) => cty_needs_parametric_struct acc fty) fields
            then Symtab.update (sname, ()) tab
            else tab)
          acc
          struct_defs
      fun loop acc =
        let val next = step acc
        in if Symtab.dest next = Symtab.dest acc then acc else loop next end
      val final = loop Symtab.empty
    in
      List.map #1 (Symtab.dest final)
    end

  (* Extract union definitions with field types. Mirrors extract_struct_defs_with_types
     but matches CUnionTag0 instead of CStructTag0. *)
  fun extract_union_def_with_types_from_decl typedef_tab (CDecl0 (specs, declrs, _)) =
        let fun find_union_def [] = NONE
              | find_union_def (CTypeSpec0 (CSUType0 (CStruct0 (CUnionTag0,
                    Some ident, Some members, _, _), _)) :: _) =
                  SOME (ident_name ident, extract_member_field_info typedef_tab members)
              | find_union_def (CTypeSpec0 (CSUType0 (CStruct0 (CUnionTag0,
                    None, Some members, _, _), _)) :: _) =
                  if List.exists (fn CStorageSpec0 (CTypedef0 _) => true | _ => false) specs
                  then (case declrs of
                      [((Some (CDeclr0 (Some td_ident, _, _, _, _)), _), _)] =>
                        SOME (ident_name td_ident,
                              extract_member_field_info typedef_tab members)
                    | _ => NONE)
                  else NONE
              | find_union_def (_ :: rest) = find_union_def rest
        in find_union_def specs end
    | extract_union_def_with_types_from_decl _ _ = NONE

  fun extract_union_defs_with_types typedef_tab (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CDeclExt0 decl => extract_union_def_with_types_from_decl typedef_tab decl
        | _ => NONE)
      ext_decls

  fun extract_struct_record_def_from_decl prefix typedef_tab (CDecl0 (specs, declrs, _)) =
        let fun find_struct_def [] = NONE
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, Some members, _, _), _)) :: _) =
                  SOME (ident_name ident, extract_member_record_field_info prefix typedef_tab members)
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    None, Some members, _, _), _)) :: _) =
                  if List.exists (fn CStorageSpec0 (CTypedef0 _) => true | _ => false) specs
                  then (case declrs of
                      [((Some (CDeclr0 (Some td_ident, _, _, _, _)), _), _)] =>
                        SOME (ident_name td_ident,
                              extract_member_record_field_info prefix typedef_tab members)
                    | _ => NONE)
                  else NONE
              | find_struct_def (_ :: rest) = find_struct_def rest
        in find_struct_def specs end
    | extract_struct_record_def_from_decl _ _ _ = NONE

  fun extract_struct_record_defs prefix typedef_tab (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CDeclExt0 decl => extract_struct_record_def_from_decl prefix typedef_tab decl
        | _ => NONE)
      ext_decls

  fun extract_member_array_field_names members =
        List.mapPartial
          (fn CDecl0 (_, [((Some (CDeclr0 (Some ident_node, derived, _, _, _)), _), _)], _) =>
                if List.exists (fn CArrDeclr0 _ => true | _ => false) derived
                then SOME (ident_name ident_node) else NONE
            | _ => NONE)
          members

  fun extract_struct_array_fields_from_decl (CDecl0 (specs, declrs, _)) =
        let fun find_struct_def [] = NONE
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    Some ident, Some members, _, _), _)) :: _) =
                  SOME (ident_name ident, extract_member_array_field_names members)
              | find_struct_def (CTypeSpec0 (CSUType0 (CStruct0 (CStructTag0,
                    None, Some members, _, _), _)) :: _) =
                  if List.exists (fn CStorageSpec0 (CTypedef0 _) => true | _ => false) specs
                  then (case declrs of
                      [((Some (CDeclr0 (Some td_ident, _, _, _, _)), _), _)] =>
                        SOME (ident_name td_ident, extract_member_array_field_names members)
                    | _ => NONE)
                  else NONE
              | find_struct_def (_ :: rest) = find_struct_def rest
        in find_struct_def specs end
    | extract_struct_array_fields_from_decl _ = NONE

  fun extract_struct_array_fields (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CDeclExt0 decl => extract_struct_array_fields_from_decl decl
        | _ => NONE)
      ext_decls

  fun extract_fundefs (CTranslUnit0 (ext_decls, _)) =
    List.mapPartial
      (fn CFDefExt0 fundef => SOME fundef | _ => NONE)
      ext_decls

  (* C11 \<section>6.3.1.1p1: every integer type has an "integer conversion rank".
     Ranks determine promotion and usual arithmetic conversion behavior.
     _Bool < char = signed char < short < int < long < long long < __int128.
     Unsigned types have the same rank as their signed counterparts. *)
  fun type_rank CBool   = 0
    | type_rank CChar   = 1
    | type_rank CSChar  = 1
    | type_rank CShort  = 2
    | type_rank CUShort = 2
    | type_rank CInt    = 3
    | type_rank CUInt   = 3
    | type_rank CLong     = 4
    | type_rank CULong   = 4
    | type_rank CLongLong  = 5
    | type_rank CULongLong = 5
    | type_rank CInt128    = 6
    | type_rank CUInt128   = 6
    | type_rank (CPtr _) = error "type_rank: pointer type has no integer conversion rank"
    | type_rank CVoid    = error "type_rank: void type has no integer conversion rank"
    | type_rank (CStruct _) = error "type_rank: struct type has no integer conversion rank"
    | type_rank (CUnion _) = error "type_rank: union type has no integer conversion rank"

  (* C11 \<section>6.3.1.1p2: integer promotion.
     If an int can represent all values of the original type, the value is
     converted to int; otherwise to unsigned int. Since all sub-int types
     (char, short, _Bool) fit in int on all supported ABIs, we always
     promote to int. Types at int rank or above are unchanged. *)
  fun integer_promote cty =
    if type_rank cty < type_rank CInt then CInt else cty

  (* C11 \<section>6.3.1.8: usual arithmetic conversions for binary operations.
     First, integer promotions are performed on both operands. Then:
     1. If both have the same type, no further conversion.
     2. If both signed or both unsigned: convert to higher rank.
     3. If unsigned rank >= signed rank: convert to unsigned type.
     4. If signed type can represent all values of the unsigned type:
        convert to the signed type.
     5. Otherwise: convert both to the unsigned type corresponding to
        the signed operand's type.
     Note: floating-point types are not supported (error in resolve_c_type). *)
  fun usual_arith_conv (lty, rty) =
    let val lp = integer_promote lty
        val rp = integer_promote rty
    in if lp = rp then lp
       else if is_signed lp = is_signed rp then
         (if type_rank lp >= type_rank rp then lp else rp)
       else
         let val (s, u) = if is_signed lp then (lp, rp) else (rp, lp)
         in if type_rank u >= type_rank s
            then u  (* C11 rule 1: unsigned rank >= signed rank *)
            else
              (* C11 rules 2+3: signed has higher rank *)
              case (bit_width_of s, bit_width_of u) of
                (SOME sw, SOME uw) =>
                  if sw > uw then s  (* rule 2: signed strictly wider, can represent all unsigned *)
                  else (* rule 3: convert to unsigned type corresponding to signed *)
                    (case s of CLong => CULong | CLongLong => CULongLong
                             | CInt => CUInt | CInt128 => CUInt128 | _ => CUInt)
              | _ => error "usual_arith_conv: cannot determine bit width for conversion"
         end
    end
end
\<close>

end
