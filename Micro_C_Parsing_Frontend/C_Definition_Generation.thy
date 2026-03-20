theory C_Definition_Generation
  imports
    C_Translation_Engine
  keywords "micro_c_translate" :: thy_decl
       and "micro_c_file" :: thy_decl
       and "prefix:" and "manifest:" and "addr:" and "gv:" and "abi:" and "compiler:"
begin

subsection \<open>Definition Generation\<close>

ML \<open>
structure C_Def_Gen : sig
  type manifest = {functions: string list option, types: string list option}
  val set_decl_prefix : string -> unit
  val set_manifest : manifest -> unit
  val set_abi_profile : C_ABI.profile -> unit
  val set_ref_universe_types : typ -> typ -> unit
  val set_ref_abort_type : typ option -> unit
  val set_pointer_model : C_Translate.pointer_model -> unit
  val define_c_function : string -> string -> term -> local_theory -> local_theory
  val process_translation_unit : C_Ast.nodeInfo C_Ast.cTranslationUnit
                                 -> local_theory -> local_theory
end =
struct
  type manifest = {functions: string list option, types: string list option}

  val current_decl_prefix : string Unsynchronized.ref = Unsynchronized.ref "c_"
  val current_manifest : manifest Unsynchronized.ref =
    Unsynchronized.ref {functions = NONE, types = NONE}
  val current_abi_profile : C_ABI.profile Unsynchronized.ref =
    Unsynchronized.ref C_ABI.LP64_LE
  val current_ref_addr_ty : typ Unsynchronized.ref =
    Unsynchronized.ref (TFree ("'addr", []))
  val current_ref_gv_ty : typ Unsynchronized.ref =
    Unsynchronized.ref (TFree ("'gv", []))
  val current_pointer_model : C_Translate.pointer_model Unsynchronized.ref =
    Unsynchronized.ref {ptr_add = SOME "c_ptr_add", ptr_shift_signed = SOME "c_ptr_shift_signed", ptr_diff = SOME "c_ptr_diff"}

  fun set_decl_prefix pfx = (current_decl_prefix := pfx)
  fun set_manifest m = (current_manifest := m)
  fun set_abi_profile abi = (current_abi_profile := abi)
  fun set_ref_universe_types addr_ty gv_ty =
    (current_ref_addr_ty := addr_ty;
     current_ref_gv_ty := gv_ty;
     C_Ast_Utils.set_ref_universe_types addr_ty gv_ty)
  fun set_ref_abort_type expr_constraint_opt =
    (C_Translate.set_ref_abort_type expr_constraint_opt)
  fun set_pointer_model model =
    (current_pointer_model := model;
     C_Translate.set_pointer_model model)

  fun define_c_function prefix name term lthy =
    let
      val full_name = prefix ^ name
      val binding = Binding.name full_name
      val term' = term |> Syntax.check_term lthy
      val ((lhs_term, (_, _)), lthy') =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, @{attributes [micro_rust_simps]}), term'))
          lthy
      val morphed_lhs = Morphism.term (Local_Theory.target_morphism lthy') lhs_term
      val (registered_term, head_desc) =
        let
          val (head, args) = Term.strip_comb morphed_lhs
        in
          case head of
            Term.Const (c, _) =>
              (Term.list_comb (Const (c, dummyT), args), "const: " ^ c)
          | _ => (morphed_lhs, "registered term")
        end
      val _ =
        (C_Translate.defined_func_consts :=
           Symtab.update (full_name, registered_term) (! C_Translate.defined_func_consts);
         writeln ("Defined: " ^ full_name ^ " (" ^ head_desc ^ ")"))
    in lthy' end

  fun define_c_global_value prefix name term lthy =
    let
      val full_name = prefix ^ "global_" ^ name
      val binding = Binding.name full_name
      val term' = term |> Syntax.check_term lthy
      val ((_, (_, _)), lthy') =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, @{attributes [micro_rust_simps]}), term'))
          lthy
      val _ = writeln ("Defined: " ^ full_name)
    in lthy' end

  fun define_named_value_if_absent full_name term lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val exists_const = can (Proof_Context.read_const {proper = true, strict = true} ctxt) full_name
      val exists_fixed = is_some (Variable.lookup_fixed ctxt full_name)
    in
      if exists_const orelse exists_fixed then lthy
      else
        let
          val binding = Binding.name full_name
          val term' = term |> Syntax.check_term lthy
          val ((_, (_, _)), lthy') =
            Local_Theory.define
              ((binding, NoSyn),
               ((Thm.def_binding binding, @{attributes [micro_rust_simps]}), term'))
              lthy
          val _ = writeln ("Defined: " ^ full_name)
        in lthy' end
    end

  val abi_is_big_endian = C_ABI.big_endian

  fun mk_bool_term true = @{term True}
    | mk_bool_term false = @{term False}

  fun define_abi_metadata prefix abi_profile lthy =
    let
      val defs = [
          ("abi_pointer_bits", HOLogic.mk_nat (C_ABI.pointer_bits abi_profile)),
          ("abi_long_bits", HOLogic.mk_nat (C_ABI.long_bits abi_profile)),
          ("abi_char_is_signed", mk_bool_term (#char_is_signed (C_Compiler.get_compiler_profile ()))),
          ("abi_big_endian", mk_bool_term (abi_is_big_endian abi_profile))
        ]
    in
      List.foldl (fn ((suffix, tm), lthy_acc) =>
        define_named_value_if_absent (prefix ^ suffix) tm lthy_acc) lthy defs
    end

  val intinf_to_int_checked = C_Ast_Utils.intinf_to_int_checked
  val struct_name_of_cty = C_Ast_Utils.struct_name_of_cty

  fun type_exists ctxt tname =
    can (Proof_Context.read_type_name {proper = true, strict = true} ctxt) tname

  fun ensure_struct_record prefix (sname, fields) lthy =
    let
      val tname = prefix ^ sname
      val ctxt = Local_Theory.target_of lthy
    in
      if type_exists ctxt tname then lthy
      else
        let
          val bad_fields =
            List.filter (fn (_, ty_opt) => case ty_opt of NONE => true | SOME _ => false) fields
          val _ =
            if null bad_fields then ()
            else
              error ("micro_c_translate: cannot auto-declare struct " ^ tname ^
                     " because field type(s) are unsupported: " ^
                     String.concatWith ", " (List.map #1 bad_fields) ^
                     ". Please provide an explicit datatype_record declaration.")
          val record_fields =
            List.map (fn (fname, SOME ty) => (Binding.name (prefix ^ sname ^ "_" ^ fname), ty)
                      | (_, NONE) => raise Match) fields
          val tfrees =
            record_fields
            |> List.foldl (fn ((_, ty), acc) => Term.add_tfreesT ty acc) []
            |> distinct (op =)
          val tfree_subst =
            tfrees
            |> map_index (fn (i, (n, sort)) =>
                 ((n, sort), Term.TFree ("'ac" ^ Int.toString i, sort)))
          fun subst_tfree (n, sort) =
            case List.find (fn ((n', s'), _) => n = n' andalso sort = s') tfree_subst of
              SOME (_, t) => t
            | NONE => Term.TFree (n, sort)
          fun subst_ty ty = Term.map_atyps (fn Term.TFree ns => subst_tfree ns | t => t) ty
          val record_fields = List.map (fn (b, ty) => (b, subst_ty ty)) record_fields
          val tyargs =
            List.map (fn (_, t as Term.TFree (_, sort)) => (NONE, (t, sort))) tfree_subst
          val lthy' =
            Datatype_Records.record
              (Binding.name tname)
              Datatype_Records.default_ctr_options
              tyargs
              record_fields
              lthy
          val _ = writeln ("Declared datatype_record: " ^ tname)
        in
          lthy'
        end
    end

  fun extract_global_consts typedef_tab struct_tab enum_tab ctxt
      (C_Ast.CTranslUnit0 (ext_decls, _)) =
    let
      val struct_names = Symtab.keys struct_tab
      fun resolve_make_const sname =
        let
          val raw =
            Proof_Context.read_const {proper = true, strict = false} ctxt
              ("make_" ^ !current_decl_prefix ^ sname)
        in
          (case raw of
             Const (n, _) => Const (n, dummyT)
           | Free (x, _) =>
               (case Variable.lookup_const ctxt x of
                  SOME c => Const (c, dummyT)
                | NONE => Free (x, dummyT))
           | _ => raw)
        end
      fun has_const_qual specs =
        List.exists (fn C_Ast.CTypeQual0 (C_Ast.CConstQual0 _) => true | _ => false) specs
      fun has_static_storage specs =
        List.exists (fn C_Ast.CStorageSpec0 (C_Ast.CStatic0 _) => true | _ => false) specs
      fun has_array_declr (C_Ast.CDeclr0 (_, derived, _, _, _)) =
            List.exists (fn C_Ast.CArrDeclr0 _ => true | _ => false) derived
      fun array_decl_size (C_Ast.CDeclr0 (_, derived, _, _, _)) =
            List.mapPartial
              (fn C_Ast.CArrDeclr0 (_, C_Ast.CArrSize0 (_, C_Ast.CConst0
                    (C_Ast.CIntConst0 (C_Ast.CInteger0 (n, _, _), _))), _) =>
                    if n < 0 then
                      error "micro_c_translate: negative array bound not supported"
                    else
                      SOME (intinf_to_int_checked "array bound" n)
                | _ => NONE) derived
            |> (fn n :: _ => SOME n | [] => NONE)
      fun init_scalar_const_value (C_Ast.CConst0 (C_Ast.CIntConst0 (C_Ast.CInteger0 (n, _, _), _))) = n
        | init_scalar_const_value (C_Ast.CConst0 (C_Ast.CCharConst0 (C_Ast.CChar0 (c, _), _))) =
            C_Ast.integer_of_char c
        | init_scalar_const_value (C_Ast.CConst0 (C_Ast.CCharConst0 (C_Ast.CChars0 _, _))) =
            error "micro_c_translate: multi-character constant not supported in initializers"
        | init_scalar_const_value (C_Ast.CVar0 (ident, _)) =
            let val name = C_Ast_Utils.ident_name ident
            in case Symtab.lookup enum_tab name of
                 SOME value => IntInf.fromInt value
               | NONE =>
                   error ("micro_c_translate: unsupported global initializer element: " ^ name)
            end
        | init_scalar_const_value (C_Ast.CUnary0 (C_Ast.CMinOp0, e, _)) =
            IntInf.~ (init_scalar_const_value e)
        | init_scalar_const_value (C_Ast.CUnary0 (C_Ast.CPlusOp0, e, _)) =
            init_scalar_const_value e
        | init_scalar_const_value (C_Ast.CCast0 (_, e, _)) =
            init_scalar_const_value e
        | init_scalar_const_value _ =
            error "micro_c_translate: non-constant global initializer element"
      fun default_const_term (C_Ast_Utils.CBool) = Const (\<^const_name>\<open>False\<close>, @{typ bool})
        | default_const_term (C_Ast_Utils.CPtr _) =
            Const (\<^const_name>\<open>c_uninitialized\<close>, dummyT)
        | default_const_term (C_Ast_Utils.CStruct sname) =
            let
              val fields =
                (case Symtab.lookup struct_tab sname of
                   SOME fs => fs
                 | NONE => error ("micro_c_translate: unknown struct in global initializer: " ^ sname))
              val make_const = resolve_make_const sname
              val field_vals = List.map (fn (_, field_cty) => default_const_term field_cty) fields
            in
              List.foldl (fn (v, acc) => acc $ v) make_const field_vals
            end
        | default_const_term cty =
            HOLogic.mk_number (C_Ast_Utils.hol_type_of cty) 0
      fun init_expr_const_term (C_Ast_Utils.CPtr _) _ =
            Const (\<^const_name>\<open>c_uninitialized\<close>, dummyT)
        | init_expr_const_term target_cty (C_Ast.CConst0 (C_Ast.CStrConst0 (C_Ast.CString0 (abr_str, _), _))) =
            (case target_cty of
               _ =>
                 error "micro_c_translate: string literal initializer requires char pointer target")
        | init_expr_const_term target_cty expr =
            HOLogic.mk_number (C_Ast_Utils.hol_type_of target_cty)
              (intinf_to_int_checked "global initializer literal"
                (init_scalar_const_value expr))
      fun init_struct_const_term sname init_list =
            let
              val fields =
                (case Symtab.lookup struct_tab sname of
                   SOME fs => fs
                 | NONE => error ("micro_c_translate: unknown struct in global initializer: " ^ sname))
              fun find_field_index _ [] _ =
                    error "micro_c_translate: struct field not found in global initializer"
                | find_field_index fname ((n, _) :: rest) i =
                    if n = fname then i else find_field_index fname rest (i + 1)
              fun resolve_field_desig [] pos = pos
                | resolve_field_desig [C_Ast.CMemberDesig0 (ident, _)] _ =
                    find_field_index (C_Ast_Utils.ident_name ident) fields 0
                | resolve_field_desig _ _ =
                    error "micro_c_translate: complex designator in global struct initializer"
              fun collect_field_items [] _ = []
                | collect_field_items ((desigs, init_item) :: rest) pos =
                    let val idx = resolve_field_desig desigs pos
                    in (idx, init_item) :: collect_field_items rest (idx + 1) end
              val field_items = collect_field_items init_list 0
              val _ = List.app (fn (idx, _) =>
                        if idx < 0 orelse idx >= List.length fields
                        then error "micro_c_translate: struct designator index out of bounds in global initializer"
                        else ()) field_items
              val base_vals = List.map (fn (_, field_cty) => default_const_term field_cty) fields
              val filled =
                List.foldl
                  (fn ((idx, init_item), acc) =>
                    let
                      val (_, field_cty) = List.nth (fields, idx)
                      val v = init_value_term field_cty init_item
                    in
                      nth_map idx (K v) acc
                    end)
                  base_vals
                  field_items
              val make_const = resolve_make_const sname
            in
              List.foldl (fn (v, acc) => acc $ v) make_const filled
            end
      and init_value_term target_cty (C_Ast.CInitExpr0 (expr, _)) =
            init_expr_const_term target_cty expr
        | init_value_term (C_Ast_Utils.CStruct sname) (C_Ast.CInitList0 (init_list, _)) =
            init_struct_const_term sname init_list
        | init_value_term _ _ =
            error "micro_c_translate: unsupported non-constant global initializer shape"
      fun process_decl specs declarators =
        if not (has_const_qual specs orelse has_static_storage specs) then []
        else
          let
            val base_cty =
              (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                 SOME C_Ast_Utils.CVoid => C_Ast_Utils.CInt
               | SOME t => t
               | NONE =>
                   (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                      SOME sn => C_Ast_Utils.CStruct sn
                    | NONE =>
                        (case C_Ast_Utils.extract_union_type_from_specs_full (!C_Translate.current_union_names) specs of
                           SOME un => C_Ast_Utils.CUnion un
                         | NONE => C_Ast_Utils.CInt)))
            fun process_one ((C_Ast.Some declr, C_Ast.Some (C_Ast.CInitExpr0 (init, _))), _) =
                  let
                    val name = C_Ast_Utils.declr_name declr
                    val ptr_depth = C_Ast_Utils.pointer_depth_of_declr declr
                    val actual_cty = C_Ast_Utils.apply_ptr_depth base_cty ptr_depth
                    val init_term = init_expr_const_term actual_cty init
                    val arr_meta =
                      (case array_decl_size declr of
                         SOME n =>
                           if ptr_depth > 0
                           then SOME (C_Ast_Utils.apply_ptr_depth base_cty (ptr_depth - 1), n)
                           else NONE
                       | NONE => NONE)
                  in SOME (name, init_term, actual_cty, arr_meta, struct_name_of_cty actual_cty) end
              | process_one ((C_Ast.Some declr, C_Ast.Some (C_Ast.CInitList0 (init_list, _))), _) =
                  let
                    val name = C_Ast_Utils.declr_name declr
                    val _ =
                      if has_array_declr declr then ()
                      else error "micro_c_translate: initializer list for non-array global declaration"
                    val ptr_depth = C_Ast_Utils.pointer_depth_of_declr declr
                    val actual_cty = C_Ast_Utils.apply_ptr_depth base_cty ptr_depth
                    val elem_cty =
                      if ptr_depth > 0 then C_Ast_Utils.apply_ptr_depth base_cty (ptr_depth - 1) else base_cty
                    fun resolve_desig_idx [] pos = pos
                      | resolve_desig_idx [C_Ast.CArrDesig0 (C_Ast.CConst0 (C_Ast.CIntConst0 (C_Ast.CInteger0 (n, _, _), _)), _)] _ =
                          intinf_to_int_checked "global array designator" n
                      | resolve_desig_idx _ _ =
                          error "micro_c_translate: complex designator in global array initializer"
                    fun collect_indices [] _ = []
                      | collect_indices ((desigs, init_item) :: rest) pos =
                          let val idx = resolve_desig_idx desigs pos
                          in (idx, init_item) :: collect_indices rest (idx + 1) end
                    val indexed_items = collect_indices init_list 0
                    val declared_size = array_decl_size declr
                    val arr_size =
                      case declared_size of
                        SOME n => n
                      | NONE =>
                          List.foldl (fn ((idx, _), acc) => Int.max (acc, idx + 1)) 0 indexed_items
                    val _ = List.app (fn (idx, _) =>
                              if idx < 0 orelse idx >= arr_size
                              then error ("micro_c_translate: designator index " ^
                                          Int.toString idx ^ " out of bounds for global array of size " ^
                                          Int.toString arr_size)
                              else ()) indexed_items
                    val zero_value = default_const_term elem_cty
                    val base_values = List.tabulate (arr_size, fn _ => zero_value)
                    val filled_values =
                      List.foldl
                        (fn ((idx, init_item), acc) =>
                          nth_map idx (K (init_value_term elem_cty init_item)) acc)
                        base_values
                        indexed_items
                    val list_term = HOLogic.mk_list (C_Ast_Utils.hol_type_of elem_cty) filled_values
                    val arr_meta =
                      SOME (elem_cty, arr_size)
                  in SOME (name, list_term, actual_cty, arr_meta, struct_name_of_cty actual_cty) end
              | process_one ((C_Ast.Some _, C_Ast.None), _) = NONE
              | process_one _ =
                  error "micro_c_translate: unsupported global declarator"
          in List.mapPartial process_one declarators end
      fun resolve_decl_type_early (C_Ast.CDecl0 (specs, _, _)) =
            C_Ast_Utils.resolve_c_type_full typedef_tab specs
        | resolve_decl_type_early _ = NONE
      fun check_static_assert expr msg_lit =
            let val v = C_Ast_Utils.eval_const_int_expr resolve_decl_type_early expr
            in if v = 0 then
                 error ("micro_c_translate: _Static_assert failed: " ^
                        C_Ast_Utils.extract_string_literal msg_lit)
               else ()
            end
      fun from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CDecl0 (specs, declarators, _))) =
            process_decl specs declarators
        | from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CStaticAssert0 (expr, msg_lit, _))) =
            (check_static_assert expr msg_lit; [])
        | from_ext_decl _ = []
    in
      List.concat (List.map from_ext_decl ext_decls)
    end

  fun process_translation_unit tu lthy =
    let
      val _ = C_Translate.defined_func_consts := Symtab.empty
      val _ = C_Translate.defined_func_fuels := Symtab.empty
      val _ = C_Translate.current_list_backed_param_modes := Symtab.empty
      val _ = C_Translate.current_struct_array_fields := Symtab.empty
      val decl_prefix = !current_decl_prefix
      val abi_profile = !current_abi_profile
      val {functions = manifest_functions, types = manifest_types} = !current_manifest
      val _ = C_Ast_Utils.set_abi_profile abi_profile
      val _ = C_Translate.set_decl_prefix decl_prefix
      val _ = C_Translate.set_ref_universe_types (!current_ref_addr_ty) (!current_ref_gv_ty)
      fun mk_name_filter NONE = NONE
        | mk_name_filter (SOME xs) =
            SOME (List.foldl (fn (x, tab) => Symtab.update (x, ()) tab) Symtab.empty xs)
      val func_filter = mk_name_filter manifest_functions
      val type_filter = mk_name_filter manifest_types
      fun keep_func name =
        (case func_filter of NONE => true | SOME tab => Symtab.defined tab name)
      fun keep_type name =
        (case type_filter of NONE => true | SOME tab => Symtab.defined tab name)
      val builtin_typedefs = C_Ast_Utils.builtin_typedefs ()
      (* Extract struct definitions to build the struct field registry.
         Use fold/update to allow user typedefs to override builtins. *)
      val typedef_defs_early =
        builtin_typedefs @ C_Ast_Utils.extract_typedefs tu
      val typedef_tab_early = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                                Symtab.empty typedef_defs_early
      val struct_defs =
        List.filter (fn (n, _) => keep_type n)
          (C_Ast_Utils.extract_struct_defs_with_types typedef_tab_early tu)
      val parametric_struct_names =
        C_Ast_Utils.derive_parametric_struct_names struct_defs
      val _ = C_Ast_Utils.set_ref_universe_types (!current_ref_addr_ty) (!current_ref_gv_ty)
      val _ = C_Ast_Utils.set_parametric_struct_names parametric_struct_names
      val struct_record_defs =
        List.filter (fn (n, _) => keep_type n)
          (C_Ast_Utils.extract_struct_record_defs decl_prefix typedef_tab_early tu)
      val struct_array_field_tab =
        Symtab.make (List.filter (fn (n, _) => keep_type n) (C_Ast_Utils.extract_struct_array_fields tu))
      val _ = C_Translate.current_struct_array_fields := struct_array_field_tab
      val union_defs =
        List.filter (fn (n, _) => keep_type n)
          (C_Ast_Utils.extract_union_defs_with_types typedef_tab_early tu)
      val union_names = List.map #1 union_defs
      val _ = C_Translate.set_union_names union_names
      val struct_tab = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                         (Symtab.make struct_defs) union_defs
      val _ = List.app (fn (sname, fields) =>
        writeln ("Registered struct: " ^ sname ^ " with fields: " ^
                 String.concatWith ", " (List.map #1 fields))) struct_defs
      val _ = List.app (fn (uname, fields) =>
        writeln ("Registered union: " ^ uname ^ " with fields: " ^
                 String.concatWith ", " (List.map #1 fields))) union_defs
      (* Extract enum constant definitions *)
      val enum_defs = List.filter (fn (n, _) => keep_type n) (C_Ast_Utils.extract_enum_defs tu)
      val enum_tab = Symtab.make enum_defs
      val _ = if null enum_defs then () else
        List.app (fn (name, value) =>
          writeln ("Registered enum constant: " ^ name ^ " = " ^
                   Int.toString value)) enum_defs
      (* Extract typedef mappings *)
      val typedef_defs =
        builtin_typedefs @ C_Ast_Utils.extract_typedefs tu
      val typedef_tab = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                          Symtab.empty typedef_defs
      val _ = if null typedef_defs then () else
        List.app (fn (name, _) =>
          writeln ("Registered typedef: " ^ name)) typedef_defs
      (* Check _Static_assert declarations at top level *)
      val C_Ast.CTranslUnit0 (all_ext_decls, _) = tu
      fun resolve_decl_type_sa (C_Ast.CDecl0 (specs, _, _)) =
            C_Ast_Utils.resolve_c_type_full typedef_tab specs
        | resolve_decl_type_sa _ = NONE
      val _ = List.app
        (fn C_Ast.CDeclExt0 (C_Ast.CStaticAssert0 (expr, msg_lit, _)) =>
              let val v = C_Ast_Utils.eval_const_int_expr resolve_decl_type_sa expr
              in if v = 0 then
                   error ("micro_c_translate: _Static_assert failed: " ^
                          C_Ast_Utils.extract_string_literal msg_lit)
                 else ()
              end
          | _ => ()) all_ext_decls
      val fundefs_raw =
        List.filter
          (fn C_Ast.CFunDef0 (_, declr, _, _, _) => keep_func (C_Ast_Utils.declr_name declr))
          (C_Ast_Utils.extract_fundefs tu)
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
      fun signatures_from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CDecl0 (specs, declarators, _))) =
            List.mapPartial
              (fn ((C_Ast.Some declr, _), _) =>
                    if declr_is_function declr andalso keep_func (C_Ast_Utils.declr_name declr)
                    then SOME (signature_of_declr specs declr) else NONE
                | _ => NONE)
              declarators
        | signatures_from_ext_decl _ = []
      val C_Ast.CTranslUnit0 (ext_decls, _) = tu
      fun fundef_signature (C_Ast.CFunDef0 (specs, declr, _, _, _)) =
            signature_of_declr specs declr
      val decl_signatures = List.concat (List.map signatures_from_ext_decl ext_decls)
      fun fundef_name (C_Ast.CFunDef0 (_, declr, _, _, _)) = C_Ast_Utils.declr_name declr
      val fun_names = List.map fundef_name fundefs_raw
      val fun_name_tab = Symtab.make (List.map (fn n => (n, ())) fun_names)
      val dep_tab =
        List.foldl
          (fn (fdef, tab) =>
            let
              val name = fundef_name fdef
              val deps =
                List.filter (fn n => n <> name andalso Symtab.defined fun_name_tab n)
                  (C_Ast_Utils.find_called_functions fdef)
            in
              Symtab.update (name, deps) tab
            end)
          Symtab.empty fundefs_raw
      val fundef_tab = Symtab.make (List.map (fn fdef => (fundef_name fdef, fdef)) fundefs_raw)
      val decl_order_names = distinct (op =) (List.map #1 decl_signatures)
      val preferred_names =
        decl_order_names @
        List.filter (fn n => not (List.exists (fn m => m = n) decl_order_names)) fun_names
      val has_cycle = Unsynchronized.ref false
      fun visit stack seen order name =
        if Symtab.defined seen name then (seen, order)
        else if List.exists (fn n => n = name) stack then
          (has_cycle := true; (seen, order))
        else
          let
            val deps = the_default [] (Symtab.lookup dep_tab name)
            val (seen', order') =
              List.foldl (fn (d, (s, ord)) => visit (name :: stack) s ord d) (seen, order) deps
            val seen'' = Symtab.update (name, ()) seen'
          in
            (seen'', order' @ [name])
          end
      val (_, topo_names) =
        List.foldl (fn (n, (s, ord)) => visit [] s ord n) (Symtab.empty, []) preferred_names
      val _ =
        if !has_cycle then
          writeln "micro_c_translate: recursion cycle detected; using deterministic SCC fallback order"
        else ()
      val fundefs = List.mapPartial (fn n => Symtab.lookup fundef_tab n) topo_names
      val _ = List.app (fn C_Ast.CFunDef0 (_, declr, _, _, _) =>
                  let val name = C_Ast_Utils.declr_name declr
                  in if C_Ast_Utils.declr_is_variadic declr then
                       error ("micro_c_translate: unsupported C construct: variadic function definition: " ^ name)
                     else ()
                  end) fundefs
      fun refine_pure_functions pure_tab =
        let
          val pure_tab' =
            List.foldl
              (fn (fdef, tab) =>
                let val name = fundef_name fdef
                in
                  if C_Ast_Utils.fundef_is_pure_with pure_tab fdef then
                    Symtab.update (name, ()) tab
                  else tab
                end)
              Symtab.empty fundefs_raw
        in
          if Symtab.dest pure_tab' = Symtab.dest pure_tab then pure_tab
          else refine_pure_functions pure_tab'
        end
      val pure_fun_tab = refine_pure_functions fun_name_tab
      val _ = C_Ast_Utils.set_pure_function_names (Symtab.keys pure_fun_tab)
      val signatures = decl_signatures @ List.map fundef_signature fundefs
      val func_ret_table = List.foldl
        (fn ((n, (rty, _)), tab) => Symtab.update (n, rty) tab)
        Symtab.empty signatures
      val func_ret_types = Unsynchronized.ref func_ret_table
      val func_param_table = List.foldl
        (fn ((n, (_, ptys)), tab) => Symtab.update (n, ptys) tab)
        Symtab.empty signatures
      val func_param_types = Unsynchronized.ref func_param_table
      val all_struct_names = Symtab.keys struct_tab
      fun has_static_storage specs =
        List.exists (fn C_Ast.CStorageSpec0 (C_Ast.CStatic0 _) => true | _ => false) specs
      fun param_declr_of_decl (C_Ast.CDecl0 (_, declarators, _)) =
            (case declarators of
               ((C_Ast.Some declr, _), _) :: _ => SOME declr
             | _ => NONE)
        | param_declr_of_decl _ = NONE
      fun param_decl_has_array pdecl =
        (case param_declr_of_decl pdecl of
           SOME (C_Ast.CDeclr0 (_, derived, _, _, _)) =>
             List.exists (fn C_Ast.CArrDeclr0 _ => true | _ => false) derived
         | NONE => false)
      val list_backed_alias_envs =
        List.foldl
          (fn (fdef, tab) =>
            Symtab.update (fundef_name fdef, C_Ast_Utils.find_list_backed_aliases struct_tab struct_array_field_tab fdef) tab)
          Symtab.empty fundefs_raw
      val caller_struct_envs =
        List.foldl
          (fn (C_Ast.CFunDef0 (_, declr, _, _, _), tab) =>
            let
              val fname = C_Ast_Utils.declr_name declr
              val pdecls = C_Ast_Utils.extract_param_decls declr
              val struct_env =
                List.foldl
                  (fn (pdecl, env) =>
                    case (param_declr_of_decl pdecl,
                          C_Ast_Utils.extract_struct_type_from_decl_full all_struct_names pdecl) of
                      (SOME pdeclr, SOME sname) =>
                        Symtab.update (C_Ast_Utils.declr_name pdeclr, sname) env
                    | _ =>
                        (case (param_declr_of_decl pdecl,
                               C_Ast_Utils.extract_union_type_from_decl_full union_names pdecl) of
                           (SOME pdeclr, SOME uname) =>
                             Symtab.update (C_Ast_Utils.declr_name pdeclr, uname) env
                         | _ => env))
                  Symtab.empty pdecls
            in
              Symtab.update (fname, struct_env) tab
            end)
          Symtab.empty fundefs_raw
      val call_sites =
        List.concat
          (List.map
            (fn fdef =>
              let
                val caller = fundef_name fdef
                val caller_aliases = the_default [] (Symtab.lookup list_backed_alias_envs caller)
                val caller_struct_env = the_default Symtab.empty (Symtab.lookup caller_struct_envs caller)
              in
                List.map (fn (callee, args) => (caller_aliases, caller_struct_env, callee, args))
                  (C_Ast_Utils.find_named_calls_with_args fdef)
              end)
            fundefs_raw)
      fun arg_is_list_backed caller_aliases caller_struct_env arg =
        (case arg of
           C_Ast.CVar0 (ident, _) =>
             List.exists (fn n => n = C_Ast_Utils.ident_name ident) caller_aliases
         | C_Ast.CMember0 (base, field_ident, _, _) =>
             let
               fun expr_struct_name (C_Ast.CVar0 (ident, _)) =
                     Symtab.lookup caller_struct_env (C_Ast_Utils.ident_name ident)
                 | expr_struct_name (C_Ast.CCast0 (_, e, _)) = expr_struct_name e
                 | expr_struct_name _ = NONE
             in
               (case expr_struct_name base of
                  SOME struct_name =>
                    List.exists (fn fname => fname = C_Ast_Utils.ident_name field_ident)
                      (the_default [] (Symtab.lookup struct_array_field_tab struct_name))
                | NONE => false)
             end
         | _ => false)
      val list_backed_param_modes =
        List.foldl
          (fn (fdef as C_Ast.CFunDef0 (specs, declr, _, _, _), tab) =>
            let
              val fname = fundef_name fdef
              val indexed_names = C_Ast_Utils.find_indexed_base_vars fdef
              val pdecls = C_Ast_Utils.extract_param_decls declr
              fun mode_for_param (i, pdecl) =
                let
                  val pname = the_default "" (C_Ast_Utils.param_name pdecl)
                  val p_cty = param_cty_of_decl pdecl
                  val relevant_calls =
                    List.filter (fn (_, _, callee, args) => callee = fname andalso i < List.length args) call_sites
                in
                  if param_decl_has_array pdecl then true
                  else if not (C_Ast_Utils.is_ptr p_cty) then false
                  else if not (has_static_storage specs) then false
                  else if not (List.exists (fn n => n = pname) indexed_names) then false
                  else not (null relevant_calls) andalso
                    List.all (fn (caller_aliases, caller_struct_env, _, args) =>
                      arg_is_list_backed caller_aliases caller_struct_env (List.nth (args, i))) relevant_calls
                end
              val modes = map_index mode_for_param pdecls
            in
              Symtab.update (fname, modes) tab
            end)
          Symtab.empty fundefs_raw
      val _ = C_Translate.current_list_backed_param_modes := list_backed_param_modes
      val lthy =
        List.foldl (fn (sdef, lthy_acc) => ensure_struct_record decl_prefix sdef lthy_acc)
          lthy struct_record_defs
      val global_const_inits =
        extract_global_consts typedef_tab struct_tab enum_tab (Local_Theory.target_of lthy) tu
      val (lthy, global_consts) =
        List.foldl (fn ((gname, init_term, gcty, garr_meta, gstruct), (lthy_acc, acc)) =>
          let
            val lthy' = define_c_global_value decl_prefix gname init_term lthy_acc
            val ctxt' = Local_Theory.target_of lthy'
            val (full_name, _) =
              Term.dest_Const
                (Proof_Context.read_const {proper = true, strict = false} ctxt'
                  (decl_prefix ^ "global_" ^ gname))
            val gterm = Const (full_name, dummyT)
          in
            (lthy', acc @ [(gname, gterm, gcty, garr_meta, gstruct)])
          end)
        (lthy, []) global_const_inits
      val lthy =
        (* Define ABI metadata after type-generation commands (e.g. datatype_record)
           so locale-target equations from these definitions cannot interfere with
           datatype package obligations. *)
        define_abi_metadata decl_prefix abi_profile lthy
    in
      (* Translate and define each function one at a time, so that later
         functions can reference earlier ones via Syntax.check_term. *)
      List.foldl (fn (fundef, lthy) =>
        let val (name, term) = C_Translate.translate_fundef
              struct_tab enum_tab typedef_tab func_ret_types func_param_types global_consts lthy fundef
        in define_c_function decl_prefix name term lthy end) lthy fundefs
    end
end
\<close>

text \<open>
  Global translation lock: the ML translation pipeline uses unsynchronized
  mutable refs for threading state through structures.  When Isabelle processes
  multiple theories that each contain @{text "micro_c_translate"} or
  @{text "micro_c_file"} commands in parallel, concurrent executions can
  clobber each other's global state, producing spurious failures such as
  "missing struct field accessor constant".  We serialize all translation
  invocations through a single mutex to prevent this.
\<close>

ML \<open>
val micro_c_translation_lock : unit Synchronized.var =
  Synchronized.var "micro_c_translation_lock" ()

fun with_micro_c_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result micro_c_translation_lock (fn () => (f (), ()))
\<close>

subsection \<open>The \<open>micro_c_translate\<close> Command\<close>

text \<open>
  The command parses inline C source via Isabelle/C's parser (reusing the
  existing infrastructure including the @{text "Root_Ast_Store"}) and
  generates @{command definition} commands for each function found.

  Usage:
  @{text [display] "micro_c_translate \<open>void f() { return; }\<close>"}
  @{text [display] "micro_c_translate prefix: my_ \<open>void f() { return; }\<close>"}
  @{text [display] "micro_c_translate abi: lp64-le \<open>void f() { return; }\<close>"}
  @{text [display] "micro_c_translate addr: 'addr gv: 'gv \<open>void f() { return; }\<close>"}

  Notes:
  \<^item> Option keywords are exactly @{text "prefix:"}, @{text "addr:"}, @{text "gv:"}, and @{text "abi:"}.
  \<^item> Currently supported @{text "abi:"} values are @{text "lp64-le"}, @{text "ilp32-le"}, and @{text "lp64-be"}.
  \<^item> When omitted, declaration prefix defaults to @{text "c_"}.
  \<^item> When omitted, @{text "abi:"} defaults to @{text "lp64-le"}.
  \<^item> When omitted, @{text "addr:"} and @{text "gv:"} default to @{text "'addr"} and @{text "'gv"}.
  \<^item> Each translation unit also defines ABI metadata constants
         @{text "<prefix>abi_pointer_bits"}, @{text "<prefix>abi_long_bits"},
         @{text "<prefix>abi_char_is_signed"}, and @{text "<prefix>abi_big_endian"}.
  \<^item> Struct declarations in the input are translated to corresponding
         @{command "datatype_record"} declarations automatically when possible.
\<close>

ML \<open>
  datatype translate_opt =
      TranslatePrefix of string
    | TranslateAddrTy of string
    | TranslateGvTy of string
    | TranslateAbi of string
    | TranslatePtrAdd of string
    | TranslatePtrShiftSigned of string
    | TranslatePtrDiff of string
    | TranslateCompiler of string
  val parse_abi_ident = Scan.one (Token.ident_with (K true)) >> Token.content_of
  val parse_abi_dash =
      Scan.one (fn tok => Token.is_kind Token.Sym_Ident tok andalso Token.content_of tok = "-") >> K ()
  val parse_abi_name =
      parse_abi_ident -- Scan.repeat (parse_abi_dash |-- parse_abi_ident)
      >> (fn (h, t) => String.concatWith "-" (h :: t))
  val parse_prefix_key = Parse.$$$ "prefix:" >> K ()
  val parse_addr_key = Parse.$$$ "addr:" >> K ()
  val parse_gv_key = Parse.$$$ "gv:" >> K ()
  val parse_abi_key = Parse.$$$ "abi:" >> K ()
  val parse_ptr_add_key = Parse.$$$ "ptr_add:" >> K ()
  val parse_ptr_shift_signed_key = Parse.$$$ "ptr_shift_signed:" >> K ()
  val parse_ptr_diff_key = Parse.$$$ "ptr_diff:" >> K ()
  val parse_compiler_key = Parse.$$$ "compiler:" >> K ()
  val parse_translate_opt =
      (parse_prefix_key |-- Parse.name >> TranslatePrefix)
      || (parse_addr_key |-- Parse.typ >> TranslateAddrTy)
      || (parse_gv_key |-- Parse.typ >> TranslateGvTy)
      || (parse_abi_key |-- parse_abi_name >> TranslateAbi)
      || (parse_ptr_add_key |-- Parse.name >> TranslatePtrAdd)
      || (parse_ptr_shift_signed_key |-- Parse.name >> TranslatePtrShiftSigned)
      || (parse_ptr_diff_key |-- Parse.name >> TranslatePtrDiff)
      || (parse_compiler_key |-- parse_abi_name >> TranslateCompiler)

  type translate_opts = {
    prefix: string option, addr: string option, gv: string option,
    abi: string option,
    ptr_add: string option, ptr_shift_signed: string option, ptr_diff: string option,
    compiler: string option
  }

  val empty_opts : translate_opts = {
    prefix = NONE, addr = NONE, gv = NONE, abi = NONE,
    ptr_add = NONE, ptr_shift_signed = NONE, ptr_diff = NONE, compiler = NONE
  }

  fun set_once _ NONE v = SOME v
    | set_once name (SOME _) _ = error ("micro_c_translate: duplicate " ^ name ^ " option")

  fun apply_translate_opt (TranslatePrefix v) (r : translate_opts) =
        {prefix = set_once "prefix" (#prefix r) v, addr = #addr r, gv = #gv r, abi = #abi r,
         ptr_add = #ptr_add r, ptr_shift_signed = #ptr_shift_signed r,
         ptr_diff = #ptr_diff r, compiler = #compiler r}
    | apply_translate_opt (TranslateAddrTy v) (r : translate_opts) =
        {prefix = #prefix r, addr = set_once "addr" (#addr r) v, gv = #gv r, abi = #abi r,
         ptr_add = #ptr_add r, ptr_shift_signed = #ptr_shift_signed r,
         ptr_diff = #ptr_diff r, compiler = #compiler r}
    | apply_translate_opt (TranslateGvTy v) (r : translate_opts) =
        {prefix = #prefix r, addr = #addr r, gv = set_once "gv" (#gv r) v, abi = #abi r,
         ptr_add = #ptr_add r, ptr_shift_signed = #ptr_shift_signed r,
         ptr_diff = #ptr_diff r, compiler = #compiler r}
    | apply_translate_opt (TranslateAbi v) (r : translate_opts) =
        {prefix = #prefix r, addr = #addr r, gv = #gv r, abi = set_once "abi" (#abi r) v,
         ptr_add = #ptr_add r, ptr_shift_signed = #ptr_shift_signed r,
         ptr_diff = #ptr_diff r, compiler = #compiler r}
    | apply_translate_opt (TranslatePtrAdd v) (r : translate_opts) =
        {prefix = #prefix r, addr = #addr r, gv = #gv r, abi = #abi r,
         ptr_add = set_once "ptr_add" (#ptr_add r) v,
         ptr_shift_signed = #ptr_shift_signed r, ptr_diff = #ptr_diff r, compiler = #compiler r}
    | apply_translate_opt (TranslatePtrShiftSigned v) (r : translate_opts) =
        {prefix = #prefix r, addr = #addr r, gv = #gv r, abi = #abi r,
         ptr_add = #ptr_add r,
         ptr_shift_signed = set_once "ptr_shift_signed" (#ptr_shift_signed r) v,
         ptr_diff = #ptr_diff r, compiler = #compiler r}
    | apply_translate_opt (TranslatePtrDiff v) (r : translate_opts) =
        {prefix = #prefix r, addr = #addr r, gv = #gv r, abi = #abi r,
         ptr_add = #ptr_add r, ptr_shift_signed = #ptr_shift_signed r,
         ptr_diff = set_once "ptr_diff" (#ptr_diff r) v, compiler = #compiler r}
    | apply_translate_opt (TranslateCompiler v) (r : translate_opts) =
        {prefix = #prefix r, addr = #addr r, gv = #gv r, abi = #abi r,
         ptr_add = #ptr_add r, ptr_shift_signed = #ptr_shift_signed r,
         ptr_diff = #ptr_diff r, compiler = set_once "compiler" (#compiler r) v}

  fun collect_translate_opts opts =
    fold apply_translate_opt opts empty_opts

  (* Shared setup: resolve options against the local theory context and
     configure global translation state.  Manifest is set by the caller. *)
  fun setup_translation_context cmd_name (opts : translate_opts) lthy =
    let
      val prefix = the_default "c_" (#prefix opts)
      val abi_profile = C_ABI.parse_profile (the_default "lp64-le" (#abi opts))
      val compiler_profile =
        (case #compiler opts of
           SOME name => C_Compiler.parse_compiler name
         | NONE => C_Compiler.default_profile)
      val addr_ty = Syntax.read_typ lthy (the_default "'addr" (#addr opts))
      val gv_ty = Syntax.read_typ lthy (the_default "'gv" (#gv opts))
      fun require_visible_const_name name =
        (case try (Syntax.check_term lthy) (Free (name, dummyT)) of
           SOME _ => name
         | NONE => error (cmd_name ^ ": missing required pointer-model constant: " ^ name))
      val pointer_model =
        { ptr_add = SOME (require_visible_const_name (the_default "c_ptr_add" (#ptr_add opts)))
        , ptr_shift_signed = SOME (require_visible_const_name (the_default "c_ptr_shift_signed" (#ptr_shift_signed opts)))
        , ptr_diff = SOME (require_visible_const_name (the_default "c_ptr_diff" (#ptr_diff opts)))
        }
      val expr_constraint =
        let
          val ref_args =
            (case try (Syntax.check_term lthy) (Free ("reference_types", dummyT)) of
               SOME (Free (_, ref_ty)) =>
                 C_Translate.strip_isa_fun_type ref_ty
             | _ => [])
          val (state_ty, abort_ty, prompt_in_ty, prompt_out_ty) =
            (case ref_args of
               [s, _, _, a, i, o] => (s, a, i, o)
             | _ => (dummyT, @{typ c_abort}, dummyT, dummyT))
        in
          SOME (Type (\<^type_name>\<open>expression\<close>,
            [state_ty, dummyT, dummyT, abort_ty, prompt_in_ty, prompt_out_ty]))
        end
      val _ = C_Def_Gen.set_decl_prefix prefix
      val _ = C_Def_Gen.set_abi_profile abi_profile
      val _ = C_Compiler.set_compiler_profile compiler_profile
      val _ = C_Def_Gen.set_ref_universe_types addr_ty gv_ty
      val _ = C_Def_Gen.set_ref_abort_type expr_constraint
      val _ = C_Def_Gen.set_pointer_model pointer_model
    in () end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>micro_c_translate\<close>
    "parse C source and generate core monad definitions"
    (Scan.repeat parse_translate_opt -- Parse.embedded_input -- Scan.repeat parse_translate_opt >>
      (fn ((opts_pre, source), opts_post) => fn lthy =>
      with_micro_c_lock (fn () =>
      let
        val opts = collect_translate_opts (opts_pre @ opts_post)
        val _ = setup_translation_context "micro_c_translate" opts lthy
        val _ = C_Def_Gen.set_manifest {functions = NONE, types = NONE}
        val thy = Proof_Context.theory_of lthy
        val context' = C_Module.exec_eval source (Context.Theory thy)
        val thy' = Context.theory_of context'
        val tu = get_CTranslUnit thy'
      in
        C_Def_Gen.process_translation_unit tu lthy
      end)))
\<close>

text \<open>
  The @{text "micro_c_file"} command loads C source from an external file,
  parses it using Isabelle/C, and generates core monad definitions.
  This enables keeping verified C code in separate @{text ".c"} files,
  identical to upstream sources.

  Usage:
  @{text [display] "micro_c_file \<open>path/to/file.c\<close>"}
  @{text [display] "micro_c_file prefix: my_ \<open>path/to/file.c\<close>"}
  @{text [display] "micro_c_file prefix: my_ manifest: \<open>path/to/manifest.txt\<close> \<open>path/to/file.c\<close>"}
  @{text [display] "micro_c_file \<open>path/to/file.c\<close> prefix: my_"}
  @{text [display] "micro_c_file \<open>path/to/file.c\<close> manifest: \<open>path/to/manifest.txt\<close>"}
  @{text [display] "micro_c_file abi: ilp32-le \<open>path/to/file.c\<close>"}
  @{text [display] "micro_c_file addr: 'addr gv: 'gv \<open>path/to/file.c\<close>"}

  Manifest format (plain text):
  @{text [display] "functions:"}
  @{text [display] "  foo"}
  @{text [display] "  - bar"}
  @{text [display] "types:"}
  @{text [display] "  my_struct"}
  @{text [display] "  my_enum"}

  Notes:
  \<^item> Option keywords are exactly @{text "prefix:"}, @{text "addr:"}, @{text "gv:"}, @{text "abi:"}, and @{text "manifest:"}.
  \<^item> Currently supported @{text "abi:"} values are @{text "lp64-le"}, @{text "ilp32-le"}, and @{text "lp64-be"}.
  \<^item> Options may appear before and/or after the C file argument.
  \<^item> Each option may appear at most once.
  \<^item> When omitted, declaration prefix defaults to @{text "c_"}.
  \<^item> When omitted, @{text "abi:"} defaults to @{text "lp64-le"}.
  \<^item> When omitted, @{text "addr:"} and @{text "gv:"} default to @{text "'addr"} and @{text "'gv"}.
  \<^item> Each translation unit also defines ABI metadata constants
         @{text "<prefix>abi_pointer_bits"}, @{text "<prefix>abi_long_bits"},
         @{text "<prefix>abi_char_is_signed"}, and @{text "<prefix>abi_big_endian"}.
  \<^item> Sections are optional; supported section headers are exactly @{text "functions:"} and @{text "types:"}.
  \<^item> Lines outside a section are rejected.
  \<^item> Leading/trailing whitespace is ignored.
  \<^item> A leading @{text "-"} on an entry is optional and ignored.
  \<^item> @{text "#"} starts a line comment.
  \<^item> Struct declarations in the input are translated to corresponding
         @{command "datatype_record"} declarations automatically when possible.
\<close>

ML \<open>
local
  datatype manifest_section = Manifest_None | Manifest_Functions | Manifest_Types
  datatype load_opt = CommonOpt of translate_opt | ManifestOpt of (theory -> Token.file)
  val parse_manifest_key = Parse.$$$ "manifest:" >> K ()
  val parse_load_opt =
      (parse_translate_opt >> CommonOpt) || (parse_manifest_key |-- Resources.parse_file >> ManifestOpt)
  val semi = Scan.option \<^keyword>\<open>;\<close>;

  fun trim s = Symbol.trim_blanks s

  fun drop_comment line =
    (case String.fields (fn c => c = #"#") line of
       [] => ""
     | x :: _ => x)

  fun parse_manifest_text text =
    let
      fun add_name sec raw (fs, ts) =
        let val name0 = trim raw
            val name = if String.isPrefix "-" name0 then trim (String.extract (name0, 1, NONE)) else name0
        in
          if name = "" then (fs, ts)
          else
            (case sec of
               Manifest_Functions => (name :: fs, ts)
             | Manifest_Types => (fs, name :: ts)
             | Manifest_None =>
                 error ("micro_c_file: manifest entry outside section (functions:/types:): " ^ raw))
        end

      fun step (raw, (sec, fs, ts)) =
        let val line = trim (drop_comment raw)
        in
          if line = "" then (sec, fs, ts)
          else if line = "functions:" then (Manifest_Functions, fs, ts)
          else if line = "types:" then (Manifest_Types, fs, ts)
          else
            let val (fs', ts') = add_name sec line (fs, ts)
            in (sec, fs', ts') end
        end

      val (_, rev_fs, rev_ts) =
        List.foldl step (Manifest_None, [], []) (String.tokens (fn c => c = #"\n" orelse c = #"\r") text)
      val fs = rev rev_fs
      val ts = rev rev_ts
    in
      { functions = if null fs then NONE else SOME fs
      , types = if null ts then NONE else SOME ts }
    end

  fun collect_load_opts opts =
    let
      fun step (CommonOpt topt) (topts, mopt) = (topt :: topts, mopt)
        | step (ManifestOpt f) (_, SOME _) = error "micro_c_file: duplicate manifest option"
        | step (ManifestOpt f) (topts, NONE) = (topts, SOME f)
      val (rev_topts, manifest_opt) = fold step opts ([], NONE)
    in (collect_translate_opts (rev rev_topts), manifest_opt) end
in
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>micro_c_file\<close>
    "load C file and generate core monad definitions"
    (Scan.repeat parse_load_opt -- Resources.parse_file -- Scan.repeat parse_load_opt --| semi >>
      (fn ((opts_pre, get_file), opts_post) => fn lthy =>
      with_micro_c_lock (fn () =>
      let
        val (opts, manifest_get_file) = collect_load_opts (opts_pre @ opts_post)
        val _ = setup_translation_context "micro_c_file" opts lthy
        val thy = Proof_Context.theory_of lthy
        val {src_path, lines, digest, pos} : Token.file = get_file thy

        (* Step 1: Parse the C file using Isabelle/C's parser *)
        val source = Input.source true (cat_lines lines) (pos, pos)
        val context' = C_Module.exec_eval source (Context.Theory thy)
        val thy' = Context.theory_of context'

        (* Step 2: Register file dependency so Isabelle rebuilds if file changes.
           Allow the same source file to be used across multiple micro_c_file
           invocations (e.g. with different manifests for layered extraction). *)
        val lthy = Local_Theory.background_theory
                     (fn thy => Resources.provide (src_path, digest) thy
                        handle ERROR msg =>
                          if String.isSubstring "Duplicate use of source file" msg
                          then thy
                          else error msg) lthy

        (* Optional manifest file controlling which functions/types are extracted. *)
        val (manifest, lthy) =
          (case manifest_get_file of
             NONE => ({functions = NONE, types = NONE}, lthy)
           | SOME get_manifest_file =>
               let
                 val {src_path = m_src, lines = m_lines, digest = m_digest, ...} : Token.file =
                   get_manifest_file thy
                 val lthy' =
                   Local_Theory.background_theory
                     (fn thy => Resources.provide (m_src, m_digest) thy
                        handle ERROR msg =>
                          if String.isSubstring "Duplicate use of source file" msg
                          then thy
                          else error msg) lthy
               in
                 (parse_manifest_text (cat_lines m_lines), lthy')
               end)

        (* Step 3: Retrieve parsed AST and translate *)
        val tu = get_CTranslUnit thy'
        val _ = C_Def_Gen.set_manifest manifest
      in
        C_Def_Gen.process_translation_unit tu lthy
      end)))
end
\<close>

end
