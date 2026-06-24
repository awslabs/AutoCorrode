(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust_Shallow_Embedding
  imports
    Micro_Rust_Parsing_Frontend.Micro_Rust_Syntax
    Core_Syntax
    Micro_Rust_Notations
    Prompts_And_Responses
    "HOL-Library.Datatype_Records"
    Autogen.Autogen
    Lenses_And_Other_Optics.Lenses_And_Other_Optics
    Tuple
  keywords
    "micro_rust_record" :: thy_decl
begin
(*>*)
section\<open>The shallow embedding of uRust into HOL\<close>

text\<open>In this section we define the shallow embedding of uRust into HOL as
a syntax transformations \<^text>\<open>urust \<Rightarrow> logic\<close> from the syntactic category of Micro Rust programs
to the category of HOL terms.\<close>

subsection\<open>Custom identifiers and identifier remapping\<close>

text\<open>The in-built syntax category \<^verbatim>\<open>id\<close> of HOL identifiers does not encompass qualified
Rust names such as \<^verbatim>\<open>Foo::Bar\<close>. The path-flattening AST translation in
\<^file>\<open>../Micro_Rust_Parsing_Frontend/Micro_Rust_Syntax.thy\<close> turns such paths into
\<^verbatim>\<open>_urust_identifier_id\<close> nodes whose payload is a plain \<^verbatim>\<open>Ast.Variable\<close> carrying
the joined name (e.g. \<^verbatim>\<open>"Foo::Bar"\<close>); downstream consumers therefore see no
structural difference between path and plain identifiers --- only the name
string contains \<^verbatim>\<open>::\<close>.

For general \<^verbatim>\<open>id\<close>s, we introduce an intermediate \<^verbatim>\<open>_urust_identifier_id_const\<close>. This allows us
to register Micro-Rust-to-HOL name changes for those identifiers which \<^emph>\<open>do\<close> fall
under the \<^verbatim>\<open>id\<close> syntax category.\<close>

syntax
  "_urust_identifier_id_const" :: \<open>id \<Rightarrow> logic\<close> ("URUST'_CONST _")

parse_ast_translation\<open>
let
  fun urust_const_ast_tr _ [Ast.Variable c] = Ast.Appl [Ast.Constant "_urust_identifier_id", Ast.Constant c]
  | urust_const_ast_tr _ asts = raise Ast.AST ("urust_const_ast_tr", asts)
in
  [(\<^syntax_const>\<open>_urust_identifier_id_const\<close>, urust_const_ast_tr)]
end
\<close>

\<comment>\<open>Path-style uRust names (\<^verbatim>\<open>Foo::Bar\<close>) and plain identifiers both reach
  \<open>lookup_id_tr\<close> (the \<open>parse_translation\<close> on \<open>_shallow_identifier_as_*\<close>)
  as the same \<^verbatim>\<open>Free name\<close> shape; resolution proceeds via the
  \<^ML_structure>\<open>Micro_Rust_Names\<close> table, populated by the
  \<^theory_text>\<open>micro_rust_notation\<close> command in
  \<^theory>\<open>Shallow_Micro_Rust.Micro_Rust_Notations\<close>.\<close>

named_theorems micro_rust_record_simps
named_theorems micro_rust_record_intros

ML\<open>
   fun number_of_type_arguments ctxt (tyname : string) =
       tyname
    |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
    |> Term.dest_Type
    |> snd
    |> List.length

   fun repeat (_ : 'a) 0 : 'a list = []
     | repeat (x : 'a) n : 'a list = x :: repeat x (n-1)

   fun generic_type_arguments ctxt tyname =
       tyname
    |> number_of_type_arguments ctxt
    |> repeat "type"

   (* Mimicking "instance {rec_name} :: (type, type, ...) localizable .." *)
   fun instantiate_localizable_class rec_name (ctxt : Proof.context) =
     let val typeargs = generic_type_arguments ctxt rec_name
         val full_tyname = Proof_Context.read_type_name {proper = true, strict = false} ctxt rec_name
                           |> Term.dest_Type |> fst
     in
     ((Class.instance_arity_cmd ([full_tyname], typeargs, @{class localizable})
       #> Proof.global_default_proof
       #> Proof_Context.theory_of)
      |> Local_Theory.background_theory) ctxt
     end
\<close>

ML\<open>
   \<comment>\<open>Register an auto-generated field lens as \<^verbatim>\<open>micro_rust_notation (field)\<close>
     under its uRust name, via the command's \<open>do_register\<close>. By default the
     uRust name is the bare (record-prefixed) HOL field name; the optional
     \<^verbatim>\<open>(hol_field = "urust_name", \<dots>)\<close> mapping passed to \<^verbatim>\<open>micro_rust_record\<close>
     overrides this per field — useful because HOL field names are usually
     disambiguated with a record-name prefix that one does not want to repeat
     at every uRust use site. The uRust name is a plain identifier
     (grammatical, so no bespoke grammar production is emitted) and the lens
     has type \<open>_ lens\<close> (so the forced \<open>field\<close> kind validates against the
     term's type).\<close>
   fun register_lens_with_micro_rust rec_name overrides field lthy =
      let val name = lens_name rec_name field
          val full_name = Local_Theory.full_name lthy (Binding.name name)
          val (rust_name, rust_pos) =
            case AList.lookup (op =) overrides field of
              SOME name_and_pos => name_and_pos
            | NONE              => (field, Position.thread_data ())
      in
        Micro_Rust_Notation_Cmd.do_register (SOME Micro_Rust_Names.NField)
          (full_name, (rust_name, rust_pos)) lthy
      end

   \<comment>\<open>Reject a uRust-name mapping whose left-hand sides are not all fields of
     the record: an unmatched entry is silently dropped otherwise, masking a
     typo in the field name.\<close>
   fun check_override_fields rec_name fields overrides =
      let val unknown = filter_out (member (op =) fields) (map fst overrides) in
        if null unknown then ()
        else error ("micro_rust_record: unknown field(s) in uRust-name mapping: "
                    ^ commas_quote unknown ^ "\nRecord " ^ quote rec_name
                    ^ " has fields: " ^ commas_quote fields)
      end

   fun register_lenses_with_micro_rust rec_name overrides thy =
      let val fields = get_fields rec_name thy in
        fold (register_lens_with_micro_rust rec_name overrides) fields thy
      end

   \<comment>\<open>Pretty-print, as a bullet list, the definitions and theorems
     \<^verbatim>\<open>micro_rust_record\<close> emits for a record (one bullet per artifact), so the
     (otherwise opaque) autogen output is replaced by the concrete names a user
     can reference. The trailing bullets record the uRust field-access names
     (\<open>urust_name \<mapsto> hol_field\<close>, collapsing to the bare field where no override
     applies) and the localizable class instance.\<close>
   fun summarise_micro_rust_record rec_name fields overrides with_fields =
      let fun urust_of f =
            case AList.lookup (op =) overrides f of
              SOME (rust_name, _) => rust_name
            | NONE                => f
          fun field_facts f =
            let val base = rec_name ^ "_" ^ f in
              [base ^ "_lens", base ^ "_lens_view_update_modify", base ^ "_lens_valid",
               base ^ "_focus", base ^ "_focus_view_update_modify", base ^ "_focus_code",
               base ^ "_update_explicit", base ^ "_update_localI"]
            end
          fun render_field_map f =
            let val rust_name = urust_of f in
              if rust_name = f then f else rust_name ^ " \<mapsto> " ^ f
            end
          val urust_facts =
            if with_fields then map (fn f => "uRust field access: " ^ render_field_map f) fields
            else []
          val bullets =
            maps field_facts fields @ urust_facts @ [rec_name ^ " :: localizable"]
      in
        Pretty.writeln (Pretty.chunks (map (fn s => Pretty.str ("• " ^ s)) bullets))
      end

   fun make_lenses ((with_fields, rec_name), overrides) _ lthy =
      let val _ =
            if with_fields orelse null overrides then ()
            else error "micro_rust_record: a uRust-name mapping cannot be combined \
                       \with [no_fields], which suppresses field registration"
          val fields = get_fields rec_name lthy
          val _ = check_override_fields rec_name fields overrides
          val _ = summarise_micro_rust_record rec_name fields overrides with_fields
      in
        lthy
     |> lens_autogen_defs                                                                          rec_name
     |> lens_autogen_defining_equations     @{attributes [micro_rust_record_simps, focus_simps]}   rec_name
     |> lens_autogen_prove_lens_validity    @{attributes [micro_rust_record_intros, focus_intros,
                                                          micro_rust_record_simps, focus_simps]}   rec_name
     |> lens_autogen_prove_update_equations @{attributes [micro_rust_record_simps, focus_simps]}
                                            @{attributes [micro_rust_record_intros, focus_intros]} rec_name
     |> focus_autogen_make_field_foci @{attributes [focus_components]} rec_name
     |> (if with_fields then
           register_lenses_with_micro_rust rec_name overrides
         else
           I)
     |> instantiate_localizable_class rec_name
      end

   \<comment>\<open>Parse an optional \<^verbatim>\<open>(hol_field = "urust_name", \<dots>)\<close> mapping after the
     record name. Each \<^verbatim>\<open>"urust_name"\<close> is position-tracked so its use-site
     markup points back at the literal in the command.\<close>
   val parse_field_overrides =
      Scan.optional
        (Parse.$$$ "(" |--
           Parse.enum1 "," (Parse.short_ident -- (Parse.$$$ "=" |-- Parse.position Parse.string))
         --| Parse.$$$ ")")
        []

   val _ =
      Outer_Syntax.local_theory' \<^command_keyword>\<open>micro_rust_record\<close> "make lenses for datatype record"
       ((((Scan.optional ((Args.bracks (Args.$$$ "no_fields")) >> K false) true) -- Parse.short_ident)
            -- parse_field_overrides) >> make_lenses)
\<close>

subsection\<open>The embedding\<close>

syntax
  \<comment>\<open>The shallow embedding of uRust into HOL\<close>
  "_shallow" :: \<open>urust \<Rightarrow> logic\<close> ("\<lbrakk>_\<rbrakk>"[0]1000)

  \<comment> \<open>Intermediate helper for applying parameters\<close>
  "_shallow_apply_params" :: \<open>logic \<Rightarrow> urust_params \<Rightarrow> logic\<close>

  \<comment> \<open>Intermediate helper for building closures\<close>
  "_shallow_abstract_args" :: \<open>urust_formal_args \<Rightarrow> urust \<Rightarrow> logic\<close>

  \<comment> \<open>Intermediate helper for lowering identifiers to HOL\<close>
  "_shallow_identifier_as_literal" :: \<open>urust_identifier \<Rightarrow> logic\<close>
  "_shallow_identifier_as_function" :: \<open>urust_identifier \<Rightarrow> logic\<close>
  "_shallow_identifier_as_field" :: \<open>urust_identifier \<Rightarrow> logic\<close>

  \<comment> \<open>Lower a uRust identifier in BINDER-INTRODUCTION position (let-pattern
     leaf, for-loop binder, etc.) to a plain \<^verbatim>\<open>Free\<close> suitable as the binder
     slot of \<open>_abs\<close>. Distinct from \<open>_shallow_identifier_as_literal\<close>: pure
     binders never consult the dispatch table --- their identifier IS the
     binder, and any registered uRust notation of the same name is shadowed
     by the let.\<close>
  "_shallow_pattern_id" :: \<open>urust_identifier \<Rightarrow> logic\<close>

  "_shallow_match_branches" :: \<open>urust_match_branches \<Rightarrow> urust_shallow_match_branches\<close>
  "_shallow_match_branch" :: \<open>urust_match_branch  \<Rightarrow> urust_shallow_match_branch \<close>
  "_shallow_match_pattern" :: \<open>urust_pattern \<Rightarrow> urust_shallow_match_pattern\<close>
  "_shallow_match_args" :: \<open>urust_pattern_args \<Rightarrow> urust_shallow_match_pattern_args \<close>
  "_shallow_match_arg" :: \<open>urust_pattern \<Rightarrow> urust_shallow_match_pattern_arg\<close>
  "_shallow_let_pattern" :: \<open>urust_pattern \<Rightarrow> pttrns\<close>
  "_shallow_let_pattern_args" :: \<open>urust_let_pattern_args \<Rightarrow> pttrns\<close>
  "_urust_struct_expr_to_args" :: \<open>urust_struct_expr_fields \<Rightarrow> urust_args\<close>
  "_urust_array_expr_to_shallow" :: \<open>urust_args \<Rightarrow> logic\<close>

  "_string_token_to_hol" :: \<open>string_token \<Rightarrow> logic\<close>

text\<open>We define the shallow embedding of uRust into HOL via a series of transformations
at the syntax level.\<close>

context
  notes [[syntax_ast_trace]]
begin
term\<open>let (x, _ :: int) = (5,6) in x+12\<close>
end


\<comment>\<open>Path-style names like \<^verbatim>\<open>Foo::Bar\<close> are resolved by the
  \<^verbatim>\<open>parse_translation\<close> for \<^verbatim>\<open>_shallow_identifier_as_*\<close> (see
  \<open>lookup_id_tr\<close> below): it looks the name up in the
  \<^ML_structure>\<open>Micro_Rust_Names\<close> table and falls back to the bare
  identifier on miss, so paths participate in the same multi-backend,
  type-driven dispatch as plain identifiers.\<close>

translations
  \<comment>\<open>The shallow embedding of a HOL term is the corresponding literal\<close>
  "_shallow(_urust_literal f)"
    \<rightharpoonup> "CONST literal f"
  "_shallow(_urust_fun_literal1 f)"
    \<rightharpoonup> "CONST lift_fun1 f"
  "_shallow(_urust_fun_literal2 f)"
    \<rightharpoonup> "CONST lift_fun2 f"
  "_shallow(_urust_fun_literal3 f)"
    \<rightharpoonup> "CONST lift_fun3 f"
  "_shallow(_urust_fun_literal4 f)"
    \<rightharpoonup> "CONST lift_fun4 f"
  "_shallow(_urust_fun_literal5 f)"
    \<rightharpoonup> "CONST lift_fun5 f"
  "_shallow(_urust_fun_literal6 f)"
    \<rightharpoonup> "CONST lift_fun6 f"
  "_shallow(_urust_fun_literal7 f)"
    \<rightharpoonup> "CONST lift_fun7 f"
  "_shallow(_urust_fun_literal8 f)"
    \<rightharpoonup> "CONST lift_fun8 f"
  "_shallow(_urust_fun_literal9 f)"
    \<rightharpoonup> "CONST lift_fun9 f"
  "_shallow(_urust_fun_literal10 f)"
    \<rightharpoonup> "CONST lift_fun10 f"
  "_shallow(_urust_fun_literal11 f)"
    \<rightharpoonup> "CONST lift_fun11 f"
  "_shallow(_urust_fun_literal12 f)"
    \<rightharpoonup> "CONST lift_fun12 f"
  "_shallow(_urust_fun_literal13 f)"
    \<rightharpoonup> "CONST lift_fun13 f"
  "_shallow(_urust_fun_literal14 f)"
    \<rightharpoonup> "CONST lift_fun14 f"
  "_shallow(_urust_numeral num)"
    \<rightharpoonup> "CONST literal (_Numeral num)" \<comment>\<open>TODO: What type should we cast numerals to by default?\<close>
  "_shallow(_urust_numeral_0)"
    \<rightharpoonup> "CONST literal 0"
  "_shallow(_urust_numeral_1)"
    \<rightharpoonup> "CONST literal 1"
  "_shallow(_urust_string_token str)"
    \<rightharpoonup> "CONST literal (_string_token_to_hol str)"
  \<comment> \<open>The shallow embedding of a shallow Micro Rust \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> is the expression itself\<close>
  "_shallow(_urust_antiquotation exp)"
    \<rightharpoonup> "exp"
  "_shallow(_urust_unit)"
    \<rightharpoonup> "CONST literal ()"
  "_shallow(_urust_pause)"
    \<rightharpoonup> "CONST pause"
  "_shallow(_urust_log priority logval)"
    \<rightharpoonup> "CONST log priority logval"
  "_shallow(_urust_parens exp)"
    \<rightharpoonup> "_shallow exp"
  \<comment>\<open>Primitive casts\<close>
  "_shallow(_urust_primitive_integral_cast_u8 e)"
    \<rightharpoonup> "CONST ucastu8 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_u16 e)"
    \<rightharpoonup> "CONST ucastu16 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_u32 e)"
    \<rightharpoonup> "CONST ucastu32 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_u64 e)"
    \<rightharpoonup> "CONST ucastu64 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_i32 e)"
    \<rightharpoonup> "CONST ucasti32 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_i64 e)"
    \<rightharpoonup> "CONST ucasti64 (_shallow e)"
  "_shallow(_urust_primitive_integral_cast_usize e)"
    \<rightharpoonup> "CONST ucastu64 (_shallow e)"
  \<comment>\<open>Raw pointer casts\<close>
  "_shallow(_urust_ptr_const_cast_u8 e)"
    \<rightharpoonup> "CONST raw_ptr_cast_u8 (_shallow e)"
  "_shallow(_urust_ptr_const_cast_u16 e)"
    \<rightharpoonup> "CONST raw_ptr_cast_u16 (_shallow e)"
  "_shallow(_urust_ptr_const_cast_u32 e)"
    \<rightharpoonup> "CONST raw_ptr_cast_u32 (_shallow e)"
  "_shallow(_urust_ptr_const_cast_u64 e)"
    \<rightharpoonup> "CONST raw_ptr_cast_u64 (_shallow e)"
  "_shallow(_urust_ptr_const_cast_usize e)"
    \<rightharpoonup> "CONST raw_ptr_cast_u64 (_shallow e)"
  "_shallow(_urust_numeral_ascription_0_u8)"
    \<rightharpoonup> "CONST ascribeu8 0"
  "_shallow(_urust_numeral_ascription_1_u8)"
    \<rightharpoonup> "CONST ascribeu8 1"
  "_shallow(_urust_numeral_ascription_u8 e)"
    \<rightharpoonup> "CONST ascribeu8 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_u16)"
    \<rightharpoonup> "CONST ascribeu16 0"
  "_shallow(_urust_numeral_ascription_1_u16)"
    \<rightharpoonup> "CONST ascribeu16 1"
  "_shallow(_urust_numeral_ascription_u16 e)"
    \<rightharpoonup> "CONST ascribeu16 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_u32)"
    \<rightharpoonup> "CONST ascribeu32 0"
  "_shallow(_urust_numeral_ascription_1_u32)"
    \<rightharpoonup> "CONST ascribeu32 1"
  "_shallow(_urust_numeral_ascription_u32 e)"
    \<rightharpoonup> "CONST ascribeu32 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_u64)"
    \<rightharpoonup> "CONST ascribeu64 0"
  "_shallow(_urust_numeral_ascription_1_u64)"
    \<rightharpoonup> "CONST ascribeu64 1"
  "_shallow(_urust_numeral_ascription_u64 e)"
    \<rightharpoonup> "CONST ascribeu64 (_Numeral e)"
  "_shallow(_urust_numeral_ascription_0_usize)"
    \<rightharpoonup> "CONST ascribeu64 0"
  "_shallow(_urust_numeral_ascription_1_usize)"
    \<rightharpoonup> "CONST ascribeu64 1"
  "_shallow(_urust_numeral_ascription_usize e)"
    \<rightharpoonup> "CONST ascribeu64 (_Numeral e)"
  \<comment>\<open>Explicit scopes are relevant for initial parsing and can be removed when operating on ASTs\<close>
  "_shallow(_urust_scoping f)"
    \<rightharpoonup> "(_shallow f)"
  \<comment>\<open>The shallow embedding of standard if-then-else conditional\<close>
  "_shallow (_urust_if_then_else c t e)"
    \<rightharpoonup> "if (_shallow c) \<lbrace> (_shallow t) \<rbrace> else \<lbrace> (_shallow e) \<rbrace>"
  "_shallow (_urust_if_then c t)"
    \<rightharpoonup> "if (_shallow c) \<lbrace> (_shallow t) \<rbrace> else \<lbrace> (CONST skip) \<rbrace>"
  \<comment>\<open>Unsafe blocks are semantically meaningless and merely included to make \<^verbatim>\<open>\<mu>Rust\<close> look closer to
     upstream Rust code.\<close>
  "_shallow (_urust_unsafe_block t)"
    \<rightharpoonup> "_shallow t"

  \<comment> \<open>TODO: Can we not have one case that handles all this? See also \<^url>\<open>https://github.com/awslabs/AutoCorrode/issues/29\<close>\<close>
  "_shallow (_urust_funcall_with_args (_urust_callable_id id) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_identifier_as_function id) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_antiquotation emb) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args emb (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_fun_literal f) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow f) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_struct f id) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_identifier_as_function id) (_shallow (_urust_args_app f args))"

  \<comment>\<open>Turbofish with args\<close>
  "_shallow (_urust_funcall_with_args (_urust_callable_with_params (_urust_callable_id id) params) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow_identifier_as_function id) params) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_with_params (_urust_callable_fun_literal f) params) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow f) params) (_shallow args)"
  "_shallow (_urust_funcall_with_args (_urust_callable_with_params (_urust_callable_struct f id) params) args)"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow_identifier_as_function id) params) (_shallow (_urust_args_app f args))"

  "_urust_struct_expr_to_args (_urust_struct_expr_fields_single (_urust_struct_expr_field fld e))"
    \<rightharpoonup> "_urust_args_single e"
  "_urust_struct_expr_to_args (_urust_struct_expr_fields_app (_urust_struct_expr_field fld e) rest)"
    \<rightharpoonup> "_urust_args_app e (_urust_struct_expr_to_args rest)"
  "_shallow (_urust_struct_expr id fields)"
    \<rightharpoonup> "_shallow (_urust_funcall_with_args (_urust_callable_id id) (_urust_struct_expr_to_args fields))"
  "_shallow (_urust_array_expr_empty)"
    \<rightharpoonup> "CONST literal ([])"
  "_shallow (_urust_array_expr args)"
    \<rightharpoonup> "_urust_array_expr_to_shallow args"
  "_urust_array_expr_to_shallow (_urust_args_single a)"
    \<rightharpoonup> "CONST bindlift2 (CONST List.list.Cons) (_shallow a) (CONST literal ([]))"
  "_urust_array_expr_to_shallow (_urust_args_app a rest)"
    \<rightharpoonup> "CONST bindlift2 (CONST List.list.Cons) (_shallow a) (_urust_array_expr_to_shallow rest)"

  "_shallow (_urust_args_app a bs)"
    \<rightharpoonup> "_urust_shallow_args_app (_shallow a) (_shallow bs)"
  "_shallow (_urust_args_single a)"
    \<rightharpoonup> "_urust_shallow_args_single (_shallow a)"
  "_shallow (_urust_funcall_no_args (_urust_callable_id id))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow_identifier_as_function id)"
  "_shallow (_urust_funcall_no_args (_urust_callable_antiquotation emb))"
    \<rightharpoonup> "_urust_shallow_fun_no_args emb"
  "_shallow (_urust_funcall_no_args (_urust_callable_fun_literal f))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow f)"
  "_shallow (_urust_funcall_no_args (_urust_callable_struct f id))"
    \<rightharpoonup> "_shallow (_urust_funcall_with_args (_urust_callable_id id) (_urust_args_single f))"

  \<comment>\<open>Turbofish no args\<close>
  "_shallow (_urust_funcall_no_args (_urust_callable_with_params (_urust_callable_id id) params))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow_apply_params (_shallow_identifier_as_function id) params)"
  "_shallow (_urust_funcall_no_args (_urust_callable_with_params (_urust_callable_fun_literal f) params))"
    \<rightharpoonup> "_urust_shallow_fun_no_args (_shallow_apply_params (_shallow f) params)"
  "_shallow (_urust_funcall_no_args (_urust_callable_with_params (_urust_callable_struct f id) params))"
    \<rightharpoonup> "_urust_shallow_fun_with_args (_shallow_apply_params (_shallow_identifier_as_function id) params) (_shallow (_urust_args_single f))"

  "_shallow (_urust_return_unit)"
    \<rightharpoonup> "_urust_shallow_return (CONST literal ())"
  "_shallow (_urust_return exp)"
    \<rightharpoonup> "_urust_shallow_return (_shallow exp)"
  "_shallow (_urust_bind_immutable pattern exp cont)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp) (_abs (_shallow_let_pattern pattern) (_shallow cont))"
  "_shallow (_urust_bind_immutable' pattern exp cont)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp) (_abs (_shallow_let_pattern pattern) (_shallow cont))"
  \<comment>\<open>Let-pattern leaves use the binder-position resolver --- their
    identifier IS the binder, so we must not emit a \<^verbatim>\<open>urust_dispatch\<close>
    marker here (it would crash \<^ML>\<open>Syntax_Trans.abs_tr\<close>).\<close>
  "_shallow_let_pattern (_urust_match_pattern_constr_no_args id)"
    \<rightharpoonup> "_shallow_pattern_id id"
  "_shallow_let_pattern _urust_match_pattern_other"
    \<rightharpoonup> "_idtdummy"
  "_shallow_let_pattern (_urust_match_pattern_grouped pat)"
    \<rightharpoonup> "_shallow_let_pattern pat"

  \<comment>\<open>Tuples\<close>
  "_shallow (_urust_tuple_args_double a b)"
    \<rightleftharpoons> "CONST tuple_base_pair (_shallow a) (_shallow b)"
  "_shallow (_urust_tuple_args_app a bs)"
    \<rightleftharpoons> "CONST tuple_cons (_shallow a) (_shallow bs)"
  "_shallow (_urust_tuple_constr args)"
    \<rightleftharpoons> "_shallow args"
  "_shallow (_urust_tuple_index_0 arg)"
    \<rightleftharpoons> "CONST tuple_index_0 (_shallow arg)"
  "_shallow (_urust_tuple_index_1 arg)"
    \<rightleftharpoons> "CONST tuple_index_1 (_shallow arg)"
  "_shallow (_urust_tuple_index_2 arg)"
    \<rightleftharpoons> "CONST tuple_index_2 (_shallow arg)"
  "_shallow (_urust_tuple_index_3 arg)"
    \<rightleftharpoons> "CONST tuple_index_3 (_shallow arg)"
  "_shallow (_urust_tuple_index_4 arg)"
    \<rightleftharpoons> "CONST tuple_index_4 (_shallow arg)"
  "_shallow (_urust_tuple_index_5 arg)"
    \<rightleftharpoons> "CONST tuple_index_5 (_shallow arg)"
  "_shallow (_urust_tuple_index_6 arg)"
    \<rightleftharpoons> "CONST tuple_index_6 (_shallow arg)"
  "_shallow (_urust_tuple_index_7 arg)"
    \<rightleftharpoons> "CONST tuple_index_7 (_shallow arg)"
  "_shallow (_urust_tuple_index_8 arg)"
    \<rightleftharpoons> "CONST tuple_index_8 (_shallow arg)"
  "_shallow (_urust_tuple_index_9 arg)"
    \<rightleftharpoons> "CONST tuple_index_9 (_shallow arg)"
  "_shallow (_urust_tuple_index_10 arg)"
    \<rightleftharpoons> "CONST tuple_index_10 (_shallow arg)"
  "_shallow (_urust_tuple_index_11 arg)"
    \<rightleftharpoons> "CONST tuple_index_11 (_shallow arg)"
  "_shallow (_urust_tuple_index_12 arg)"
    \<rightleftharpoons> "CONST tuple_index_12 (_shallow arg)"
  "_shallow (_urust_tuple_index_13 arg)"
    \<rightleftharpoons> "CONST tuple_index_13 (_shallow arg)"
  "_shallow (_urust_tuple_index_14 arg)"
    \<rightleftharpoons> "CONST tuple_index_14 (_shallow arg)"
  "_shallow (_urust_tuple_index_15 arg)"
    \<rightleftharpoons> "CONST tuple_index_15 (_shallow arg)"
  "_shallow_let_pattern (_urust_let_pattern_tuple args)"
    \<rightleftharpoons> "_shallow_let_pattern_args args"
  "_shallow_let_pattern_args (_urust_let_pattern_tuple_base_pair fst_pat snd_pat)"
    \<rightleftharpoons> "_pattern (_shallow_let_pattern fst_pat) (_pattern (_shallow_let_pattern snd_pat) (_idtdummy :: Tuple.tnil))"
  "_shallow_let_pattern_args (_urust_let_pattern_tuple_app fst_pat snd_pat)"
    \<rightleftharpoons> "_pattern (_shallow_let_pattern fst_pat) (_shallow_let_pattern_args snd_pat)"

  "_shallow (_urust_bind_mutable (_urust_identifier_hol_id var) exp cont)"
    \<rightharpoonup> "CONST bind (Ref::new \<langle>(_shallow exp)\<rangle>) (\<lambda>var. (_shallow cont))"
  \<comment>\<open>Mutable binding with tuple pattern: \<^verbatim>\<open>let mut (x, y) = expr\<close>. The \<^verbatim>\<open>mut\<close> annotation is
      dropped since Rust's local-variable mutability is not modelled in the shallow embedding.\<close>
  "_shallow (_urust_bind_mutable_pattern args exp cont)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp) (_abs (_shallow_let_pattern_args args) (_shallow cont))"
  "_shallow (_urust_sequence seqA seqB)"
    \<rightharpoonup> "CONST sequence (_shallow seqA) (_shallow seqB)"
  "_shallow (_urust_sequence_mono seqA)"
    \<rightharpoonup> "CONST sequence (_shallow seqA) (CONST skip)"

  "_shallow (_urust_identifier ident)"
    \<rightharpoonup> "CONST literal (_shallow_identifier_as_literal ident)"
  "_shallow (_urust_true)"
    \<rightharpoonup> "_urust_shallow_bool_true"
  "_shallow (_urust_false)"
    \<rightharpoonup> "_urust_shallow_bool_false"

  "_shallow (_urust_field_access exp fld)"
    \<rightharpoonup> "_urust_shallow_field_access (_shallow exp) (_shallow_identifier_as_field fld)"

  "_shallow (_urust_propagate exp)"
    \<rightharpoonup> "_urust_shallow_propagate (_shallow exp)"
  "_shallow (_urust_borrow (_urust_array_expr_empty))"
    \<rightharpoonup> "_shallow (_urust_array_expr_empty)"
  "_shallow (_urust_borrow (_urust_array_expr args))"
    \<rightharpoonup> "_shallow (_urust_array_expr args)"
  "_shallow (_urust_borrow_mut (_urust_array_expr_empty))"
    \<rightharpoonup> "_shallow (_urust_array_expr_empty)"
  "_shallow (_urust_borrow_mut (_urust_array_expr args))"
    \<rightharpoonup> "_shallow (_urust_array_expr args)"
  "_shallow (_urust_borrow exp)"
    \<rightharpoonup> "CONST bindlift1 (CONST ro_ref_from_ref) (_shallow exp)"
  "_shallow (_urust_borrow_mut exp)"
    \<rightharpoonup> "CONST bindlift1 (CONST mut_ref_from_ref) (_shallow exp)"
  "_shallow (_urust_deref exp)"
    \<rightharpoonup> "_urust_shallow_store_dereference (_shallow exp)"

  "_shallow (_urust_assign lhs exp)"
    \<rightharpoonup> "_urust_shallow_store_update (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"

  "_shallow (_urust_word_assign_or lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_or (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_word_assign_xor lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_xor (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_word_assign_and lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_and (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"

  "_shallow (_urust_assign_add lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_add (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_assign_minus lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_minus (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_assign_mul lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_mul (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_assign_mod lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_mod (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_word_assign_shift_left lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_shift_left (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"
  "_shallow (_urust_word_assign_shift_right lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_shift_right (_shallow (_urust_lhs_as_urust lhs)) (_shallow exp)"

  "_shallow (_urust_closure_no_args exp)"
    \<rightharpoonup> "CONST literal (CONST FunctionBody (_shallow exp))"
  "_shallow (_urust_closure_with_args args exp)"
    \<rightharpoonup> "CONST literal (_shallow_abstract_args args exp)"

  \<comment>\<open>Closure-formal lowering routes the binder through \<^verbatim>\<open>_abs\<close> (and
    hence \<^ML>\<open>Syntax_Trans.abs_tr\<close>) so the source position carried by
    the formal's \<open>id_position\<close> survives into a \<open>_constrainAbs\<close>
    wrapper. The decoder then emits \<open>Markup.bound\<close> at the binder's
    source range, paired with each in-scope use site --- which is what
    makes ctrl-click on a closure-body identifier jump back to the
    \<^verbatim>\<open>|x|\<close> binder.

    The previous form \<open>\<lambda>arg. _\<close> using a translations meta-variable
    discarded the \<open>_constrain\<close> wrapper at substitution time and so
    produced binder-markup-less closures.\<close>
  "_shallow_abstract_args (_urust_formal_single id) exp"
    \<rightharpoonup> "_abs id (CONST FunctionBody (_shallow exp))"
  "_shallow_abstract_args (_urust_formal_app id args) exp"
    \<rightharpoonup> "_abs id (_shallow_abstract_args args exp)"

  "_shallow_apply_params f (_urust_param_app p params)"
    \<rightharpoonup> "_shallow_apply_params (f p) params"
  "_shallow_apply_params f (_urust_param_single p)"
    \<rightharpoonup> "f p"

  (* Explicit translations for specific macro forms. *)
  "_shallow (_urust_macro_no_args (URUST_CONST panic))"
    \<rightharpoonup> "CONST panic (CONST String.implode [])"
  "_shallow (_urust_macro_no_args (URUST_CONST unimplemented))"
    \<rightharpoonup> "CONST unimplemented (CONST String.implode [])"
  "_shallow (_urust_macro_no_args (URUST_CONST todo))"
    \<rightharpoonup> "CONST unimplemented (CONST String.implode [])"
  "_shallow (_urust_macro_no_args (URUST_CONST fatal))"
    \<rightharpoonup> "CONST fatal (CONST String.implode [])"

  "_shallow (_urust_macro_with_args
      (URUST_CONST assert) (_urust_args_single exp))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert) (_urust_args_app exp rest))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert) (_urust_args_single exp))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert) (_urust_args_app exp rest))"
    \<rightharpoonup> "CONST assert (_shallow exp)"

  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_ne) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_ne (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_ne) (_urust_args_app expA (_urust_args_app expB rest)))"
    \<rightharpoonup> "CONST assert_ne (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_eq) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_eq (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_eq) (_urust_args_app expA (_urust_args_app expB rest)))"
    \<rightharpoonup> "CONST assert_eq (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert_ne) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_ne (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert_ne) (_urust_args_app expA (_urust_args_app expB rest)))"
    \<rightharpoonup> "CONST assert_ne (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert_eq) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_eq (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert_eq) (_urust_args_app expA (_urust_args_app expB rest)))"
    \<rightharpoonup> "CONST assert_eq (_shallow expA) (_shallow expB)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_app first rest))"
    \<rightharpoonup> "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single first))"
  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST panic (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST panic (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST panic) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST panic (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_app first rest))"
    \<rightharpoonup> "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single first))"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST unimplemented (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST unimplemented (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST unimplemented (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_app first rest))"
    \<rightharpoonup> "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_single first))"
  "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST unimplemented (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST unimplemented (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST unimplemented (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_app first rest))"
    \<rightharpoonup> "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single first))"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST fatal (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST fatal (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST fatal (_string_token_to_hol str)"

  "_shallow (_urust_macro_no_args (URUST_CONST unreachable))"
    \<rightharpoonup> "CONST panic (CONST String.implode [])"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unreachable) (_urust_args_app first rest))"
    \<rightharpoonup> "_shallow (_urust_macro_with_args
       (URUST_CONST unreachable) (_urust_args_single first))"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unreachable) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST panic (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unreachable) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST panic (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unreachable) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST panic (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args (URUST_CONST vec) args)"
    \<rightharpoonup> "_shallow (_urust_array_expr args)"
  "_shallow (_urust_macro_no_args (URUST_CONST vec))"
    \<rightharpoonup> "_shallow (_urust_array_expr_empty)"

  "_shallow (_urust_macro_with_args (URUST_CONST addr_of) (_urust_args_single exp))"
    \<rightharpoonup> "CONST bindlift1 (CONST ref_address) (_shallow exp)"
  "_shallow (_urust_macro_with_args (URUST_CONST addr_of_mut) (_urust_args_single exp))"
    \<rightharpoonup> "CONST bindlift1 (CONST ref_address) (_shallow exp)"

  "_shallow (_urust_matches_macro expr pat)"
    \<rightharpoonup> "_urust_shallow_match (_shallow expr)
         (_urust_shallow_match2
           (_urust_shallow_match1 (_shallow_match_pattern pat) (CONST literal (CONST True)))
           (_urust_shallow_match1 _urust_shallow_match_pattern_other (CONST literal (CONST False))))"

 "_shallow (_urust_index exp idx)"
    \<rightharpoonup> "_urust_shallow_index (_shallow exp) (_shallow idx)"

  "_shallow (_urust_add x y)"
    \<rightharpoonup> "_urust_shallow_add (_shallow x) (_shallow y)"
  "_shallow (_urust_minus x y)"
    \<rightharpoonup> "_urust_shallow_minus (_shallow x) (_shallow y)"
  "_shallow (_urust_mul x y)"
    \<rightharpoonup> "_urust_shallow_mul (_shallow x) (_shallow y)"
  "_shallow (_urust_div x y)"
    \<rightharpoonup> "_urust_shallow_div (_shallow x) (_shallow y)"
  "_shallow (_urust_mod x y)"
    \<rightharpoonup> "_urust_shallow_mod (_shallow x) (_shallow y)"

  "_shallow (_urust_equality x y)"
    \<rightharpoonup> "_urust_shallow_equality (_shallow x) (_shallow y)"
  "_shallow (_urust_nonequality x y)"
    \<rightharpoonup> "_urust_shallow_nonequality (_shallow x) (_shallow y)"
  "_shallow (_urust_greater_equal x y)"
    \<rightharpoonup> "_urust_shallow_bool_ge (_shallow x) (_shallow y)"
  "_shallow (_urust_greater x y)"
    \<rightharpoonup> "_urust_shallow_bool_gt (_shallow x) (_shallow y)"
  "_shallow (_urust_less_equal x y)"
    \<rightharpoonup> "_urust_shallow_bool_le (_shallow x) (_shallow y)"
  "_shallow (_urust_less x y)"
    \<rightharpoonup> "_urust_shallow_bool_lt (_shallow x) (_shallow y)"

  "_shallow (_urust_bitwise_or x y)"
    \<rightharpoonup> "_urust_shallow_word_bitwise_or (_shallow x) (_shallow y)"
  "_shallow (_urust_bitwise_and x y)"
    \<rightharpoonup> "_urust_shallow_word_bitwise_and (_shallow x) (_shallow y)"
  "_shallow (_urust_bitwise_xor x y)"
    \<rightharpoonup> "_urust_shallow_word_bitwise_xor (_shallow x) (_shallow y)"
  "_shallow (_urust_shift_left x y)"
    \<rightharpoonup> "_urust_shallow_word_shift_left (_shallow x) (_shallow y)"
  "_shallow (_urust_shift_right x y)"
    \<rightharpoonup> "_urust_shallow_word_shift_right (_shallow x) (_shallow y)"

  "_shallow (_urust_negation exp)"
    \<rightharpoonup> "_urust_shallow_negation (_shallow exp)"
  "_shallow (_urust_bool_conjunction x y)"
    \<rightharpoonup> "_urust_shallow_bool_conjunction (_shallow x) (_shallow y)"
  "_shallow (_urust_bool_disjunction x y)"
    \<rightharpoonup> "_urust_shallow_bool_disjunction (_shallow x) (_shallow y)"

  "_shallow( _urust_range x y)"
    \<rightharpoonup> "_urust_shallow_range (_shallow x) (_shallow y)"
  "_shallow( _urust_range_eq x y)"
    \<rightharpoonup> "_urust_shallow_range_eq (_shallow x) (_shallow y)"

  "_shallow (_urust_let_else (_urust_let_pattern_tuple args) exp el tail)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp)
                       (_abs (_shallow_let_pattern (_urust_let_pattern_tuple args)) (_shallow tail))"
  "_shallow (_urust_if_let (_urust_let_pattern_tuple args) exp this)"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp)
                       (_abs (_shallow_let_pattern (_urust_let_pattern_tuple args)) (_shallow this))"
  "_shallow (_urust_if_let_else (_urust_let_pattern_tuple args) exp this that )"
    \<rightharpoonup> "CONST Core_Expression.bind (_shallow exp)
                       (_abs (_shallow_let_pattern (_urust_let_pattern_tuple args)) (_shallow this))"
  "_shallow (_urust_let_else ptrn exp el tail)"
    \<rightharpoonup> "_urust_shallow_let_else (_shallow_match_pattern ptrn) (_shallow exp) (_shallow el) (_shallow tail)"
  "_shallow (_urust_if_let ptrn exp this)"
    \<rightharpoonup> "_urust_shallow_if_let (_shallow_match_pattern ptrn) (_shallow exp) (_shallow this)"
  "_shallow (_urust_if_let_else ptrn exp this that )"
    \<rightharpoonup> "_urust_shallow_if_let_else (_shallow_match_pattern ptrn) (_shallow exp) (_shallow this) (_shallow that)"

  "_shallow (_urust_match_case exp branches)"
    \<rightharpoonup> "_urust_shallow_match (_shallow exp) (_shallow_match_branches branches)"

  "_shallow_match_branches (_urust_match1 pattern exp)"
    \<rightharpoonup> "_urust_shallow_match1 (_shallow_match_pattern pattern) (_shallow exp)"
  "_shallow_match_branches (_urust_match1_guard pattern guard exp)"
    \<rightharpoonup> "_urust_shallow_match1_guard (_shallow_match_pattern pattern) (_shallow guard) (_shallow exp)"
  "_shallow_match_branches (_urust_match2 b0 b1)"
    \<rightharpoonup> "_urust_shallow_match2 (_shallow_match_branches b0) (_shallow_match_branches b1)"

  "_shallow_match_pattern _urust_match_pattern_other"
    \<rightharpoonup> "_urust_shallow_match_pattern_other"
  "_shallow_match_pattern (_urust_match_pattern_num_const num)"
    \<rightharpoonup> "_urust_shallow_match_pattern_num_const num"
  "_shallow_match_pattern (_urust_match_pattern_zero)"
    \<rightharpoonup> "_urust_shallow_match_pattern_zero"
  "_shallow_match_pattern (_urust_match_pattern_one)"
    \<rightharpoonup> "_urust_shallow_match_pattern_one"
  \<comment>\<open>Match-arm constructor heads continue to route through the
    value-position \<^verbatim>\<open>_shallow_identifier_as_literal\<close>: \<open>case_tr\<close>
    downstream tolerates a \<^verbatim>\<open>urust_dispatch\<close> marker as the head and
    the term_check phase resolves it after type inference (which is
    necessary for value-position match arms like \<open>match x { number::three => \<dots> }\<close>
    where the registration target is a non-constructor constant).\<close>
  "_shallow_match_pattern (_urust_match_pattern_constr_no_args id)"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_no_args (_shallow_identifier_as_literal id)"
  "_shallow_match_pattern (_urust_match_pattern_constr_with_args id args)"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_with_args (_shallow_identifier_as_literal id) (_shallow_match_args args)"
  "_shallow_match_pattern (_urust_match_pattern_disjunction p1 p2)"
    \<rightharpoonup> "_urust_shallow_match_pattern_disjunction (_shallow_match_pattern p1) (_shallow_match_pattern p2)"
  "_shallow_match_pattern (_urust_match_pattern_grouped pat)"
    \<rightharpoonup> "_shallow_match_pattern pat"
  "_shallow_match_pattern (_urust_let_pattern_tuple (_urust_let_pattern_tuple_base_pair a b))"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_with_args (CONST Pair)
      (_urust_shallow_match_pattern_args_app (_shallow_match_arg a)
        (_urust_shallow_match_pattern_args_single
          (_urust_shallow_match_pattern_arg_pattern
            (_urust_shallow_match_pattern_constr_with_args (CONST Pair)
              (_urust_shallow_match_pattern_args_app (_shallow_match_arg b)
                (_urust_shallow_match_pattern_args_single
                  (_urust_shallow_match_pattern_arg_pattern
                    (_urust_shallow_match_pattern_constr_no_args (CONST TNil)))))))))"

  "_shallow_match_args (_urust_match_pattern_args_single arg)"
    \<rightharpoonup> "_urust_shallow_match_pattern_args_single (_shallow_match_arg arg)"
  "_shallow_match_args (_urust_match_pattern_args_app a bs)"
    \<rightharpoonup> "_urust_shallow_match_pattern_args_app (_shallow_match_arg a) (_shallow_match_args bs)"


  "_shallow (_urust_match_switch exp branches)"
    \<rightharpoonup> "_urust_shallow_switch (_shallow exp) (_shallow_match_branches branches)"

  "_shallow (_urust_for_loop x iter body)"
    \<rightharpoonup> "_urust_shallow_for_loop (_shallow_let_pattern x) (_shallow iter) (_shallow body)"

  "_shallow (_urust_while_loop (_urust_antiquotation fuel) cond body)"
    \<rightharpoonup> "_urust_shallow_while_loop fuel (_shallow cond) (_shallow body)"
  "_shallow (_urust_loop (_urust_antiquotation fuel) body)"
    \<rightharpoonup> "_urust_shallow_loop fuel (_shallow body)"

  \<comment>\<open>While let — tuple pattern special case (irrefutable)\<close>
  "_shallow (_urust_while_let (_urust_antiquotation fuel) (_urust_let_pattern_tuple args) expr body)"
    \<rightharpoonup> "CONST bounded_while fuel
          (CONST Core_Expression.bind (_shallow expr)
            (_abs (_shallow_let_pattern (_urust_let_pattern_tuple args))
              (CONST Core_Expression.sequence (_shallow body) (CONST Core_Expression.literal (CONST HOL.True)))))
          (CONST skip)"

  \<comment>\<open>While let — general pattern case\<close>
  "_shallow (_urust_while_let (_urust_antiquotation fuel) ptrn expr body)"
    \<rightharpoonup> "_urust_shallow_while_let fuel (_shallow_match_pattern ptrn) (_shallow expr) (_shallow body)"

micro_rust_notation \<open>lift_fun1 Some\<close> ("Some")
micro_rust_notation \<open>lift_fun1 Ok\<close>   ("Ok")
micro_rust_notation \<open>lift_fun1 Err\<close>  ("Err")

text\<open>By default, we map all identifiers to HOL through the identity function on their names.
We register this as a parse translation rather than a rule so that names registered via
\<^theory_text>\<open>micro_rust_notation\<close> (which the translation looks up in
\<^ML_structure>\<open>Micro_Rust_Names\<close>) take precedence.\<close>

\<comment>\<open>NB: We could save some manual invocations of \<^theory_text>\<open>micro_rust_notation\<close> if we changed the
default renaming convention here, and e.g. prepend all field names with \<^verbatim>\<open>field_lens_\<close>,
for example.\<close>
parse_translation\<open>
let
  \<comment>\<open>Lower a uRust identifier in \<open>kind\<close>-position to HOL: if \<open>name\<close> has any
    backends registered in \<^ML_structure>\<open>Micro_Rust_Names\<close>, emit a typed
    \<^const>\<open>urust_dispatch\<close> marker that the term_check phase resolves
    against the occurrence's inferred type. Otherwise fall back to the
    bare identifier (the historical \<open>K hd\<close> behaviour: a fresh free
    variable named \<open>name\<close> --- which is what unregistered uRust
    identifiers should still produce).

    The arg arrives as a position-tagged identifier
    \<open>_constrain $ Free name $ Free <pos>\<close> after the \<open>id_position\<close>
    grammar; strip positions only for the lookup, not for the fallback
    return value (so unregistered names retain their source markup).\<close>
  \<comment>\<open>Extract the source position(s) of a position-tagged identifier
    \<open>_constrain $ Free name $ Free <encoded-pos>\<close>. Returns \<open>[]\<close> for
    untagged identifiers; the use-site markup is then emitted at
    \<open>Position.none\<close> and silently dropped.\<close>
  fun source_positions_of (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ _ $ enc) =
        (case Term_Position.decode_position1 enc of
          SOME {pos, ...} => [pos]
        | NONE => [])
    | source_positions_of _ = [];

  \<comment>\<open>Pick the leftmost decoded source position (if any) to fold into
    the marker; \<open>Position.none\<close> when nothing is attached.\<close>
  fun pick_pos source_positions =
    (case source_positions of p :: _ => p | [] => Position.none);

  \<comment>\<open>Lower a uRust identifier in \<open>kind\<close>-position to HOL. After AST
     flattening of paths into \<^verbatim>\<open>_urust_identifier_id\<close>, plain identifiers
     and path identifiers (\<open>foo::bar\<close>) arrive uniformly as
     \<^verbatim>\<open>Free name\<close> (possibly \<open>_constrain\<close>-wrapped with a source position).
     For paths the name simply contains \<open>::\<close> separators; downstream
     consumers only look at the name string, so no shape match is needed.

     We ALWAYS emit a \<^verbatim>\<open>urust_dispatch\<close> marker carrying the original
     \<open>arg\<close> as a witness. HOL elaboration resolves the witness through
     normal binding, and the term_check phase uses witness precedence:
     a \<^verbatim>\<open>Bound\<close> witness (a \<lambda>-binder of the same name) wins over any
     table registration; a \<^verbatim>\<open>Free\<close> or \<^verbatim>\<open>Const\<close> witness defers to the
     table, falling back to itself on miss. This is what stops a
     registered \<open>("mask")\<close> from hijacking a \<open>\<lambda>mask. \<dots> mask \<dots>\<close> use site.

     Path identifiers (\<open>Foo::Bar\<close>) cannot be HOL binders, so the witness
     elaborates to a \<^verbatim>\<open>Free\<close> with a \<open>::\<close>-containing name; the table
     lookup proceeds exactly as for plain ids.\<close>
  fun lookup_id_tr kind ctxt [arg] =
        (case Term_Position.strip_positions arg of
          Free (name, _) =>
            \<comment>\<open>Only emit a marker when the table actually has a registration
              for this \<open>(kind, name)\<close>. If there is none, return the bare
              \<open>arg\<close> --- otherwise we'd disrupt downstream constructions
              like \<open>_abs\<close> binders that expect the binder slot to be a
              recognisable \<open>Free\<close>/\<open>_constrain\<close>-wrapped shape, not a
              \<open>urust_dispatch\<close> application.\<close>
            (case Micro_Rust_Names.lookups ctxt kind name of
               [] => arg
             | _ =>
                 \<comment>\<open>Markup emission is deferred to \<open>Micro_Rust_Dispatch.resolve\<close>:
                   we emit the use-site markup ONLY when a marker is
                   actually replaced by a registered backend, never
                   when the witness ends up winning (\<lambda>-binder shadow).\<close>
                 Micro_Rust_Dispatch.mk_marker kind name
                   (pick_pos (source_positions_of arg)) arg)
        | _ => arg)
    | lookup_id_tr _ _ ts = hd ts;
in
  [(\<^syntax_const>\<open>_urust_identifier_id\<close>, K hd),
   (\<^syntax_const>\<open>_shallow_identifier_as_literal\<close>,
      lookup_id_tr Micro_Rust_Names.NLiteral),
   (\<^syntax_const>\<open>_shallow_identifier_as_function\<close>,
      lookup_id_tr Micro_Rust_Names.NFunction),
   (\<^syntax_const>\<open>_shallow_identifier_as_field\<close>,
      lookup_id_tr Micro_Rust_Names.NField)]
end
\<close>

\<comment>\<open>Binder-introduction resolver: a let-pattern leaf or other binder slot.
  Pure identity --- the identifier IS the binder, so the dispatch table
  is never consulted. A registered uRust notation of the same name is
  silently shadowed by the let, mirroring Rust's lexical scoping. Runs
  at parse-translation time so \<^ML>\<open>Syntax_Trans.abs_tr\<close> sees the bare
  \<^verbatim>\<open>Free\<close>/\<open>_constrain\<close> shape it expects.

  Match-arm constructor heads do NOT use this resolver --- they keep
  routing through the value-position \<open>_shallow_identifier_as_literal\<close>
  so the term_check phase can resolve registered names AFTER type
  inference (necessary for value-position match arms like
  \<open>match x { number::three => \<dots> }\<close> where the registration target is a
  non-constructor constant).\<close>
parse_translation\<open>
  [(\<^syntax_const>\<open>_shallow_pattern_id\<close>, fn _ => hd)]
\<close>

ML\<open>
  fun known_constructor_name ctxt name =
    let
      val full = Proof_Context.intern_const ctxt name
      val thy = Proof_Context.theory_of ctxt
    in
      if can (Sign.the_const_type thy) full andalso Code.is_constr thy full
      then SOME full
      else NONE
    end;

  \<comment>\<open>Resolve a constructor identifier \<open>id\<close> to its fully-qualified
    \<^verbatim>\<open>Const\<close>. We must preserve the original \<^verbatim>\<open>_constrain $ _ $ <pos\<close>
    wrapper so the decoder's namespace markup ends up at the user's
    source token --- otherwise pattern heads like \<open>Some\<close> in
    \<open>match x { Some(y) => \<dots> }\<close> or \<open>if let Some(y) = \<dots>\<close> have no
    clickable entity ref attached.\<close>
  fun preserve_position id new_inner =
    (case id of
      Const (\<^syntax_const>\<open>_constrain\<close>, T) $ _ $ pos_enc =>
        Const (\<^syntax_const>\<open>_constrain\<close>, T) $ new_inner $ pos_enc
    | _ => new_inner);

  fun resolve_constructor_id ctxt id =
    (case Term_Position.strip_positions id of
      t as Const _ => SOME (preserve_position id t)
    | Free (name, _) =>
        Option.map (fn n => preserve_position id (Syntax.const n))
                   (known_constructor_name ctxt name)
    | _ => NONE);

  fun dest_ident_name ctxt t =
    (case Term_Position.strip_positions t of
      Free (name, _) => name
    | Const (name, _) => name
    | _ => error ("invalid identifier term: " ^ Syntax.string_of_term ctxt t));

  fun canonical_name s = Long_Name.base_name s;

  fun name_matches a b = a = b orelse canonical_name a = canonical_name b;

  fun term_name_of (Const (name, _)) = SOME name
    | term_name_of (Free (name, _)) = SOME name
    | term_name_of _ = NONE;

  fun type_name_of (Type (name, _)) = SOME name
    | type_name_of _ = NONE;

  fun resolve_struct_constructor ctxt id =
    let
      val id_name = dest_ident_name ctxt id
      val id_name' = canonical_name id_name
      val thy = Proof_Context.theory_of ctxt
      val sugars = Ctr_Sugar.ctr_sugars_of ctxt

      fun from_sugar ({T, ctrs, selss, ...} : Ctr_Sugar.ctr_sugar) =
        let
          val ty_name_opt = Option.map canonical_name (type_name_of T)
          val entries =
            map_index (fn (i, ctr) =>
              (ctr, (nth selss i handle Subscript => []))) ctrs
          val direct =
            map_filter (fn (ctr, sels) =>
              (case term_name_of ctr of
                SOME ctor_name =>
                  if name_matches ctor_name id_name' then SOME (canonical_name ctor_name, ctr, sels)
                  else NONE
              | NONE => NONE)) entries
          val fallback =
            (case (ty_name_opt, entries) of
              (SOME ty_name, [(ctr, sels)]) =>
                if ty_name = id_name' then
                  (case term_name_of ctr of
                    SOME ctor_name => [(canonical_name ctor_name, ctr, sels)]
                  | NONE => [])
                else []
            | _ => [])
        in
          direct @ fallback
        end

      val raw_candidates = maps from_sugar sugars

      fun record_candidate rec_name =
        let
          val resolved_name_opt =
            (type_name_of (Proof_Context.read_type_name {proper = true, strict = false} ctxt rec_name)
              handle ERROR _ => NONE)
          val info_opt =
            (case resolved_name_opt of
              SOME resolved_name => Record.get_info thy resolved_name
            | NONE => Record.get_info thy rec_name)
          val key_name = the_default rec_name resolved_name_opt
        in
          (case info_opt of
            NONE => NONE
          | SOME info =>
              let
                val (ext_name, _) = #extension info
                val field_names = map fst (#fields info) @ ["more"]
                val ctor = Const (ext_name, dummyT)
                val sels = map (fn f => Const (f, dummyT)) field_names
              in
                SOME (canonical_name key_name, ctor, sels)
              end)
        end

      val record_raw_candidates =
        map_filter record_candidate (distinct (op =) [id_name, id_name'])

      fun insert_unique (key, value) acc =
        if AList.defined (op =) acc key then acc else AList.update (op =) (key, value) acc
      val unique_candidates =
        fold (fn (key, ctr, sels) => insert_unique (key, (ctr, sels)))
          (raw_candidates @ record_raw_candidates) []

      val ctor_msg =
        if null unique_candidates then
          "unknown constructor/type"
        else
          unique_candidates
          |> map fst
          |> rev
          |> space_implode ", "
    in
      (case unique_candidates of
        [] =>
          error ("struct pattern " ^ quote id_name ^ ": no matching constructor or single-constructor record/datatype found")
      | [(_, res)] => res
      | _ =>
          error ("struct pattern " ^ quote id_name ^ " is ambiguous; candidates: " ^ ctor_msg))
    end;

  fun struct_pattern_tr ctxt ts =
    let
      val mk = Syntax.const
      fun mk_args [p] = mk \<^syntax_const>\<open>_urust_match_pattern_args_single\<close> $ p
        | mk_args (p :: ps) = mk \<^syntax_const>\<open>_urust_match_pattern_args_app\<close> $ p $ mk_args ps
        | mk_args [] = error "struct pattern: empty field list"
      fun mk_pattern_shorthand fld =
        mk \<^syntax_const>\<open>_urust_match_pattern_constr_no_args\<close> $ fld

      fun struct_field_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_field\<close>, _) $ fld $ p) =
              (SOME (canonical_name (dest_ident_name ctxt fld), p), false)
        | struct_field_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_field_short\<close>, _) $ fld) =
              (SOME (canonical_name (dest_ident_name ctxt fld), mk_pattern_shorthand fld), false)
        | struct_field_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_rest\<close>, _)) =
              (NONE, true)
        | struct_field_destruct t =
            error ("struct pattern: invalid field syntax: " ^ Syntax.string_of_term ctxt t)

      fun struct_fields_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_fields_single\<close>, _) $ fld) =
              (case struct_field_destruct fld of
                (SOME e, has_rest) => ([e], has_rest)
              | (NONE, has_rest) => ([], has_rest))
        | struct_fields_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_fields_app\<close>, _) $ fld $ rest) =
              let
                val (entry_opt, has_rest0) = struct_field_destruct fld
                val (rest_entries, has_rest1) = struct_fields_destruct rest
                val _ =
                  if has_rest0 andalso has_rest1 then
                    error "struct pattern: multiple `..` rest entries"
                  else
                    ()
                val entries =
                  (case entry_opt of
                    SOME e => e :: rest_entries
                  | NONE => rest_entries)
              in
                (entries, has_rest0 orelse has_rest1)
              end
        | struct_fields_destruct t =
            error ("struct pattern: invalid field list syntax: " ^ Syntax.string_of_term ctxt t)

      fun tr [id, fields] =
        let
          val (ctor, sels) = resolve_struct_constructor ctxt id
          val ctor_name =
            (case term_name_of ctor of
              SOME n => canonical_name n
            | NONE => dest_ident_name ctxt id)
          val selector_names = map (canonical_name o dest_ident_name ctxt) sels
          val (field_entries, is_open) = struct_fields_destruct fields
          val field_names = map fst field_entries
          fun is_optional_selector s = (s = "more")
          val duplicate_fields = Library.duplicates (op =) field_names
          val _ =
            if null duplicate_fields then ()
            else error ("struct pattern for " ^ quote ctor_name ^ " has duplicate field(s): " ^
              space_implode ", " duplicate_fields)
          val extra_fields =
            filter (fn f => not (member (op =) selector_names f)) field_names
          val missing_fields =
            if is_open then
              []
            else
              filter (fn s =>
                not (member (op =) field_names s) andalso not (is_optional_selector s)) selector_names
          val _ =
            if null extra_fields then ()
            else error ("struct pattern for " ^ quote ctor_name ^ " has unknown field(s): " ^
              space_implode ", " extra_fields)
          val _ =
            if null missing_fields then ()
            else error ("struct pattern for " ^ quote ctor_name ^ " is missing field(s): " ^
              space_implode ", " missing_fields)
          val ordered_pats =
            map (fn s =>
              (case AList.lookup (op =) field_entries s of
                SOME p => p
              | NONE =>
                  if is_optional_selector s orelse is_open then
                    Syntax.const \<^syntax_const>\<open>_urust_match_pattern_other\<close>
                  else error ("internal error: struct field lookup failed for " ^ quote s))) selector_names
        in
          mk \<^syntax_const>\<open>_urust_match_pattern_constr_with_args\<close> $ ctor $ mk_args ordered_pats
        end
        | tr args = Term.list_comb (mk \<^syntax_const>\<open>_urust_match_pattern_struct\<close>, args)
    in
      tr ts
    end;

  fun struct_expr_tr ctxt ts =
    let
      val mk = Syntax.const
      fun mk_antiquotation t = mk \<^syntax_const>\<open>_urust_antiquotation\<close> $ t
      fun mk_callable_lifted ctor arity =
        if arity >= 0 andalso arity <= 14 then
          mk_antiquotation (mk ("lift_fun" ^ Int.toString arity) $ ctor)
        else
          error ("struct expression: constructor arity " ^ Int.toString arity ^
            " is unsupported (max 14)")
      fun mk_args [e] = mk \<^syntax_const>\<open>_urust_args_single\<close> $ e
        | mk_args (e :: es) = mk \<^syntax_const>\<open>_urust_args_app\<close> $ e $ mk_args es
        | mk_args [] = error "struct expression: empty field list"

      fun struct_field_destruct
            (Const (\<^syntax_const>\<open>_urust_struct_expr_field\<close>, _) $ fld $ e) =
              (canonical_name (dest_ident_name ctxt fld), e)
        | struct_field_destruct t =
            error ("struct expression: invalid field syntax: " ^ Syntax.string_of_term ctxt t)

      fun struct_fields_destruct
            (Const (\<^syntax_const>\<open>_urust_struct_expr_fields_single\<close>, _) $ fld) =
              [struct_field_destruct fld]
        | struct_fields_destruct
            (Const (\<^syntax_const>\<open>_urust_struct_expr_fields_app\<close>, _) $ fld $ rest) =
              struct_field_destruct fld :: struct_fields_destruct rest
        | struct_fields_destruct t =
            error ("struct expression: invalid field list syntax: " ^ Syntax.string_of_term ctxt t)

      fun tr [id, fields] =
        let
          val (ctor, sels) = resolve_struct_constructor ctxt id
          val ctor_name =
            (case term_name_of ctor of
              SOME n => canonical_name n
            | NONE => dest_ident_name ctxt id)
          val selector_names = map (canonical_name o dest_ident_name ctxt) sels
          val field_entries = struct_fields_destruct fields
          val field_names = map fst field_entries
          fun is_optional_selector s = (s = "more")
          val duplicate_fields = Library.duplicates (op =) field_names
          val _ =
            if null duplicate_fields then ()
            else error ("struct expression for " ^ quote ctor_name ^ " has duplicate field(s): " ^
              space_implode ", " duplicate_fields)
          val extra_fields =
            filter (fn f => not (member (op =) selector_names f)) field_names
          val missing_fields =
            filter (fn s =>
              not (member (op =) field_names s) andalso not (is_optional_selector s)) selector_names
          val _ =
            if null extra_fields then ()
            else error ("struct expression for " ^ quote ctor_name ^ " has unknown field(s): " ^
              space_implode ", " extra_fields)
          val _ =
            if null missing_fields then ()
            else error ("struct expression for " ^ quote ctor_name ^ " is missing field(s): " ^
              space_implode ", " missing_fields)
          val ordered_exprs =
            map (fn s =>
              (case AList.lookup (op =) field_entries s of
                SOME e => e
              | NONE =>
                  if is_optional_selector s then
                    mk_antiquotation (Syntax.const \<^const_syntax>\<open>undefined\<close>)
                  else error ("internal error: struct field lookup failed for " ^ quote s))) selector_names
          val callable = mk_callable_lifted ctor (length ordered_exprs)
        in
          if null ordered_exprs then
            mk \<^syntax_const>\<open>_urust_funcall_no_args\<close> $ callable
          else
            mk \<^syntax_const>\<open>_urust_funcall_with_args\<close> $ callable $ mk_args ordered_exprs
        end
        | tr args = Term.list_comb (mk \<^syntax_const>\<open>_urust_struct_expr\<close>, args)
    in
      tr ts
    end;

  fun shallow_match_arg_tr ctxt ts =
    let
      val pat =
        (case ts of
          [] => error "_shallow_match_arg: missing pattern argument"
        | p :: _ => p)
      val mk = Syntax.const
      val mk_arg_id = fn id => mk \<^syntax_const>\<open>_urust_shallow_match_pattern_arg_id\<close> $ id
      val mk_arg_dummy = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_arg_dummy\<close>
      val mk_arg_pat = fn p => mk \<^syntax_const>\<open>_urust_shallow_match_pattern_arg_pattern\<close> $ p
      val mk_pair = mk \<^const_syntax>\<open>Pair\<close>
      val mk_tnil = mk \<^const_syntax>\<open>TNil\<close>
      val mk_nil = mk \<^const_syntax>\<open>Nil\<close>
      val mk_cons = mk \<^const_syntax>\<open>Cons\<close>
      val mk_shallow = fn t => mk \<^syntax_const>\<open>_shallow\<close> $ t
      val mk_pat_literal = fn e => mk \<^syntax_const>\<open>_urust_shallow_match_pattern_literal\<close> $ e
      val mk_literal_expr = fn v => mk \<^const_syntax>\<open>literal\<close> $ v
      fun mk_bit_syntax b = mk (if b = 1 then \<^const_syntax>\<open>True\<close> else \<^const_syntax>\<open>False\<close>)
      fun mk_bits_syntax len = map mk_bit_syntax o Integer.radicify 2 len
      fun plain_strings_of str = map fst (Lexicon.explode_string (str, Position.none))
      fun ascii_ord_of c =
        if Symbol.is_ascii c then ord c
        else if c = "\<newline>" then 10
        else error ("Bad character in string token: " ^ quote c)
      fun mk_char_syntax i = Term.list_comb (mk \<^const_syntax>\<open>Char\<close>, mk_bits_syntax 8 i)
      fun mk_string_syntax [] = mk \<^const_syntax>\<open>Nil\<close>
        | mk_string_syntax (c :: cs) =
            mk \<^const_syntax>\<open>Cons\<close> $ mk_char_syntax (ascii_ord_of c) $ mk_string_syntax cs
      fun string_token_to_hol t =
        (case t of
          Free (str, _) => (mk \<^const_syntax>\<open>String.implode\<close>) $ mk_string_syntax (plain_strings_of str)
        | _ => error ("_shallow_match_arg: expected string token, got: " ^ Syntax.string_of_term ctxt t))

      fun parse_num_token tok =
        (case try (Lexicon.read_num #> #value) tok of
          SOME n => n
        | NONE =>
            (case try (Lexicon.read_num #> #value) (Long_Name.base_name tok) of
              SOME n => n
            | NONE => error ("_shallow_match_arg: bad numeral token: " ^ quote tok)))

      fun num_const_to_hol t =
        (case try Numeral.dest_num_syntax t of
          SOME n => Numeral.mk_number_syntax n
        | NONE =>
            (case t of
              Const (\<^syntax_const>\<open>_constrain\<close>, _) $ u $ _ => num_const_to_hol u
            | Free (num, _) => Numeral.mk_number_syntax (parse_num_token num)
            | Const (num, _) => Numeral.mk_number_syntax (parse_num_token num)
            | _ => error ("_shallow_match_arg: expected numeral token, got: " ^ Syntax.string_of_term ctxt t)))

      fun shallow_expr_of t =
        (case t of
          Const (\<^syntax_const>\<open>_urust_literal\<close>, _) $ v =>
            mk_literal_expr v
        | Const (\<^syntax_const>\<open>_urust_string_token\<close>, _) $ s =>
            mk_literal_expr (string_token_to_hol s)
        | Const (\<^syntax_const>\<open>_urust_match_pattern_true\<close>, _) =>
            mk_literal_expr (mk \<^const_syntax>\<open>True\<close>)
        | Const (\<^syntax_const>\<open>_urust_match_pattern_false\<close>, _) =>
            mk_literal_expr (mk \<^const_syntax>\<open>False\<close>)
        | Const (\<^syntax_const>\<open>_urust_match_pattern_string\<close>, _) $ s =>
            mk_literal_expr (string_token_to_hol s)
        | Const (\<^syntax_const>\<open>_urust_match_pattern_literal\<close>, _) $ v =>
            mk_literal_expr v
        | Const (\<^syntax_const>\<open>_urust_match_pattern_num_const\<close>, _) $ n =>
            mk_literal_expr (num_const_to_hol n)
        | _ => mk_shallow t)

      fun tuple_args_destruct (Const (\<^syntax_const>\<open>_urust_let_pattern_tuple_base_pair\<close>, _) $ a $ b) = [a, b]
        | tuple_args_destruct (Const (\<^syntax_const>\<open>_urust_let_pattern_tuple_app\<close>, _) $ a $ rest) =
            a :: tuple_args_destruct rest
        | tuple_args_destruct t =
            error ("_shallow_match_arg: invalid tuple args: " ^ Syntax.string_of_term ctxt t)

      fun slice_args_destruct (Const (\<^syntax_const>\<open>_urust_match_pattern_slice_args_empty\<close>, _)) = []
        | slice_args_destruct (Const (\<^syntax_const>\<open>_urust_match_pattern_slice_args_single\<close>, _) $ a) = [a]
        | slice_args_destruct (Const (\<^syntax_const>\<open>_urust_match_pattern_slice_args_app\<close>, _) $ a $ rest) =
            a :: slice_args_destruct rest
        | slice_args_destruct t =
            error ("_shallow_match_arg: invalid slice args: " ^ Syntax.string_of_term ctxt t)

      fun is_slice_rest (Const (\<^syntax_const>\<open>_urust_match_pattern_slice_rest\<close>, _)) = true
        | is_slice_rest _ = false

      fun split_slice_rest elems =
        let
          fun go pref [] = (rev pref, NONE, [])
            | go pref (x :: xs) =
                if is_slice_rest x then (rev pref, SOME (), xs)
                else go (x :: pref) xs
        in
          go [] elems
        end

      fun mk_args_single a = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_args_single\<close> $ a
      fun mk_args_app a b = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_args_app\<close> $ a $ b
      fun mk_pat_no_args c = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_constr_no_args\<close> $ c
      fun mk_pat_with_args c args = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_constr_with_args\<close> $ c $ args
      fun mk_pat_slice_suffix p = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_slice_suffix\<close> $ p

      fun mk_pair_pat arg1 pat2 =
            mk_pat_with_args mk_pair
              (mk_args_app arg1 (mk_args_single (mk_arg_pat pat2)))

      fun tuple_pattern_of _ [] = mk_pat_no_args mk_tnil
        | tuple_pattern_of conv (p :: ps) =
            mk_pair_pat (conv p) (tuple_pattern_of conv ps)

      fun struct_field_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_field\<close>, _) $ fld $ p) =
              (canonical_name (dest_ident_name ctxt fld), p)
        | struct_field_destruct t =
            error ("_shallow_match_arg: invalid struct field: " ^ Syntax.string_of_term ctxt t)

      fun struct_fields_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_fields_single\<close>, _) $ fld) =
              [struct_field_destruct fld]
        | struct_fields_destruct
            (Const (\<^syntax_const>\<open>_urust_match_pattern_struct_fields_app\<close>, _) $ fld $ rest) =
              struct_field_destruct fld :: struct_fields_destruct rest
        | struct_fields_destruct t =
            error ("_shallow_match_arg: invalid struct fields: " ^ Syntax.string_of_term ctxt t)

      fun pats_to_args _ [] = error "_shallow_match_arg: empty struct pattern"
        | pats_to_args conv [p] = mk_args_single (conv p)
        | pats_to_args conv (p :: ps) = mk_args_app (conv p) (pats_to_args conv ps)

      and shallow_match_pattern_of pat =
            (case pat of
              Const (\<^syntax_const>\<open>_urust_match_pattern_other\<close>, _) =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_other\<close>
            | Const (\<^syntax_const>\<open>_urust_match_pattern_num_const\<close>, _) $ num =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_num_const\<close> $ num
            | Const (\<^syntax_const>\<open>_urust_match_pattern_zero\<close>, _) =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_zero\<close>
            | Const (\<^syntax_const>\<open>_urust_match_pattern_one\<close>, _) =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_one\<close>
            | Const (\<^syntax_const>\<open>_urust_match_pattern_true\<close>, _) =>
                mk_pat_literal (mk_literal_expr (mk \<^const_syntax>\<open>True\<close>))
            | Const (\<^syntax_const>\<open>_urust_match_pattern_false\<close>, _) =>
                mk_pat_literal (mk_literal_expr (mk \<^const_syntax>\<open>False\<close>))
            | Const (\<^syntax_const>\<open>_urust_match_pattern_string\<close>, _) $ s =>
                mk_pat_literal (mk_literal_expr (string_token_to_hol s))
            | Const (\<^syntax_const>\<open>_urust_match_pattern_literal\<close>, _) $ lit =>
                mk_pat_literal (mk_literal_expr lit)
            | Const (\<^syntax_const>\<open>_urust_match_pattern_constr_no_args\<close>, _) $ id =>
                let
                  val id' = the_default id (resolve_constructor_id ctxt id)
                in
                  mk \<^syntax_const>\<open>_urust_shallow_match_pattern_constr_no_args\<close> $ id'
                end
            | Const (\<^syntax_const>\<open>_urust_match_pattern_constr_with_args\<close>, _) $ id $ args =>
                let
                  val id' = the_default id (resolve_constructor_id ctxt id)
                in
                  mk_pat_with_args id' (shallow_match_args_of args)
                end
            | Const (\<^syntax_const>\<open>_urust_match_pattern_as\<close>, _) $ id $ p =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_as\<close> $ id $ shallow_match_pattern_of p
            | Const (\<^syntax_const>\<open>_urust_match_pattern_borrow\<close>, _) $ p =>
                shallow_match_pattern_of p
            | Const (\<^syntax_const>\<open>_urust_match_pattern_borrow_mut\<close>, _) $ p =>
                shallow_match_pattern_of p
            | Const (\<^syntax_const>\<open>_urust_match_pattern_range\<close>, _) $ lo $ hi =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_range\<close> $ shallow_expr_of lo $ shallow_expr_of hi
            | Const (\<^syntax_const>\<open>_urust_match_pattern_range_eq\<close>, _) $ lo $ hi =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_range_eq\<close> $ shallow_expr_of lo $ shallow_expr_of hi
            | Const (\<^syntax_const>\<open>_urust_match_pattern_slice_empty\<close>, _) =>
                mk_pat_no_args mk_nil
            | Const (\<^syntax_const>\<open>_urust_match_pattern_slice\<close>, _) $ args =>
                shallow_slice_pattern_of args
            | Const (\<^syntax_const>\<open>_urust_match_pattern_struct\<close>, _) $ id $ fields =>
                let
                  val (ctor, sels) = resolve_struct_constructor ctxt id
                  val ctor_name =
                    (case term_name_of ctor of
                      SOME n => canonical_name n
                    | NONE => dest_ident_name ctxt id)
                  val selector_names = map (canonical_name o dest_ident_name ctxt) sels
                  val field_entries = struct_fields_destruct fields
                  val field_names = map fst field_entries
                  fun is_optional_selector s = (s = "more")
                  val duplicate_fields = Library.duplicates (op =) field_names
                  val _ =
                    if null duplicate_fields then ()
                    else error ("struct pattern for " ^ quote ctor_name ^ " has duplicate field(s): " ^
                      space_implode ", " duplicate_fields)
                  val extra_fields =
                    filter (fn f => not (member (op =) selector_names f)) field_names
                  val missing_fields =
                    filter (fn s =>
                      not (member (op =) field_names s) andalso not (is_optional_selector s)) selector_names
                  val _ =
                    if null extra_fields then ()
                    else error ("struct pattern for " ^ quote ctor_name ^ " has unknown field(s): " ^
                      space_implode ", " extra_fields)
                  val _ =
                    if null missing_fields then ()
                    else error ("struct pattern for " ^ quote ctor_name ^ " is missing field(s): " ^
                      space_implode ", " missing_fields)
                  val ordered_pats =
                    map (fn s =>
                      (case AList.lookup (op =) field_entries s of
                        SOME p => p
                      | NONE =>
                          if is_optional_selector s then Syntax.const \<^syntax_const>\<open>_urust_match_pattern_other\<close>
                          else error ("internal error: field lookup failed for " ^ quote s))) selector_names
                in
                  mk_pat_with_args ctor (pats_to_args shallow_match_arg_of ordered_pats)
                end
            | Const (\<^syntax_const>\<open>_urust_let_pattern_tuple\<close>, _) $ args =>
                tuple_pattern_of shallow_match_arg_of (tuple_args_destruct args)
            | Const (\<^syntax_const>\<open>_urust_match_pattern_disjunction\<close>, _) $ p1 $ p2 =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_disjunction\<close>
                  $ shallow_match_pattern_of p1 $ shallow_match_pattern_of p2
            | Const (\<^syntax_const>\<open>_urust_match_pattern_grouped\<close>, _) $ p =>
                shallow_match_pattern_of p
            | _ =>
                error ("_shallow_match_arg: invalid pattern: " ^ Syntax.string_of_term ctxt pat))

      and shallow_slice_pattern_of args =
            let
              val elems = slice_args_destruct args
              val (prefix, rest_opt, suffix) = split_slice_rest elems

              fun mk_closed [] = mk_pat_no_args mk_nil
                | mk_closed (p :: ps) =
                    mk_pat_with_args mk_cons
                      (mk_args_app (shallow_match_arg_of p)
                        (mk_args_single (mk_arg_pat (mk_closed ps))))

              fun mk_open [] = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_other\<close>
                | mk_open (p :: ps) =
                    mk_pat_with_args mk_cons
                      (mk_args_app (shallow_match_arg_of p)
                        (mk_args_single (mk_arg_pat (mk_open ps))))

              fun mk_open_with_tail [] tail_pat = tail_pat
                | mk_open_with_tail (p :: ps) tail_pat =
                    mk_pat_with_args mk_cons
                      (mk_args_app (shallow_match_arg_of p)
                        (mk_args_single (mk_arg_pat (mk_open_with_tail ps tail_pat))))
            in
              (case rest_opt of
                NONE => mk_closed elems
                | SOME _ =>
                    if null suffix then
                      mk_open prefix
                    else
                      let
                        val suffix_rev_pat = mk_closed (rev suffix)
                      in
                        mk_open_with_tail prefix (mk_pat_slice_suffix suffix_rev_pat)
                      end)
            end

      and shallow_match_args_of args =
            (case args of
              Const (\<^syntax_const>\<open>_urust_match_pattern_args_single\<close>, _) $ arg =>
                mk_args_single (shallow_match_arg_of arg)
            | Const (\<^syntax_const>\<open>_urust_match_pattern_args_app\<close>, _) $ a $ bs =>
                mk_args_app (shallow_match_arg_of a) (shallow_match_args_of bs)
            | _ =>
                error ("_shallow_match_arg: invalid args: " ^ Syntax.string_of_term ctxt args))

      and shallow_match_arg_of pat =
            (case pat of
              Const (\<^syntax_const>\<open>_urust_match_pattern_other\<close>, _) => mk_arg_dummy
            | Const (\<^syntax_const>\<open>_urust_match_pattern_constr_no_args\<close>, _) $ id =>
                (case resolve_constructor_id ctxt id of
                  SOME _ => mk_arg_pat (shallow_match_pattern_of pat)
                | NONE => mk_arg_id id)
            | _ => mk_arg_pat (shallow_match_pattern_of pat))
    in
      shallow_match_arg_of pat
    end;

  fun shallow_match_pattern_tr ctxt ts =
    let
      val mk = Syntax.const
      fun tr [pat] =
        (case shallow_match_arg_tr ctxt [pat] of
          Const (\<^syntax_const>\<open>_urust_shallow_match_pattern_arg_pattern\<close>, _) $ p => p
        | _ => mk \<^syntax_const>\<open>_shallow_match_pattern\<close> $ pat)
        | tr args = Term.list_comb (mk \<^syntax_const>\<open>_shallow_match_pattern\<close>, args)
    in
      tr ts
    end;

  val _ = Theory.setup (Sign.parse_translation [(\<^syntax_const>\<open>_urust_struct_expr\<close>, struct_expr_tr),
                                                (\<^syntax_const>\<open>_urust_match_pattern_struct\<close>, struct_pattern_tr),
                                                (\<^syntax_const>\<open>_shallow_match_pattern\<close>, shallow_match_pattern_tr),
                                                (\<^syntax_const>\<open>_shallow_match_arg\<close>, shallow_match_arg_tr)]);
\<close>

parse_translation\<open>
let

\<comment>\<open>This is largely copied from \<^verbatim>\<open>HOL/Tools/String_Syntax.ML\<close> which defines a parse translation for
\<^text>\<open>_Literal ''foo''\<close> into \<^typ>\<open>char list\<close>. Unfortunately, parse translations don't seem to be
applied recursively, so instead of converting \<^text>\<open>_string_token_to_hol "foo"\<close> into
\<^text>\<open>_Literal ''foo''\<close>, we have to replicate the translation for \<^text>\<open>_Literal\<close> here.\<close>

fun mk_bit_syntax b =
  Syntax.const (if b = 1 then \<^const_syntax>\<open>True\<close> else \<^const_syntax>\<open>False\<close>);

fun mk_bits_syntax len = map mk_bit_syntax o Integer.radicify 2 len;

fun plain_strings_of str =
  map fst (Lexicon.explode_string (str, Position.none));

fun ascii_ord_of c =
  if Symbol.is_ascii c then ord c
  else if c = "\<newline>" then 10
  else error ("Bad character: " ^ quote c);

fun mk_char_syntax i =
  list_comb (Syntax.const \<^const_syntax>\<open>Char\<close>, mk_bits_syntax 8 i);

fun mk_string_syntax [] = Syntax.const \<^const_syntax>\<open>Nil\<close>
  | mk_string_syntax (c :: cs) =
      Syntax.const \<^const_syntax>\<open>Cons\<close> $ mk_char_syntax (ascii_ord_of c)
        $ mk_string_syntax cs;

fun str_tok_to_hol ctxt [Free (str, _)] =
    (Syntax.const \<^const_syntax>\<open>String.implode\<close>) $ mk_string_syntax (plain_strings_of str)
  | str_tok_to_hol ctxt args =
    Term.list_comb (Syntax.const \<^syntax_const>\<open>_string_token_to_hol\<close>, args)

in
  [(\<^syntax_const>\<open>_string_token_to_hol\<close>, str_tok_to_hol)]
end
\<close>

end
