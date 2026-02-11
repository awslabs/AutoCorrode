(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust_Shallow_Embedding
  imports
    Micro_Rust_Parsing_Frontend.Micro_Rust_Syntax
    Core_Syntax
    Prompts_And_Responses
    "HOL-Library.Datatype_Records"
    Autogen.Autogen
    Lenses_And_Other_Optics.Lenses_And_Other_Optics
    Tuple
  keywords
    "notation_nano_rust"
    "notation_nano_rust_field"
    "notation_nano_rust_function"
    "micro_rust_record" :: thy_decl
begin
(*>*)
section\<open>The shallow embedding of uRust into HOL\<close>

text\<open>In this section we define the shallow embedding of uRust into HOL as
a syntax transformations \<^text>\<open>urust \<Rightarrow> logic\<close> from the syntactic category of Micro Rust programs
to the category of HOL terms.\<close>

subsection\<open>Custom identifiers and identifier remapping\<close>

text\<open>The in-built syntax category \<^verbatim>\<open>id\<close> of HOL identifiers does not encompass qualified
Rust names such as \<^verbatim>\<open>Foo::Bar\<close>. To still be able to use those in Micro Rust, the abstract syntax
parser for uRust outputs these as \<^verbatim>\<open>urust_path_string_identifier\<close> entries. We just have
to add a way to parse these as HOL terms.

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

text\<open>Entries marked \<^verbatim>\<open>_shallow_unparsed_path_string\<close> are waiting to be resolved by a parse
translation to a proper HOL term, by looking up the string token in a map.\<close>
syntax
  "_shallow_unparsed_path_string" :: \<open>string_token \<Rightarrow> logic\<close>
    ("URUST'_SHALLOW'_UNPARSED'_PATH'_STRING _")

text\<open>Define the map in which Rust path literals (\<^verbatim>\<open>Foo::Bar\<close>) will be looked up in.\<close>
ML\<open>
  structure RustPathResolution = Generic_Data
  (
    type T = string Symtab.table;
    val empty = Symtab.empty;
    val merge = Symtab.merge (op =);
  );

  fun add_rust_path_resolution key value =
    Symtab.insert (op =) (key, value) |>
    RustPathResolution.map;

  fun get_rust_path_resolution key =
    RustPathResolution.get #> (fn tab => Symtab.lookup tab key)
\<close>

text\<open>Add the parse translation which will perform the lookup.\<close>
parse_translation\<open>
  let
    fun internal_path_translator ctx [Term.Const (rust_name, the_typ)] =
      let
        val rust_resolution = ctx |> Context.Proof |> get_rust_path_resolution rust_name
      in
        case rust_resolution of
            SOME term_name =>
            \<comment> \<open>Note that we cannot have a term map, at least not a naive one, since at this point
                generics still need to be unified.\<close>
            Term.Const (term_name, the_typ)
          | NONE =>
            \<comment> \<open>In the \<^verbatim>\<open>NONE\<close> case, this will output a somewhat nice error message of the form
              \<^verbatim>\<open>Foo::Bar constant not found\<close>\<close>
              Term.Const (rust_name, the_typ)
      end
      | internal_path_translator _ args =
          Term.list_comb (Syntax.const \<^syntax_const>\<open>_shallow_unparsed_path_string\<close>, args);
  in [
    (\<^syntax_const>\<open>_shallow_unparsed_path_string\<close>, internal_path_translator)
  ] end
\<close>

ML\<open>
\<comment> \<open>Replace \<^verbatim>\<open>pattern\<close> by \<^verbatim>\<open>replacement\<close> in \<^verbatim>\<open>original\<close>.\<close>
fun replace_string (pattern: string) (replacement: string) (original: string)  =
    let
        val original_size = String.size original
        val pattern_size = String.size pattern
        
        fun loop start acc =
            if start > original_size - pattern_size
            then String.concat (List.rev (String.extract(original, start, NONE) :: acc))
            else if String.substring(original, start, pattern_size) = pattern
            then loop (start + pattern_size) (replacement :: acc)
            else loop (start + 1)
                 (String.str(String.sub(original, start)) :: acc)
    in
        if pattern_size = 0 orelse original_size = 0
        then original
        else loop 0 []
    end;

replace_string "Hello" "Hi" "Hello, world! Hello, universe!" ;

replace_string "::" "_" "a::b::c";

replace_string  "one" "1" "one two one two";
\<close>

text\<open>Core helper that registers \<^verbatim>\<open>nano_rust_name\<close> as notation for \<^verbatim>\<open>hol_name\<close> in uRust. There are
three cases:
1. \<^verbatim>\<open>nano_rust_name\<close> falls in the \<^verbatim>\<open>id\<close> syntax category. We only add a simple \<^verbatim>\<open>translations\<close> macro.
2. \<^verbatim>\<open>nano_rust_name\<close> is a path identifier (\<^verbatim>\<open>Foo::Bar\<close>). We just have to register them as a  \<^verbatim>\<open>RustPathResolution\<close>
3. \<^verbatim>\<open>nano_rust_name\<close> contains other special characters (e.g. \<^verbatim>\<open>fatal!\<close>). We need to add a syntax entry and a \<^verbatim>\<open>translations\<close> step.
\<close>
ML\<open>
   fun notation_nano_rust ty (hol_name, nano_rust_name) = let
     (* If the Nano Rust name is an identifier, we only need to register a translation
        rule which converts it into the respective HOL identifier.

        If the Nano Rust name is not an identifier, for example `Foo::Bar`, then we
        insert it into the `RustPathResolution` map. *)

     (* Ordinary identifier *)
     fun simple_hol_notation_nano_rust ty hol_name nano_rust_name thy: local_theory = (
        let val translation_in = "_shallow_identifier_as_" ^ ty ^ "(URUST_CONST " ^ " " ^ nano_rust_name ^ ")"
            val translation_out = "CONST " ^ hol_name
            val translation = Syntax.Parse_Rule (("logic",translation_in), ("logic",translation_out)) in
        thy |> Local_Theory.translations_cmd true [translation]
     end)

     val remove_colons = String.translate (fn #":" => "" | c => String.str c)
     val is_path_notation = remove_colons #> Symbol_Pos.is_identifier 

     (* Path notation *)
     fun custom_path_notation_nano_rust hol_identifier nano_rust_name thy: local_theory =
        let
          \<comment> \<open>TODO: the calls to \<^verbatim>\<open>replace_string\<close> are for backwards compatibility. Remove them?\<close>
          val actual_name = nano_rust_name |> replace_string "'_" "_" |> replace_string "':" ":"
        in
          thy |> Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none}
          (K (add_rust_path_resolution actual_name hol_identifier))
        end

     fun remove_dots long_identifier =
           (long_identifier |> String.explode |> filter (fn c : char => (c <> #".")) |> String.implode)

     (* Complex identifier which needs to be treated as a custom keyword *)
     fun custom_hol_notation_nano_rust ty hol_identifier nano_rust_name thy: local_theory = (
        let val mode = Syntax.mode_default
            val syntax_constant = "_urust_identifier_" ^ (remove_dots hol_identifier)
            val translation_in = "_shallow_identifier_as_" ^ ty ^ " " ^ syntax_constant
            val translation_out = "CONST " ^ hol_identifier
            val translation = Syntax.Parse_Rule (("logic",translation_in), ("logic",translation_out)) in
        thy |> Local_Theory.syntax_cmd true mode [(syntax_constant, "urust_identifier", Mixfix.mixfix nano_rust_name)]
            |> Local_Theory.translations_cmd true [translation]
     end)
  in
    if Symbol_Pos.is_identifier nano_rust_name then
      simple_hol_notation_nano_rust ty hol_name nano_rust_name
    else if is_path_notation nano_rust_name then
      custom_path_notation_nano_rust hol_name nano_rust_name
    else
      custom_hol_notation_nano_rust ty hol_name nano_rust_name
  end
\<close>

ML\<open>
   \<comment>\<open>TODO: We should actually be able to do the right thing automatically here, by looking at the type
of the HOL constant that's being registered: Fields are lenses, and functions are \<^text>\<open>function_body\<close>'s.\<close>
   Outer_Syntax.local_theory @{command_keyword "notation_nano_rust"}
      "Add a named HOL literal to Micro Rust"
      (((Parse.long_ident || Parse.short_ident) -- (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")")) >> (notation_nano_rust "literal"));
   Outer_Syntax.local_theory @{command_keyword "notation_nano_rust_field"}
      "Add a named Micro Rust field to Micro Rust"
      (((Parse.long_ident || Parse.short_ident) -- (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")")) >> notation_nano_rust "field");
   Outer_Syntax.local_theory @{command_keyword "notation_nano_rust_function"}
      "Add a named Micro Rust function to Micro Rust"
      (((Parse.long_ident || Parse.short_ident) -- (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")")) >> notation_nano_rust "function")
\<close>

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
     let val typeargs = generic_type_arguments ctxt rec_name in
     ((Class.instance_arity_cmd ([rec_name], typeargs, @{class localizable})
       #> Proof.global_default_proof
       #> Proof_Context.theory_of)
      |> Local_Theory.background_theory) ctxt
     end
\<close>

ML\<open>
   fun register_lens_with_micro_rust rec_name field =
      notation_nano_rust "field" (lens_name rec_name field, field)
   fun register_lenses_with_micro_rust rec_name thy =
      let val fields = get_fields rec_name thy in fold (register_lens_with_micro_rust rec_name) fields thy end

   fun make_lenses (with_fields, rec_name) _ =
       lens_autogen_defs                                                                          rec_name
    #> lens_autogen_defining_equations     @{attributes [micro_rust_record_simps, focus_simps]}   rec_name
    #> lens_autogen_prove_lens_validity    @{attributes [micro_rust_record_intros, focus_intros,
                                                         micro_rust_record_simps, focus_simps]}   rec_name
    #> lens_autogen_prove_update_equations @{attributes [micro_rust_record_simps, focus_simps]}
                                           @{attributes [micro_rust_record_intros, focus_intros]} rec_name
    #> focus_autogen_make_field_foci @{attributes [focus_components]} rec_name
    #> (if with_fields then
          register_lenses_with_micro_rust rec_name
        else
          I)
    #> instantiate_localizable_class rec_name

   val _ =
      Outer_Syntax.local_theory' \<^command_keyword>\<open>micro_rust_record\<close> "make lenses for datatype record"
       (((Scan.optional ((Args.bracks (Args.$$$ "no_fields")) >> K false) true) -- Parse.short_ident) >> make_lenses)
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

  "_shallow_match_branches" :: \<open>urust_match_branches \<Rightarrow> urust_shallow_match_branches\<close>
  "_shallow_match_branch" :: \<open>urust_match_branch  \<Rightarrow> urust_shallow_match_branch \<close>
  "_shallow_match_pattern" :: \<open>urust_pattern \<Rightarrow> urust_shallow_match_pattern\<close>
  "_shallow_match_args" :: \<open>urust_pattern_args \<Rightarrow> urust_shallow_match_pattern_args \<close>
  "_shallow_match_arg" :: \<open>urust_pattern \<Rightarrow> urust_shallow_match_pattern_arg\<close>
  "_shallow_let_pattern" :: \<open>urust_pattern \<Rightarrow> pttrns\<close>
  "_shallow_let_pattern_args" :: \<open>urust_let_pattern_args \<Rightarrow> pttrns\<close>

  "_string_token_to_hol" :: \<open>string_token \<Rightarrow> logic\<close>

text\<open>We define the shallow embedding of uRust into HOL via a series of transformations
at the syntax level.\<close>

context
  notes [[syntax_ast_trace]]
begin
term\<open>let (x, _ :: int) = (5,6) in x+12\<close>
end


translations
  "_shallow_identifier_as_function (_urust_path_string_identifier s)" \<rightharpoonup> "_shallow_unparsed_path_string s"
  "_shallow_identifier_as_literal (_urust_path_string_identifier s)" \<rightharpoonup> "_shallow_unparsed_path_string s"
  "_shallow_identifier_as_field (_urust_path_string_identifier s)" \<rightharpoonup> "_shallow_unparsed_path_string s"

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
  "_shallow_let_pattern (_urust_match_pattern_constr_no_args id)"
    \<rightharpoonup> "_shallow_identifier_as_literal id"
  "_shallow_let_pattern _urust_match_pattern_other"
    \<rightharpoonup> "_idtdummy"

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
  "_shallow_let_pattern (_urust_let_pattern_tuple args)"
    \<rightleftharpoons> "_shallow_let_pattern_args args"
  "_shallow_let_pattern_args (_urust_let_pattern_tuple_base_pair fst_pat snd_pat)"
    \<rightleftharpoons> "_pattern (_shallow_let_pattern fst_pat) (_pattern (_shallow_let_pattern snd_pat) (_idtdummy :: Tuple.tnil))"
  "_shallow_let_pattern_args (_urust_let_pattern_tuple_app fst_pat snd_pat)"
    \<rightleftharpoons> "_pattern (_shallow_let_pattern fst_pat) (_shallow_let_pattern_args snd_pat)"

  "_shallow (_urust_bind_mutable (_urust_identifier_hol_id var) exp cont)"
    \<rightharpoonup> "CONST bind (Ref::new \<langle>(_shallow exp)\<rangle>) (\<lambda>var. (_shallow cont))"
  "_shallow (_urust_sequence seqA seqB)"
    \<rightharpoonup> "CONST sequence (_shallow seqA) (_shallow seqB)"
  "_shallow (_urust_sequence_mono seqA)"
    \<rightharpoonup> "CONST sequence (_shallow seqA) (CONST skip)"

  "_shallow (_urust_identifier ident)"
    \<rightharpoonup> "CONST literal (_shallow_identifier_as_literal ident)"

  "_shallow (_urust_field_access exp fld)"
    \<rightharpoonup> "_urust_shallow_field_access (_shallow exp) (_shallow_identifier_as_field fld)"

  "_shallow (_urust_propagate exp)"
    \<rightharpoonup> "_urust_shallow_propagate (_shallow exp)"
  "_shallow (_urust_borrow exp)"
    \<rightharpoonup> "CONST bindlift1 (CONST ro_ref_from_ref) (_shallow exp)"
  "_shallow (_urust_borrow_mut exp)"
    \<rightharpoonup> "CONST bindlift1 (CONST mut_ref_from_ref) (_shallow exp)"
  "_shallow (_urust_deref exp)"
    \<rightharpoonup> "_urust_shallow_store_dereference (_shallow exp)"

  "_shallow (_urust_assign lhs exp)"
    \<rightharpoonup> "_urust_shallow_store_update (_shallow lhs) (_shallow exp)"

  "_shallow (_urust_word_assign_or lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_or (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_word_assign_xor lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_xor (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_word_assign_and lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_and (_shallow lhs) (_shallow exp)"

  "_shallow (_urust_assign_add lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_add (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_assign_minus lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_minus (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_assign_mul lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_mul (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_assign_mod lhs exp)"
    \<rightharpoonup> "_urust_shallow_assign_mod (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_word_assign_shift_left lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_shift_left (_shallow lhs) (_shallow exp)"
  "_shallow (_urust_word_assign_shift_right lhs exp)"
    \<rightharpoonup> "_urust_shallow_word_assign_shift_right (_shallow lhs) (_shallow exp)"

  "_shallow (_urust_closure_no_args exp)"
    \<rightharpoonup> "CONST literal (CONST FunctionBody (_shallow exp))"
  "_shallow (_urust_closure_with_args args exp)"
    \<rightharpoonup> "CONST literal (_shallow_abstract_args args exp)"

  "_shallow_abstract_args (_urust_formal_single (_urust_identifier_hol_id arg)) exp"
    \<rightharpoonup> "\<lambda>arg. CONST FunctionBody (_shallow exp)"
  "_shallow_abstract_args (_urust_formal_app (_urust_identifier_hol_id arg) args) exp"
    \<rightharpoonup> "\<lambda>arg. _shallow_abstract_args args exp"

  "_shallow_apply_params f (_urust_param_app p params)"
    \<rightharpoonup> "_shallow_apply_params (f p) params"
  "_shallow_apply_params f (_urust_param_single p)"
    \<rightharpoonup> "f p"

  (* Explicit translations for specific macro forms. More may be added as needed *)
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert) (_urust_args_single exp))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST debug_assert) (_urust_args_single exp))"
    \<rightharpoonup> "CONST assert (_shallow exp)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_ne) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_ne (_shallow expA) (_shallow expB)"
  "_shallow (_urust_macro_with_args
      (URUST_CONST assert_eq) (_urust_args_app expA (_urust_args_single expB)))"
    \<rightharpoonup> "CONST assert_eq (_shallow expA) (_shallow expB)"

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
       (URUST_CONST unimplemented) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST unimplemented (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST unimplemented (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST unimplemented) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST unimplemented (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST todo) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST unimplemented (_string_token_to_hol str)"

  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_identifier a)))"
    \<rightharpoonup> "CONST fatal (_shallow_identifier_as_literal a)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_literal x)))"
    \<rightharpoonup> "CONST fatal (CONST String.implode x)"
  "_shallow (_urust_macro_with_args
       (URUST_CONST fatal) (_urust_args_single (_urust_string_token str)))"
    \<rightharpoonup> "CONST fatal (_string_token_to_hol str)"

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
  "_shallow_match_pattern (_urust_match_pattern_constr_no_args id)"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_no_args (_shallow_identifier_as_literal id)"
  "_shallow_match_pattern (_urust_match_pattern_constr_with_args id args)"
    \<rightharpoonup> "_urust_shallow_match_pattern_constr_with_args (_shallow_identifier_as_literal id) (_shallow_match_args args)"
  "_shallow_match_pattern (_urust_match_pattern_disjunction p1 p2)"
    \<rightharpoonup> "_urust_shallow_match_pattern_disjunction (_shallow_match_pattern p1) (_shallow_match_pattern p2)"
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


abbreviation urust_constructor_some :: \<open>'a \<Rightarrow> ('s, 'a option, 'abort, 'i, 'o) function_body\<close> where
   \<open>urust_constructor_some \<equiv> lift_fun1 Some\<close>
abbreviation urust_constructor_ok :: \<open>'a \<Rightarrow> ('s, ('a, 'e) result, 'abort, 'i, 'o) function_body\<close> where
   \<open>urust_constructor_ok \<equiv> lift_fun1 Ok\<close>
abbreviation urust_constructor_err :: \<open>'e \<Rightarrow> ('s, ('a, 'e) result, 'abort, 'i, 'o) function_body\<close> where
   \<open>urust_constructor_err \<equiv> lift_fun1 Err\<close>

notation_nano_rust_function urust_constructor_some ("Some")
notation_nano_rust_function urust_constructor_ok   ("Ok")
notation_nano_rust_function urust_constructor_err  ("Err")

text\<open>By default, we map all identifiers to HOL through the identity function on their names.
We have to register this as a parse translation rather than a rule to give precedence to namings
registers via \<^text>\<open>notation_nano_rust\<close>, which use translation rules.\<close>

\<comment>\<open>NB: We could save some manual invocations of \<^text>\<open>notation_nano_rust\<close> if we changed the
default renaming convention here, and e.g. prepend all field names with \<^verbatim>\<open>field_lens_\<close>,
for example.\<close>
parse_translation\<open>[(\<^syntax_const>\<open>_urust_identifier_id\<close>, K hd),
                   (\<^syntax_const>\<open>_shallow_identifier_as_literal\<close>, K hd),
                   (\<^syntax_const>\<open>_shallow_identifier_as_function\<close>, K hd),
                   (\<^syntax_const>\<open>_shallow_identifier_as_field\<close>, K hd)]\<close>

ML\<open>
  fun starts_upper s =
    size s > 0 andalso Char.isUpper (String.sub (s, 0));

  fun dest_ident_name ctxt (Free (name, _)) = name
    | dest_ident_name ctxt (Const (name, _)) = name
    | dest_ident_name ctxt t =
        error ("invalid identifier term: " ^ Syntax.string_of_term ctxt t);

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

      fun tuple_args_destruct (Const (\<^syntax_const>\<open>_urust_let_pattern_tuple_base_pair\<close>, _) $ a $ b) = [a, b]
        | tuple_args_destruct (Const (\<^syntax_const>\<open>_urust_let_pattern_tuple_app\<close>, _) $ a $ rest) =
            a :: tuple_args_destruct rest
        | tuple_args_destruct t =
            error ("_shallow_match_arg: invalid tuple args: " ^ Syntax.string_of_term ctxt t)

      fun mk_args_single a = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_args_single\<close> $ a
      fun mk_args_app a b = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_args_app\<close> $ a $ b
      fun mk_pat_no_args c = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_constr_no_args\<close> $ c
      fun mk_pat_with_args c args = mk \<^syntax_const>\<open>_urust_shallow_match_pattern_constr_with_args\<close> $ c $ args

      fun mk_pair_pat arg1 pat2 =
            mk_pat_with_args mk_pair
              (mk_args_app arg1 (mk_args_single (mk_arg_pat pat2)))

      fun tuple_pattern_of [] = mk_pat_no_args mk_tnil
        | tuple_pattern_of (p :: ps) =
            mk_pair_pat (shallow_match_arg_of p) (tuple_pattern_of ps)

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
            | Const (\<^syntax_const>\<open>_urust_match_pattern_constr_no_args\<close>, _) $ id =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_constr_no_args\<close> $ id
            | Const (\<^syntax_const>\<open>_urust_match_pattern_constr_with_args\<close>, _) $ id $ args =>
                mk_pat_with_args id (shallow_match_args_of args)
            | Const (\<^syntax_const>\<open>_urust_let_pattern_tuple\<close>, _) $ args =>
                tuple_pattern_of (tuple_args_destruct args)
            | Const (\<^syntax_const>\<open>_urust_match_pattern_disjunction\<close>, _) $ p1 $ p2 =>
                mk \<^syntax_const>\<open>_urust_shallow_match_pattern_disjunction\<close>
                  $ shallow_match_pattern_of p1 $ shallow_match_pattern_of p2
            | _ =>
                error ("_shallow_match_arg: invalid pattern: " ^ Syntax.string_of_term ctxt pat))

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
                if starts_upper (dest_ident_name ctxt id)
                then mk_arg_pat (shallow_match_pattern_of pat)
                else mk_arg_id id
            | _ => mk_arg_pat (shallow_match_pattern_of pat))
    in
      shallow_match_arg_of pat
    end;

  val _ = Theory.setup (Sign.parse_translation [(\<^syntax_const>\<open>_shallow_match_arg\<close>, shallow_match_arg_tr)]);
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
