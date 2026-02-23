(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust_Syntax
  imports Main
begin
(*>*)

section\<open>Micro Rust abstract syntax\<close>

text\<open>In this section, we introduce the abstract syntax of Micro Rust. We operate on a purely syntactic
level, extending Isabelle/HOL by a new syntactic category \<^text>\<open>urust\<close> for uRust programs that's separate from the syntactic
categories of HOL propositions, types and terms. Both the shallow and the deep embedding of Micro Rust into
HOL become syntax transformations \<^text>\<open>urust \<Rightarrow> logic\<close> from \<^text>\<open>urust\<close> into the category \<^text>\<open>logic\<close> of HOL terms.
Further, a Micro-Rust-to-Rust translation may be implemented in ML to automatically export Micro Rust to Rust.\<close>

subsection\<open>Syntax categories\<close>

text\<open>We introduce various syntax categories used in the specification of the grammar of Micro Rust.
The most important one is \<^text>\<open>urust\<close>, which is the category of all syntactically well-formed
Micro Rust expressions:\<close>

nonterminal urust

text\<open>An uninterpreted 'embedding' of Micro Rust into HOL which allows us to cast any Micro Rust parsing
problem as a term-parsing problem.\<close>

syntax
  "_urust_expression" :: \<open>urust \<Rightarrow> logic\<close> ("\<guillemotleft>_\<guillemotright>")

text\<open>The following is the syntax category of Micro Rust identifiers.\<close>

nonterminal urust_identifier

text\<open>Wildcard patterns are represented by \<^verbatim>\<open>_urust_match_pattern_other\<close> and are not valid
identifiers. We intentionally avoid a wildcard identifier to keep pattern parsing unambiguous.\<close>

text\<open>HOL identifiers can be used as Micro Rust identifiers:\<close>
syntax
  "_urust_identifier_id" :: \<open>id \<Rightarrow> urust_identifier\<close>
    ("_" [0]1000)

text\<open>The following are intermediate syntax categories required for the definition of \<^text>\<open>urust\<close>.\<close>
nonterminal urust_args \<comment>\<open>Comma-separated lists of uRust terms\<close>
nonterminal urust_formal_args \<comment> \<open>Comma-separated lists of uRust identifiers\<close>
nonterminal urust_params \<comment> \<open>Comma-separated lists of parameters (HOL terms)\<close>
nonterminal urust_callable
nonterminal urust_fun_literal
nonterminal urust_lhs
nonterminal urust_antiquotation
nonterminal urust_tuple_args
nonterminal urust_struct_expr_fields
nonterminal urust_struct_expr_field

nonterminal urust_match_branch \<comment> \<open>A single branch of a match statement\<close>
nonterminal urust_match_branches \<comment> \<open>Comma-separate lists of match branches\<close>
nonterminal urust_pattern
nonterminal urust_pattern_args
nonterminal urust_pattern_slice_args
nonterminal urust_pattern_struct_fields
nonterminal urust_pattern_struct_field
nonterminal urust_let_pattern_args

nonterminal urust_integral_type

subsection\<open>Core abstract syntax of \<^verbatim>\<open>\<mu>Rust\<close>\<close>

syntax
  \<comment>\<open>Identifiers (variable names) are valid \<^verbatim>\<open>\<mu>Rust\<close> terms\<close>
  "_urust_identifier" :: "urust_identifier \<Rightarrow> urust"
    ("_" [0]1000)
  "_urust_numeral" :: "num_const \<Rightarrow> urust"
    ("_" [0]1000)
  "_urust_numeral_0" :: "urust"
    ("0")
  "_urust_numeral_1" :: "urust"
    ("1")
  "_urust_u8" :: "urust_integral_type"
    ("u8")
  "_urust_u16" :: "urust_integral_type"
    ("u16")
  "_urust_u32" :: "urust_integral_type"
    ("u32")
  "_urust_u64" :: "urust_integral_type"
    ("u64")
  "_urust_usize" :: "urust_integral_type"
    ("usize")
  "_urust_parens" :: "urust \<Rightarrow> urust"
    ("'(_')" [0]999)
  "_urust_string_token" :: "string_token \<Rightarrow> urust"
    ("_")
  \<comment>\<open>Any HOL term can be explicitly lifted to \<^verbatim>\<open>\<mu>Rust\<close> as a literal\<close>
  "_urust_literal" :: "'value \<Rightarrow> urust"
    ("\<llangle>_\<rrangle>" [0]1000)
  "_urust_fun_literal1" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>1" [0]1000)
  "_urust_fun_literal2" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>2" [0]1000)
  "_urust_fun_literal3" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>3" [0]1000)
  "_urust_fun_literal4" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>4" [0]1000)
  "_urust_fun_literal5" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>5" [0]1000)
  "_urust_fun_literal6" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>6" [0]1000)
  "_urust_fun_literal7" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>7" [0]1000)
  "_urust_fun_literal8" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>8" [0]1000)
  "_urust_fun_literal9" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>9" [0]1000)
  "_urust_fun_literal10" :: "'value \<Rightarrow> urust_fun_literal"
    ("\<llangle>_\<rrangle>\<^sub>1\<^sub>0" [0]1000)
  \<comment>\<open>Primitive casts\<close>
  "_urust_primitive_integral_cast_u8" :: "urust \<Rightarrow> urust"
    ("(_) as/ u8" [100]1000)
  "_urust_primitive_integral_cast_u16" :: "urust \<Rightarrow> urust"
    ("(_) as/ u16" [100]1000)
  "_urust_primitive_integral_cast_u32" :: "urust \<Rightarrow> urust"
    ("(_) as/ u32" [100]1000)
  "_urust_primitive_integral_cast_u64" :: "urust \<Rightarrow> urust"
    ("(_) as/ u64" [100]1000)
  "_urust_primitive_integral_cast_usize" :: "urust \<Rightarrow> urust"
    ("(_) as/ usize" [100]1000)
  "_urust_primitive_integral_cast_i32" :: "urust \<Rightarrow> urust"
    ("(_) as/ i32" [100]1000)
  "_urust_primitive_integral_cast_i64" :: "urust \<Rightarrow> urust"
    ("(_) as/ i64" [100]1000)
  \<comment>\<open>Integral literals at a given type\<close>
  "_urust_numeral_ascription_0_u8" :: "urust"
    ("0'_u8")
  "_urust_numeral_ascription_1_u8" :: "urust"
    ("1'_u8")
  "_urust_numeral_ascription_u8" :: "num_const \<Rightarrow> urust"
    ("_'_u8")
  "_urust_numeral_ascription_0_u16" :: "urust"
    ("0'_u16")
  "_urust_numeral_ascription_1_u16" :: "urust"
    ("1'_u16")
  "_urust_numeral_ascription_u16" :: "num_const \<Rightarrow> urust"
    ("_'_u16")
  "_urust_numeral_ascription_0_u32" :: "urust"
    ("0'_u32")
  "_urust_numeral_ascription_1_u32" :: "urust"
    ("1'_u32")
  "_urust_numeral_ascription_u32" :: "num_const \<Rightarrow> urust"
    ("_'_u32")
  "_urust_numeral_ascription_0_u64" :: "urust"
    ("0'_u64")
  "_urust_numeral_ascription_1_u64" :: "urust"
    ("1'_u64")
  "_urust_numeral_ascription_u64" :: "num_const \<Rightarrow> urust"
    ("_'_u64")
  "_urust_numeral_ascription_0_usize" :: "urust"
    ("0'_usize")
  "_urust_numeral_ascription_1_usize" :: "urust"
    ("1'_usize")
  "_urust_numeral_ascription_usize" :: "num_const \<Rightarrow> urust"
    ("_'_usize")
  \<comment> \<open>Breakpoints\<close>
  "_urust_pause" :: "urust" 
    ("\<y>\<i>\<e>\<l>\<d>")
  \<comment> \<open>Logging\<close>
  "_urust_log" :: "'value \<Rightarrow> 'value \<Rightarrow> urust" 
    ("\<l>\<o>\<g> \<llangle>_\<rrangle> \<llangle>_\<rrangle>")
  \<comment> \<open>The special unit value\<close>
  "_urust_unit" :: "urust"
    ("'(')")
  \<comment>\<open>Until 'abstract Micro Rust' is expressive enough, we might need to explicitly embed raw HOL expressions.\<close>
  "_urust_antiquotation" :: "'a \<Rightarrow> urust_antiquotation"
    ("\<epsilon>'\<open>//_'\<close>"[0]1000)
  "" :: \<open>urust_antiquotation \<Rightarrow> urust\<close> ("_")
  \<comment>\<open>Place expressions (valid assignment/update LHS forms).\<close>
  "_urust_lhs_identifier" :: "urust_identifier \<Rightarrow> urust_lhs"
    ("_" [0]1000)
  "_urust_lhs_parens" :: "urust_lhs \<Rightarrow> urust_lhs"
    ("'(_')" [0]999)
  "_urust_lhs_deref" :: \<open>urust \<Rightarrow> urust_lhs\<close>
    ("*_" [200]100)
  "_urust_lhs_field_access" :: \<open>urust_lhs \<Rightarrow> urust_identifier \<Rightarrow> urust_lhs\<close>
    ("_._" [99,1000]100)
  "_urust_lhs_index" :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust_lhs\<close>
    ("_/ '[_']" [100,0]100)
  "_urust_lhs_antiquotation" :: \<open>urust_antiquotation \<Rightarrow> urust_lhs\<close>
  "_urust_lhs_as_urust" :: \<open>urust_lhs \<Rightarrow> urust\<close>
  \<comment>\<open>Introducing an explicit scope within a Micro Rust program\<close>
  "_urust_scoping" :: "urust \<Rightarrow> urust"
    ("{/ _/ }"[0]1000)
  \<comment>\<open>Functions, closures, and macros\<close>
  "_urust_callable_id" :: "urust_identifier \<Rightarrow> urust_callable"
    ("_")
  "" :: "urust_antiquotation \<Rightarrow> urust_callable"
    ("_")
  "_urust_callable_fun_literal" :: "urust_fun_literal \<Rightarrow> urust_callable"
    ("_")
  "_urust_callable_struct" :: "urust \<Rightarrow> urust_identifier \<Rightarrow> urust_callable"
    ("_._" [999,1000]1000)
  "_urust_args_single" :: "urust \<Rightarrow> urust_args"
    ("_")
  "_urust_args_app" :: "urust \<Rightarrow> urust_args \<Rightarrow> urust_args"
    ("_,/ _")
  "_urust_macro_no_args" :: "urust_identifier \<Rightarrow> urust"
    ("_'!/ '(')" [1000]999)
  "_urust_macro_with_args" :: "urust_identifier \<Rightarrow> urust_args \<Rightarrow> urust"
    ("_'!/ '(_')" [1000,0]999)
  "_urust_funcall_with_args" :: "urust_callable \<Rightarrow> urust_args \<Rightarrow> urust"
    ("_/ '(_')"[1000,0]999)
  "_urust_funcall_no_args" :: "urust_callable \<Rightarrow> urust"
    ("_/ '(')"[1000]999)
  "_urust_param_single" :: "logic \<Rightarrow> urust_params"
    ("_")
  "_urust_param_app" :: "logic \<Rightarrow> urust_params \<Rightarrow> urust_params"
    ("_,/ _")
  "_urust_formal_single" :: "urust_identifier \<Rightarrow> urust_formal_args"
    ("_")
  "_urust_formal_app" :: "urust_identifier \<Rightarrow> urust_formal_args \<Rightarrow> urust_formal_args"
    ("_,/ _")
  "_urust_closure_with_args" :: "urust_formal_args \<Rightarrow> urust \<Rightarrow> urust"
    ("'|_'| _"[1000,20]10)
  "_urust_closure_no_args" :: "urust \<Rightarrow> urust"
    ("'|'| _"[20]10)
  "_urust_callable_with_params" :: "urust_callable \<Rightarrow> urust_params \<Rightarrow> urust_callable"
    ("_':':'<_'>" [1000,20]1000)
  \<comment>\<open>Tuples\<close>
  "_urust_tuple_args_double" :: "urust \<Rightarrow> urust \<Rightarrow> urust_tuple_args"
    ("_,/ _" [0,0]1000)
  "_urust_tuple_args_app" :: "urust \<Rightarrow> urust_tuple_args \<Rightarrow> urust_tuple_args"
    ("_,/ _" [0,1000]1000)
  "_urust_tuple_constr" :: "urust_tuple_args \<Rightarrow> urust"
    ("'(_')" [1000]998)
  "_urust_tuple_index_0" :: "urust \<Rightarrow> urust"
    ("_'.0" [998]998)
  "_urust_tuple_index_1" :: "urust \<Rightarrow> urust"
    ("_'.1" [998]998)
  "_urust_tuple_index_2" :: "urust \<Rightarrow> urust"
    ("_'.2" [998]998)
  "_urust_tuple_index_3" :: "urust \<Rightarrow> urust"
    ("_'.3" [998]998)
  "_urust_tuple_index_4" :: "urust \<Rightarrow> urust"
    ("_'.4" [998]998)
  "_urust_tuple_index_5" :: "urust \<Rightarrow> urust"
    ("_'.5" [998]998)
  "_urust_tuple_index_6" :: "urust \<Rightarrow> urust"
    ("_'.6" [998]998)
  "_urust_tuple_index_7" :: "urust \<Rightarrow> urust"
    ("_'.7" [998]998)
  "_urust_tuple_index_8" :: "urust \<Rightarrow> urust"
    ("_'.8" [998]998)
  "_urust_tuple_index_9" :: "urust \<Rightarrow> urust"
    ("_'.9" [998]998)
  "_urust_tuple_index_10" :: "urust \<Rightarrow> urust"
    ("_'.10" [998]998)
  "_urust_tuple_index_11" :: "urust \<Rightarrow> urust"
    ("_'.11" [998]998)
  "_urust_tuple_index_12" :: "urust \<Rightarrow> urust"
    ("_'.12" [998]998)
  "_urust_tuple_index_13" :: "urust \<Rightarrow> urust"
    ("_'.13" [998]998)
  "_urust_tuple_index_14" :: "urust \<Rightarrow> urust"
    ("_'.14" [998]998)
  "_urust_tuple_index_15" :: "urust \<Rightarrow> urust"
    ("_'.15" [998]998)
  \<comment>\<open>Array literals: [e0, e1, ...]. Lowered to Cons/Nil lists.\<close>
  "_urust_array_expr_empty" :: \<open>urust\<close>
    ("'[]")
  "_urust_array_expr" :: \<open>urust_args \<Rightarrow> urust\<close>
    ("'[_']")
  \<comment>\<open>Struct expressions: Foo { foo: a, goo: b }\<close>
  "_urust_struct_expr" :: \<open>urust_identifier \<Rightarrow> urust_struct_expr_fields \<Rightarrow> urust\<close>
    ("_/ {/ _/ }" [1000, 0] 1000)
  "_urust_struct_expr_field" :: \<open>urust_identifier \<Rightarrow> urust \<Rightarrow> urust_struct_expr_field\<close>
    ("_ :/ _" [1000, 0] 1000)
  "_urust_struct_expr_fields_single" :: \<open>urust_struct_expr_field \<Rightarrow> urust_struct_expr_fields\<close>
    ("_")
  "_urust_struct_expr_fields_app" :: \<open>urust_struct_expr_field \<Rightarrow> urust_struct_expr_fields \<Rightarrow> urust_struct_expr_fields\<close>
    ("_,/ _" [1000, 100] 100)
  \<comment>\<open>We have very basic support for tuple patterns: identifiers and tuple destruction\<close>
  "_urust_let_pattern_tuple" :: "urust_let_pattern_args \<Rightarrow> urust_pattern"
    ("'(_')")
  "_urust_let_pattern_tuple_base_pair" :: "urust_pattern \<Rightarrow> urust_pattern \<Rightarrow> urust_let_pattern_args"
    ("_, _")
  "_urust_let_pattern_tuple_app" :: "urust_pattern \<Rightarrow> urust_let_pattern_args \<Rightarrow> urust_let_pattern_args"
    ("(_), (_)")
  \<comment>\<open>The monadic composition of two Micro Rust programs, ignoring the result of the first\<close>
  "_urust_sequence" :: "urust \<Rightarrow> urust \<Rightarrow> urust"
    ("_;_" [11,10]10)
  "_urust_sequence_mono" :: "urust \<Rightarrow> urust"
    ("_;" [11]10)
  \<comment>\<open>Add immutable binding\<close>
  "_urust_bind_immutable" :: "urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust"
    ("let/ _/ =/ _;// _" [1000,20,10]10)
  "_urust_bind_immutable'" :: "urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust"
    ("const/ _/ =/ _;// _" [1000,20,10]10)
  \<comment>\<open>Add mutable binding\<close>
  "_urust_bind_mutable" :: "urust_identifier \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust"
    ("let/ mut/ _/ =/ _;// _" [1000,20,10]10)
  \<comment>\<open>Boolean literals as expressions\<close>
  "_urust_true" :: \<open>urust\<close>
    ("true" 1000)
  "_urust_false" :: \<open>urust\<close>
    ("false" 1000)
  \<comment>\<open>Standard if-then-else conditional\<close>
  "_urust_if_then_else" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else/ {/ _/ }"[20,0,0]21)
  \<comment>\<open>Rust-style else-if conditional (desugared to nested ifs)\<close>
  "_urust_if_then_else_if" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else if/ _/ / {/ _/ }"[20,0,20,0]21)
  "_urust_if_then_else_if_else" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else if/ _/ / {/ _/ }/ else/ _"[20,0,20,0,11]21)
  \<comment>\<open>Standard if-then conditional\<close>
  "_urust_if_then" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }"[20,0]20)
  "_urust_return" :: \<open>urust \<Rightarrow> urust\<close>
    ("return _;")
  "_urust_return_unit" :: \<open>urust\<close>
    ("return/ ;")
  \<comment>\<open>Unsafe\<close>
  "_urust_unsafe_block" :: \<open>urust \<Rightarrow> urust\<close>
    ("unsafe/ {/ _ /}")
  \<comment>\<open>Indexing and accessing\<close>
  "_urust_field_access" :: \<open>urust \<Rightarrow> urust_identifier \<Rightarrow> urust\<close>
    ("_._" [99,1000]100)
  "_urust_index" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("_/ '[_']" [100,0]100)
  \<comment> \<open>Path identifiers (e.g. \<^verbatim>\<open>Foo::Bar\<close>), with the \<^verbatim>\<open>string_token\<close> containing the full path.
      We will add parse AST transformations to construct these below.\<close>
  "_urust_path_string_identifier" :: \<open>string_token \<Rightarrow> urust_identifier\<close>
    ("URUST'_PATH'_STRING'_IDENTIFIER _")

  \<comment>\<open>Other control flow constructs\<close>
  "_urust_for_loop"
    :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("for _ in (_) {/ _/ }" [100,20,0]11)

  "_urust_let_else" :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("let _ = (_) else { (_) } ; (_)" [100,20,0,10]10)

  "_urust_if_let" :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if let _ = (_) { (_) }" [100,20,0]11)

  "_urust_if_let_else" :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if let _ = (_) { (_) } else { (_) }" [100,20,0,0]11)

  \<comment>\<open>Rust-style statement sequencing: block-like expressions may omit a trailing semicolon.\<close>
  "_urust_sequence_if_then_else"
    :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else/ {/ _/ }/ _" [20,0,0,10]10)
  "_urust_sequence_if_then_else_if"
    :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else if/ _/ / {/ _/ }/ _" [20,0,20,0,10]10)
  "_urust_sequence_if_then_else_if_else"
    :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ else if/ _/ / {/ _/ }/ else/ _/ _" [20,0,20,0,11,10]10)
  "_urust_sequence_if_then"
    :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if/ _/ / {/ _/ }/ _" [20,0,10]10)
  "_urust_sequence_for_loop"
    :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("for _ in (_) {/ _/ }/ _" [100,20,0,10]10)
  "_urust_sequence_if_let"
    :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if let _ = (_) { (_) }/ _" [100,20,0,10]10)
  "_urust_sequence_if_let_else"
    :: \<open>urust_pattern \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("if let _ = (_) { (_) } else { (_) }/ _" [100,20,0,0,10]10)
  "_urust_sequence_temporary_match"
    :: \<open>urust \<Rightarrow> urust_match_branches \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("match (_) {/ _/ }/ _" [20,10,10]10)
  "_urust_sequence_scoping"
    :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("{/ _/ }/ _" [0,10]10)
  "_urust_sequence_unsafe_block"
    :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    ("unsafe/ {/ _ /}/ _" [0,10]10)

  \<comment> \<open>We distinguish two types of matches. The first is the usual \<^verbatim>\<open>case\<close> on datatypes.
      The second is more of a C-style \<^verbatim>\<open>switch\<close> statement via a match. It is hard to distinguish
      these at first parsing time. Instead, we distinguish them via a \<^emph>\<open>parse AST translation\<close>. The
      distinguishing property (on the AST level) is that the \<^verbatim>\<open>switch\<close>-style matches must contain
      only numeral, other and \<^verbatim>\<open>id\<close> clauses, while the \<^verbatim>\<open>case\<close> style matches cannot contain numeral
      clauses.
     We add two syntax clauses which this AST translation will insert, which will then be used
      as a handle for further translations of the syntax tree later on.\<close>
  "_urust_match_case" :: "[urust, urust_match_branches] \<Rightarrow> urust"   ("match'_case (_) {/ _/ }" [20, 10]20)
  "_urust_match_switch" :: "[urust, urust_match_branches] \<Rightarrow> urust"   ("match'_switch (_) {/ _/ }" [20, 10]20)
  \<comment> \<open>This is \<^verbatim>\<open>temporary\<close> since we will disambiguate between two styles of matches\<close>
  "_urust_temporary_match"  :: "[urust, urust_match_branches] \<Rightarrow> urust"  ("match (_) {/ _/ }" [20, 10]20)
  "_urust_match1" :: "[urust_pattern, urust] \<Rightarrow> urust_match_branches"  ("(2_ \<Rightarrow>/ _)" [100, 20] 21)
  "_urust_match1_guard" :: "[urust_pattern, urust, urust] \<Rightarrow> urust_match_branches"
    ("(2_ if _ \<Rightarrow>/ _)" [100, 0, 20] 21)
  "_urust_match2" :: "[urust_match_branches, urust_match_branches] \<Rightarrow> urust_match_branches"  ("_/, _" [21, 20]20)

  \<comment>\<open>Basic case patterns, restricted to constructor identifiers followed by a potentially empty list of argument identifiers, and numerals\<close>
  "_urust_match_pattern_other" :: \<open>urust_pattern\<close>
    ("'_")
  "_urust_match_pattern_constr_no_args" :: \<open>urust_identifier \<Rightarrow> urust_pattern\<close>
    ("_" [0]1000)
  "_urust_match_pattern_num_const" :: \<open>num_const \<Rightarrow> urust_pattern\<close>
    ("_" [1000]1000)
  "_urust_match_pattern_zero" :: \<open>urust_pattern\<close>
    ("0" 1000)
  "_urust_match_pattern_one" :: \<open>urust_pattern\<close>
    ("1" 1000)
  "_urust_match_pattern_true" :: \<open>urust_pattern\<close>
    ("true" 1000)
  "_urust_match_pattern_false" :: \<open>urust_pattern\<close>
    ("false" 1000)
  "_urust_match_pattern_string" :: \<open>string_token \<Rightarrow> urust_pattern\<close>
    ("_" [1000]1000)
  \<comment>\<open>Generic literal pattern. Useful as a fallback for values without dedicated token syntax
      (e.g. chars as \<^verbatim>\<open>\<llangle>CHR ''a''\<rrangle>\<close>).\<close>
  "_urust_match_pattern_literal" :: \<open>'a \<Rightarrow> urust_pattern\<close>
    ("\<llangle>_\<rrangle>" [1000]1000)
  "_urust_match_pattern_constr_with_args" :: \<open>urust_identifier \<Rightarrow> urust_pattern_args \<Rightarrow> urust_pattern\<close>
    ("_ '(_')"[1000,100]1000)
  "_urust_match_pattern_args_single" :: \<open>urust_pattern \<Rightarrow> urust_pattern_args\<close>
    ("_")
  "_urust_match_pattern_args_app" :: \<open>urust_pattern \<Rightarrow> urust_pattern_args \<Rightarrow> urust_pattern_args\<close>
    ("_,/ _"[1000,100]100)

  \<comment>\<open>Slice/list patterns: [p0, p1, ...]\<close>
  "_urust_match_pattern_slice_empty" :: \<open>urust_pattern\<close>
    ("'[]")
  "_urust_match_pattern_slice" :: \<open>urust_pattern_slice_args \<Rightarrow> urust_pattern\<close>
    ("'[_']")
  "_urust_match_pattern_slice_args_empty" :: \<open>urust_pattern_slice_args\<close>
    ("")
  "_urust_match_pattern_slice_args_single" :: \<open>urust_pattern \<Rightarrow> urust_pattern_slice_args\<close>
    ("_")
  "_urust_match_pattern_slice_args_app" :: \<open>urust_pattern \<Rightarrow> urust_pattern_slice_args \<Rightarrow> urust_pattern_slice_args\<close>
    ("_,/ _"[1000,100]100)
  "_urust_match_pattern_slice_rest" :: \<open>urust_pattern\<close>
    (".." 1000)

  \<comment>\<open>Struct patterns: Foo { foo: p, goo: q }\<close>
  "_urust_match_pattern_struct" :: \<open>urust_identifier \<Rightarrow> urust_pattern_struct_fields \<Rightarrow> urust_pattern\<close>
    ("_/ {/ _/ }" [1000, 0] 1000)
  "_urust_match_pattern_struct_field" :: \<open>urust_identifier \<Rightarrow> urust_pattern \<Rightarrow> urust_pattern_struct_field\<close>
    ("_ :/ _" [1000, 100] 1000)
  "_urust_match_pattern_struct_field_short" :: \<open>urust_identifier \<Rightarrow> urust_pattern_struct_field\<close>
    ("_" [1000]1000)
  "_urust_match_pattern_struct_rest" :: \<open>urust_pattern_struct_field\<close>
    ("..")
  "_urust_match_pattern_struct_fields_single" :: \<open>urust_pattern_struct_field \<Rightarrow> urust_pattern_struct_fields\<close>
    ("_")
  "_urust_match_pattern_struct_fields_app" :: \<open>urust_pattern_struct_field \<Rightarrow> urust_pattern_struct_fields \<Rightarrow> urust_pattern_struct_fields\<close>
    ("_,/ _" [1000, 100] 100)

  \<comment>\<open>Disjunctive patterns: p1 | p2 (right-associative)\<close>
  "_urust_match_pattern_disjunction" :: \<open>urust_pattern \<Rightarrow> urust_pattern \<Rightarrow> urust_pattern\<close>
    ("_ '|/ _" [1000, 100] 100)
  \<comment>\<open>Grouped patterns: (p)\<close>
  "_urust_match_pattern_grouped" :: \<open>urust_pattern \<Rightarrow> urust_pattern\<close>
    ("'(_')" [1000]1000)
  \<comment>\<open>\<^verbatim>\<open>id @ pat\<close> alias pattern\<close>
  "_urust_match_pattern_as" :: \<open>urust_identifier \<Rightarrow> urust_pattern \<Rightarrow> urust_pattern\<close>
    ("_ @/ _" [1000, 1000] 1000)
  \<comment>\<open>Binding mode annotations. Current semantics are a frontend-only desugaring and do not
      model borrow-checking behavior. We intentionally do not support Rust's @{text "ref"} and
      @{text "ref mut"} pattern binders here, because they collide with existing `ref` syntax
      used pervasively in this development.\<close>
  "_urust_match_pattern_borrow" :: \<open>urust_pattern \<Rightarrow> urust_pattern\<close>
    ("&_" [1000]1000)
  "_urust_match_pattern_borrow_mut" :: \<open>urust_pattern \<Rightarrow> urust_pattern\<close>
    ("& mut _" [1000]1000)
  \<comment>\<open>Range patterns (currently lowered to guarded matches in the shallow embedding).\<close>
  "_urust_match_pattern_range" :: \<open>urust_pattern \<Rightarrow> urust_pattern \<Rightarrow> urust_pattern\<close>
    (infix \<open>..\<close> 41)
  "_urust_match_pattern_range_eq" :: \<open>urust_pattern \<Rightarrow> urust_pattern \<Rightarrow> urust_pattern\<close>
    (infix \<open>..=\<close> 41)

  \<comment> \<open>See the rust documentation for a list of expression precedences and fixities:
       https://doc.rust-lang.org/reference/expressions.html\<close>

  "_urust_propagate" :: \<open>urust \<Rightarrow> urust\<close>
    ("_'?" [400]400)

  "_urust_negation" :: \<open>urust \<Rightarrow> urust\<close>
    ("'! _" [300]300)
  "_urust_double_negation" :: \<open>urust \<Rightarrow> urust\<close>
    ("'!'! _" [300]300)
  "_urust_borrow" :: \<open>urust \<Rightarrow> urust\<close>
    ("&_" [200]100)
  "_urust_borrow_mut" :: \<open>urust \<Rightarrow> urust\<close>
    ("& mut _" [200]100)
  "_urust_deref" :: \<open>urust \<Rightarrow> urust\<close>
    ("*_" [200]100)
  "_urust_double_deref" :: \<open>urust \<Rightarrow> urust\<close>
    ("**_" [200]100)

  \<comment>\<open>Arithmetic expressions\<close>
  "_urust_mul" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "*" 50)
  "_urust_div" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "'/" 50)
  "_urust_mod" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "%" 50)

  "_urust_add" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "+" 49)
  "_urust_minus" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "-" 49)

  "_urust_shift_right" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl ">>" 48)
  "_urust_shift_left" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "<<" 48)

  "_urust_bitwise_and" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "&" 47)
  "_urust_bitwise_xor" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "^" 46)
  "_urust_bitwise_or" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl "|" 45)

  "_urust_equality" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "==" 44)
  "_urust_nonequality" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "!=" 44)

  \<comment>\<open>Comparison\<close>
  "_urust_greater_equal" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix ">=" 44)
  "_urust_less_equal" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "<=" 44)
  "_urust_greater" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix ">" 44)
  "_urust_less" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix "<" 44)

  "_urust_bool_conjunction" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl \<open>&&\<close> 43)

  "_urust_bool_disjunction" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixl \<open>||\<close> 42)

  "_urust_range" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix \<open>..\<close> 41)
  "_urust_range_eq" :: \<open>urust \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infix \<open>..=\<close> 41)

  "_urust_assign" :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
    (infixr "=" 40)

  "_urust_assign_add"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "+=" 40)
  "_urust_assign_minus"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "-=" 40)
  "_urust_assign_mul"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "*=" 40)
  "_urust_assign_mod"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "%=" 40)
  "_urust_word_assign_and"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "&=" 40)
  "_urust_word_assign_or"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "|=" 40)
  "_urust_word_assign_xor"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "^=" 40)
  "_urust_word_assign_shift_left"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr "<<=" 40)
  "_urust_word_assign_shift_right"
     :: \<open>urust_lhs \<Rightarrow> urust \<Rightarrow> urust\<close>
     (infixr ">>=" 40)

translations
  "_urust_lhs_as_urust (_urust_lhs_identifier id)" => "_urust_identifier id"
  "_urust_lhs_as_urust (_urust_lhs_parens lhs)" => "_urust_parens (_urust_lhs_as_urust lhs)"
  "_urust_lhs_as_urust (_urust_lhs_deref ex)" => "ex" (* Deref is basically a no-op on a LHS *)
  "_urust_lhs_as_urust (_urust_lhs_field_access lhs fld)" =>
    "_urust_field_access (_urust_lhs_as_urust lhs) fld"
  "_urust_lhs_as_urust (_urust_lhs_index lhs idx)" =>
    "_urust_index (_urust_lhs_as_urust lhs) idx"
  "_urust_lhs_as_urust (_urust_lhs_antiquotation a)" => "_urust_antiquotation a"
  \<comment>\<open>Rust slice literals (&[...]) are currently front-end sugar for list literals.\<close>
  "_urust_borrow (_urust_array_expr_empty)" => "_urust_array_expr_empty"
  "_urust_borrow (_urust_array_expr args)" => "_urust_array_expr args"
  "_urust_borrow_mut (_urust_array_expr_empty)" => "_urust_array_expr_empty"
  "_urust_borrow_mut (_urust_array_expr args)" => "_urust_array_expr args"
  "_urust_if_then_else_if c t c' t'" => "_urust_if_then_else c t (_urust_if_then c' t')"
  "_urust_if_then_else_if_else c t c' t' e" => "_urust_if_then_else c t (_urust_if_then_else c' t' e)"
  "_urust_sequence_if_then_else c t e next" => "_urust_sequence (_urust_if_then_else c t e) next"
  "_urust_sequence_if_then_else_if c t c' t' next" =>
    "_urust_sequence (_urust_if_then_else_if c t c' t') next"
  "_urust_sequence_if_then_else_if_else c t c' t' e next" =>
    "_urust_sequence (_urust_if_then_else_if_else c t c' t' e) next"
  "_urust_sequence_if_then c t next" => "_urust_sequence (_urust_if_then c t) next"
  "_urust_sequence_for_loop x iter body next" => "_urust_sequence (_urust_for_loop x iter body) next"
  "_urust_sequence_if_let ptrn exp this next" => "_urust_sequence (_urust_if_let ptrn exp this) next"
  "_urust_sequence_if_let_else ptrn exp this that next" =>
    "_urust_sequence (_urust_if_let_else ptrn exp this that) next"
  "_urust_sequence_scoping body next" => "_urust_sequence (_urust_scoping body) next"
  "_urust_sequence_unsafe_block body next" => "_urust_sequence (_urust_unsafe_block body) next"

subsection\<open>Breaking long identifiers\<close>

text\<open>Expressions of the form \<^verbatim>\<open>foo.bar\<close> are parsed by Isabelle's inner syntax parser
as single tokens of syntactic type \<^text>\<open>longid\<close>, which doesn't match the Rust meaning as a
call to a structure method.

We temporarily interpret \<^text>\<open>longid\<close> as atomic callables to get through the parsing stage, and
then use a manual parse AST translation to break the \<^text>\<open>longid\<close> into its parts and reinterpret
calls as structure method calls.\<close>

experiment
  notes [[syntax_ast_trace]]
begin
\<comment> \<open>Currently, field indexing does not yet fit in our grammar\<close>
(*
term\<open>\<guillemotleft>foo.bar.boo.far\<guillemotright>\<close>
*)
end

nonterminal urust_temporary_long_identifier
syntax
  \<comment>\<open>Mark those as temporary to indicate that semantics definitions need not deal with it.
It is immediately removed after parsing.\<close>
  "_urust_temporary_long_id" :: \<open>longid \<Rightarrow> urust_temporary_long_identifier\<close>
    ("_" [0]1000)

  \<comment>\<open>Allow long ids in a few grammar productions normally taking ordinary identifiers\<close>
  "_urust_temporary_callable_id_long" :: \<open>urust_temporary_long_identifier \<Rightarrow> urust_callable\<close>
    ("_" [0]1000)
  "_urust_temporary_callable_struct_long" :: "urust \<Rightarrow> urust_temporary_long_identifier \<Rightarrow> urust_callable"
    ("_._" [999,1000]1000)
  "_urust_temporary_field_access_long" :: \<open>urust \<Rightarrow> urust_temporary_long_identifier \<Rightarrow> urust\<close>
    ("_._" [99,1000]100)
  "_urust_temporary_identifier_long" :: \<open>urust_temporary_long_identifier \<Rightarrow> urust\<close>
    ("_" [0]1000)
  "_urust_temporary_lhs_identifier_long" :: \<open>urust_temporary_long_identifier \<Rightarrow> urust_lhs\<close>
    ("_" [0]1000)

experiment
  notes [[syntax_ast_trace]]
begin
\<comment> \<open>At this point it fits, but we just get \<^verbatim>\<open>foo.bar.boo.far\<close> - the splitting is not yet being done\<close>
(*
term\<open>\<guillemotleft>foo.bar.boo.far\<guillemotright>\<close>
*)
end

text\<open>Handle double negation \<^verbatim>\<open>!!\<close> by expanding to nested single negations.\<close>
parse_ast_translation\<open>
let
  fun double_neg_tr [x] =
    Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_negation\<close>)
      [Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_negation\<close>) [x]]
  | double_neg_tr args = raise Ast.AST ("double_neg_tr", args)
in
  [(\<^syntax_const>\<open>_urust_double_negation\<close>, K double_neg_tr)]
end
\<close>

text\<open>Handle double dereference \<^verbatim>\<open>**\<close> by expanding to nested single dereferences.\<close>
parse_ast_translation\<open>
let
  fun double_deref_tr [x] =
    Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_deref\<close>)
      [Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_deref\<close>) [x]]
  | double_deref_tr args = raise Ast.AST ("double_deref_tr", args)
in
  [(\<^syntax_const>\<open>_urust_double_deref\<close>, K double_deref_tr)]
end
\<close>

text\<open>First, we register a parse AST translation splitting long IDs at dots (".") and emitting them
as an anonymous \<^ML>\<open>Ast.Appl\<close>, with one \<^text>\<open>urust_identifier\<close> argument per component.\<close>
ML\<open>
  fun split_at_dots str = let
     val scan_to_dot = (Scan.repeat (Scan.unless ($$ ".") (Scan.one Symbol.not_eof)))
     val skip_over_dot = ($$ ".") || Scan.succeed ""
     val extract_part = (scan_to_dot --| skip_over_dot) >> implode
     val splitter = Scan.finite Symbol.stopper
             (Scan.repeat (Scan.unless (Scan.one Symbol.is_eof) extract_part)) in
     fst (splitter (Symbol.explode str))
   end

  val split_long_identifier = Ast.pretty_ast #> Pretty.string_of #> split_at_dots

  fun ast_urust_identifier_id str =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_identifier_id\<close>) [Ast.Variable str]
\<close>

text\<open>Lower slice patterns to nested list constructor patterns:
\<^verbatim>\<open>[a, b, c]\<close> becomes \<^verbatim>\<open>Cons(a, Cons(b, Cons(c, Nil)))\<close>.\<close>
parse_ast_translation\<open>
let
  val mk = Ast.mk_appl
  val cons_id = mk (Ast.Constant \<^syntax_const>\<open>_urust_identifier_id\<close>) [Ast.Variable "Cons"]
  val nil_id = mk (Ast.Constant \<^syntax_const>\<open>_urust_identifier_id\<close>) [Ast.Variable "Nil"]

  fun mk_pat_no_args id =
    mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_constr_no_args\<close>) [id]
  fun mk_pat_with_args id args =
    mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_constr_with_args\<close>) [id, args]
  fun mk_args_single a =
    mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_args_single\<close>) [a]
  fun mk_args_app a bs =
    mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_args_app\<close>) [a, bs]

  fun slice_args_destruct (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice_args_empty\<close>) = []
    | slice_args_destruct (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice_args_single\<close>, a]) = [a]
    | slice_args_destruct (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice_args_app\<close>, a, bs]) =
        a :: slice_args_destruct bs
    | slice_args_destruct ast = raise Ast.AST ("slice_args_destruct", [ast])

  fun has_slice_rest [] = false
    | has_slice_rest (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice_rest\<close> :: _) = true
    | has_slice_rest (_ :: xs) = has_slice_rest xs

  fun mk_list_pattern [] = mk_pat_no_args nil_id
    | mk_list_pattern (a :: as') =
        mk_pat_with_args cons_id (mk_args_app a (mk_args_single (mk_list_pattern as')))

  fun slice_empty_pattern_tr [] = mk_list_pattern []
    | slice_empty_pattern_tr xs =
        mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice_empty\<close>) xs

  fun slice_pattern_tr [args] =
        let
          val elems = slice_args_destruct args
        in
          if has_slice_rest elems
          then mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice\<close>) [args]
          else mk_list_pattern elems
        end
    | slice_pattern_tr xs =
        mk (Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_slice\<close>) xs
in
  [(\<^syntax_const>\<open>_urust_match_pattern_slice_empty\<close>, K slice_empty_pattern_tr),
   (\<^syntax_const>\<open>_urust_match_pattern_slice\<close>, K slice_pattern_tr)]
end
\<close>

parse_ast_translation\<open>
let
  \<comment>\<open>ML representations of the relevant Nano Rust grammar productions\<close>
  \<comment>\<open>This does currently only work for long identifiers of the form \<^text>\<open>id.id\<close>.\<close>
  fun break_long_identifier [long_id] =
     let val parts = long_id |> split_long_identifier
         val parts_as_ids = map (ast_urust_identifier_id) parts
     in Ast.Appl parts_as_ids end
  | break_long_identifier args =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_long_id\<close>) args
in
  [(\<^syntax_const>\<open>_urust_temporary_long_id\<close>, K break_long_identifier)]
end
\<close>

experiment
  notes [[syntax_ast_trace]]
begin
\<comment> \<open>At this point it fits, but we just get \<^verbatim>\<open>foo.bar.boo.far\<close> - the splitting is not yet being done\<close>
(*
term\<open>\<guillemotleft>foo.bar.boo.far\<guillemotright>\<close>
*)
end

text\<open>Next, we go through all temporary grammar productions using long IDs and adjust them according to the
intended meaning of the "." operator in the respective context. For example, where a long identifier is used
as a standalone uRust term, dots are field projections. In contrast, if a long identifier is used as a callable,
it should be converted into a method invocation.

Note that since parse AST translations are called bottom-up, by the time the parse AST translations below
are called, long IDs have already been converted into anynomous AST applications, which gives us easy
access to the components of the long ID.\<close>
ML\<open>
  fun ast_urust_identifier ast =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_identifier\<close>) [ast]
  fun ast_urust_lhs_identifier ast =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_lhs_identifier\<close>) [ast]
  fun ast_urust_field_access func obj  =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_field_access\<close>) [obj, func]
  fun ast_urust_lhs_field_access func obj  =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_lhs_field_access\<close>) [obj, func]
  fun ast_urust_callable_struct func obj  =
     Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_callable_struct\<close>) [obj, func]

  fun long_id_struct_access_into_callable head projections =
     let val (body, method) = split_last projections
         val obj = fold ast_urust_field_access body head
         val res = ast_urust_callable_struct method obj
     in res end

  fun long_id_field_access_into_urust head projections =
     let val res = fold ast_urust_field_access projections head
     in res end

  fun long_id_field_access_into_lhs head projections =
     let val res = fold ast_urust_lhs_field_access projections head
     in res end
\<close>
parse_ast_translation\<open>
let
  fun debug_result str res = (*
      writeln ("parse AST translation for temporary long " ^ str ^ ", result "
              ^ (Pretty.string_of (Ast.pretty_ast res))) *)
      ()

  fun convert_temporary_identifier_long [Ast.Appl (head :: projections)] =
     let val head = ast_urust_identifier head
         val res = fold ast_urust_field_access projections head
         val _ = debug_result "ID" res
     in res end
   | convert_temporary_identifier_long args =
      Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_identifier_long\<close>) args

  fun convert_temporary_callable_id_long [Ast.Appl (head :: projections)] =
     let val head = ast_urust_identifier head
         val (body, method) = split_last projections
         val obj = fold ast_urust_field_access body head
         val res = ast_urust_callable_struct method obj
         val _ = debug_result "callable id" res
     in res end
   | convert_temporary_callable_id_long args =
      Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_callable_id_long\<close>) args

  fun convert_temporary_callable_struct_long [head, Ast.Appl projections] =
     let val res = long_id_struct_access_into_callable head projections
         val _ = debug_result "callable struct" res
     in res end
   | convert_temporary_callable_struct_long args =
      Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_callable_struct_long\<close>) args

  fun convert_temporary_field_access_long [head, Ast.Appl projections] =
     let val res = long_id_field_access_into_urust head projections
         val _ = debug_result "field access" res
     in res end
   | convert_temporary_field_access_long args =
      Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_field_access_long\<close>) args

  fun convert_temporary_lhs_identifier_long [Ast.Appl (head :: projections)] =
     let val head = ast_urust_lhs_identifier head
         val res = fold ast_urust_lhs_field_access projections head
         val _ = debug_result "lhs id" res
     in res end
   | convert_temporary_lhs_identifier_long args =
      Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_lhs_identifier_long\<close>) args
in
  [(\<^syntax_const>\<open>_urust_temporary_identifier_long\<close>,      K convert_temporary_identifier_long),
   (\<^syntax_const>\<open>_urust_temporary_callable_id_long\<close>,     K convert_temporary_callable_id_long),
   (\<^syntax_const>\<open>_urust_temporary_callable_struct_long\<close>, K convert_temporary_callable_struct_long),
   (\<^syntax_const>\<open>_urust_temporary_field_access_long\<close>,    K convert_temporary_field_access_long),
   (\<^syntax_const>\<open>_urust_temporary_lhs_identifier_long\<close>,   K convert_temporary_lhs_identifier_long) ]
end
\<close>

subsection\<open>Interpreting path identifiers\<close>

nonterminal path_identifier \<comment> \<open>An identifier of the form \<^verbatim>\<open>foo::bar\<close>\<close>
nonterminal path_identifier_long \<comment> \<open>An identifier of the form \<^verbatim>\<open>foo::bar.boo\<close>\<close>

syntax
  "_path_builder_two_id" :: \<open>id \<Rightarrow> id \<Rightarrow> path_identifier\<close>
    ("_':': _"[0,0]1000)
  "_path_builder_more" :: \<open>id \<Rightarrow> path_identifier \<Rightarrow> path_identifier\<close>
    ("_':': _"[0,1000]1000)
  \<comment> \<open>We will transform \<^verbatim>\<open>_urust_temporary_path_identifier\<close> into \<^verbatim>\<open>_urust_path_string_identifier\<close>,
     where the string token contains the string representation of the \<^verbatim>\<open>path_identifier\<close> argument\<close>
  "_urust_temporary_path_identifier" :: \<open>path_identifier \<Rightarrow> urust_identifier\<close>
    ("_")

  \<comment> \<open>Unfortunately, we need to do a bit more work to support \<^verbatim>\<open>foo::bar.boo\<close>. The \<^verbatim>\<open>bar.boo\<close> is
      a \<^verbatim>\<open>longid\<close> that is the last argument of the implicit list of type \<^verbatim>\<open>path_identifier_long\<close>.\<close>
  "_path_builder_two_longid" :: \<open>id \<Rightarrow> longid \<Rightarrow> path_identifier_long\<close>
    ("_':': _"[0,0]1000)
  "_path_builder_more_longid" :: \<open>id \<Rightarrow> path_identifier_long \<Rightarrow> path_identifier_long\<close>
    ("_':': _"[0,1000]1000)
  \<comment> \<open>Such \<^emph>\<open>long\<close> paths are not \<^verbatim>\<open>urust_identifier\<close>s: they indicate method or field accesses
      of a path. In other words, \<^verbatim>\<open>foo::bar.boo\<close> must be parsed as \<^verbatim>\<open>(foo::bar).boo\<close>. We
      add temporary clauses to the \<^verbatim>\<open>urust_callable\<close> and \<^verbatim>\<open>urust\<close> grammar, and remove them
      with parse AST translations.\<close>
  "_urust_temporary_path_identifier_long_method" :: \<open>path_identifier_long \<Rightarrow> urust_callable\<close>
    ("_")
  "_urust_temporary_path_identifier_long_field" :: \<open>path_identifier_long \<Rightarrow> urust\<close>
    ("_")

text\<open>When the AST is initially built, we get a \<^verbatim>\<open>_urust_temporary_path_identifier\<close> with a
\<^verbatim>\<open>path_identifier\<close> argument. We will convert that argument to a \<^verbatim>\<open>string_token\<close>, which makes it
easier to parse that in a later stage to a term. That means we must turn the
\<^verbatim>\<open>_urust_temporary_path_identifier\<close> into a \<^verbatim>\<open>_urust_path_string_identifier\<close>\<close>
parse_ast_translation\<open>
  let
    fun path_arg_to_rust_name
        (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_path_builder_two_id\<close>, Ast.Variable secondlast, Ast.Variable last]) =
            secondlast ^ "::" ^ last
      | path_arg_to_rust_name
        (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_path_builder_more\<close>, Ast.Variable head, tail]) =
            head ^ "::" ^ path_arg_to_rust_name tail;
    fun path_translator grammar_el ctx args =
      let
        val rust_name = path_arg_to_rust_name (hd args);
      in
        Ast.mk_appl (Ast.Constant grammar_el) [Ast.Constant rust_name]
      end
      | path_translator grammar_el _ args =
          Ast.mk_appl (Ast.Constant grammar_el) args;
  in [
    (\<^syntax_const>\<open>_urust_temporary_path_identifier\<close>, path_translator \<^syntax_const>\<open>_urust_path_string_identifier\<close>)
  ]end
\<close>

text\<open>We take the same approach for \<^verbatim>\<open>_urust_temporary_path_identifier_long_{field,method}\<close>, but now
need to split the last identifier at the dots. Unfortunately, we cannot rely on AST parse
translations possibly happening again and taking care of things, but need to manually invoke the
same steps done for splitting longid's.\<close>
parse_ast_translation\<open>
  let
    \<comment> \<open>Split \<^verbatim>\<open>foo.bar.zoo\<close> into \<^verbatim>\<open>("foo", ["bar", "zoo"])\<close>\<close>
    fun split_longid longid_el =
      let
        val parts = split_long_identifier longid_el
      in
        (hd parts, tl parts)
      end;

    \<comment> \<open>Split the \<^verbatim>\<open>_path_builder\<close> syntax representation of \<^verbatim>\<open>foo::bar.zoo.far\<close> into \<^verbatim>\<open>("foo::bar", ["zoo", "far"])\<close>\<close>
    fun split_path_n_field 
      (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_path_builder_two_longid\<close>, Ast.Variable secondlast, last]) =
        let 
          val (tailhead, tailtail) = split_longid last
        in
          (secondlast ^ "::" ^ tailhead, tailtail)
        end
      | split_path_n_field
        (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_path_builder_more_longid\<close>, Ast.Variable head, tail]) =
        let
          val (path, field) = split_path_n_field tail
        in
          (head ^ "::" ^ path, field)
        end;

    \<comment> \<open>Convert a string \<^verbatim>\<open>"foo::bar"\<close> into a uRust grammar entry\<close>
    fun urust_path_string_to_identifier arg =
      Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_path_string_identifier\<close>) [Ast.Constant arg];

    \<comment> \<open>Convert the argument of syntax type \<^verbatim>\<open>_path_identifier_long\<close> into its path string and
        field/method accesses, then use the \<^verbatim>\<open>ast_joiner\<close> argument to turn it into a urust grammar
        entry. The 'syntax type' of \<^verbatim>\<open>ast_joiner\<close> is \<^verbatim>\<open>urust \<rightarrow> urust_identifier list \<rightarrow> urust\<close>.\<close>
    fun path_translator grammar_el (ast_joiner: Ast.ast -> Ast.ast list -> Ast.ast) ctx [arg] =
      let
        val (path, field) = split_path_n_field arg
      in
        ast_joiner
          (path |> urust_path_string_to_identifier |> ast_urust_identifier)
          (field |> map ast_urust_identifier_id)
      end
      | path_translator grammar_el _ _ args =
          Ast.mk_appl (Ast.Constant grammar_el) args;
  in [
    (\<^syntax_const>\<open>_urust_temporary_path_identifier_long_field\<close>,
      path_translator \<^syntax_const>\<open>_urust_temporary_path_identifier_long_field\<close> long_id_field_access_into_urust),
    (\<^syntax_const>\<open>_urust_temporary_path_identifier_long_method\<close>,
      path_translator \<^syntax_const>\<open>_urust_temporary_path_identifier_long_method\<close> long_id_struct_access_into_callable)
  ] end
\<close>

text\<open>Now we add an AST translation that converts \<^verbatim>\<open>_urust_temporary_match\<close> to the appropriate type
of match, i.e. \<^verbatim>\<open>match_case\<close> or \<^verbatim>\<open>match_select\<close>s.\<close>
parse_ast_translation\<open>
  let
    \<comment> \<open>Get the head constants of an AST node\<close>
    fun pattern_ast_to_head_const (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match_pattern_grouped\<close>, pat]) =
          pattern_ast_to_head_const pat
      | pattern_ast_to_head_const (Ast.Appl (Ast.Constant c :: tl)) = c
      | pattern_ast_to_head_const (Ast.Constant c) = c
      | pattern_ast_to_head_const _ = \<^syntax_const>\<open>_urust_match_pattern_other\<close>

    \<comment> \<open>Get the list of patterns from a \<^verbatim>\<open>_urust_match2\<close> node in the AST\<close>
    fun branches_ast_to_pattern_list (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match2\<close>, left, right]) =
          branches_ast_to_pattern_list left @ branches_ast_to_pattern_list right
      | branches_ast_to_pattern_list (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match1\<close>, clause, _]) =
          [pattern_ast_to_head_const clause]
      | branches_ast_to_pattern_list (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match1_guard\<close>, clause, _, _]) =
          [pattern_ast_to_head_const clause]
      | branches_ast_to_pattern_list _ = []

    \<comment> \<open>Detect guards in match branches\<close>
    fun branches_ast_has_guard (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match2\<close>, left, right]) =
          branches_ast_has_guard left orelse branches_ast_has_guard right
      | branches_ast_has_guard (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_urust_match1_guard\<close>, _, _, _]) = true
      | branches_ast_has_guard _ = false

    \<comment> \<open>Is this pattern valid in a \<^verbatim>\<open>match_case\<close>?\<close>
    fun pat_is_match_case pat =
      pat <> \<^syntax_const>\<open>_urust_match_pattern_num_const\<close> andalso
      pat <> \<^syntax_const>\<open>_urust_match_pattern_zero\<close> andalso
      pat <> \<^syntax_const>\<open>_urust_match_pattern_one\<close>

    \<comment> \<open>Is this pattern valid in a \<^verbatim>\<open>match_switch\<close>?\<close>
    fun pat_is_match_switch pat =
      (pat = \<^syntax_const>\<open>_urust_match_pattern_num_const\<close>)
      orelse (pat = \<^syntax_const>\<open>_urust_match_pattern_constr_no_args\<close>)
      orelse (pat = \<^syntax_const>\<open>_urust_match_pattern_other\<close>)
      orelse (pat = \<^syntax_const>\<open>_urust_match_pattern_zero\<close>)
      orelse (pat = \<^syntax_const>\<open>_urust_match_pattern_one\<close>)

    \<comment> \<open>Determine whether a temporary match should become \<^verbatim>\<open>match_case\<close> or \<^verbatim>\<open>match_switch\<close>.\<close>
    fun match_selector_hd branches =
      let
        val patterns = branches_ast_to_pattern_list branches
        val has_guard = branches_ast_has_guard branches
        val is_match_case = has_guard orelse (patterns |> List.all pat_is_match_case)
        val is_match_select = (not has_guard) andalso (patterns |> List.all pat_is_match_switch)
      in
        (
          \<comment> \<open>Note that we default to \<^verbatim>\<open>is_match_case\<close>! If you explicitly want your match to be
              parsed as a switch statement, use \<^verbatim>\<open>match_switch {...}\<close>\<close>
          if is_match_case then \<^syntax_const>\<open>_urust_match_case\<close>
          else (if is_match_select then \<^syntax_const>\<open>_urust_match_switch\<close>
          else
            \<comment> \<open>User wrote down a mixed 'illegal' match. We thus do not know how to change the
               AST in a meaningful way, and keep it as is.
               The problem is now that this will give a very poor error message, so add some logging\<close>
            let
              val _ = writeln "Error: detected match with mixed numeral and constructors" 
            in
              \<^syntax_const>\<open>_urust_temporary_match\<close>
            end
          )
        )
      end

    \<comment> \<open>Replace a \<^verbatim>\<open>_urust_temporary_match\<close> AST node with arguments \<^verbatim>\<open>[arg, branches]\<close> with the
        appropriate match AST node\<close>
    fun match_selector _ [arg, branches] =
      Ast.mk_appl (Ast.Constant (match_selector_hd branches)) [arg, branches]
      | match_selector _ args =
          Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_temporary_match\<close>) args

    \<comment> \<open>Semicolon-free statement form: \<^verbatim>\<open>match ... { ... } next\<close> desugars to sequencing after
        first disambiguating temporary match syntax.\<close>
    fun match_sequence_selector _ [arg, branches, next] =
      let
        val selected_match = Ast.mk_appl (Ast.Constant (match_selector_hd branches)) [arg, branches]
      in
        Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_sequence\<close>) [selected_match, next]
      end
      | match_sequence_selector _ args =
          Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_urust_sequence_temporary_match\<close>) args
  in [
    (\<^syntax_const>\<open>_urust_temporary_match\<close>, match_selector),
    (\<^syntax_const>\<open>_urust_sequence_temporary_match\<close>, match_sequence_selector)
  ] end
\<close>

(* At this point, parsing returns 'abstract' objects -- only after e.g. shallowly
embedding them, do we get actual HOL terms. The below \<^verbatim>\<open>experiment\<close>
nevertheless uses \<^verbatim>\<open>term\<close> to check what parsing produces,
which is useful for debugging purposes.

Of course, these calls fail, so they must be commented out when building. They
could come in handy when making changes to the uRust syntax in the future. *)
(*
experiment
  notes [[syntax_ast_trace]]
begin
term\<open>\<guillemotleft>foo.bar.boo.far\<guillemotright>\<close>
term\<open>\<guillemotleft>foo.bar.boo(3)\<guillemotright>\<close>
term\<open>\<guillemotleft>(foo).bar.boo\<guillemotright>\<close>
term\<open>\<guillemotleft>foo::bar\<guillemotright>\<close>
term\<open>\<guillemotleft>foo::bar::zoo.boo.far\<guillemotright>\<close>
term\<open>\<guillemotleft>foo::bar.boo(3)\<guillemotright>\<close>
term\<open>\<guillemotleft>match 3 {
a \<Rightarrow> 2,
2 \<Rightarrow> 6,
0 \<Rightarrow> 7,
1 \<Rightarrow> 8,
_ \<Rightarrow> 7
}\<guillemotright>\<close>
end
*)

(*<*)
end
(*>*)
