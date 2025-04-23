(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Core_Syntax
  imports Core_Expression Rust_Iterator Result_Type Numeric_Types Option_Type
    Range_Type Bool_Type Global_Store
begin
(*>*)

section\<open>Syntax \& Semantics of shallowly embedded Micro Rust\<close>

text\<open>This section defines the core syntax and semantics of shallowly embedded Micro Rust.
While most syntax is directly bound to a semantic constant, we use \<^text>\<open>syntax\<close>
and \<^text>\<open>translations\<close> exclusively, rather than \<^text>\<open>consts\<close>, to allow
for a uniform treatment of all syntax and semantics.

While we try to keep the look-and-feel of shallowly embedded Micro Rust close to real Rust,
we have to use slightly deviating syntax for peaceful coexistence with HOL.\<close>

\<comment>\<open>Hanno: Having syntax and semantics in a single place
will also simplify the introduction of abstract syntax and potentially a deep embedding of Micro Rust.\<close>

subsection\<open>Syntax\<close>

subsubsection\<open>Conditionals\<close>
syntax
  "_urust_shallow_two_armed_conditional"
     :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
         ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
    ("if _ \<lbrace>_\<rbrace> else \<lbrace>_\<rbrace>" [20,0,0]11)
  "_urust_shallow_one_armed_conditional"
     :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
         ('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
    ("if _ \<lbrace> _ \<rbrace>" [20,0]11)

subsubsection\<open>Bindings\<close>
syntax
  "_urust_shallow_let_in"
    :: \<open>id \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
    ("let/ (_)/ =/ (_);/ (_)" [1000,20,10]10)

subsubsection\<open>Sequencing\<close>
syntax
  "_urust_shallow_sequence"
    \<comment> \<open>TODO: constrain the types\<close>
    :: \<open>('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
    ("/ _/ ;/ _/ "[11,10]10)

subsubsection\<open>Loops\<close>
syntax
  "_urust_shallow_for_loop"
    :: \<open>'a \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
    ("for (_) in (_) \<lbrace> (_) \<rbrace>" [20,100,0]11)

  "_urust_shallow_range"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c range\<close>
    ("\<langle>_\<dots>_\<rangle>" [166,166]166)

  "_urust_shallow_range_eq"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c range\<close>
    ("\<langle>_\<dots>=_\<rangle>" [166,166]166)

subsubsection\<open>Function application\<close>
nonterminal urust_shallow_args
syntax
  "_urust_shallow_args_single"
    :: \<open>logic \<Rightarrow> urust_shallow_args\<close>
    ("_")
  "_urust_shallow_args_app"
    :: \<open>logic \<Rightarrow> urust_shallow_args \<Rightarrow> urust_shallow_args\<close>
    ("_,/ _")
  "_urust_shallow_fun_with_args"
    :: \<open>logic \<Rightarrow> urust_shallow_args \<Rightarrow> logic\<close>
    ("_/ \<langle>_\<rangle>"[999,999]999)
  "_urust_shallow_fun_no_args"
    :: \<open>logic \<Rightarrow> logic\<close>
    ("_/ \<langle> \<rangle>"[999]999)

subsubsection\<open>Structured access\<close>
syntax
  "_urust_method_call_no_args"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
    ("/ _/ \<cdot>/ _/ \<langle> \<rangle>" [899,899]899)
  "_urust_method_call_with_args"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> urust_shallow_args \<Rightarrow> 'c\<close>
    ("/ _/ \<cdot>/ _/ \<langle>_\<rangle>" [899,899,0]899)

  "_urust_shallow_field_access"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
    ("_\<bullet>_" [899,1000]899)

  "_urust_shallow_index"
    :: \<open>'a \<Rightarrow> 'idx \<Rightarrow> 'b\<close>
    ("_/ '_'[(_)']" [899,0]899)

subsubsection\<open>Scoping\<close>
syntax
  "_urust_shallow_scope"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    ("\<lbrace>(_)\<rbrace>" [0]1000)

subsubsection\<open>Literals\<close>
syntax
  "_urust_shallow_literal"
    :: \<open>'v \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    ("\<up>_" [900]900)

subsubsection\<open>Boolean expressions\<close>
syntax
  "_urust_shallow_bool_true"
    :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    ("`True")
  "_urust_shallow_bool_false"
    :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    ("`False")
  "_urust_shallow_negation"
    :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    ("!\<^sub>\<mu>_" [300]300)
  "_urust_shallow_bool_conjunction"
    :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    (infixr "&&\<^sub>\<mu>" 50)
  "_urust_shallow_bool_disjunction"
    :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    (infixr "||\<^sub>\<mu>" 50)
  "_urust_shallow_equality"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "==\<^sub>\<mu>" 48)
  "_urust_shallow_nonequality"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "!=\<^sub>\<mu>" 48)
  "_urust_shallow_bool_le"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
    (infix "\<le>\<^sub>\<mu>" 49)
  "_urust_shallow_bool_lt"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
    (infix "<\<^sub>\<mu>" 49)
  "_urust_shallow_bool_ge"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
    (infix "\<ge>\<^sub>\<mu>" 49)
  "_urust_shallow_bool_gt"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
    (infix ">\<^sub>\<mu>" 49)
  "_urust_shallow_add"
    :: \<open>('s, 'v :: plus, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "+\<^sub>\<mu>" 49)
  "_urust_shallow_minus"
    :: \<open>('s, 'v :: minus, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "-\<^sub>\<mu>" 49)
  "_urust_shallow_mul"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "*\<^sub>\<mu>" 49)
  "_urust_shallow_div"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "'/\<^sub>\<mu>" 49)
  "_urust_shallow_mod"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    (infix "%\<^sub>\<mu>" 49)

subsubsection\<open>Pattern matching\<close>

nonterminal urust_shallow_match_branch \<comment> \<open>A single branch of a match statement\<close>
nonterminal urust_shallow_match_branches \<comment> \<open>Comma-separate lists of match branches\<close>
nonterminal urust_shallow_match_pattern
nonterminal urust_shallow_match_pattern_arg
nonterminal urust_shallow_match_pattern_args

syntax
  "_urust_shallow_match" :: "[('s, 'v, 'r, 'abort, 'i, 'o) expression, urust_shallow_match_branches] \<Rightarrow> ('sp, 'vp, 'rp, 'abort, 'i, 'o) expression"  ("match (_) \<lbrace>/ _/ \<rbrace>" [20, 20]20)
  \<comment>\<open>Basic case branches\<close>
  "_urust_shallow_match1" :: "[urust_shallow_match_pattern, 'b] \<Rightarrow> urust_shallow_match_branches"  ("(2_ \<Rightarrow>/ _)" [100, 20] 21)
  "_urust_shallow_match2" :: "[urust_shallow_match_branches, urust_shallow_match_branches] \<Rightarrow> urust_shallow_match_branches"  ("_/, _" [21, 20]20)
  \<comment>\<open>Basic case patterns, restricted to constructor identifiers followed by a potentially empty list of argument identifiers\<close>
  "_urust_shallow_match_pattern_other" :: \<open>urust_shallow_match_pattern\<close>
    ("'_")
  "_urust_shallow_match_pattern_constr_no_args" :: \<open>logic \<Rightarrow> urust_shallow_match_pattern\<close>
    ("\<guillemotleft>_\<guillemotright>")
  "_urust_shallow_match_pattern_constr_with_args" :: \<open>logic \<Rightarrow> urust_shallow_match_pattern_args \<Rightarrow> urust_shallow_match_pattern\<close>
    ("\<guillemotleft>_\<guillemotright> '(_')"[0,100]100)
  "_urust_shallow_match_pattern_arg_id" :: \<open>id \<Rightarrow> urust_shallow_match_pattern_arg\<close>
    ("_")
  "_urust_shallow_match_pattern_arg_dummy" :: \<open>urust_shallow_match_pattern_arg\<close>
    ("'_")
  "_urust_shallow_match_pattern_args_single" :: \<open>urust_shallow_match_pattern_arg \<Rightarrow> urust_shallow_match_pattern_args\<close>
    ("_")
  "_urust_shallow_match_pattern_args_app" :: \<open>urust_shallow_match_pattern_arg \<Rightarrow> urust_shallow_match_pattern_args \<Rightarrow> urust_shallow_match_pattern_args\<close>
    ("_ _"[1000,100]100)

syntax
  "_urust_shallow_return"
    :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'r, 'r, 'abort, 'i, 'o) expression\<close>
    ("return _" [20]20)
  "_urust_shallow_if_let_else"
    :: \<open>urust_shallow_match_pattern   \<Rightarrow>
              ('s, 'w, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
    ("if let _ = (_) \<lbrace> (_) \<rbrace> else \<lbrace> (_) \<rbrace>" [100,20,0,0]11)
  "_urust_shallow_if_let"
    :: \<open>urust_shallow_match_pattern   \<Rightarrow>
              ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'b, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'unit, 'r, 'abort, 'i, 'o) expression\<close>
    ("if let _ = (_) \<lbrace> (_) \<rbrace>" [20,20,0]11)
  "_urust_shallow_let_else"
    :: \<open>urust_shallow_match_pattern \<Rightarrow>
              ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'w, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
              ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
    ("let _ = (_) else \<lbrace> (_) \<rbrace> ; (_)" [100,20,0,10]10)

subsection \<open>Error propagation\<close>
syntax
  "_urust_shallow_propagate"
  :: \<open>('s,'a,'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s,'b,'r, 'abort, 'i, 'o) expression\<close>
  ("_'?")

subsubsection\<open>Unit, option and result type constructors\<close>
syntax
  "_urust_shallow_unit_unit"
    :: \<open>('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
    ("`\<langle>\<rangle>")
  "_urust_shallow_option_none"
    :: \<open>('s, 'v option, 'r, 'abort, 'i, 'o) expression\<close>
    ("`None")
  "_urust_shallow_option_some"
    :: \<open>'v \<Rightarrow> ('s, 'v option, 'r, 'abort, 'i, 'o) expression\<close>
    ("`Some (_)" [100]100)
  "_urust_shallow_result_ok"
    :: \<open>'v \<Rightarrow> ('s, 'e + 'v, 'r, 'abort, 'i, 'o) expression\<close>
    ("`Ok (_)" [100]100)
  "_urust_shallow_result_err"
    :: \<open>'v \<Rightarrow> ('s, 'e + 'v, 'r, 'abort, 'i, 'o) expression\<close>
    ("`Err (_)" [100]100)

subsubsection\<open>Global store\<close>
syntax
  "_urust_shallow_store_update"
    :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
    ("\<star>_ \<leftarrow> (_)" [100,20]15)
  "_urust_shallow_store_ref_new"
    :: \<open>('s, ('a, 'b, 'v) ref, 'abort, 'i, 'o) function_body\<close>
    ("Ref::new")
  "_urust_shallow_store_dereference"
    :: \<open>'a \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>
    ("\<^sup>\<star>_" [200]200)

subsubsection\<open>Bitwise expressions\<close>
syntax
   "_urust_shallow_word_shift_left"  :: \<open>('s, 'l0 word, 64 word, 'l0 word, 'r, 'abort, 'i, 'o) urust_binop3\<close> (infixr "<<\<^sub>\<mu>" 54)
   "_urust_shallow_word_shift_right" :: \<open>('s, 'l0 word, 64 word, 'l0 word, 'r, 'abort, 'i, 'o) urust_binop3\<close> (infixr ">>\<^sub>\<mu>" 54)
   "_urust_shallow_word_bitwise_or"  :: \<open>('s, 'l word, 'r, 'abort, 'i, 'o) urust_binop\<close> (infixr "|\<^sub>\<mu>" 54)
   "_urust_shallow_word_bitwise_xor" :: \<open>('s, 'l word, 'r, 'abort, 'i, 'o) urust_binop\<close> (infixr "^\<^sub>\<mu>" 54)
   "_urust_shallow_word_bitwise_and" :: \<open>('s, 'l word, 'r, 'abort, 'i, 'o) urust_binop\<close> (infixr "&\<^sub>\<mu>" 54)

subsubsection\<open>Assignment-oriented expressions\<close>
syntax
   "_urust_shallow_word_assign_or"
     :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
     (infix "|=\<^sub>\<mu>" 52)
   "_urust_shallow_word_assign_xor"
     :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
     (infix "^=\<^sub>\<mu>" 52)
   "_urust_shallow_word_assign_and"
     :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
     (infix "&=\<^sub>\<mu>" 52)
   "_urust_shallow_assign_add"
     :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
     (infix "+=\<^sub>\<mu>" 52)

subsection\<open>Special notation for HOL identifiers\<close>

nonterminal urust_hol_identifier
syntax
   "_urust_hol_id_u64_from_u16" :: \<open>urust_hol_identifier\<close> ("u64::from\<^sub>u\<^sub>1\<^sub>6")

subsection\<open>Semantics\<close>

text\<open>We now give meaning to the syntax for shallowly embedded Micro Rust defined above.
Most of the time, we directly bind the corresponding grammar production to the respective
HOL constant via \<^text>\<open>translations\<close>. For overloaded syntrax such as \<^text>\<open>expect\<close>, we map
the syntax to an undefined generic constant, and use adhoc-overloading for type-based dispatch.\<close>

consts
  unwrap :: \<open>'a \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
  expect :: \<open>'a \<Rightarrow> String.literal \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
  store_update_const :: \<open>('a, 'b, 'v) ref \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  store_reference_const :: \<open>'v \<Rightarrow> ('s, ('a, 'b, 'v) ref, 'abort, 'i, 'o) function_body\<close>
  store_dereference_const :: \<open>'a \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>
  index_const :: \<open>'a \<Rightarrow> 'idx \<Rightarrow> ('s,'b, 'abort, 'i, 'o) function_body\<close>
  negation_const :: \<open>('s,'v,'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s,'v,'c, 'abort, 'i, 'o) expression\<close>
  propagate_const :: \<open>('s,'v,'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s,'w,'c, 'abort, 'i, 'o) expression\<close>
  assign_add_const :: \<open>('a, 'b, 'v) ref \<Rightarrow> 'w \<Rightarrow> ('s,unit, 'abort, 'i, 'o) function_body\<close>

syntax
  "_urust_shallow_match_convert_branches" :: \<open>urust_shallow_match_branches \<Rightarrow> case_basic_branches\<close>
  "_urust_shallow_match_convert_branch" :: \<open>urust_shallow_match_branch \<Rightarrow> case_basic_branch\<close>
  "_urust_shallow_match_convert_pattern" :: \<open>urust_shallow_match_pattern \<Rightarrow> case_basic_pattern\<close>
  "_urust_shallow_match_convert_args" :: \<open>urust_shallow_match_pattern_args \<Rightarrow> case_basic_pattern_args\<close>
  "_urust_shallow_match_convert_arg" :: \<open>urust_shallow_match_pattern_arg \<Rightarrow> case_basic_pattern_arg\<close>
  "_anonymous_var" :: \<open>logic\<close>
  "_anonymous_case" :: \<open>logic \<Rightarrow> logic\<close>

translations
  \<comment>\<open>Conditionals\<close>
  "_urust_shallow_two_armed_conditional test this that"
    \<rightleftharpoons> "CONST two_armed_conditional test this that"
  "_urust_shallow_one_armed_conditional test this"
    \<rightleftharpoons> "(CONST one_armed_conditional test this)"
  "_urust_shallow_if_let_else ptrn exp this that"
    \<rightleftharpoons> "_urust_shallow_match exp
                             (_urust_shallow_match2
                                (_urust_shallow_match1 ptrn this)
                                (_urust_shallow_match1 _urust_shallow_match_pattern_other that))"
  "_urust_shallow_if_let ptrn exp this"
    \<rightleftharpoons> "_urust_shallow_match exp
                             (_urust_shallow_match2
                                (_urust_shallow_match1 ptrn this)
                                (_urust_shallow_match1 _urust_shallow_match_pattern_other (CONST skip)))"

  "_urust_shallow_let_else ptrn exp that after"
    \<rightleftharpoons> "_urust_shallow_match exp
                             (_urust_shallow_match2
                                (_urust_shallow_match1 ptrn after)
                                (_urust_shallow_match1 _urust_shallow_match_pattern_other that))"

  \<comment>\<open>Let bindings\<close>
  "_urust_shallow_let_in x exp cont"
    \<rightleftharpoons> "CONST bind exp (\<lambda>x. cont)"

  \<comment>\<open>Loops\<close>
  "_urust_shallow_for_loop i xs body"
    \<rightleftharpoons> "CONST for_loop (CONST funcall1 (CONST into_iter) xs) (\<lambda>i. body)"

  \<comment> \<open>Ranges\<close>
  "_urust_shallow_range lower upper"
    \<rightleftharpoons> "CONST funcall2 (CONST range_new) lower upper"
  "_urust_shallow_range_eq lower upper"
    \<rightleftharpoons> "CONST funcall2 (CONST range_eq_new) lower upper"

  \<comment> \<open>Indexing\<close>
  "_urust_shallow_index exp idx"
    \<rightharpoonup> "CONST funcall2 (CONST index_const) exp idx"
  \<comment>\<open>Boolean expressions\<close>
  "_urust_shallow_bool_true"
    \<rightleftharpoons> "CONST true"
  "_urust_shallow_bool_false"
    \<rightleftharpoons> "CONST false"
  "_urust_shallow_negation e"
    \<rightleftharpoons> "CONST negation_const e"
  "_urust_shallow_bool_conjunction a b"
    \<rightleftharpoons> "CONST urust_conj a b"
  "_urust_shallow_bool_disjunction a b"
    \<rightleftharpoons> "CONST urust_disj a b"

  "_urust_shallow_bool_le a b"
    \<rightleftharpoons> "(CONST comp_le) a b"
  "_urust_shallow_bool_lt a b"
    \<rightleftharpoons> "(CONST comp_lt) a b"
  "_urust_shallow_bool_ge a b"
    \<rightleftharpoons> "(CONST comp_ge) a b"
  "_urust_shallow_bool_gt a b"
    \<rightleftharpoons> "(CONST comp_gt) a b"
  "_urust_shallow_field_access obj attr"
    \<rightleftharpoons> "(CONST bindlift1) (CONST focus_lens_const attr) obj"

  \<comment>\<open>Equality\<close>
  "_urust_shallow_equality a b"
    \<rightleftharpoons> "CONST urust_eq a b"
  "_urust_shallow_nonequality a b"
    \<rightleftharpoons> "CONST urust_neq a b"

  \<comment>\<open>Lifting HOL values\<close>
  "_urust_shallow_literal v"
    \<rightleftharpoons> "CONST literal v"

  \<comment>\<open>Sequencing, scoping, returning ...\<close>
  "_urust_shallow_scope e"
    \<rightleftharpoons> "CONST scoped e"
  "_urust_shallow_sequence a b"
    \<rightleftharpoons> "CONST sequence a b"
  "_urust_shallow_unit_unit"
    \<rightleftharpoons> "CONST skip"
  "_urust_shallow_return exp"
    \<rightleftharpoons> "(CONST return_func) exp"

  \<comment>\<open>Option type\<close>
  "_urust_shallow_option_some v"
    \<rightleftharpoons> "CONST Option_Type.some v"
  "_urust_shallow_option_none"
    \<rightleftharpoons> "CONST Option_Type.none"
  \<comment>\<open>Result type\<close>
  "_urust_shallow_result_ok v"
    \<rightleftharpoons> "CONST Result_Type.ok v"
  "_urust_shallow_result_err e"
    \<rightleftharpoons> "CONST Result_Type.err e"

  \<comment> \<open>Error propagation\<close>
  "_urust_shallow_propagate x"
    \<rightleftharpoons> "CONST propagate_const x"

  \<comment>\<open>References\<close>
  "_urust_shallow_store_update x y"
    \<rightleftharpoons> "CONST bind2 (CONST call_deep2 (CONST store_update_const)) x y"
  "_urust_shallow_store_ref_new"
    \<rightleftharpoons> "CONST store_reference_const"
  "_urust_shallow_store_dereference ptr"
    \<rightleftharpoons> "(CONST bind) ptr (CONST call_deep1 (CONST store_dereference_const))"
  "_urust_shallow_word_assign_or ptr assign"
    \<rightharpoonup> "_urust_shallow_store_update ptr (_urust_shallow_word_bitwise_or (_urust_shallow_store_dereference ptr) assign)"
  "_urust_shallow_word_assign_xor ptr assign"
    \<rightharpoonup> "_urust_shallow_store_update ptr (_urust_shallow_word_bitwise_xor (_urust_shallow_store_dereference ptr) assign)"
  "_urust_shallow_word_assign_and ptr assign"
    \<rightharpoonup> "_urust_shallow_store_update ptr (_urust_shallow_word_bitwise_and (_urust_shallow_store_dereference ptr) assign)"
  "_urust_shallow_assign_add ptr assign"
    \<rightharpoonup> "CONST funcall2 (CONST assign_add_const) ptr assign"

  \<comment>\<open>Function call syntax for up to 8 arguments. Add more if needed\<close>
  "_urust_shallow_fun_no_args func"
    \<rightleftharpoons> "CONST funcall0 func"
  "_urust_shallow_fun_with_args func (_urust_shallow_args_single a0)"
    \<rightleftharpoons> "CONST funcall1 func a0"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_single a1))"
    \<rightleftharpoons> "CONST funcall2 func a0 a1"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1 (_urust_shallow_args_single a2)))"
    \<rightleftharpoons> "CONST funcall3 func a0 a1 a2"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_single a3))))"
    \<rightleftharpoons> "CONST funcall4 func a0 a1 a2 a3"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_app a3
       (_urust_shallow_args_single a4)))))"
    \<rightleftharpoons> "CONST funcall5 func a0 a1 a2 a3 a4"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_app a3
       (_urust_shallow_args_app a4 (_urust_shallow_args_single a5))))))"
    \<rightleftharpoons> "CONST funcall6 func a0 a1 a2 a3 a4 a5"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_app a3
       (_urust_shallow_args_app a4 (_urust_shallow_args_app a5
       (_urust_shallow_args_single a6)))))))"
    \<rightleftharpoons> "CONST funcall7 func a0 a1 a2 a3 a4 a5 a6"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_app a3
       (_urust_shallow_args_app a4 (_urust_shallow_args_app a5
       (_urust_shallow_args_app a6 (_urust_shallow_args_single a7))))))))"
    \<rightleftharpoons> "CONST funcall8 func a0 a1 a2 a3 a4 a5 a6 a7"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_app a3
       (_urust_shallow_args_app a4 (_urust_shallow_args_app a5
       (_urust_shallow_args_app a6 (_urust_shallow_args_app a7
       (_urust_shallow_args_single a8)))))))))"
    \<rightleftharpoons> "CONST funcall9 func a0 a1 a2 a3 a4 a5 a6 a7 a8"
  "_urust_shallow_fun_with_args func
       (_urust_shallow_args_app a0 (_urust_shallow_args_app a1
       (_urust_shallow_args_app a2 (_urust_shallow_args_app a3
       (_urust_shallow_args_app a4 (_urust_shallow_args_app a5
       (_urust_shallow_args_app a6 (_urust_shallow_args_app a7
       (_urust_shallow_args_app a8 (_urust_shallow_args_single a9))))))))))"
    \<rightleftharpoons> "CONST funcall10 func a0 a1 a2 a3 a4 a5 a6 a7 a8 a9"

  \<comment>\<open>These rules decompose method calls into calls using explicit self arguments.
     The translation is one-way; otherwise it fires for basically all functions.\<close>
  "_urust_method_call_no_args self method"
    \<rightharpoonup> "_urust_shallow_fun_with_args method (_urust_shallow_args_single self)"
  "_urust_method_call_with_args self method args"
    \<rightharpoonup> "_urust_shallow_fun_with_args method (_urust_shallow_args_app self args)"

  \<comment>\<open>Bitwise expressions\<close>
  "_urust_shallow_word_shift_left a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_shift_left_shift64 a b"
  "_urust_shallow_word_shift_right a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_shift_right_shift64 a b"
  "_urust_shallow_word_bitwise_xor a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_bitwise_xor a b"
  "_urust_shallow_word_bitwise_or a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_bitwise_or a b"
  "_urust_shallow_word_bitwise_and a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_bitwise_and a b"

  \<comment>\<open>Arithmetic expressions\<close>
  "_urust_shallow_add a b"
    \<rightleftharpoons> "CONST urust_add a b"
  "_urust_shallow_minus a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_minus_no_wrap a b"
  "_urust_shallow_mul a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_mul_no_wrap a b"
  "_urust_shallow_div a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_udiv a b"
  "_urust_shallow_mod a b"
    \<rightleftharpoons> "CONST Numeric_Types.word_umod a b"

   "_urust_hol_id_u64_from_u16" \<rightleftharpoons> "CONST Numeric_Types.u64_from_u16"

text\<open>We turn to the semantics of \<^text>\<open>match\<close> expressions. We essentially want to replace \<^text>\<open>match exp { body }\<close> with a bind of \<^text>\<open>exp\<close>
and a normal \<^text>\<open>case\<close> expression. Unfortunately, since there is no anonymou \<^text>\<open>case\<close> expression in HOL, we have to find a fresh variable for this,
but at this stage of parsing, we have no canonical choice. We thus introduce a dummy syntax construction for anonymous case expressions and convert them
into a lambda over a HOL-case at the "parse translation" stage (that is, when we move from AST to terms).\<close>

translations
  "_urust_shallow_match exp branches"
    \<rightharpoonup> "(CONST bind) exp (_anonymous_case (_case_basic_syntax _anonymous_var (_urust_shallow_match_convert_branches branches)))"
  "_urust_shallow_match_convert_branches (_urust_shallow_match1 pattern exp)"
    \<rightharpoonup> "_case_basic1 (_urust_shallow_match_convert_pattern pattern) exp"
  "_urust_shallow_match_convert_branches (_urust_shallow_match2 b0 b1)"
    \<rightharpoonup> "_case_basic2 (_urust_shallow_match_convert_branches b0) (_urust_shallow_match_convert_branches b1)"

  "_urust_shallow_match_convert_pattern _urust_shallow_match_pattern_other"
    \<rightharpoonup> "_case_basic_pattern_other"
  "_urust_shallow_match_convert_pattern (_urust_shallow_match_pattern_constr_no_args id)"
    \<rightharpoonup> "_case_basic_pattern_constr_no_args id"
  "_urust_shallow_match_convert_pattern (_urust_shallow_match_pattern_constr_with_args id args)"
    \<rightharpoonup> "_case_basic_pattern_constr_with_args id (_urust_shallow_match_convert_args args)"

  "_urust_shallow_match_convert_args (_urust_shallow_match_pattern_args_single arg)"
    \<rightharpoonup> "_case_basic_pattern_args_single (_urust_shallow_match_convert_arg arg)"
  "_urust_shallow_match_convert_args (_urust_shallow_match_pattern_args_app a as)"
    \<rightharpoonup> "_case_basic_pattern_args_app (_urust_shallow_match_convert_arg a) (_urust_shallow_match_convert_args as)"

  "_urust_shallow_match_convert_arg (_urust_shallow_match_pattern_arg_id id)"
    \<rightharpoonup> "_case_basic_pattern_arg_id id"
  "_urust_shallow_match_convert_arg (_urust_shallow_match_pattern_arg_dummy)"
    \<rightharpoonup> "_case_basic_pattern_arg_dummy"

\<comment>\<open>todo: add print translation for this so the case expressions remain readable\<close>
parse_translation\<open>
let fun anonymous_case_tr _
     \<comment>\<open>Identify dummy variable in case expression and replace it with a freshly bound variable in
a lambda abstraction\<close>
     [(c as Const (\<^const_syntax>\<open>case_guard\<close>, ty0))
         $ guard
         $ (Const ("_anonymous_var",_))
         $ case_body] =
     Abs ("anon_case",
          dummyT, c $ guard $ (Bound 0) $ case_body)
in
  [(\<^syntax_const>\<open>_anonymous_case\<close>, anonymous_case_tr)]
end
\<close>

section\<open>Syntactic support for \<^emph>\<open>expect\<close> and friends\<close>

text\<open>The \<^verbatim>\<open>?\<close> operator is used to propagate error conditions directly
to the return values of functions. This adhoc overloading allows the propagation
operator to be used at option and result types.\<close>
adhoc_overloading propagate_const \<rightleftharpoons> propagate_option propagate_result

subsection\<open>Unary negation operator\<close>
text\<open>Rust uses the same tm\<open>!\<close> operator for both boolean and bitwise negation.
We use adhoc overloading here to resolve the distinction via types.\<close>

adhoc_overloading negation_const \<rightleftharpoons> negation Numeric_Types.word_bitwise_not

subsection \<open>Index syntax support\<close>

adhoc_overloading index_const \<rightleftharpoons>
  list_index array_index vector_index list_index_range array_index_range vector_index_range

subsection\<open>Manipulating and querying 'structures'\<close>

text\<open>This section introduces syntax which gives the manipulation of structured data in uRust the same
look-and-feel as in Rust: Fields are accessed via \<^text>\<open>struct\<cdot>attr\<close>, which is just syntactic sugar for
\<^text>\<open>attr \<langle>struct\<rangle>\<close>. To leverage, 'attributes' must be defined as functions
of type \<^typ>\<open>'struct \<Rightarrow> ('s, 'value_type, 'r, 'abort, 'i, 'o) expression\<close>. The same notation works for member \<^emph>\<open>functions\<close>,
which are of type \<^text>\<open>'struct \<Rightarrow> 'arg0 \<Rightarrow> \<dots> \<Rightarrow> 'argn \<Rightarrow> 's, 'value_type, 'r, 'abort, 'i, 'o) expression\<close>. This in fact
mimicks the way member functions are defined in Rust itself, taking a \<^text>\<open>self\<close> argument.

If there are multiple structures using the same name for an attribute or member function, an uninterpreted
constant can be introduced under the respective name, and overloaded depending on the type of the 'structure'
that's being accessed. This is reminiscent of compile-time dispatch of member functions, which also relies on
type information.\<close>

(*<*)

\<comment>\<open>Some tests\<close>

context
  fixes attr :: \<open>('struct::localizable,'val) lens\<close>
  fixes func  :: \<open>'struct \<Rightarrow> 'arg0 \<Rightarrow> ('s, 'val, 'abort, 'i, 'o) function_body\<close>
  fixes s :: 'struct
  fixes v :: 'arg0
  fixes e :: \<open>('s, 'arg0, 'r, 'abort, 'i, 'o) expression\<close>
begin
term\<open>(\<up>s)\<bullet>attr\<close>
term\<open>\<up>s\<cdot>func\<langle>\<up>v\<rangle>\<close>

term\<open>match true \<lbrace> \<guillemotleft>True\<guillemotright> \<Rightarrow> \<up>False, \<guillemotleft>False\<guillemotright> \<Rightarrow> \<up>True \<rbrace>\<close>
end

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, 'abort, 'i, 'o) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, 'abort, 'i, 'o) function_body\<close>
begin
term\<open>g \<langle>\<up>c\<rangle>\<close>
term\<open>g \<langle>(\<up>c)\<rangle>\<close>
term\<open>f \<langle>\<up>a,\<up>b\<rangle>\<close>
term\<open>f \<langle>g\<langle>\<up>c\<rangle>, \<up>b\<rangle>\<close>
end

context
  fixes x :: \<open>nat\<close>
  fixes y :: \<open>nat\<close>
  fixes cb :: \<open>('a, 'b, 'abort, 'i, 'o) function_body\<close>
  fixes getter :: \<open>nat \<Rightarrow> ('a, 'b, 'abort, 'i, 'o) function_body\<close>
  fixes test :: \<open>nat \<Rightarrow> nat \<Rightarrow>  ('a, 'b, 'abort, 'i, 'o) function_body\<close>
begin
term \<open>cb\<langle>\<rangle>\<close>
term \<open>\<up>x\<cdot>test \<langle>\<up>y\<rangle>\<close>
term \<open>\<up>x\<cdot>getter\<langle>\<rangle>\<close>
term \<open>getter\<langle>\<up>x\<rangle>\<close>
end

term\<open>skip\<close>

\<comment>\<open>We have a clash of notation between ranges and function application -- fix this\<close>
term\<open>
  let b = \<up>42;
  skip
\<close>

term \<open>
  let b = `\<langle>\<rangle>;
  skip
\<close>

context
  fixes msg :: \<open>String.literal\<close>
  fixes oog :: \<open>String.literal\<close>
  fixes oof :: \<open>String.literal\<close>
  fixes aah :: \<open>String.literal\<close>
  fixes foo :: \<open>('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
begin

value[nbe]\<open>
  skip; skip
\<close>

term\<open>
  match (panic msg) \<lbrace>
    \<guillemotleft>Some\<guillemotright>(_) \<Rightarrow> \<lbrace> panic oof; skip \<rbrace>,
    _ \<Rightarrow> skip
  \<rbrace>;

  if let \<guillemotleft>Some\<guillemotright>(a) = (panic msg) \<lbrace>
    panic oof
  \<rbrace> ;
  true
\<close>

term\<open>
  let x = \<up>0x1;
  let y = \<up>(0x0::64 word);

  if let \<guillemotleft>Some\<guillemotright>(a) = panic msg \<lbrace>
    panic oof
  \<rbrace>;
  let z = \<up>(x + y);
  let y = a;
  skip
\<close>

value\<open>
  let x = \<up>(0x1 :: 64 word);
  let y = \<up>(0x0::64 word);

  (if let \<guillemotleft>Some\<guillemotright>(x) = panic msg \<lbrace>
    panic oog
  \<rbrace>);

  let z = \<up>(x + y);
  let v = `Some \<up>(0::64 word);
  let z = \<up>v\<cdot>unwrap\<langle>\<rangle>;
  skip
\<close>

value[simp]\<open>
  let \<guillemotleft>Some\<guillemotright>(f) = `Some \<up>(0::nat) else \<lbrace>
    return `None
  \<rbrace>;
  return `None
\<close>

value[simp]\<open>
  (if let \<guillemotleft>Some\<guillemotright>(f) = `Some \<up>(0::nat) \<lbrace>
    panic (String.implode ''oh oh'')
  \<rbrace>);
  skip;
  return `\<langle>\<rangle>
\<close>

value [nbe] \<open>evaluate ((return (\<up>True) ; skip)::(unit, unit, bool, 'abort, 'i, 'o) expression) ()\<close>
value [nbe] \<open>evaluate ((panic msg; skip)::(unit, unit, bool, 'abort, 'i, 'o) expression) ()\<close>
value [nbe] \<open>evaluate ((skip ; skip)::(unit, unit, bool, 'abort, 'i, 'o) expression) ()\<close>
value [nbe] \<open>evaluate ((skip ; skip ; panic msg)::(unit, unit, bool, 'abort, 'i, 'o) expression) ()\<close>

value[simp]\<open>let x = panic msg; skip\<close>
value[simp]\<open>let x = f; let y = g; \<up>(x + y)\<close>

value\<open>
  let x = \<up>0x1;
  let y = \<up>(0x0::64 word);

  skip;
  panic oof
\<close>

context
  fixes x::nat and y::nat
begin
  term\<open>\<up>x \<le>\<^sub>\<mu> \<up>y\<close>
  term\<open>\<up>x \<ge>\<^sub>\<mu> \<up>y\<close>
  term\<open>\<up>x >\<^sub>\<mu> \<up>y\<close>
  term\<open>\<up>x <\<^sub>\<mu> \<up>y\<close>
  term\<open>\<up>(0x0::nat)\<close>
  term\<open>(\<up>x \<le>\<^sub>\<mu> \<up>y); true\<close>
end

value\<open>evaluate ((\<up>(0x2::nat) \<le>\<^sub>\<mu> \<up>0x1)::(unit, bool, unit, unit, unit, unit) expression) ()\<close>

value\<open>
  let x = \<up>0x1;
  let y = \<up>(0x0::64 word);

  if \<up>(x \<le> y) \<lbrace>
    panic oof;
    panic aah
  \<rbrace>;

  let z = \<up>(x + y);

  assert(\<up>(x = 0x0))
\<close>

value\<open>
  let x = \<up>0x1;
  let y = \<up>(0x0::64 word);

  if \<up>(x \<le> y) \<lbrace>
    panic oof;
    panic aah
  \<rbrace>;

  if panic msg \<lbrace>
    assert(\<up>False);
    assert(\<up>True)
  \<rbrace>;

  let z = \<up>(x + y);
  assert(\<up>(x = 0x0))
\<close>

term\<open>\<up>12 <<\<^sub>\<mu> \<up>42\<close>
term\<open>\<up>12 >>\<^sub>\<mu> \<up>42\<close>
term\<open>\<up>12 &\<^sub>\<mu> \<up>42\<close>
term\<open>\<up>12 |\<^sub>\<mu> \<up>42\<close>
term\<open>\<up>12 ^\<^sub>\<mu> \<up>42\<close>
term\<open>\<up>1 <<\<^sub>\<mu> (\<up>8 >>\<^sub>\<mu> \<up>2)\<close>
term\<open>\<up>1 &\<^sub>\<mu> (\<up>8 >>\<^sub>\<mu> \<up>2)\<close>

value[simp]\<open>
  skip; skip
\<close>

value[simp]\<open>
  \<lbrace>skip\<rbrace>; skip
\<close>


value[simp]\<open>
  (one_armed_conditional true skip); skip
\<close>

value[simp]\<open>
  if let \<guillemotleft>Ok\<guillemotright>(s) = panic msg \<lbrace> skip \<rbrace>
\<close>

value[simp]\<open>
  if let \<guillemotleft>Ok\<guillemotright>(s) = panic msg \<lbrace>
     skip
  \<rbrace>; skip
\<close>

term\<open>\<lambda>(v :: ('s, ('v,'e) result, 'r, 'abort, 'i, 'o) expression).
  v\<cdot>result_expect\<langle>\<up>(String.implode ''oh my!'')\<rangle>
\<close>

context
  fixes r :: \<open>('s, 'r, 'r, 'abort, 'i, 'o) expression\<close> and e :: \<open>String.literal\<close>
begin
term \<open>\<lbrace>
  match true \<lbrace>
    \<guillemotleft>True\<guillemotright> \<Rightarrow> false,
    \<guillemotleft>False\<guillemotright> \<Rightarrow> true \<rbrace>
\<rbrace>\<close>
end

context
  fixes r :: \<open>('s, bool option, 'r, 'abort, 'i, 'o) expression\<close> and e :: \<open>String.literal\<close>
begin
term\<open>
  match r \<lbrace>
    \<guillemotleft>None\<guillemotright> \<Rightarrow> \<lbrace>
      false
    \<rbrace>,
    \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> true
  \<rbrace>
\<close>

term\<open>
  match r \<lbrace>
    \<guillemotleft>None\<guillemotright> \<Rightarrow> \<lbrace>
      let anon_case = r;
      match \<up>anon_case \<lbrace>
         \<guillemotleft>None\<guillemotright> \<Rightarrow> \<up>(case anon_case of _ \<Rightarrow> False),
         \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> false
      \<rbrace>
    \<rbrace>,
    \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> true
  \<rbrace>
\<close>

term\<open>
  \<up>42 +\<^sub>\<mu> \<up>42
\<close>

term\<open>
\<lbrace>
  match r \<lbrace>
    \<guillemotleft>None\<guillemotright> \<Rightarrow> \<lbrace>
      if panic e \<lbrace>
        skip
      \<rbrace>;
      true
    \<rbrace>,
    \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> \<up>s
  \<rbrace>
\<rbrace> = \<lbrace>
  let r = r;
  match (\<up>r) \<lbrace>
    \<guillemotleft>None\<guillemotright> \<Rightarrow> \<lbrace>
      let y = panic e;
      if \<up>y \<lbrace>
        skip
      \<rbrace>;
      true
    \<rbrace>,
    \<guillemotleft>Some\<guillemotright>(s) \<Rightarrow> \<up>s
  \<rbrace>
\<rbrace>\<close>
end

term\<open>
  match x \<lbrace>
    \<guillemotleft>Ok\<guillemotright>(y) \<Rightarrow> \<up>y,
    \<guillemotleft>Err\<guillemotright>(e) \<Rightarrow> \<lbrace> return \<up>e \<rbrace>
   \<rbrace>\<close>

value\<open>
  let \<guillemotleft>Err\<guillemotright>(e) = `Ok (\<up>()) else \<lbrace>
    panic oof
  \<rbrace>;
  \<up>e
\<close>

term \<open>
  let x = Ref::new\<langle>\<up>42\<rangle>;
  \<up>x +=\<^sub>\<mu> \<up>12
\<close>

(*>*)
end

(*<*)
end
(*>*)
