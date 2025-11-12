(*<*)
theory Num_Case_Expression
  imports
    Main
    Misc.WordAdditional
begin
(*>*)

section\<open>Case expressions over numerals\<close>

text\<open>Unlike in languages such as Rust, we cannot do case splits on numeral types in native Isabelle.
We'd like to be able to do e.g.:
\<^verbatim>\<open>
term\<open>case (4 :: nat) of
  (2 :: nat) \<Rightarrow> True
| 4 \<Rightarrow> False\<close>\<close>
and
\<^verbatim>\<open>
term\<open>case (4 :: 64 word) of
  2 \<Rightarrow> True
| 4 \<Rightarrow> False\<close>
\<close>.

Besides being more readable than nesting if/else statements, this will also be helpful when
shallowly embedding \<mu>Rust in Isabelle, since Rust \<^emph>\<open>does\<close> support these kinds of matches.

This file constructs an \<^verbatim>\<open>ncase\<close> match statement, that does allow you to write the above\<close>

nonterminal case_num_pattern
nonterminal case_num_branch
nonterminal case_num_branches

syntax
  \<comment>\<open>Numeral case expressions\<close>
  "_case_num_syntax" :: "['a, case_num_branches] \<Rightarrow> 'b"  ("(ncase _ of/ _)" [20, 20]20)
  \<comment> \<open>We also add a 'functional' version of this, which turns out to be useful when parsing
      \<mu>Rust. This is because we have to first evaluate the argument before pattern matching,
      which will be parsed as a \<^verbatim>\<open>bind arg (pattern_match_function)\<close>. By having notation for
      the function, we don't need to introduce an anonymous lambda (which comes with its own problems)\<close>
  "_case_num_fun_syntax" :: "[case_num_branches] \<Rightarrow> 'b"  ("(ncase'_fun of/ _)" [20]20)
  \<comment>\<open>Numeral case branches\<close>
  "_case_num1" :: "[case_num_pattern, 'b] \<Rightarrow> case_num_branch"  ("(2_ \<Rightarrow>/ _)" [100, 20] 21)
  "_case_num2" :: "[case_num_branch, case_num_branches] \<Rightarrow> case_num_branches"  ("_/ | _" [21, 20]20)
  \<comment>\<open>Numeral case patterns\<close>
  "_case_num_pattern_other" :: \<open>case_num_pattern\<close>
    ("'_")
  "_case_num_pattern_numeral" :: \<open>num_const \<Rightarrow> case_num_pattern\<close>
    ("_" 100)
  \<comment> \<open>Turns out we need special branches to support matching on 0 and 1, since these are notations of their own\<close>
  "_case_num_pattern_zero" :: \<open>case_num_pattern\<close>
    ("0")
  "_case_num_pattern_one" :: \<open>case_num_pattern\<close>
    ("1")
  \<comment> \<open>Note: cannot take \<^verbatim>\<open>logic\<close> arguments, because that will conflict with the \<^verbatim>\<open>_\<close> defined above\<close>
  "_case_num_pattern_const" :: \<open>id \<Rightarrow> case_num_pattern\<close>
    ("_" 100)
  "_case_num_branch_as_branches" :: \<open>case_num_branch \<Rightarrow> case_num_branches\<close>
    ("_")

text\<open>Now we define the 'raw' function that such \<^verbatim>\<open>ncase\<close> statements will be parsed down to.\<close>
definition ncase_selector_raw :: \<open>('a option \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b\<close> where
  \<open>ncase_selector_raw cases arg \<equiv>
    case List.find (\<lambda> (ma, b). case ma of None \<Rightarrow> True | Some a \<Rightarrow> a = arg) cases of
      None \<Rightarrow> undefined
    | Some (ma, b) \<Rightarrow> b\<close>

definition \<open>ncase_selector \<equiv> ncase_selector_raw\<close>

lemmas ncase_def = ncase_selector_def
lemmas ncase_simps = ncase_selector_def ncase_selector_raw_def
text\<open>We have separate definitions so that users can more easily see what's going on underneath
the syntax. That is, \<^verbatim>\<open>ncase_selector\<close> should always be pretty printed as \<^verbatim>\<open>ncase _ of _\<close>,
but by unfolding @{thm ncase_def} you can see the raw clauses being operated on, without
reducing the entire \<^verbatim>\<open>ncase\<close> construct.\<close>

translations
  \<comment> \<open>Parse \<^verbatim>\<open>ncase arg of cases\<close> as \<^verbatim>\<open>(ncase_fun of cases) arg\<close>, print the other way around\<close>
  "_case_num_syntax arg cases" \<rightleftharpoons>
    "_case_num_fun_syntax cases arg"
  \<comment> \<open>The rest of the rules are \<^emph>\<open>just\<close> parsing rules, since we don't want e.g.
       \<^term>\<open>[(None, a)]\<close> to print as \<^verbatim>\<open>_ \<Rightarrow> a\<close>!\<close>
  "_case_num_fun_syntax cases" \<rightharpoonup>
    "CONST ncase_selector cases"
  "_case_num2 left right" \<rightharpoonup>
    "CONST Cons left right"
  "_case_num1 _case_num_pattern_other result" \<rightharpoonup>
    "CONST Pair (CONST None) result"
  "_case_num1 (_case_num_pattern_zero) result" \<rightharpoonup>
    "CONST Pair (CONST Some 0) result"
  "_case_num1 (_case_num_pattern_one) result" \<rightharpoonup>
    "CONST Pair (CONST Some 1) result"
  "_case_num1 (_case_num_pattern_numeral num) result" \<rightharpoonup>
    "CONST Pair (CONST Some (_Numeral num)) result"
  "_case_num1 (_case_num_pattern_const c) result" \<rightharpoonup>
    "CONST Pair (CONST Some c) result"
  "_case_num_branch_as_branches branch" \<rightharpoonup>
    "CONST Cons branch (CONST Nil)"

experiment
begin
definition twentyfive :: nat where \<open>twentyfive \<equiv> 25\<close>

term\<open>ncase (4 :: nat) of
  3 \<Rightarrow> True
| 4 \<Rightarrow> False
| twentyfive \<Rightarrow> False
| 0 \<Rightarrow> False
| 1 \<Rightarrow> False
| _ \<Rightarrow> True\<close>
\<comment> \<open>Prints as: 
\<^term>\<open>ncase_selector [(Some 3, True), (Some 4, False), (Some twentyfive, False), (None, True)] 4\<close>\<close>

term\<open>ncase_fun of
  3 \<Rightarrow> True
| 4 \<Rightarrow> False
| twentyfive \<Rightarrow> False
| 0 \<Rightarrow> False
| 1 \<Rightarrow> False
| _ \<Rightarrow> True\<close>
\<comment> \<open>Prints as: 
\<^term>\<open>ncase_selector [(Some 3, True), (Some 4, False), (Some twentyfive, False), (None, True)]\<close>\<close>
end


text\<open>We have the desired \<^verbatim>\<open>ncase\<close> - now we add pretty printing\<close>

nonterminal printing_only

syntax
  \<comment> \<open>Tag to print as a branch of a case expression\<close>
  "_case_print_tag" :: "logic \<Rightarrow> logic"
  \<comment> \<open>Tag that ensures arguments are printed as a branch\<close>
  "_case_print_tag_num" :: "logic \<Rightarrow> logic \<Rightarrow> printing_only" ("(2_ \<Rightarrow>/ _)")

translations
  \<comment> \<open>When printing, the \<^verbatim>\<open>_case_print_tag\<close> is pushed down and ensures things are printed as branches\<close>
  "_case_num_syntax arg (_case_print_tag cases)" <=
    "CONST ncase_selector cases arg"
  "_case_num_fun_syntax (_case_print_tag cases)" <=
    "CONST ncase_selector cases"
  "_case_num2 (_case_print_tag left) (_case_print_tag (CONST Cons right1 right2))" <=
    "_case_print_tag (CONST Cons left (CONST Cons right1 right2))"
  "_case_num_branch_as_branches (_case_print_tag left)" <=
    "_case_print_tag (CONST Cons left (CONST Nil))"
  "_case_num1 _case_num_pattern_other result" <=
    "_case_print_tag (CONST Pair (CONST None) result)"
  "_case_print_tag_num num result" <=
    "_case_print_tag (CONST Pair (CONST Some num) result)"
  "_case_num_branch_as_branches (_case_print_tag branch)" <=
    "_case_print_tag (_case_num_branch_as_branches branch)"

experiment
begin
definition twentyfive :: nat where \<open>twentyfive \<equiv> 25\<close>

term\<open>ncase (4 :: nat) of
  3 \<Rightarrow> True
| 4 \<Rightarrow> False
| twentyfive \<Rightarrow> True
| 0 \<Rightarrow> False
| 1 \<Rightarrow> False
| _ \<Rightarrow> True\<close>
\<comment> \<open>Prints as:
\<^term>\<open>ncase 4 of 3 \<Rightarrow> True | 4 \<Rightarrow> False | twentyfive \<Rightarrow> True | _ \<Rightarrow> True\<close>\<close>

term\<open>ncase_fun of
  3 \<Rightarrow> True
| 4 \<Rightarrow> False
| twentyfive \<Rightarrow> False
| 0 \<Rightarrow> False
| 1 \<Rightarrow> False
| _ \<Rightarrow> True\<close>
\<comment> \<open>Prints as: 
\<^term>\<open>ncase_fun of 3 \<Rightarrow> True | 4 \<Rightarrow> False | twentyfive \<Rightarrow> False | _ \<Rightarrow> True\<close>\<close>

\<comment> \<open>Showcasing simplification rules\<close>
lemma test1:
  shows \<open>(ncase (4 :: nat) of
          3 \<Rightarrow> True
        | 4 \<Rightarrow> False
        | 1 \<Rightarrow> True
        | 0 \<Rightarrow> False
        | _ \<Rightarrow> True) = False\<close>
  \<comment> \<open>Using @{thm ncase_def} will just get rid of the pretty syntax\<close>
  apply (simp add: ncase_def)
  apply (simp add: ncase_selector_raw_def)
  done

lemma test2:
  shows \<open>(ncase (4 :: nat) of
          4 \<Rightarrow> False
        | 3 \<Rightarrow> True
        | 0 \<Rightarrow> False
        | 1 \<Rightarrow> False
        | _ \<Rightarrow> True) = False\<close>
  \<comment> \<open>Using @{thm ncase_simps} will get rid of the syntax and simplify as expected\<close>
  by (simp add: ncase_simps)
end

(*<*)
end
(*>*)