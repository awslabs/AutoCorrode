(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Tutorial
  imports
    Micro_Rust_Std_Lib.StdLib_All
begin

section\<open>Verifying \<mu>Rust programs with AutoCorrode\<close>

text\<open>Welcome! In this tutorial you will verify small \<mu>Rust programs using AutoCorrode's
automation. Each exercise is self-contained. The key tools you will use:

\<^item> \<^verbatim>\<open>crush_boot f: ... contract: ...\<close> -- unfolds the function and contract, sets up a
  weakest-precondition goal
\<^item> \<^verbatim>\<open>crush_base\<close> -- runs the automation to discharge the goal\<close>

subsection\<open>Bounded Vector Record\<close>

text\<open>Exercises 5--6 use a simplified bounded vector, modelled as a record with a length
field and an array of optional values. You can skip this until you get to these exercises.\<close>

declare [[typedef_overloaded]]

datatype_record ('a, 'l) bounded_vec =
  bvec_len    :: \<open>64 word\<close>
  bvec_values :: \<open>('a option, 'l) array\<close> \<comment>\<open>use None to represent an "uninitialized value"\<close>
micro_rust_record bounded_vec

definition bvec_abs :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> 'a list\<close> where
  \<open>bvec_abs v \<equiv> List.map_filter (array_nth (bvec_values v)) [0 ..< unat (bvec_len v)]\<close>

definition bvec_well_formed :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> bool\<close> where
  \<open>bvec_well_formed v \<equiv> unat (bvec_len v) \<le> LENGTH('l) \<and>
    (\<forall>i < unat (bvec_len v). array_nth (bvec_values v) i \<noteq> None)\<close>

text\<open>The following locale is boilerplate that makes types like \<^typ>\<open>nat\<close> and \<^typ>\<open>bool\<close>
available as mutable references. You can ignore its details.\<close>
locale tutorial_ctx =
    reference reference_types +
    ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism +
    ref_bool: reference_allocatable reference_types _ _ _ _ _ _ _ bool_prism
  for
  reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and nat_prism :: \<open>('gv, nat) prism\<close>
  and bool_prism :: \<open>('gv, bool) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_bool.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun


section\<open>Exercise 1: Hello Crush (warm-up)\<close>

text\<open>This function clamps a value \<^term>\<open>x\<close> to the range \<^term>\<open>[lo, hi]\<close>.
The contract and function are given. Your task: write the proof.\<close>

definition clamp :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>clamp lo hi x \<equiv> FunctionBody \<lbrakk>
    if (x < lo) {
      lo
    } else {
      if (x > hi) {
        hi
      } else {
        x
      }
    }
  \<rbrakk>\<close>

definition clamp_contract where
  \<open>clamp_contract lo hi x \<equiv>
    let pre  = \<langle>lo \<le> hi\<rangle> in
    let post = \<lambda>r. \<langle>r \<ge> lo \<and> r \<le> hi\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto clamp_contract

text\<open>TODO: Replace \<^verbatim>\<open>oops\<close> with a proof.
Hint: \<^verbatim>\<open>apply (crush_boot f:clamp_def contract: clamp_contract_def)\<close> sets up the goal
      \<^verbatim>\<open>apply (crush_base)\<close> discharges it.)\<close>
lemma clamp_spec:
  shows \<open>\<Gamma>; clamp lo hi x \<Turnstile>\<^sub>F clamp_contract lo hi x\<close>
  oops


section\<open>Exercise 2: Write the Contract\<close>

text\<open>This function returns the maximum of two natural numbers.
The function is given. Your task: strengthen the postcondition and prove the spec.\<close>

definition max_of :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>max_of a b \<equiv> FunctionBody \<lbrakk>
    if (b > a) {
      b
    } else {
      a
    }
  \<rbrakk>\<close>

text\<open>TODO: Strengthen the postcondition.
Hint: Isabelle has a built-in \<^term>\<open>max\<close> function.\<close>
value \<open>max (0::nat) (1::nat)\<close>

definition max_of_contract where
  \<open>max_of_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto max_of_contract

text\<open>TODO: Prove the specification once your contract is correct.\<close>
lemma max_of_spec:
  shows \<open>\<Gamma>; max_of a b \<Turnstile>\<^sub>F max_of_contract a b\<close>
  oops

text\<open>Bonus: prove the specification manually, without \<^verbatim>\<open>crush_base\<close>.
Hints:
\<^item> \<^verbatim>\<open>wp_two_armed_conditionalI\<close> splits the goal on the if-condition
\<^item> \<^verbatim>\<open>wp_literalI\<close> evaluates a literal/pure expression\<close>
thm wp_two_armed_conditionalI
thm wp_literalI
text \<open>After that, the following separation logic simplifications may be helpful\<close>
thm asepconj_pure_UNIV
thm asepconj_False_True
thm aentails_refl
thm asepconj_UNIV_idempotent

lemma max_of_spec_manual:
  shows \<open>\<Gamma>; max_of a b \<Turnstile>\<^sub>F max_of_contract a b\<close>
  oops

section\<open>Exercise 3: Mutable State\<close>

text\<open>This function computes the absolute difference of two natural numbers
using a local mutable variable. Note the use of \<^verbatim>\<open>let mut\<close> and dereferencing with \<^verbatim>\<open>*\<close>.

Because we allocate a mutable reference, the precondition must include
\<^term>\<open>can_alloc_reference\<close> (the capability to allocate). The postcondition
should return this capability (we are done with the reference) along with
a pure fact about the result.\<close>

definition abs_diff :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>abs_diff a b \<equiv> FunctionBody \<lbrakk>
    let mut result = \<llangle>0 :: nat\<rrangle>;
    if (a > b) {
      result = \<llangle>a - b\<rrangle>;
    } else {
      result = \<llangle>b - a\<rrangle>;
    };
    *result
  \<rbrakk>\<close>

text\<open>TODO: Write the contract\<close>
definition abs_diff_contract where
  \<open>abs_diff_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto abs_diff_contract

text\<open>TODO: Prove the specification.\<close>
lemma abs_diff_spec:
  shows \<open>\<Gamma>; abs_diff a b \<Turnstile>\<^sub>F abs_diff_contract a b\<close>
  oops

section\<open>Exercise 4: Modular Verification\<close>

text\<open>In this exercise, a helper function \<^term>\<open>double\<close> is already verified.
Your task: write and verify a \<^term>\<open>quadruple\<close> function that calls \<^term>\<open>double\<close> twice,
\<^emph>\<open>without\<close> re-verifying \<^term>\<open>double\<close> from scratch.

This demonstrates modular verification: you reuse the specification of a
callee rather than inlining its implementation.\<close>

definition double :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>double n \<equiv> FunctionBody \<lbrakk>
    \<llangle>n + n\<rrangle>
  \<rbrakk>\<close>

definition double_contract where
  \<open>double_contract n \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = 2 * n\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto double_contract

lemma double_spec:
  shows \<open>\<Gamma>; double n \<Turnstile>\<^sub>F double_contract n\<close>
  apply (crush_boot f: double_def contract: double_contract_def)
  apply crush_base
  done

text\<open>TODO: Define \<^term>\<open>quadruple\<close> using \<^term>\<open>double\<close>\<close>
definition quadruple :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>quadruple n \<equiv> FunctionBody \<lbrakk>
    undefined
  \<rbrakk>\<close>

text\<open>TODO: Write the contract for \<^term>\<open>quadruple\<close>.\<close>
definition quadruple_contract where
  \<open>quadruple_contract n \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto quadruple_contract

text\<open>TODO: Prove the specification using \<^term>\<open>double_spec\<close>.
Hint: use \<^verbatim>\<open>specs add: double_spec\<close> and \<^verbatim>\<open>contracts add: double_contract_def\<close>
as arguments to \<^verbatim>\<open>crush_base\<close>.\<close>
lemma quadruple_spec:
  shows \<open>\<Gamma>; quadruple n \<Turnstile>\<^sub>F quadruple_contract n\<close>
  oops

section\<open>Exercise 5: Data Structures and Abstraction Functions\<close>

text\<open>Real verified code relates low-level data (arrays, machine words) to
high-level mathematical objects (lists, natural numbers) via an \<^emph>\<open>abstraction function\<close>.

Above (before the locale) we defined \<^typ>\<open>('a, 'l) bounded_vec\<close> --- a record with
a length field \<^term>\<open>bvec_len\<close> and an array \<^term>\<open>bvec_values\<close> of optional values.
The abstraction function \<^term>\<open>bvec_abs\<close> extracts the logical list content,
and \<^term>\<open>bvec_well_formed\<close> asserts the invariant that all slots below the length are occupied.

The following functions use Rust-like field access syntax: \<^verbatim>\<open>v.bvec_len\<close>, \<^verbatim>\<open>v.bvec_values[idx]\<close>.\<close>

text\<open>This function checks whether the bounded vector is empty.\<close>
definition bvec_is_empty :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>bvec_is_empty v \<equiv> FunctionBody \<lbrakk> v.bvec_len == 0 \<rbrakk>\<close>

text\<open>TODO: Write the contract\<close>
definition bvec_is_empty_contract :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> ('s::sepalg, bool, 'b) function_contract\<close> where
  \<open>bvec_is_empty_contract v \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_is_empty_contract

text\<open>This lemma may be useful. TODO: Complete the proof\<close>
lemma bvec_is_empty:
  assumes \<open>bvec_well_formed v\<close>
    shows \<open>bvec_len v = 0 \<longleftrightarrow> bvec_abs v = []\<close>
  using assms oops

text\<open>TODO: Prove the specification.\<close>
lemma bvec_is_empty_spec:
  shows \<open>\<Gamma>; bvec_is_empty v \<Turnstile>\<^sub>F bvec_is_empty_contract v\<close>
  oops

section\<open>Exercise 6: Indexing a Data Structure (stretch)\<close>

text\<open>This function looks up an element in the bounded vector by index.\<close>

definition bvec_get :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> 64 word \<Rightarrow> ('s, 'a option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>bvec_get v idx \<equiv> FunctionBody \<lbrakk>
    if idx < v.bvec_len {
      return v.bvec_values[idx];
    }
    None
 \<rbrakk>\<close>

text\<open>TODO: Write the contract for the in-bound case.
Hints:
\<^item> Precondition: the vector is well-formed and the index is in bounds
  (\<^verbatim>\<open>unat idx < unat (bvec_len v)\<close>).
\<^item> Postcondition: the result is \<^verbatim>\<open>Some (bvec_abs v ! unat idx)\<close>.\<close>
definition bvec_get_contract :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> 64 word \<Rightarrow> ('s::sepalg, 'a option, 'b) function_contract\<close> where
  \<open>bvec_get_contract v idx \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_get_contract

text\<open>TODO: Prove the specification.\<close>
thm WordAdditional.lt_word_to_natI
lemma bvec_get_spec:
  shows \<open>\<Gamma>; bvec_get v idx \<Turnstile>\<^sub>F bvec_get_contract v idx\<close>
  oops

section\<open>Exercise 7: Searching with a Loop (stretch)\<close>

text\<open>This function searches the bounded vector for a given value, using a for-loop
with a mutable boolean accumulator. It combines mutable state, loops, and the
abstraction function. The implementation does not return early to make the loop
invariant simpler.\<close>

definition bvec_contains :: \<open>(nat, 'l::len) bounded_vec \<Rightarrow> nat \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>bvec_contains v needle \<equiv> FunctionBody \<lbrakk>
    let mut found = \<llangle>False\<rrangle>;
    for i in 0..v.bvec_len {
      if (v.bvec_values[i] == Some(needle)) {
        found = True;
      }
    };
    *found
  \<rbrakk>\<close>

definition bvec_contains_contract :: \<open>(nat, 'l::len) bounded_vec \<Rightarrow> nat \<Rightarrow> ('s::sepalg, bool, 'b) function_contract\<close> where
  \<open>bvec_contains_contract v needle \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>bvec_well_formed v\<rangle> \<star> \<langle>unat (bvec_len v) = LENGTH('l)\<rangle> in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>bvec_well_formed v\<rangle> \<star> \<langle>r \<longleftrightarrow> needle \<in> set (bvec_abs v)\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_contains_contract

text\<open>TODO: Write the loop invariant
Hints:
\<^item> \<^verbatim>\<open>List.map_filter (array_nth (bvec_values v)) [0..<i])\<close> gives the prefix of the vector up to element i\<close>
thm wp_raw_for_loop_framedI'
term \<open>(List.map_filter (array_nth (bvec_values v)) [0..<i])\<close>

lemma bvec_contains_spec:
  shows \<open>\<Gamma>; bvec_contains v needle \<Turnstile>\<^sub>F bvec_contains_contract v needle\<close>
proof (crush_boot f: bvec_contains_def contract: bvec_contains_contract_def, goal_cases)
  case 1
  moreover have \<open>unat (bvec_len v) < 2 ^ LENGTH(64)\<close>
    using More_Word.unat_lt2p[of \<open>bvec_len v\<close>] by simp
  ultimately show ?case
    apply crush_base
    subgoal for found_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. undefined\<close> and
          \<tau>=\<open>\<lambda>_. \<bottom>\<close> and
          \<theta>=\<open>\<lambda>_. \<bottom>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      oops


section\<open>Exercise 8: Mutating a Data Structure (stretch)\<close>

text\<open>So far, the bounded vector was passed by value. In this exercise, we take a
\<^emph>\<open>mutable reference\<close> to the vector and modify it in place.

The contract now uses \<^emph>\<open>points-to\<close> predicates: \<^verbatim>\<open>ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v\<close> says that \<^term>\<open>ptr\<close>
currently points to value \<^term>\<open>v\<close>. After mutation, we existentially quantify over the
new state: \<^verbatim>\<open>\<Squnion>g' v'. ptr \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>...\<rangle>\<close>.

This function clears the vector by setting its length to zero.\<close>

definition bvec_clear :: \<open>('addr, 'gv, (nat, 'l::len) bounded_vec) ref \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>bvec_clear self \<equiv> FunctionBody \<lbrakk>
    self.bvec_len = 0;
  \<rbrakk>\<close>

text\<open>TODO: Write the contract and prove the specification.
Hints:
\<^item> Precondition: \<^verbatim>\<open>ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>bvec_well_formed v\<rangle>\<close>
\<^item> Postcondition: the pointer still exists, the new value is well-formed and its
  abstract list is empty. Use \<^verbatim>\<open>\<Squnion>g' v'. ptr \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>...\<rangle>\<close>.
\<^item> For the proof, add \<^verbatim>\<open>micro_rust_record_simps\<close> to the simp set.\<close>
definition bvec_clear_contract :: \<open>(('addr, 'gv) gref, 'gv, (nat, 'l::len) bounded_vec) focused \<Rightarrow> 'gv \<Rightarrow> (nat, 'l) bounded_vec \<Rightarrow> ('s::sepalg, unit, 'abort) function_contract\<close> where
  \<open>bvec_clear_contract ptr g v \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>_. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_clear_contract

lemma bvec_clear_spec:
  shows \<open>\<Gamma>; bvec_clear ptr \<Turnstile>\<^sub>F bvec_clear_contract ptr g v\<close>
  oops

section\<open>Exercise 9: Push with Capacity Check (stretch)\<close>

text\<open>This exercise verifies a \<^verbatim>\<open>push\<close> operation on the bounded vector. It writes an
element at the current length position and increments the length --- but only if
there is capacity. Otherwise it returns an error.

The key design pattern here is \<^emph>\<open>two-layer specification\<close>:
\<^item> The contract specifies the \<^emph>\<open>raw record update\<close> (what crush can verify).
\<^item> A separate pure lemma (\<^term>\<open>bvec_push_result\<close>) connects the raw update to
  the abstract list.

This avoids mixing abstraction-function reasoning with separation-logic automation.\<close>

definition bvec_push :: \<open>('addr, 'gv, (nat, 'l::len) bounded_vec) ref \<Rightarrow> nat \<Rightarrow> ('s, (unit, nat) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>bvec_push self elem \<equiv> FunctionBody \<lbrakk>
    if *self.bvec_len < \<llangle>of_nat LENGTH('l) :: 64 word\<rrangle> {
      self.bvec_values[*self.bvec_len] = Some(elem);
      self.bvec_len = *self.bvec_len + 1;
      Ok(())
    } else {
      Err(elem)
    }
  \<rbrakk>\<close>

text\<open>TODO: Write the contract and prove the specification.
Hints:
\<^item> Precondition: \<^verbatim>\<open>ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat (bvec_len v) \<le> LENGTH('l)\<rangle> \<star> \<langle>LENGTH('l) < 2 ^ LENGTH(64)\<rangle>\<close>
\<^item> Ok postcondition: assert capacity wasn't full, and existentially quantify over
  the new global value, stating the pointer now holds the updated record:
  @{verbatim \<open>\<langle>unat (bvec_len v) < LENGTH('l)\<rangle> \<star>
  (\<Squnion>g'. ptr \<mapsto>\<langle>\<top>\<rangle> g'\<down>(make_bounded_vec (bvec_len v + 1)
    (array_update (bvec_values v) (unat (bvec_len v)) (Some elem))))\<close>}
\<^item> Err postcondition: capacity was full, error carries the element back, pointer unchanged.
\<^item> For the proof: \<^verbatim>\<open>crush_base simp add: unat_eq_of_nat word_le_nat_alt word_less_nat_alt unat_of_nat_len\<close>
  followed by \<^verbatim>\<open>cases v; simp add: nth_focus_array_components micro_rust_record_simps\<close>.\<close>
definition bvec_push_contract :: \<open>(('addr, 'gv) gref, 'gv, (nat, 'l::len) bounded_vec) focused \<Rightarrow> 'gv \<Rightarrow> (nat, 'l) bounded_vec \<Rightarrow> nat \<Rightarrow> ('s::sepalg, (unit, nat) result, 'abort) function_contract\<close> where
  \<open>bvec_push_contract ptr g v elem \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>_. \<langle>True\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_push_contract

lemma bvec_push_spec:
  shows \<open>\<Gamma>; bvec_push ptr elem \<Turnstile>\<^sub>F bvec_push_contract ptr g v elem\<close>
  oops

text\<open>Bonus: prove that the abstract list grew by one element.\<close>
lemma bvec_push_result:
  assumes \<open>bvec_well_formed v\<close>
      and \<open>unat (bvec_len v) < LENGTH('l)\<close>
      and \<open>LENGTH('l) < 2 ^ LENGTH(64)\<close>
    shows \<open>bvec_abs (make_bounded_vec (bvec_len v + 1)
             (array_update (bvec_values v) (unat (bvec_len v)) (Some elem)) :: (nat, 'l::len) bounded_vec)
           = bvec_abs v @ [elem]\<close>
  oops

section\<open>Solutions\<close>

paragraph\<open>Exercise 1\<close>
lemma clamp_spec_solution:
  shows \<open>\<Gamma>; clamp lo hi x \<Turnstile>\<^sub>F clamp_contract lo hi x\<close>
  apply (crush_boot f: clamp_def contract: clamp_contract_def)
  apply crush_base
  done

paragraph\<open>Exercise 2\<close>
definition max_of_contract_solution where
  \<open>max_of_contract_solution a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = max a b\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto max_of_contract_solution

lemma max_of_spec_solution:
  shows \<open>\<Gamma>; max_of a b \<Turnstile>\<^sub>F max_of_contract_solution a b\<close>
  apply (crush_boot f: max_of_def contract: max_of_contract_solution_def)
  apply crush_base
  done

lemma max_of_spec_manual_solution:
  shows \<open>\<Gamma>; max_of a b \<Turnstile>\<^sub>F max_of_contract_solution a b\<close>
  apply (crush_boot f: max_of_def contract: max_of_contract_solution_def)
  apply (intro wp_two_armed_conditionalI)
  apply (intro wp_literalI)
  apply (simp add: asepconj_False_True asepconj_UNIV_idempotent aentails_refl)
  apply (intro wp_literalI)
  apply (simp add: asepconj_False_True asepconj_UNIV_idempotent aentails_refl)
  done

paragraph\<open>Exercise 3\<close>
definition abs_diff_contract_solution where
  \<open>abs_diff_contract_solution a b \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (max a b) - (min a b)\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto abs_diff_contract_solution

lemma abs_diff_spec_solution:
  shows \<open>\<Gamma>; abs_diff a b \<Turnstile>\<^sub>F abs_diff_contract_solution a b\<close>
  apply (crush_boot f: abs_diff_def contract: abs_diff_contract_solution_def)
  apply crush_base
  done

paragraph\<open>Exercise 4\<close>
definition quadruple_solution :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>quadruple_solution n \<equiv> FunctionBody \<lbrakk>
    double(double(n))
  \<rbrakk>\<close>

definition quadruple_contract_solution where
  \<open>quadruple_contract_solution n \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = 4 * n\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto quadruple_contract_solution

lemma quadruple_spec_solution:
  shows \<open>\<Gamma>; quadruple_solution n \<Turnstile>\<^sub>F quadruple_contract_solution n\<close>
  apply (crush_boot f: quadruple_solution_def contract: quadruple_contract_solution_def)
  apply (crush_base specs add: double_spec contracts add: double_contract_def)
  done

paragraph\<open>Exercise 5\<close>
definition bvec_is_empty_contract_solution :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> ('s::sepalg, bool, 'b) function_contract\<close> where
  \<open>bvec_is_empty_contract_solution v \<equiv>
    let pre  = \<langle>bvec_well_formed v\<rangle> in
    let post = \<lambda>r. \<langle>bvec_well_formed v \<and> (r \<longleftrightarrow> bvec_abs v = [])\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_is_empty_contract_solution

lemma bvec_is_empty_solution:
  assumes \<open>bvec_well_formed v\<close>
    shows \<open>bvec_len v = 0 \<longleftrightarrow> bvec_abs v = []\<close>
  using assms by (simp add: bvec_well_formed_def bvec_abs_def map_filter_def unat_eq_zero)

lemma bvec_is_empty_spec_solution:
  shows \<open>\<Gamma>; bvec_is_empty v \<Turnstile>\<^sub>F bvec_is_empty_contract_solution v\<close>
  apply (crush_boot f: bvec_is_empty_def contract: bvec_is_empty_contract_solution_def)
  apply (crush_base simp add: bvec_abs_def bvec_well_formed_def map_filter_def unat_eq_zero)
  done

paragraph\<open>Exercise 6\<close>
definition bvec_get_contract_solution :: \<open>('a, 'l::len) bounded_vec \<Rightarrow> 64 word \<Rightarrow> ('s::sepalg, 'a option, 'b) function_contract\<close> where
  \<open>bvec_get_contract_solution v idx \<equiv>
    let pre  = \<langle>bvec_well_formed v\<rangle> \<star> \<langle>unat idx < unat (bvec_len v)\<rangle> in
    let post = \<lambda>r. \<langle>bvec_well_formed v\<rangle> \<star> \<langle>r = Some (bvec_abs v ! unat idx)\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_get_contract_solution

lemma bvec_get_spec_solution:
  shows \<open>\<Gamma>; bvec_get v idx \<Turnstile>\<^sub>F bvec_get_contract_solution v idx\<close>
  apply (crush_boot f: bvec_get_def contract: bvec_get_contract_solution_def)
  apply (crush_base simp add: bvec_abs_def bvec_well_formed_def map_filter_def)
  apply (simp add: WordAdditional.lt_word_to_natI)
  done

paragraph\<open>Exercise 7\<close>
lemma bvec_contains_spec_solution:
  shows \<open>\<Gamma>; bvec_contains v needle \<Turnstile>\<^sub>F bvec_contains_contract v needle\<close>
proof (crush_boot f: bvec_contains_def contract: bvec_contains_contract_def, goal_cases)
  case 1
  moreover note More_Word.unat_lt2p[of \<open>bvec_len v\<close>]
  ultimately show ?case
    apply crush_base
    subgoal for found_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. found_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(needle \<in> set (List.map_filter (array_nth (bvec_values v)) [0..<i]))\<close> and
          \<tau>=\<open>\<lambda>_. \<bottom>\<close> and
          \<theta>=\<open>\<lambda>_. \<bottom>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      apply (crush_base simp add: bvec_abs_def bvec_well_formed_def map_filter_def
             take_map take_upt More_Word.unat_of_nat_eq)
      apply fastforce
      done
  done
qed

paragraph\<open>Exercise 8\<close>
definition bvec_clear_contract_solution :: \<open>(('addr, 'gv) gref, 'gv, (nat, 'l::len) bounded_vec) focused \<Rightarrow> 'gv \<Rightarrow> (nat, 'l) bounded_vec \<Rightarrow> ('s::sepalg, unit, 'abort) function_contract\<close> where
  \<open>bvec_clear_contract_solution ptr g v \<equiv>
    let pre  = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>bvec_well_formed v\<rangle> in
    let post = \<lambda>_. \<Squnion>g' v'. ptr \<mapsto>\<langle>\<top>\<rangle> g'\<down>v' \<star> \<langle>bvec_well_formed v' \<and> bvec_abs v' = []\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto bvec_clear_contract_solution

lemma bvec_clear_spec_solution:
  shows \<open>\<Gamma>; bvec_clear ptr \<Turnstile>\<^sub>F bvec_clear_contract_solution ptr g v\<close>
  apply (crush_boot f: bvec_clear_def contract: bvec_clear_contract_solution_def)
  apply (crush_base simp add: bvec_abs_def bvec_well_formed_def micro_rust_record_simps)
  done

paragraph\<open>Exercise 9\<close>
definition bvec_push_contract_solution :: \<open>(('addr, 'gv) gref, 'gv, (nat, 'l::len) bounded_vec) focused \<Rightarrow> 'gv \<Rightarrow> (nat, 'l) bounded_vec \<Rightarrow> nat \<Rightarrow> ('s::sepalg, (unit, nat) result, 'abort) function_contract\<close> where
  \<open>bvec_push_contract_solution ptr g v elem \<equiv>
    let pre  = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star>
               \<langle>unat (bvec_len v) \<le> LENGTH('l)\<rangle> \<star> \<langle>LENGTH('l) < 2 ^ LENGTH(64)\<rangle> in
    let post = \<lambda>r. case r of
      Ok _ \<Rightarrow> \<langle>unat (bvec_len v) < LENGTH('l)\<rangle> \<star>
             (\<Squnion>g'. ptr \<mapsto>\<langle>\<top>\<rangle> g'\<down>(make_bounded_vec (bvec_len v + 1)
               (array_update (bvec_values v) (unat (bvec_len v)) (Some elem))))
    | Err e \<Rightarrow> \<langle>unat (bvec_len v) = LENGTH('l)\<rangle> \<star> \<langle>e = elem\<rangle> \<star>
               ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v in
    make_function_contract pre post\<close>
ucincl_proof bvec_push_contract_solution
  by (auto split!: result.splits intro: ucincl_intros)

lemma bvec_push_spec_solution:
  shows \<open>\<Gamma>; bvec_push ptr elem \<Turnstile>\<^sub>F bvec_push_contract_solution ptr g v elem\<close>
  apply (crush_boot f: bvec_push_def contract: bvec_push_contract_solution_def)
  apply (crush_base simp add: unat_eq_of_nat word_le_nat_alt word_less_nat_alt unat_of_nat_len)
  apply (cases v; simp add: nth_focus_array_components micro_rust_record_simps)
  done

lemma bvec_push_result_solution:
  assumes \<open>bvec_well_formed v\<close>
      and \<open>unat (bvec_len v) < LENGTH('l)\<close>
      and \<open>LENGTH('l) < 2 ^ LENGTH(64)\<close>
    shows \<open>bvec_abs (make_bounded_vec (bvec_len v + 1)
             (array_update (bvec_values v) (unat (bvec_len v)) (Some elem)) :: (nat, 'l::len) bounded_vec)
           = bvec_abs v @ [elem]\<close>
  using assms
  by (simp add: bvec_abs_def bvec_well_formed_def map_filter_def
       unat_word_ariths take_bit_nat_eq_self_iff array_nth_update upt_Suc_append
       filter_id_conv comp_def)

end
end
