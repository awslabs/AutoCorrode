(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Simple_C_Functions
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Micro_Rust_Std_Lib.StdLib_All"
begin

section \<open>First End-to-End C Verification Example\<close>

text \<open>
  This theory demonstrates end-to-end verification of C source code using
  AutoCorrode. The pipeline is:
  \<^enum> Parse C source via @{text micro_c_translate} to produce HOL definitions
  \<^enum> Define a separation-logic contract
  \<^enum> Prove the contract using @{text crush_boot} and @{text crush_base}
\<close>

subsection \<open>Locale Setup\<close>

text \<open>
  The locale provides the reference infrastructure: allocation, dereference,
  and update operations with their separation-logic specifications.
  This is the same boilerplate as the Rust examples.
\<close>

locale c_verification_ctx =
    reference reference_types +
    ref_int: reference_allocatable reference_types _ _ _ _ _ _ _ int_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
    and int_prism :: \<open>('gv, int) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_int.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

subsection \<open>C Swap Function\<close>

text \<open>Parse the C swap function.\<close>
micro_c_translate \<open>
void swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}
\<close>

thm c_swap_def

text \<open>
  The contract for swap: given two disjoint references with values
  @{text lval} and @{text rval}, after swap the references hold each
  other's original values.
\<close>
definition c_swap_contract ::
    \<open>('addr, 'gv, int) Global_Store.ref \<Rightarrow> ('addr, 'gv, int) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> 'gv \<Rightarrow> int \<Rightarrow> int \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>c_swap_contract lref rref lg rg lval rval \<equiv>
    let pre  = can_alloc_reference \<star>
               lref \<mapsto>\<langle>\<top>\<rangle> lg\<down>lval \<star> rref \<mapsto>\<langle>\<top>\<rangle> rg\<down>rval in
    let post = \<lambda> _.
               can_alloc_reference \<star>
               lref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. rval) \<sqdot> (lg\<down>lval) \<star>
               rref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. lval) \<sqdot> (rg\<down>rval) in
    make_function_contract pre post\<close>
ucincl_auto c_swap_contract

text \<open>Prove that the C swap function satisfies its contract.\<close>
lemma c_swap_spec:
  shows \<open>\<Gamma>; c_swap lref rref \<Turnstile>\<^sub>F c_swap_contract lref rref lg rg lval rval\<close>
  apply (crush_boot f: c_swap_def contract: c_swap_contract_def)
  apply crush_base
  done

subsection \<open>C Max Function\<close>

text \<open>A simple function exercising conditionals and return.\<close>
micro_c_translate \<open>
int max(int a, int b) {
  if (a > b) return a;
  else return b;
}
\<close>

thm c_max_def

definition c_max_contract ::
    \<open>int \<Rightarrow> int \<Rightarrow> ('s::{sepalg}, int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = Orderings.max a b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_max_contract

lemma c_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_max a b \<Turnstile>\<^sub>F c_max_contract a b\<close>
  apply (crush_boot f: c_max_def contract: c_max_contract_def)
  apply (crush_base simp add: max_def)
  done

subsection \<open>C Abs Function\<close>

micro_c_translate \<open>
int abs_val(int x) {
  if (x > 0) return x;
  else return 0 - x;
}
\<close>

thm c_abs_val_def

definition c_abs_val_contract ::
    \<open>int \<Rightarrow> ('s::{sepalg}, int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_abs_val_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = abs x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_abs_val_contract

lemma c_abs_val_spec [crush_specs]:
  shows \<open>\<Gamma>; c_abs_val x \<Turnstile>\<^sub>F c_abs_val_contract x\<close>
  apply (crush_boot f: c_abs_val_def contract: c_abs_val_contract_def)
  apply (crush_base simp add: abs_if)
  done

end

end
