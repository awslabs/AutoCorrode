(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Simple_C_Functions
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
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
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
    and c_int_prism :: \<open>('gv, c_int) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
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
    \<open>('addr, 'gv, c_int) Global_Store.ref \<Rightarrow> ('addr, 'gv, c_int) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> 'gv \<Rightarrow> c_int \<Rightarrow> c_int \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
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

text \<open>
  The contract for max uses signed comparison on words.
  The translated code uses @{const c_signed_less} which compares
  @{term "sint b < sint a"} (operands swapped for >).
\<close>
definition c_max_contract ::
    \<open>c_int \<Rightarrow> c_int \<Rightarrow> ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if sint b < sint a then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_max_contract

lemma c_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_max a b \<Turnstile>\<^sub>F c_max_contract a b\<close>
  apply (crush_boot f: c_max_def contract: c_max_contract_def)
  apply (crush_base simp add: c_signed_less_def)
  done

subsection \<open>C Abs Function\<close>

micro_c_translate \<open>
int abs_val(int x) {
  if (x > 0) return x;
  else return 0 - x;
}
\<close>

thm c_abs_val_def

text \<open>
  The abs function requires a no-overflow precondition: subtraction
  overflows when x is the minimum signed value. The precondition
  ensures the negation is safe.
\<close>
definition c_abs_val_contract ::
    \<open>c_int \<Rightarrow> ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_abs_val_contract x \<equiv>
    let pre  = \<langle>-(2^31 :: int) < sint x\<rangle>;
        post = \<lambda>r. \<langle>r = (if sint x > sint (0 :: c_int) then x else word_of_int (0 - sint x))\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_abs_val_contract

lemma c_abs_val_spec [crush_specs]:
  shows \<open>\<Gamma>; c_abs_val x \<Turnstile>\<^sub>F c_abs_val_contract x\<close>
  apply (crush_boot f: c_abs_val_def contract: c_abs_val_contract_def)
  apply (crush_base simp add: c_signed_less_def c_signed_sub_def c_signed_overflow_def Let_def)
  done

end

section \<open>C Unsigned Arithmetic Verification\<close>

text \<open>
  This section demonstrates verification of C code using unsigned integer types.
  Unsigned arithmetic wraps modulo @{term \<open>2^32\<close>} and uses @{const c_unsigned_add}
  instead of @{const c_signed_add}.
\<close>

locale c_uint_verification_ctx =
    reference reference_types +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
    and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
unsigned int u_add(unsigned int a, unsigned int b) {
  return a + b;
}
\<close>

thm c_u_add_def

text \<open>
  The contract for @{text u_add}: unsigned addition wraps, so the result is
  always @{term \<open>a + b\<close>} (Isabelle word addition already wraps).
  No overflow precondition needed.
\<close>
definition c_u_add_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_add_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_add_contract

lemma c_u_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_add a b \<Turnstile>\<^sub>F c_u_add_contract a b\<close>
  apply (crush_boot f: c_u_add_def contract: c_u_add_contract_def)
  apply (crush_base simp add: c_unsigned_add_def)
  done

micro_c_translate \<open>
unsigned int u_max(unsigned int a, unsigned int b) {
  if (a > b) return a;
  else return b;
}
\<close>

thm c_u_max_def

definition c_u_max_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if b < a then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_max_contract

lemma c_u_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_max a b \<Turnstile>\<^sub>F c_u_max_contract a b\<close>
  apply (crush_boot f: c_u_max_def contract: c_u_max_contract_def)
  apply (crush_base simp add: c_unsigned_less_def)
  done

subsection \<open>Comma Operator\<close>

micro_c_translate \<open>
unsigned int comma_test(unsigned int a, unsigned int b) {
    unsigned int x = (a, b);
    return x;
}
\<close>

definition c_comma_test_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_comma_test_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_comma_test_contract

lemma c_comma_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_comma_test a b \<Turnstile>\<^sub>F c_comma_test_contract a b\<close>
  apply (crush_boot f: c_comma_test_def contract: c_comma_test_contract_def)
  apply crush_base
  done

subsection \<open>Multiple Declarations\<close>

micro_c_translate \<open>
unsigned int multi_decl_add(unsigned int a, unsigned int b) {
    unsigned int x = a, y = b;
    return x + y;
}
\<close>

definition c_multi_decl_add_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_multi_decl_add_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_multi_decl_add_contract

lemma c_multi_decl_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_multi_decl_add a b \<Turnstile>\<^sub>F c_multi_decl_add_contract a b\<close>
  apply (crush_boot f: c_multi_decl_add_def contract: c_multi_decl_add_contract_def)
  apply (crush_base simp add: c_unsigned_add_def)
  done

subsection \<open>Pre-Increment\<close>

micro_c_translate \<open>
unsigned int pre_inc_test(unsigned int init) {
    unsigned int x = init;
    unsigned int r = ++x;
    return r;
}
\<close>

definition c_pre_inc_test_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_pre_inc_test_contract init \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = init + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_pre_inc_test_contract

lemma c_pre_inc_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_pre_inc_test init \<Turnstile>\<^sub>F c_pre_inc_test_contract init\<close>
  apply (crush_boot f: c_pre_inc_test_def contract: c_pre_inc_test_contract_def)
  apply (crush_base simp add: c_unsigned_add_def)
  done

subsection \<open>Post-Increment\<close>

micro_c_translate \<open>
unsigned int post_inc_test(unsigned int init) {
    unsigned int x = init;
    unsigned int r = x++;
    return r;
}
\<close>

definition c_post_inc_test_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_post_inc_test_contract init \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = init\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_post_inc_test_contract

lemma c_post_inc_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_post_inc_test init \<Turnstile>\<^sub>F c_post_inc_test_contract init\<close>
  apply (crush_boot f: c_post_inc_test_def contract: c_post_inc_test_contract_def)
  apply (crush_base simp add: c_unsigned_add_def)
  done

subsection \<open>Post-Decrement\<close>

micro_c_translate \<open>
unsigned int post_dec_test(unsigned int init) {
    unsigned int x = init;
    unsigned int r = x--;
    return r;
}
\<close>

definition c_post_dec_test_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_post_dec_test_contract init \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = init\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_post_dec_test_contract

lemma c_post_dec_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_post_dec_test init \<Turnstile>\<^sub>F c_post_dec_test_contract init\<close>
  apply (crush_boot f: c_post_dec_test_def contract: c_post_dec_test_contract_def)
  apply (crush_base simp add: c_unsigned_sub_def)
  done

subsection \<open>Not-Equal Operator\<close>

micro_c_translate \<open>
unsigned int neq_test(unsigned int a, unsigned int b) {
  if (a != b) return 1;
  else return 0;
}
\<close>

definition c_neq_test_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_neq_test_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if a \<noteq> b then 1 else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_neq_test_contract

lemma c_neq_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_neq_test a b \<Turnstile>\<^sub>F c_neq_test_contract a b\<close>
  apply (crush_boot f: c_neq_test_def contract: c_neq_test_contract_def)
  apply (crush_base simp add: c_unsigned_neq_def)
  done

subsection \<open>Logical NOT\<close>

micro_c_translate \<open>
unsigned int is_zero(unsigned int x) {
  if (!x) return 1;
  else return 0;
}
\<close>

definition c_is_zero_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_is_zero_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if x = 0 then 1 else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_is_zero_contract

lemma c_is_zero_spec [crush_specs]:
  shows \<open>\<Gamma>; c_is_zero x \<Turnstile>\<^sub>F c_is_zero_contract x\<close>
  apply (crush_boot f: c_is_zero_def contract: c_is_zero_contract_def)
  apply (crush_base simp add: c_unsigned_eq_def)
  done

subsection \<open>Unary Plus\<close>

micro_c_translate \<open>
unsigned int uplus(unsigned int x) { return +x; }
\<close>

definition c_uplus_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_uplus_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_uplus_contract

lemma c_uplus_spec [crush_specs]:
  shows \<open>\<Gamma>; c_uplus x \<Turnstile>\<^sub>F c_uplus_contract x\<close>
  apply (crush_boot f: c_uplus_def contract: c_uplus_contract_def)
  apply crush_base
  done

subsection \<open>Ternary Operator\<close>

micro_c_translate \<open>
unsigned int ternary_max(unsigned int a, unsigned int b) {
  return (a > b) ? a : b;
}
\<close>

definition c_ternary_max_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_ternary_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if b < a then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_ternary_max_contract

lemma c_ternary_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_ternary_max a b \<Turnstile>\<^sub>F c_ternary_max_contract a b\<close>
  apply (crush_boot f: c_ternary_max_def contract: c_ternary_max_contract_def)
  apply (crush_base simp add: c_unsigned_less_def)
  done

subsection \<open>Compound Assignment\<close>

micro_c_translate \<open>
unsigned int add_assign(unsigned int a, unsigned int b) {
  unsigned int x = a;
  x += b;
  return x;
}
\<close>

definition c_add_assign_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_add_assign_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_add_assign_contract

lemma c_add_assign_spec [crush_specs]:
  shows \<open>\<Gamma>; c_add_assign a b \<Turnstile>\<^sub>F c_add_assign_contract a b\<close>
  apply (crush_boot f: c_add_assign_def contract: c_add_assign_contract_def)
  apply (crush_base simp add: c_unsigned_add_def)
  done

end

end
