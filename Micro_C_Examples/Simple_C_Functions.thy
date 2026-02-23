(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Simple_C_Functions
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    "Micro_Rust_Std_Lib.StdLib_All"
begin

micro_rust_record c_point
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

section \<open>C Struct Verification\<close>

text \<open>
  This section demonstrates verification of C code operating on structs.
  The function @{text swap_coords} swaps the x and y fields of a
  point struct via a pointer.
\<close>

locale c_struct_verification_ctx =
    reference reference_types +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_point: reference_allocatable reference_types _ _ _ _ _ _ _ c_point_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
    and c_int_prism :: \<open>('gv, c_int) prism\<close>
    and c_point_prism :: \<open>('gv, c_point) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_point.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
struct point {
  int x;
  int y;
};
void swap_coords(struct point *p) {
  int t = p->x;
  p->x = p->y;
  p->y = t;
}
\<close>

thm c_swap_coords_def

text \<open>
  The contract for swap\_coords: given a reference to a c\_point with value
  @{text pval}, after execution the x and y fields are swapped.
\<close>
definition c_swap_coords_contract ::
    \<open>('addr, 'gv, c_point) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> c_point \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>c_swap_coords_contract pref pg pval \<equiv>
    let pre  = can_alloc_reference \<star>
               pref \<mapsto>\<langle>\<top>\<rangle> pg\<down>pval in
    let post = \<lambda> _.
               can_alloc_reference \<star>
               pref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. make_c_point (c_point_y pval) (c_point_x pval)) \<sqdot> (pg\<down>pval) in
    make_function_contract pre post\<close>
ucincl_auto c_swap_coords_contract

lemma c_swap_coords_spec:
  shows \<open>\<Gamma>; c_swap_coords pref \<Turnstile>\<^sub>F c_swap_coords_contract pref pg pval\<close>
  apply (crush_boot f: c_swap_coords_def contract: c_swap_coords_contract_def)
  apply crush_base
  apply (all \<open>cases pval; simp add: c_point_c_point_x_update_explicit c_point_c_point_y_update_explicit\<close>)
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

end
section \<open>C Array Verification\<close>

text \<open>
  This section demonstrates verification of C array indexing operations.
  Arrays are modeled as references to @{typ \<open>c_int list\<close>}.
  Array indexing uses @{const focus_nth} (focus-based access).
\<close>

context c_verification_ctx begin

subsection \<open>C Array Functions\<close>

micro_c_translate \<open>
int read_at(int *arr, int idx) {
  return arr[idx];
}
\<close>

thm c_read_at_def

micro_c_translate \<open>
void write_at(int *arr, int idx, int val) {
  arr[idx] = val;
}
\<close>

thm c_write_at_def

subsection \<open>Read-at Contract and Proof\<close>

text \<open>
  The contract for @{text read_at}: given a reference to a @{typ \<open>c_int list\<close>}
  and a valid index, the function returns the element at that index.
  The @{const c_idx_to_nat} function converts the C integer index to a natural number.
\<close>

definition c_read_at_contract ::
    \<open>('addr, 'gv, c_int list) Global_Store.ref \<Rightarrow> c_int \<Rightarrow>
     'gv \<Rightarrow> c_int list \<Rightarrow> ('s, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_at_contract arr idx g vs \<equiv>
    let pre  = arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>c_idx_to_nat idx < length vs\<rangle>;
        post = \<lambda>r. arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>r = vs ! (c_idx_to_nat idx)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_at_contract

lemma c_read_at_spec:
  shows \<open>\<Gamma>; c_read_at arr idx \<Turnstile>\<^sub>F c_read_at_contract arr idx g vs\<close>
  apply (crush_boot f: c_read_at_def contract: c_read_at_contract_def)
  apply crush_base
  done

end

end

