(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Memory_Operations
  imports
    C_Pointer_Types
    C_Sizeof
begin

section \<open>C Pointer Arithmetic\<close>

text \<open>
  In C, pointer arithmetic @{text "p + n"} advances the pointer by
  @{text "n * sizeof(*p)"} bytes. We define this as pure address arithmetic
  on @{type gref} values.
\<close>

definition c_ptr_add :: \<open>(nat, 'b) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'b) gref\<close> where
  \<open>c_ptr_add p n stride \<equiv> make_gref (gref_address p + n * stride)\<close>

text \<open>A convenience abbreviation using @{const c_sizeof} for the stride.\<close>

abbreviation c_ptr_add_typed :: \<open>(nat, 'b) gref \<Rightarrow> nat \<Rightarrow> 'v itself \<Rightarrow> (nat, 'b) gref\<close> where
  \<open>c_ptr_add_typed p n T \<equiv> c_ptr_add p n (c_sizeof T)\<close>

subsection \<open>Basic Pointer Arithmetic Lemmas\<close>

lemma c_ptr_add_zero [simp]: \<open>c_ptr_add p 0 stride = p\<close>
  by (simp add: c_ptr_add_def)

lemma c_ptr_add_address [simp]:
  \<open>gref_address (c_ptr_add p n stride) = gref_address p + n * stride\<close>
  by (simp add: c_ptr_add_def)

lemma c_ptr_add_add:
  \<open>c_ptr_add (c_ptr_add p m stride) n stride = c_ptr_add p (m + n) stride\<close>
  by (simp add: c_ptr_add_def algebra_simps)

lemma c_ptr_add_null_guard:
  assumes \<open>\<not> is_null_nat p\<close> and \<open>n * stride < gref_address p + n * stride\<close>
  shows \<open>\<not> is_null_nat (c_ptr_add p n stride)\<close>
  using assms by (simp add: is_null_nat_def c_ptr_add_def)

section \<open>C Pointer Subtraction\<close>

definition c_ptr_diff :: \<open>(nat, 'b) gref \<Rightarrow> (nat, 'b) gref \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>c_ptr_diff p q stride \<equiv> (gref_address p - gref_address q) div stride\<close>

end
