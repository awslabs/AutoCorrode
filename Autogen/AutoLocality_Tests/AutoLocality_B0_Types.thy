(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Types
  imports AutoLocality_B0_Base
begin
(*>*)

section\<open>Language and type diversity\<close>

subsection\<open>Ad-hoc overloading with one source name\<close>

datatype_record b0_other =
  b0_x :: nat
  b0_y :: nat
  b0_z :: nat

locality_init for b0_other

consts b0_overloaded_attr :: \<open>'a \<Rightarrow> bool\<close>
consts b0_overloaded_op :: \<open>'a \<Rightarrow> 'a\<close>

definition b0_state_concrete_attr :: \<open>b0_state \<Rightarrow> bool\<close> where
  \<open>b0_state_concrete_attr R \<equiv> b0_a R > 0\<close>

definition b0_state_concrete_op :: \<open>b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_state_concrete_op R \<equiv> update_b0_b Suc R\<close>

definition b0_other_concrete_attr :: \<open>b0_other \<Rightarrow> bool\<close> where
  \<open>b0_other_concrete_attr R \<equiv> b0_x R > 0\<close>

definition b0_other_concrete_op :: \<open>b0_other \<Rightarrow> b0_other\<close> where
  \<open>b0_other_concrete_op R \<equiv> update_b0_y Suc R\<close>

adhoc_overloading b0_overloaded_attr
  \<rightleftharpoons> b0_state_concrete_attr
adhoc_overloading b0_overloaded_attr
  \<rightleftharpoons> b0_other_concrete_attr
adhoc_overloading b0_overloaded_op
  \<rightleftharpoons> b0_state_concrete_op
adhoc_overloading b0_overloaded_op
  \<rightleftharpoons> b0_other_concrete_op

locality_lemma for b0_state:
  \<open>b0_overloaded_attr :: b0_state \<Rightarrow> bool\<close> footprint [b0_a] .
locality_lemma for b0_state:
  \<open>b0_overloaded_op :: b0_state \<Rightarrow> b0_state\<close> footprint [b0_b] .
locality_lemma for b0_other:
  \<open>b0_overloaded_attr :: b0_other \<Rightarrow> bool\<close> footprint [b0_x] .
locality_lemma for b0_other:
  \<open>b0_overloaded_op :: b0_other \<Rightarrow> b0_other\<close> footprint [b0_y] .

lemma b0_overloading_state_ambient:
  shows \<open>b0_overloaded_attr
      (b0_set_c n (b0_overloaded_op R :: b0_state)) =
    b0_overloaded_attr R\<close>
  by simp

lemma b0_overloading_state_restricted:
  shows \<open>b0_overloaded_attr
      (b0_set_d n (b0_overloaded_op R :: b0_state)) =
    b0_overloaded_attr R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_overloading_other_ambient:
  shows \<open>b0_overloaded_attr
      (update_b0_z f (b0_overloaded_op R :: b0_other)) =
    b0_overloaded_attr R\<close>
  by simp

lemma b0_overloading_other_restricted:
  shows \<open>b0_overloaded_attr
      (update_b0_z f (b0_overloaded_op R :: b0_other)) =
    b0_overloaded_attr R\<close>
  by (simp only: [[locality_cancel]])

subsection\<open>Sorted polymorphism and type-changing updates\<close>

datatype_record ('a::linorder, 'phantom) b0_poly =
  b0_payload :: 'a
  b0_flag :: bool
  b0_count :: nat

locality_init for b0_poly

definition b0_poly_raise ::
    \<open>'a::linorder \<Rightarrow>
      ('a, 'phantom) b0_poly \<Rightarrow> ('a, 'phantom) b0_poly\<close> where
  \<open>b0_poly_raise value R \<equiv> update_b0_payload (max value) R\<close>

definition b0_poly_flagged ::
    \<open>('a::linorder, 'phantom) b0_poly \<Rightarrow> bool\<close> where
  \<open>b0_poly_flagged R \<equiv> b0_flag R\<close>

definition b0_poly_below ::
    \<open>'a::linorder \<Rightarrow> ('a, 'phantom) b0_poly \<Rightarrow> bool\<close> where
  \<open>b0_poly_below bound R \<equiv> b0_payload R < bound\<close>

locality_lemma for b0_poly:
  \<open>b0_poly_raise\<close> footprint [b0_payload] .
locality_lemma for b0_poly:
  \<open>b0_poly_flagged\<close> footprint [b0_flag] .
locality_lemma for b0_poly:
  \<open>b0_poly_below\<close> footprint [b0_payload] .

lemma b0_polymorphic_ambient:
  shows \<open>b0_poly_below bound
      (update_b0_count g (update_b0_flag f R)) =
    b0_poly_below bound R\<close>
  by simp

text\<open>Production polymorphic and phantom-changing behavior is covered by
AutoLocality_Test_Polymorphic and the later record-index stress suite.\<close>

subsection\<open>Rigid partial-application prefixes\<close>

definition b0_policy_a :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_policy_a R \<equiv> b0_a R\<close>

definition b0_policy_b :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_policy_b R \<equiv> b0_b R\<close>

definition b0_policy_c :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_policy_c R \<equiv> b0_c R\<close>

definition b0_policy_attr ::
    \<open>(b0_state \<Rightarrow> nat) \<Rightarrow> b0_state \<Rightarrow> bool\<close> where
  \<open>b0_policy_attr policy R \<equiv> policy R > 0\<close>

locality_lemma for b0_state:
  \<open>b0_policy_attr b0_policy_a\<close> footprint [b0_a]
  by (auto simp add: b0_policy_attr_def b0_policy_a_def)
locality_lemma for b0_state:
  \<open>b0_policy_attr b0_policy_b\<close> footprint [b0_b]
  by (auto simp add: b0_policy_attr_def b0_policy_b_def)

lemma b0_rigid_prefix_a:
  shows \<open>b0_policy_attr b0_policy_a (b0_set_c n R) =
    b0_policy_attr b0_policy_a R\<close>
  by simp

lemma b0_rigid_prefix_b:
  shows \<open>b0_policy_attr b0_policy_b (b0_set_a n R) =
    b0_policy_attr b0_policy_b R\<close>
  by (simp only: [[locality_cancel]])

text\<open>
The same head and arity with an unregistered rigid prefix must not borrow the
footprint of either registered prefix.  This semantic control observes the
field changed by the operation, so a spurious cancellation would make the
goal false.
\<close>

lemma b0_unregistered_rigid_prefix_definitional_control:
  shows \<open>b0_policy_attr b0_policy_c (b0_set_c n R) = (n > 0)\<close>
  by (simp add:
    b0_policy_attr_def b0_policy_c_def b0_set_c_def)

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "unregistered rigid prefix does not borrow a registered footprint"
    ctxt
    "b0_policy_attr b0_policy_c (b0_set_c n R) = \
      \b0_policy_attr b0_policy_c R"
\<close>

subsection\<open>Higher-order update and multiple record slots\<close>

definition b0_lens_c ::
    \<open>(nat \<Rightarrow> nat) \<Rightarrow> b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_lens_c f R \<equiv> update_b0_c f R\<close>

locality_lemma for b0_state: \<open>b0_lens_c\<close> footprint [b0_c] .

definition b0_pair_attr ::
    \<open>b0_state \<Rightarrow> b0_state \<Rightarrow> bool\<close> where
  \<open>b0_pair_attr L R \<equiv> b0_a L < b0_b R\<close>

locality_lemma for b0_state:
  \<open>b0_pair_attr\<close> [0] footprint [b0_a] .
locality_lemma for b0_state:
  \<open>b0_pair_attr\<close> [1] footprint [b0_b] .

lemma b0_lens_shaped_operation:
  shows \<open>b0_has_a (b0_lens_c f R) = b0_has_a R\<close>
  by simp

lemma b0_multiple_record_slots_ambient:
  shows \<open>b0_pair_attr (b0_set_c n L) (b0_set_a m R) =
    b0_pair_attr L R\<close>
  by simp

lemma b0_multiple_record_slots_restricted_left:
  shows \<open>b0_pair_attr (b0_set_d n L) R = b0_pair_attr L R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_multiple_record_slots_restricted_right:
  shows \<open>b0_pair_attr L (b0_set_c n R) = b0_pair_attr L R\<close>
  by (simp only: [[locality_cancel]])

subsection\<open>Standard record inheritance\<close>

record b0_standard_base =
  b0_std_a :: nat
  b0_std_b :: nat

record b0_standard_ext = b0_standard_base +
  b0_std_c :: nat

locality_init for b0_standard_ext

definition b0_std_bump_a ::
    \<open>b0_standard_ext \<Rightarrow> b0_standard_ext\<close> where
  \<open>b0_std_bump_a R \<equiv> b0_std_a_update Suc R\<close>

definition b0_std_set_c ::
    \<open>nat \<Rightarrow> b0_standard_ext \<Rightarrow> b0_standard_ext\<close> where
  \<open>b0_std_set_c n R \<equiv> b0_std_c_update (\<lambda>_. n) R\<close>

definition b0_std_has_b :: \<open>b0_standard_ext \<Rightarrow> bool\<close> where
  \<open>b0_std_has_b R \<equiv> b0_std_b R > 0\<close>

locality_lemma for b0_standard_ext:
  \<open>b0_std_bump_a\<close> footprint [b0_std_a] .
locality_lemma for b0_standard_ext:
  \<open>b0_std_set_c\<close> footprint [b0_std_c] .
locality_lemma for b0_standard_ext:
  \<open>b0_std_has_b\<close> footprint [b0_std_b] .

lemma b0_standard_extension_ambient:
  shows \<open>b0_std_has_b (b0_std_bump_a (b0_std_set_c n R)) =
    b0_std_has_b R\<close>
  by simp

lemma b0_standard_extension_restricted:
  shows \<open>b0_std_has_b
      (b0_std_a_update f (b0_std_c_update g R)) =
    b0_std_has_b R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_standard_inherited_selector:
  shows \<open>b0_std_c (b0_std_bump_a R) = b0_std_c R\<close>
  by simp

(*<*)
end
(*>*)
