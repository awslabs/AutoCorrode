(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Traversal
  imports AutoLocality_B0_Base
begin
(*>*)

section\<open>Simplifier traversal and trigger boundaries\<close>

text\<open>
These tests distinguish the syntax at the root from the complete recursive
walk performed by the Simplifier.  Callback counts for the deliberately
non-triggering roots belong to the frozen instrumentation API; the black-box
claims here concern only the observable rewrite result.
\<close>

datatype_record b0_walk =
  b0_walk_a :: nat
  b0_walk_b :: nat
  b0_walk_c :: nat

locality_init for b0_walk

definition b0_walk_set_b ::
    \<open>nat \<Rightarrow> b0_walk \<Rightarrow> b0_walk\<close> where
  \<open>b0_walk_set_b n R \<equiv> update_b0_walk_b (\<lambda>_. n) R\<close>

definition b0_walk_set_c ::
    \<open>nat \<Rightarrow> b0_walk \<Rightarrow> b0_walk\<close> where
  \<open>b0_walk_set_c n R \<equiv> update_b0_walk_c (\<lambda>_. n) R\<close>

definition b0_walk_pred :: \<open>b0_walk \<Rightarrow> bool\<close> where
  \<open>b0_walk_pred R \<equiv> b0_walk_a R > 0\<close>

definition b0_walk_between ::
    \<open>nat \<Rightarrow> b0_walk \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>b0_walk_between lo R hi \<equiv> lo < b0_walk_a R \<and>
    b0_walk_a R < hi\<close>

locality_lemma for b0_walk:
  \<open>b0_walk_set_b\<close> footprint [b0_walk_b] .
locality_lemma for b0_walk:
  \<open>b0_walk_set_c\<close> footprint [b0_walk_c] .
locality_lemma for b0_walk:
  \<open>b0_walk_pred\<close> footprint [b0_walk_a] .
locality_lemma for b0_walk:
  \<open>b0_walk_between\<close> [0] footprint [b0_walk_a] .

subsection\<open>Exact family arity and fewer root arguments\<close>

lemma b0_exact_family_arity:
  shows \<open>b0_walk_between lo (b0_walk_set_b n R) hi =
    b0_walk_between lo R hi\<close>
  by (simp only: [[locality_cancel]])

text\<open>
At the root, the following term is missing its final argument and contains no
complete matching descendant.  The equality is established extensionally
with cancellation disabled; the white-box suite must additionally assert zero
root and nested callbacks before the extensional argument is introduced.
\<close>

lemma b0_fewer_arguments_definitional_control:
  shows \<open>b0_walk_between lo (b0_walk_set_b n R) =
    b0_walk_between lo R\<close>
proof (rule ext)
  fix hi
  show \<open>b0_walk_between lo (b0_walk_set_b n R) hi =
    b0_walk_between lo R hi\<close>
    supply [[locality_no_cancel]]
    by (simp add: b0_walk_between_def b0_walk_set_b_def)
qed

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "fewer arguments with no matching descendant remain unchanged"
    ctxt
    "b0_walk_between lo (b0_walk_set_b n R)"
    "b0_walk_between lo (b0_walk_set_b n R)"
\<close>

subsection\<open>Incomplete outer roots with matching descendants\<close>

definition b0_outer_family :: \<open>bool \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>b0_outer_family flag n \<equiv> flag \<and> n > 0\<close>

lemma b0_fewer_root_arguments_nested_match:
  shows \<open>b0_outer_family
      (b0_walk_pred (b0_walk_set_b n R)) =
    b0_outer_family (b0_walk_pred R)\<close>
  by (simp only: [[locality_cancel]])

lemma b0_different_root_head_nested_match:
  shows \<open>\<not> b0_walk_pred
      (b0_walk_set_c n (b0_walk_set_b m R)) =
    (\<not> b0_walk_pred R)\<close>
  by simp

subsection\<open>Higher-order superterms with a proper matching prefix\<close>

definition b0_higher_attr :: \<open>b0_walk \<Rightarrow> 'a\<close> where
  \<open>b0_higher_attr R \<equiv> undefined\<close>

locality_lemma for b0_walk:
  \<open>b0_higher_attr\<close> footprint [] .

text\<open>
The registered redex has result type instantiated to a function and is a
proper application prefix of the complete term.
\<close>

lemma b0_extra_argument_superterm:
  shows \<open>(b0_higher_attr (b0_walk_set_b n R) ::
      nat \<Rightarrow> nat) k =
    b0_higher_attr R k\<close>
  by (simp only: [[locality_cancel]])

subsection\<open>Deeply nested matches and repeated family visits\<close>

definition b0_join_flags :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>b0_join_flags left right \<equiv> left \<or> right\<close>

lemma b0_deep_nested_matching_terms:
  shows \<open>b0_join_flags
      (b0_walk_pred
        (b0_walk_set_b n
          (b0_walk_set_c m
            (b0_walk_set_b p
              (b0_walk_set_c q R)))))
      (b0_walk_pred
        (b0_walk_set_c r
          (b0_walk_set_b s
            (b0_walk_set_c t R)))) =
    b0_join_flags (b0_walk_pred R) (b0_walk_pred R)\<close>
  by simp

lemma b0_nested_family_applications:
  shows \<open>b0_outer_family
      (b0_join_flags
        (b0_walk_pred (b0_walk_set_b n R))
        (b0_walk_pred (b0_walk_set_c m R))) =
    b0_outer_family
      (b0_join_flags (b0_walk_pred R) (b0_walk_pred R))\<close>
  by (simp only: [[locality_cancel]])

subsection\<open>Ambient rewrites creating and removing matches\<close>

definition b0_reveal_match :: \<open>b0_walk \<Rightarrow> bool\<close> where
  \<open>b0_reveal_match R \<equiv>
    b0_walk_pred (b0_walk_set_b (b0_walk_b R + 1) R)\<close>

lemma b0_rewrite_creates_match_ambient:
  shows \<open>b0_reveal_match R = b0_walk_pred R\<close>
  by (simp add: b0_reveal_match_def)

lemma b0_rewrite_creates_match_restricted:
  shows \<open>b0_reveal_match R = b0_walk_pred R\<close>
  by (simp only: b0_reveal_match_def [[locality_cancel]])

definition b0_remove_match :: \<open>b0_walk \<Rightarrow> bool\<close> where
  \<open>b0_remove_match R \<equiv>
    b0_walk_pred (b0_walk_set_c (b0_walk_c R + 1) R)\<close>

lemma b0_remove_match_simps [simp]:
  shows \<open>b0_remove_match R = b0_walk_pred R\<close>
  supply [[locality_no_cancel]]
  by (simp add:
    b0_remove_match_def b0_walk_pred_def b0_walk_set_c_def)

lemma b0_rewrite_removes_match:
  shows \<open>b0_remove_match R = b0_walk_pred R\<close>
  by simp

definition b0_remove_before_trigger :: \<open>b0_walk \<Rightarrow> bool\<close> where
  \<open>b0_remove_before_trigger R \<equiv>
    (if False then b0_walk_pred (b0_walk_set_c 0 R) else True)\<close>

lemma b0_remove_before_trigger_simps [simp]:
  shows \<open>b0_remove_before_trigger R\<close>
  by (simp add: b0_remove_before_trigger_def)

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "ambient rewrite removes the matching branch"
    ctxt "b0_remove_before_trigger R" "True"
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "ambient rewrite removes the matching branch before cancellation"
    ctxt "b0_remove_before_trigger R = b0_walk_pred R"
\<close>

subsection\<open>Unregistered same-shape operation\<close>

definition b0_walk_unregistered_a ::
    \<open>b0_walk \<Rightarrow> b0_walk\<close> where
  \<open>b0_walk_unregistered_a R \<equiv> update_b0_walk_a Suc R\<close>

text\<open>
This operation has the same operation shape as registered families but no
locality declaration.  The expected equation observes its real state change;
borrowing a disjoint registered footprint would turn the goal false.
\<close>

lemma b0_unregistered_operation_definitional_control:
  shows \<open>b0_walk_pred (b0_walk_unregistered_a R) =
    (Suc (b0_walk_a R) > 0)\<close>
  by (simp add:
    b0_walk_pred_def b0_walk_unregistered_a_def)

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "unregistered operation does not receive cancellation"
    ctxt
    "b0_walk_pred (b0_walk_unregistered_a R) = b0_walk_pred R"
\<close>

(*<*)
end
(*>*)
