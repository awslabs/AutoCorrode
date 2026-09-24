(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Lifecycle
  imports AutoLocality_B0_Base
begin
(*>*)

section\<open>Locale declaration, replay, and interpretation lifecycle\<close>

definition b0_lineage_attr ::
    \<open>(b0_state \<Rightarrow> nat) \<Rightarrow> b0_state \<Rightarrow> bool\<close> where
  \<open>b0_lineage_attr projection R \<equiv> projection R > 0\<close>

definition b0_parent_projection :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_parent_projection R \<equiv> b0_a R\<close>

definition b0_child_projection :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_child_projection R \<equiv> b0_b R\<close>

locale b0_parent =
  fixes step :: \<open>nat \<Rightarrow> nat\<close>
begin

definition b0_parent_attr :: \<open>b0_state \<Rightarrow> bool\<close> where
  \<open>b0_parent_attr R \<equiv> step (b0_a R) > 0\<close>

definition b0_parent_op :: \<open>b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_parent_op R \<equiv> update_b0_a step R\<close>

end

text\<open>Registration happens on context re-entry, after the locale
definitions have been established.\<close>

context b0_parent begin

locality_lemma for b0_state: \<open>b0_parent_attr\<close> footprint [b0_a] .
locality_lemma for b0_state: \<open>b0_parent_op\<close> footprint [b0_a] .
locality_lemma for b0_state:
  \<open>b0_lineage_attr b0_parent_projection\<close> footprint [b0_a]
  by (auto simp add: b0_lineage_attr_def b0_parent_projection_def)

lemma b0_parent_ambient:
  shows \<open>b0_parent_attr (b0_set_c n R) = b0_parent_attr R\<close>
  by simp

lemma b0_parent_restricted:
  shows \<open>b0_parent_attr (b0_set_d n R) = b0_parent_attr R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_parent_dispatch_lineage:
  shows \<open>b0_lineage_attr b0_parent_projection (b0_set_c n R) =
    b0_lineage_attr b0_parent_projection R\<close>
  by simp

end

locale b0_child =
  fixes step :: \<open>nat \<Rightarrow> nat\<close>
    and shift :: \<open>nat \<Rightarrow> nat\<close>
begin

definition b0_child_attr :: \<open>b0_state \<Rightarrow> bool\<close> where
  \<open>b0_child_attr R \<equiv> shift (b0_b R) > 1\<close>

definition b0_child_op :: \<open>b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_child_op R \<equiv> update_b0_b shift R\<close>

end

text\<open>The explicit sublocale edge composes the parent declaration
morphism before child-local semantic registrations are added.\<close>

sublocale b0_child \<subseteq> b0_parent step .

context b0_child begin

locality_lemma for b0_state: \<open>b0_child_attr\<close> footprint [b0_b] .
locality_lemma for b0_state: \<open>b0_child_op\<close> footprint [b0_b] .
locality_lemma for b0_state:
  \<open>b0_lineage_attr b0_child_projection\<close> footprint [b0_b]
  by (auto simp add: b0_lineage_attr_def b0_child_projection_def)

lemma b0_child_inherited_parent_dispatch:
  shows \<open>b0_parent_attr (b0_set_c n (b0_child_op R)) =
    b0_parent_attr (b0_child_op R)\<close>
  by simp

lemma b0_child_semantic_registration:
  shows \<open>b0_child_attr (b0_set_d n (b0_parent_op R)) =
    b0_child_attr (b0_parent_op R)\<close>
  by (simp only: [[locality_cancel]])

lemma b0_child_semantic_only_family_entry:
  shows \<open>b0_lineage_attr b0_child_projection (b0_set_d n R) =
    b0_lineage_attr b0_child_projection R\<close>
  by simp

end

locale b0_grandchild = b0_child step shift
  for step shift +
  fixes twist :: \<open>nat \<Rightarrow> nat\<close>
begin

definition b0_grandchild_op :: \<open>b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_grandchild_op R \<equiv> update_b0_c twist R\<close>

definition b0_grandchild_attr :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_grandchild_attr R \<equiv> b0_d R\<close>

end

context b0_grandchild begin

locality_lemma for b0_state: \<open>b0_grandchild_op\<close> footprint [b0_c] .
locality_lemma for b0_state: \<open>b0_grandchild_attr\<close> footprint [b0_d] .

lemma b0_grandchild_nested_lifecycle:
  shows \<open>b0_grandchild_attr
      (b0_child_op (b0_parent_op (b0_grandchild_op R))) =
    b0_grandchild_attr R\<close>
  by simp

end

subsection\<open>Global activations and replay into distinct targets\<close>

global_interpretation b0_global_one:
  b0_grandchild Suc \<open>\<lambda>n. n + 2\<close> \<open>\<lambda>n. n * 2\<close> .

global_interpretation b0_global_one_replay:
  b0_grandchild Suc \<open>\<lambda>n. n + 2\<close> \<open>\<lambda>n. n * 2\<close> .

global_interpretation b0_global_two:
  b0_grandchild \<open>\<lambda>n. n + 3\<close> \<open>\<lambda>n. n * 3\<close>
    \<open>\<lambda>n. n + 4\<close> .

lemma b0_global_first_activation:
  shows \<open>b0_global_one.b0_parent_attr
      (b0_set_d n (b0_global_one.b0_child_op R)) =
    b0_global_one.b0_parent_attr (b0_global_one.b0_child_op R)\<close>
  by simp

lemma b0_global_exact_replay:
  shows \<open>b0_global_one.b0_child_attr
      (b0_set_c n (b0_global_one.b0_parent_op R)) =
    b0_global_one.b0_child_attr
      (b0_global_one.b0_parent_op R)\<close>
  by (simp only: [[locality_cancel]])

lemma b0_global_distinct_target:
  shows \<open>b0_global_two.b0_grandchild_attr
      (b0_global_two.b0_child_op (b0_global_two.b0_parent_op R)) =
    b0_global_two.b0_grandchild_attr R\<close>
  by simp

subsection\<open>Interpretation into locale targets\<close>

locale b0_target_left =
  fixes target_step :: \<open>nat \<Rightarrow> nat\<close>
begin

interpretation local_parent: b0_parent target_step .

lemma b0_locale_target_left:
  shows \<open>b0_parent.b0_parent_attr target_step (b0_set_c n R) =
    b0_parent.b0_parent_attr target_step R\<close>
  by simp

end

locale b0_target_right =
  fixes target_step :: \<open>nat \<Rightarrow> nat\<close>
begin

interpretation local_parent: b0_parent target_step .

lemma b0_locale_target_right:
  shows \<open>b0_parent.b0_parent_attr target_step (b0_set_d n R) =
    b0_parent.b0_parent_attr target_step R\<close>
  by (simp only: [[locality_cancel]])

end

subsection\<open>Assumption-dependent flexible prefixes\<close>

locale b0_flexible_prefix =
  fixes stored_prefix :: \<open>nat \<Rightarrow> nat\<close>
    and actual_prefix :: \<open>nat \<Rightarrow> nat\<close>
  assumes prefix_eq: \<open>stored_prefix = actual_prefix\<close>
begin

definition b0_flexible_attr :: \<open>b0_state \<Rightarrow> bool\<close> where
  \<open>b0_flexible_attr R \<equiv> stored_prefix (b0_a R) > 7\<close>

end

context b0_flexible_prefix begin

locality_lemma for b0_state: \<open>b0_flexible_attr\<close> footprint [b0_a] .

lemma b0_flexible_prefix_ambient:
  shows \<open>b0_flexible_prefix.b0_flexible_attr actual_prefix
      (b0_set_c n R) =
    b0_flexible_prefix.b0_flexible_attr actual_prefix R\<close>
  using prefix_eq
  by simp

lemma b0_flexible_prefix_restricted:
  shows \<open>b0_flexible_prefix.b0_flexible_attr actual_prefix
      (b0_set_d n R) =
    b0_flexible_prefix.b0_flexible_attr actual_prefix R\<close>
  using prefix_eq
  by (simp only: prefix_eq [[locality_cancel]])

end

subsection\<open>Proof-context isolation for flexible-prefix matching\<close>

locale b0_context_isolation =
  fixes stored_prefix :: \<open>nat \<Rightarrow> nat\<close>
    and actual_prefix :: \<open>nat \<Rightarrow> nat\<close>
begin

definition b0_isolated_attr :: \<open>b0_state \<Rightarrow> bool\<close> where
  \<open>b0_isolated_attr R \<equiv> stored_prefix (b0_a R) > 11\<close>

end

context b0_context_isolation begin

locality_lemma for b0_state: \<open>b0_isolated_attr\<close> footprint [b0_a] .

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "flexible prefix without equality before a proving context"
    ctxt
    "b0_context_isolation.b0_isolated_attr actual_prefix \
      \(b0_set_c n R) = \
      \b0_context_isolation.b0_isolated_attr actual_prefix R"
\<close>

context
  assumes prefix_eq: \<open>stored_prefix = actual_prefix\<close>
begin

declare prefix_eq [simp]

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_proves
    "flexible prefix with equality after a non-proving context"
    ctxt
    "b0_context_isolation.b0_isolated_attr actual_prefix \
      \(b0_set_c n R) = \
      \b0_context_isolation.b0_isolated_attr actual_prefix R"
\<close>

end

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "flexible prefix without equality after a proving context"
    ctxt
    "b0_context_isolation.b0_isolated_attr actual_prefix \
      \(b0_set_c n R) = \
      \b0_context_isolation.b0_isolated_attr actual_prefix R"
\<close>

context
  assumes prefix_eq: \<open>stored_prefix = actual_prefix\<close>
begin

declare prefix_eq [simp]

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_proves
    "flexible prefix with equality after the second non-proving probe"
    ctxt
    "b0_context_isolation.b0_isolated_attr actual_prefix \
      \(b0_set_c n R) = \
      \b0_context_isolation.b0_isolated_attr actual_prefix R"
\<close>

end

end

subsection\<open>Scoped opt-out and restoration\<close>

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "enabled cancellation removes the opaque redex"
    ctxt "b0_has_a (b0_set_c n R)" "b0_has_a R"
  val _ = AutoLocality_B0_Blackbox.assert_proves
    "enabled cancellation proves the cancellation equation"
    ctxt "b0_has_a (b0_set_c n R) = b0_has_a R"
\<close>

context
  notes [[locality_no_cancel]]
begin

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "disabled cancellation retains the opaque redex"
    ctxt "b0_has_a (b0_set_c n R)" "b0_has_a (b0_set_c n R)"
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "disabled cancellation does not prove the cancellation equation"
    ctxt "b0_has_a (b0_set_c n R) = b0_has_a R"
\<close>

text\<open>This unfolding lemma is a semantic control, not opt-out evidence.\<close>

lemma b0_opt_out_definitional_control:
  shows \<open>b0_has_a (b0_set_c n R) = b0_has_a R\<close>
  by (simp add: b0_has_a_def b0_set_c_def)

context
begin

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "nested disabled cancellation retains the opaque redex"
    ctxt "b0_has_a (b0_set_d n R)" "b0_has_a (b0_set_d n R)"
  val _ = AutoLocality_B0_Blackbox.assert_not_proves
    "nested disabled cancellation does not prove the cancellation equation"
    ctxt "b0_has_a (b0_set_d n R) = b0_has_a R"
\<close>

text\<open>This unfolding lemma is likewise only a semantic control.\<close>

lemma b0_opt_out_nested_definitional_control:
  shows \<open>b0_has_a (b0_set_d n R) = b0_has_a R\<close>
  by (simp add: b0_has_a_def b0_set_d_def)

end

end

lemma b0_opt_out_restored:
  shows \<open>b0_has_a (b0_set_c n R) = b0_has_a R\<close>
  by (simp only: [[locality_cancel]])

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "restored cancellation removes the opaque redex"
    ctxt "b0_has_a (b0_set_c n R)" "b0_has_a R"
  val _ = AutoLocality_B0_Blackbox.assert_proves
    "restored cancellation proves the cancellation equation"
    ctxt "b0_has_a (b0_set_c n R) = b0_has_a R"
\<close>

(*<*)
end
(*>*)
