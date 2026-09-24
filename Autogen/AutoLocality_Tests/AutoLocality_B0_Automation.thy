(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Automation
  imports
    AutoLocality_Tests.AutoLocality_B0_All
    Crush.Crush
begin
(*>*)

section\<open>Production automation paths through Crush\<close>

text\<open>
These proofs use the high-level AutoCorrode entry point with no diagnostic
stepping and no custom branch.  The first simplification phase must see the
same installed AutoLocality procedures as an ordinary downstream proof.
This theory is intentionally downstream of Crush and belongs in the separate
B0 session based on Crush, not in the semantic Autogen umbrella.
\<close>

lemma b0_crush_base_record:
  shows \<open>b0_has_a (b0_set_c n (b0_set_b m R)) = b0_has_a R\<close>
  by (crush_base)

lemma b0_crush_base_locale:
  shows \<open>b0_global_one.b0_parent_attr
      (b0_set_d n (b0_global_one.b0_child_op R)) =
    b0_global_one.b0_parent_attr (b0_global_one.b0_child_op R)\<close>
  by (crush_base)

lemma b0_crush_base_standard_record:
  shows \<open>b0_std_has_b
      (b0_std_bump_a (b0_std_set_c n R)) =
    b0_std_has_b R\<close>
  by (crush_base)

lemma b0_crush_base_nested_traversal:
  shows \<open>b0_join_flags
      (b0_walk_pred (b0_walk_set_b n R))
      (b0_walk_pred (b0_walk_set_c m R)) =
    b0_join_flags (b0_walk_pred R) (b0_walk_pred R)\<close>
  by (crush_base)

subsection\<open>Scoped opt-out under Crush\<close>

context
  notes [[locality_no_cancel]]
begin

text\<open>
The following unfolding proofs are controls only: they show that the goals
remain semantically true while cancellation is disabled.  The semantic suite
contains the conclusive public Simplifier probes.  A negative
@{method crush_base} callback/count assertion is deferred to the frozen
instrumentation API because safely asserting method failure here would require
diagnostic or internal control.
\<close>

lemma b0_crush_base_opt_out_definitional_control:
  shows \<open>b0_has_a (b0_set_c n R) = b0_has_a R\<close>
  by (crush_base simp add: b0_has_a_def b0_set_c_def)

context
begin

lemma b0_crush_base_opt_out_inherited_definitional_control:
  shows \<open>b0_has_a (b0_set_d n R) = b0_has_a R\<close>
  by (crush_base simp add: b0_has_a_def b0_set_d_def)

end

end

lemma b0_crush_base_opt_out_restored:
  shows \<open>b0_has_a (b0_set_c n R) = b0_has_a R\<close>
  by (crush_base)

(*<*)
end
(*>*)
