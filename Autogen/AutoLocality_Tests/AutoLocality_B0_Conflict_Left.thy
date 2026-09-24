(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Conflict_Left
  imports AutoLocality_B0_Conflict_Base
begin
(*>*)

locality_lemma for b0_conflict:
  \<open>b0_conflict_shared_op\<close> footprint [b0_conflict_a] .
locality_lemma for b0_conflict:
  \<open>b0_conflict_shared_attr\<close> footprint [b0_conflict_b] .

definition b0_conflict_left_only ::
    \<open>b0_conflict \<Rightarrow> b0_conflict\<close> where
  \<open>b0_conflict_left_only R \<equiv> update_b0_conflict_c Suc R\<close>

locality_lemma for b0_conflict:
  \<open>b0_conflict_left_only\<close> footprint [b0_conflict_c] .

lemma b0_conflict_left_fixture:
  shows \<open>b0_conflict_shared_attr (b0_conflict_left_only R) =
    b0_conflict_shared_attr R\<close>
  by simp

(*<*)
end
(*>*)
