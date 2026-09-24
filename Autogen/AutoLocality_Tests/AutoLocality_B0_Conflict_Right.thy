(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Conflict_Right
  imports AutoLocality_B0_Conflict_Base
begin
(*>*)

locality_lemma for b0_conflict:
  \<open>b0_conflict_shared_op\<close> footprint [b0_conflict_a] .
locality_lemma for b0_conflict:
  \<open>b0_conflict_shared_attr\<close> footprint [b0_conflict_b] .

definition b0_conflict_right_only ::
    \<open>b0_conflict \<Rightarrow> bool\<close> where
  \<open>b0_conflict_right_only R \<equiv> b0_conflict_c R = 0\<close>

locality_lemma for b0_conflict:
  \<open>b0_conflict_right_only\<close> footprint [b0_conflict_c] .

lemma b0_conflict_right_fixture:
  shows \<open>b0_conflict_right_only (b0_conflict_shared_op R) =
    b0_conflict_right_only R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_conflict_right_shared_attribute_smoke:
  shows \<open>b0_conflict_shared_attr (b0_conflict_shared_op R) =
    b0_conflict_shared_attr R\<close>
  by simp

(*<*)
end
(*>*)
