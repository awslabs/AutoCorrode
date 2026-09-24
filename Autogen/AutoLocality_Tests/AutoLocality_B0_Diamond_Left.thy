(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Diamond_Left
  imports AutoLocality_B0_Diamond_Base
begin
(*>*)

definition b0_diamond_left_op ::
    \<open>b0_diamond \<Rightarrow> b0_diamond\<close> where
  \<open>b0_diamond_left_op R \<equiv> update_b0_dc Suc R\<close>

definition b0_diamond_left_attr ::
    \<open>b0_diamond \<Rightarrow> nat\<close> where
  \<open>b0_diamond_left_attr R \<equiv> b0_da R\<close>

locality_lemma for b0_diamond:
  \<open>b0_diamond_left_op\<close> footprint [b0_dc] .
locality_lemma for b0_diamond:
  \<open>b0_diamond_left_attr\<close> footprint [b0_da] .

lemma b0_diamond_left_branch:
  shows \<open>b0_diamond_common_attr (b0_diamond_left_op R) =
    b0_diamond_common_attr R\<close>
  by simp

(*<*)
end
(*>*)
