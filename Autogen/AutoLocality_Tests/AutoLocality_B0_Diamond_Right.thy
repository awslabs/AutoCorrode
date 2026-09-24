(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Diamond_Right
  imports AutoLocality_B0_Diamond_Base
begin
(*>*)

definition b0_diamond_right_op ::
    \<open>b0_diamond \<Rightarrow> b0_diamond\<close> where
  \<open>b0_diamond_right_op R \<equiv> update_b0_dd Suc R\<close>

definition b0_diamond_right_attr ::
    \<open>b0_diamond \<Rightarrow> nat\<close> where
  \<open>b0_diamond_right_attr R \<equiv> b0_dc R\<close>

locality_lemma for b0_diamond:
  \<open>b0_diamond_right_op\<close> footprint [b0_dd] .
locality_lemma for b0_diamond:
  \<open>b0_diamond_right_attr\<close> footprint [b0_dc] .

lemma b0_diamond_right_branch:
  shows \<open>b0_diamond_common_attr (b0_diamond_right_op R) =
    b0_diamond_common_attr R\<close>
  by (simp only: [[locality_cancel]])

(*<*)
end
(*>*)
