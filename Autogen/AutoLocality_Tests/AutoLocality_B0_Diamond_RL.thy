(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Diamond_RL
  imports
    AutoLocality_B0_Diamond_Right
    AutoLocality_B0_Diamond_Left
begin
(*>*)

section\<open>Right-then-left import join\<close>

lemma b0_diamond_rl_common_origin:
  shows \<open>b0_diamond_common_attr
      (b0_diamond_right_op
        (b0_diamond_left_op (b0_diamond_common_op R))) =
    b0_diamond_common_attr R\<close>
  by simp

lemma b0_diamond_rl_distinct_families:
  shows \<open>b0_diamond_left_attr
      (b0_diamond_right_op (b0_diamond_left_op R)) =
    b0_diamond_left_attr R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_diamond_rl_sibling_visibility:
  shows \<open>b0_diamond_right_attr
      (b0_diamond_common_op (b0_diamond_right_op R)) =
    b0_diamond_right_attr R\<close>
  by simp

(*<*)
end
(*>*)
