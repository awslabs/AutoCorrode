(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Diamond_LR
  imports
    AutoLocality_B0_Diamond_Left
    AutoLocality_B0_Diamond_Right
begin
(*>*)

section\<open>Left-then-right import join\<close>

lemma b0_diamond_lr_common_origin:
  shows \<open>b0_diamond_common_attr
      (b0_diamond_right_op
        (b0_diamond_left_op (b0_diamond_common_op R))) =
    b0_diamond_common_attr R\<close>
  by simp

lemma b0_diamond_lr_distinct_families:
  shows \<open>b0_diamond_left_attr
      (b0_diamond_right_op (b0_diamond_left_op R)) =
    b0_diamond_left_attr R\<close>
  by (simp only: [[locality_cancel]])

lemma b0_diamond_lr_sibling_visibility:
  shows \<open>b0_diamond_right_attr
      (b0_diamond_common_op (b0_diamond_right_op R)) =
    b0_diamond_right_attr R\<close>
  by simp

(*<*)
end
(*>*)
