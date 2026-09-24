(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Diamond_Right
  imports AutoLocality_Test_Diamond_Base
begin
(*>*)

definition diamond_right_op :: \<open>diamond_rec \<Rightarrow> diamond_rec\<close> where
  \<open>diamond_right_op R \<equiv> update_dib Suc R\<close>

definition diamond_right_attr :: \<open>diamond_rec \<Rightarrow> bool\<close> where
  \<open>diamond_right_attr R \<equiv> dic R > 0\<close>

locality_lemma for diamond_rec: \<open>diamond_right_op\<close> footprint [dib] .
locality_lemma for diamond_rec: \<open>diamond_right_attr\<close> footprint [dic] .

(*<*)
end
(*>*)
