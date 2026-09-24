(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Diamond_Left
  imports AutoLocality_Test_Diamond_Base
begin
(*>*)

definition diamond_left_op :: \<open>diamond_rec \<Rightarrow> diamond_rec\<close> where
  \<open>diamond_left_op R \<equiv> update_dic Suc R\<close>

definition diamond_left_attr :: \<open>diamond_rec \<Rightarrow> bool\<close> where
  \<open>diamond_left_attr R \<equiv> dia R > 0\<close>

locality_lemma for diamond_rec: \<open>diamond_left_op\<close> footprint [dic] .
locality_lemma for diamond_rec: \<open>diamond_left_attr\<close> footprint [dia] .

(*<*)
end
(*>*)
