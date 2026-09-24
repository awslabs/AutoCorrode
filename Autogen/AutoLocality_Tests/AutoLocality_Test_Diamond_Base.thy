(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Diamond_Base
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Common ancestor for import-diamond tests\<close>

datatype_record diamond_rec =
  dia :: nat
  dib :: nat
  dic :: nat

locality_init for diamond_rec

definition diamond_base_op :: \<open>diamond_rec \<Rightarrow> diamond_rec\<close> where
  \<open>diamond_base_op R \<equiv> update_dia Suc R\<close>

definition diamond_base_attr :: \<open>diamond_rec \<Rightarrow> bool\<close> where
  \<open>diamond_base_attr R \<equiv> dib R > 0\<close>

locality_lemma for diamond_rec: \<open>diamond_base_op\<close> footprint [dia] .
locality_lemma for diamond_rec: \<open>diamond_base_attr\<close> footprint [dib] .

(*<*)
end
(*>*)
