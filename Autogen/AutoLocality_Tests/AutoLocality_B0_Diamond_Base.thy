(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Diamond_Base
  imports AutoLocality_B0_Base
begin
(*>*)

section\<open>Common-origin import fixture\<close>

datatype_record b0_diamond =
  b0_da :: nat
  b0_db :: nat
  b0_dc :: nat
  b0_dd :: nat

locality_init for b0_diamond

definition b0_diamond_common_op ::
    \<open>b0_diamond \<Rightarrow> b0_diamond\<close> where
  \<open>b0_diamond_common_op R \<equiv> update_b0_da Suc R\<close>

definition b0_diamond_common_attr ::
    \<open>b0_diamond \<Rightarrow> bool\<close> where
  \<open>b0_diamond_common_attr R \<equiv> b0_db R > 0\<close>

locality_lemma for b0_diamond:
  \<open>b0_diamond_common_op\<close> footprint [b0_da] .
locality_lemma for b0_diamond:
  \<open>b0_diamond_common_attr\<close> footprint [b0_db] .

(*<*)
end
(*>*)
