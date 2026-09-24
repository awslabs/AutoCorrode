(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Conflict_Base
  imports Autogen.AutoLocality
begin
(*>*)

section\<open>Independent sibling-merge fixture\<close>

text\<open>
The two child theories independently register the same shared operation and
attribute.  A later ROOT integrator should enter both branches independently
so their smoke lemmas execute, but must not join them through an ordinary
theory import.  Two-order merge failure requires the frozen pure merge API or
an external expected-failure child session so the expected conflict does not
abort normal processing.
\<close>

datatype_record b0_conflict =
  b0_conflict_a :: nat
  b0_conflict_b :: nat
  b0_conflict_c :: nat

locality_init for b0_conflict

definition b0_conflict_shared_op ::
    \<open>b0_conflict \<Rightarrow> b0_conflict\<close> where
  \<open>b0_conflict_shared_op R \<equiv> update_b0_conflict_a Suc R\<close>

definition b0_conflict_shared_attr ::
    \<open>b0_conflict \<Rightarrow> bool\<close> where
  \<open>b0_conflict_shared_attr R \<equiv> b0_conflict_b R > 0\<close>

(*<*)
end
(*>*)
