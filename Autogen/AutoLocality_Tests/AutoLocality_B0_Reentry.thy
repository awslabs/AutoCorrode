(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Reentry
  imports AutoLocality_B0_Lifecycle
begin
(*>*)

section\<open>Exact registration replay\<close>

text\<open>
Immediate same-target duplicate registrations are covered in
AutoLocality_B0_Base.  Descendant locale declaration replay is
deferred to the Stage-2 registry and lifecycle tests and is not a B0 gate.
\<close>

locality_init for b0_state

lemma b0_top_level_reentry:
  shows \<open>b0_read_b (b0_set_c n (b0_set_a m R)) = b0_read_b R\<close>
  by simp

(*<*)
end
(*>*)
