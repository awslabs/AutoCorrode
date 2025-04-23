(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Vector_Optics
  imports Focus Misc.Vector
begin
(*>*)

section\<open>Optics for vectors\<close>

lift_definition nth_focus_vector :: \<open>nat \<Rightarrow> (('v, 'l::len) vector, 'v) focus\<close> is
  \<open>\<lambda>idx. make_focus_raw_via_view_modify (vector_nth_opt idx) (vector_over_nth idx)\<close>
by (simp add: is_valid_focus_via_modifyI vector_over_nth_is_valid)

(*<*)
end
(*>*)