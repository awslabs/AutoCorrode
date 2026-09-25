(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Sibling_Merge
  imports AutoLocality_Test_Sibling_Left AutoLocality_Test_Sibling_Right
begin
(*>*)

lemma sibling_dispatch_merge:
  shows \<open>sibling_dispatch_attr
      (update_sibling_dispatch_b f R) =
    sibling_dispatch_attr R\<close>
  by (simp only: [[locality_cancel]])

(*<*)
end
(*>*)
