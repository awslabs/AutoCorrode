(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Sibling_Left
  imports AutoLocality_Test_Sibling_Base
begin
(*>*)

locality_init for sibling_dispatch_rec

locality_lemma for sibling_dispatch_rec:
  \<open>sibling_dispatch_attr\<close> footprint [sibling_dispatch_a] .

(*<*)
end
(*>*)
