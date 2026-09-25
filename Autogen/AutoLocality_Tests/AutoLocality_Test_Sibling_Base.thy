(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Sibling_Base
  imports Autogen.AutoLocality
begin
(*>*)

datatype_record sibling_dispatch_rec =
  sibling_dispatch_a :: nat
  sibling_dispatch_b :: nat

definition sibling_dispatch_attr ::
    \<open>sibling_dispatch_rec \<Rightarrow> bool\<close> where
  \<open>sibling_dispatch_attr R \<equiv> sibling_dispatch_a R > 0\<close>

(*<*)
end
(*>*)
