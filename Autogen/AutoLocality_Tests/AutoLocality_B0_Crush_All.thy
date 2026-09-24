(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Crush_All
  imports
    AutoLocality_Tests.AutoLocality_B0_All
    AutoLocality_B0_Automation
begin
(*>*)

section\<open>AutoLocality B0 Crush umbrella\<close>

text\<open>
This downstream umbrella combines the fast semantic B0 suite with its
representative @{method crush_base} proofs.  A later ROOT integrator should
place it in a separate session based on Crush; the semantic umbrella remains
available in, or directly above, Autogen without a Crush dependency.
\<close>

(*<*)
end
(*>*)
