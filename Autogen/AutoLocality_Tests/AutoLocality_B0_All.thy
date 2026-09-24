(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_All
  imports
    AutoLocality_B0_Reentry
    AutoLocality_B0_Types
    AutoLocality_B0_Traversal
    AutoLocality_B0_Diamond_LR
    AutoLocality_B0_Diamond_RL
begin
(*>*)

section\<open>AutoLocality B0 semantic umbrella\<close>

text\<open>
This fast umbrella contains only semantic B0 tests and has no import path to
@{verbatim \<open>Crush.Crush\<close>}.  A later ROOT integrator should place it in,
or directly above, the Autogen session.  Crush-facing B0 tests belong in a
separate session based on Crush and enter through
@{verbatim \<open>AutoLocality_B0_Crush_All\<close>}.

The conflict fixtures are not executable through this umbrella.  A later ROOT
integrator should enter the left and right branch theories independently so
each branch smoke test runs.  Testing merge failure in both import orders
requires the frozen pure merge API or an external expected-failure child
session; importing both branches here would make ordinary processing fail.
\<close>

(*<*)
end
(*>*)
