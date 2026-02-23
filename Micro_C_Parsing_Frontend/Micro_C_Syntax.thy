(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_C_Syntax
  imports
    "Isabelle_C.C_Main"
begin

section \<open>Isabelle/C Parser Integration\<close>

text \<open>Verify that the Isabelle/C parser loads and can parse trivial C code.\<close>

C \<open>
int main(void) {
  return 0;
}
\<close>

C \<open>
void swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}
\<close>

end
