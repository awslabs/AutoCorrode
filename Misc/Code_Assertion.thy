(* Author: Florian Haftmann, TU Muenchen
   SPDX-License-Identifier: MIT *)

theory Code_Assertion
  imports Main
begin

ML_file \<open>Tools/code_assertion.ML\<close>

attribute_setup code_assert = Code_Assertion.attribute
  \<open>check code generation for each global interpretation using the given definitions and target language\<close>

text \<open>
  E.g. use
\<close>

text \<open>
  @{attribute code_assert}: operation in OCaml
\<close>

text \<open>
  in a locale whose @{command global_interpretation}s shall be checked accordingly.

  Use
\<close>

text \<open>
  @{command declare} [[@{attribute code_apply_assertion}]]
\<close>

text \<open>
  and
\<close>

text \<open>
  @{command declare} [[@{attribute code_apply_assertion} = false]]
\<close>

text \<open>
  to switch assertions on and off as needed.
\<close>

end