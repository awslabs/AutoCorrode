(* Author: Florian Haftmann, TU Muenchen
   SPDX-License-Identifier: MIT *)

theory Code_Assertion
  imports Main
  keywords "code_assertion" :: thy_decl
begin

ML_file \<open>Tools/code_assertion.ML\<close>

text \<open>
  E.g. use
\<close>

text \<open>
  @{command code_assertion} operation in OCaml
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