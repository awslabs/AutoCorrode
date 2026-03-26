(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Markup_Test
  imports Main
begin
(*>*)

section \<open>Test section with markup\<close>

text \<open>This theory exercises various Isabelle comment and markup styles
that I/CS must handle correctly.\<close>

definition a_val where "a_val = (1::nat)"

text \<open>A multiline text block.
It can span several lines and contain \<^emph>\<open>markup\<close>.\<close>

(* An old-style ML comment inside the theory body *)
definition b_val where
  "b_val = a_val + 1" \<comment> \<open>inline comment on a definition\<close>

subsection \<open>A subsection\<close>

lemma a_val_eq: "a_val = 1"
  by (simp add: a_val_def)

(*<*)
(* Document markers: (*<*) hides from document, (*>*) shows again *)
(*>*)

lemma b_val_eq: "b_val = 2"
  by (simp add: b_val_def a_val_def)

end
