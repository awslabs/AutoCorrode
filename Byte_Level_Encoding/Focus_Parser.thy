(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Focus_Parser
  imports Lenses_And_Other_Optics.Focus Lenses_And_Other_Optics.List_Optics Lenses_And_Other_Optics.Array_Optics
begin
(*>*)

section\<open>Focus parsers\<close>

subsection\<open>Definition\<close>

datatype ('a, 'r) focus_parser
  = FocusParser (run_parser: \<open>('a, 'r \<times> 'a) focus\<close>)

subsection\<open>Parser combinators\<close>

text\<open>Parsers can be sequenced:\<close>

lift_definition iso_focus_prod_assoc :: \<open>('a \<times> 'b \<times> 'c, ('a \<times> 'b) \<times> 'c) focus\<close> is
  \<open>iso\<^sub>\<integral> (\<lambda>(x,y,z). ((x,y),z)) (\<lambda>((x,y),z). (x,y,z))\<close>
by (simp add: case_prod_beta iso_focus_raw_valid)

text\<open>Use eta expansion during code generation to avoid ML value restriction:\<close>
definition iso_focus_prod_assoc_lazy :: \<open>unit \<Rightarrow> ('a \<times> 'b \<times> 'c, ('a \<times> 'b) \<times> 'c) focus\<close> where
  \<open>iso_focus_prod_assoc_lazy _ = iso_focus_prod_assoc\<close>

declare iso_focus_prod_assoc_lazy_def [of \<open>()\<close>, symmetric, code_unfold]
declare iso_focus_prod_assoc_lazy_def [THEN  arg_cong[where f="Rep_focus"], simplified iso_focus_prod_assoc.rep_eq, code]

lemma iso_focus_prod_components[focus_components]:
  shows \<open>focus_view iso_focus_prod_assoc (x,y,z) = Some ((x,y),z)\<close>
    and \<open>focus_update iso_focus_prod_assoc ((x,y),z) t = (x,y,z)\<close> 
by (transfer; clarsimp simp add: iso_focus_raw_components)+

definition focus_parser_sequence :: \<open>('a, 'r) focus_parser \<Rightarrow> ('a, 's) focus_parser \<Rightarrow>
     ('a, 'r \<times> 's) focus_parser\<close> (infixl "--\<^sub>\<integral>" 58) where
  \<open>focus_parser_sequence p0 p1 \<equiv> FocusParser (run_parser p0 \<diamondop> (id\<^sub>\<integral> \<times>\<^sub>\<integral> run_parser p1) \<diamondop> iso_focus_prod_assoc)\<close>

text\<open>Parsers can be refined by applying a focus to a parsing result:\<close>
definition focus_parser_map :: \<open>('a, 'r) focus_parser \<Rightarrow> ('r, 's) focus \<Rightarrow>
      ('a, 's) focus_parser\<close> (infixl ">>\<^sub>\<integral>" 61) where
  \<open>focus_parser_map p0 f \<equiv> FocusParser (run_parser p0 \<diamondop> (f \<times>\<^sub>\<integral> id\<^sub>\<integral>))\<close>

text\<open>With sequencing and forgetting, we can build a sequence combinator for parsers which forgets
the result of one of the two parsers:\<close>
abbreviation focus_parser_sequence_forgetL :: \<open>('a, 'r) focus_parser \<Rightarrow> ('a, 's) focus_parser \<Rightarrow>
      ('a, 's) focus_parser\<close> (infixl "|--\<^sub>\<integral>" 58) where
  \<open>focus_parser_sequence_forgetL p0 p1 \<equiv> (p0 --\<^sub>\<integral> p1) >>\<^sub>\<integral> snd\<^sub>\<integral>\<close>

abbreviation focus_parser_sequence_forgetR :: \<open>('a, 'r) focus_parser \<Rightarrow> ('a, 's) focus_parser \<Rightarrow>
      ('a, 'r) focus_parser\<close> (infixl "--|\<^sub>\<integral>" 58) where
  \<open>focus_parser_sequence_forgetR p0 p1 \<equiv> (p0 --\<^sub>\<integral> p1) >>\<^sub>\<integral> fst\<^sub>\<integral>\<close>

bundle code_parser_notation
begin
  notation focus_parser_sequence (infixl "--" 58)
  notation focus_parser_map (infixl ">>" 61)
  notation focus_parser_sequence_forgetR (infixl "--|" 58) 
  notation focus_parser_sequence_forgetL (infixl "|--" 58) 
end

subsection\<open>Closing a parser\<close>

text\<open>After parsing, we can forget the remaining data to obtain a focus onto the target value type:\<close>
definition run_parser_partial :: \<open>('a, 'r) focus_parser \<Rightarrow> ('a, 'r) focus\<close> where
  \<open>run_parser_partial p \<equiv> run_parser p \<diamondop> fst\<^sub>\<integral>\<close>

text\<open>We may also want to check that we have consumed all data before closing the parser:\<close>
definition run_parser_all :: \<open>('a list, 'r) focus_parser \<Rightarrow> ('a list, 'r) focus\<close> where
  \<open>run_parser_all p \<equiv> run_parser p \<diamondop> (id\<^sub>\<integral> \<times>\<^sub>\<integral> list_empty_focus) \<diamondop> fst\<^sub>\<integral>\<close>

subsection\<open>Basic parsers\<close>

text\<open>Parse a single element from a list:\<close>
definition parse_single :: \<open>('a list, 'a) focus_parser\<close> where
  [code_unfold]: \<open>parse_single \<equiv> FocusParser list_nonempty_focus\<close>

text\<open>Parse a fixed number of elements off a list, into an array:\<close>
definition parse_array :: \<open>('a list, ('a, 'l::{len}) array) focus_parser\<close> where
  \<open>parse_array \<equiv> FocusParser list_minlen_focus\<close>

abbreviation parse_array2 :: \<open>('a list, ('a, 2) array) focus_parser\<close> where
  \<open>parse_array2 \<equiv> parse_array\<close>
abbreviation parse_array4 :: \<open>('a list, ('a, 4) array) focus_parser\<close> where
  \<open>parse_array4 \<equiv> parse_array\<close>
abbreviation parse_array8 :: \<open>('a list, ('a, 8) array) focus_parser\<close> where
  \<open>parse_array8 \<equiv> parse_array\<close>

(*<*)
end
(*>*)
