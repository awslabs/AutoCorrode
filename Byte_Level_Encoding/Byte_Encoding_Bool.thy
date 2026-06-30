(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Bool
  imports Byte_Encoding_Word_Nat
begin
(*>*)

section\<open>Byte encoding for booleans\<close>

text\<open>A boolean occupies a single byte: \<^verbatim>\<open>True\<close> is encoded as \<^verbatim>\<open>1\<close> and
\<^verbatim>\<open>False\<close> as \<^verbatim>\<open>0\<close>. Unlike the word encodings, decoding is \<^emph>\<open>partial\<close>: only
the bytes \<^verbatim>\<open>0\<close> and \<^verbatim>\<open>1\<close> are valid encodings, so the projection returns
\<^term>\<open>None\<close> on any other byte. The encoding is therefore a genuine prism
rather than an isomorphism, in the same spirit as the niche encoding for
optional non-null pointers (see \<^verbatim>\<open>Niche_Encoding_Option_NonNull\<close>).

Unlike the word encodings, a boolean occupies a single byte, so there is no
endianness and no intermediate array/list layer: the encoding is a prism
directly from \<^typ>\<open>byte\<close>.\<close>

definition bool_to_byte :: \<open>bool \<Rightarrow> byte\<close> where
  \<open>bool_to_byte b = (if b then 1 else 0)\<close>

definition byte_to_bool :: \<open>byte \<Rightarrow> bool option\<close> where
  \<open>byte_to_bool w = (if w = 0 then Some False else if w = 1 then Some True else None)\<close>

definition bool_byte_prism :: \<open>(byte, bool) prism\<close> where
  \<open>bool_byte_prism \<equiv> make_prism bool_to_byte byte_to_bool\<close>

lemma bool_byte_prism_valid:
  shows \<open>is_valid_prism bool_byte_prism\<close>
by (auto simp add: is_valid_prism_def bool_byte_prism_def bool_to_byte_def byte_to_bool_def
  split: if_splits)

lift_definition bool_byte_focus :: \<open>(byte, bool) focus\<close> is \<open>prism_to_focus_raw bool_byte_prism\<close>
using bool_byte_prism_valid prism_to_focus_raw_valid by blast

(*<*)
end
(*>*)
