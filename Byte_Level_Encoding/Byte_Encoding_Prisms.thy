(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Prisms
  imports Byte_Encoding_Word_Nat
begin
(*>*)

section\<open>Generic prism material for byte encodings\<close>

text\<open>This theory collects the byte-encoding prism machinery that is generic, that
is, not tied to any particular record layout: the \<^verbatim>\<open>fixed_width_prism\<close> predicate,
the fixed-width facts for the word leaf prisms, and the \<^verbatim>\<open>split_prism\<close> bridge from
a consume-all prism to a remaining-returning one.  It is imported by the other
\<^verbatim>\<open>Byte_Encoding_xxx\<close> theories.\<close>

subsection\<open>Fixed-width byte prisms\<close>

text\<open>A byte-list prism is \<^emph>\<open>fixed-width\<close> at \<^term>\<open>n\<close> when it is valid, every
embedding has length \<^term>\<open>n\<close>, and every successful projection consumes exactly
\<^term>\<open>n\<close> bytes.  The width lets a pair split a concatenation at the right
boundary, and the projection-length fact is what makes the width \<^emph>\<open>compose\<close>.\<close>

definition fixed_width_prism :: \<open>nat \<Rightarrow> (byte list, 'a) prism \<Rightarrow> bool\<close> where
  \<open>fixed_width_prism n p \<longleftrightarrow> is_valid_prism p \<and> (\<forall>a. length (prism_embed p a) = n)
      \<and> (\<forall>bs a. prism_project p bs = Some a \<longrightarrow> length bs = n)\<close>

lemma fixed_width_prismI:
  assumes \<open>is_valid_prism p\<close>
      and \<open>\<And>a. length (prism_embed p a) = n\<close>
      and \<open>\<And>bs a. prism_project p bs = Some a \<Longrightarrow> length bs = n\<close>
    shows \<open>fixed_width_prism n p\<close>
  using assms by (auto simp add: fixed_width_prism_def)

lemma fixed_width_prism_valid:
  assumes \<open>fixed_width_prism n p\<close>
    shows \<open>is_valid_prism p\<close>
  using assms by (simp add: fixed_width_prism_def)

subsection\<open>Leaf fields: the fixed-width word prisms\<close>

text\<open>The little-endian word byte-list prisms are fixed-width (2/4/8/16 bytes), so
they serve as the leaf fields of a record.  These are the facts a record
combinator looks up for each \<^verbatim>\<open>u16\<close>/\<^verbatim>\<open>u32\<close>/\<^verbatim>\<open>u64\<close>/\<^verbatim>\<open>u128\<close> field.\<close>

lemma fixed_width_word16_le: \<open>fixed_width_prism 2 word16_byte_list_prism_le\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism word16_byte_list_prism_le\<close>
    by (rule word_byte_array_prism_validity)
next
  fix a show \<open>length (prism_embed word16_byte_list_prism_le a) = 2\<close>
    by (simp add: word_byte_array_prism_defs word_byte_array_iso_prism_defs prism_compose_def
        iso_prism_def list_fixlen_prism_def list_fixlen_embed_def)
next
  fix bs a assume \<open>prism_project word16_byte_list_prism_le bs = Some a\<close>
  then show \<open>length bs = 2\<close>
    by (auto simp add: word_byte_array_prism_defs prism_compose_def list_fixlen_prism_def
        list_fixlen_project_def bind_eq_Some_conv split: if_splits)
qed

lemma fixed_width_word32_le: \<open>fixed_width_prism 4 word32_byte_list_prism_le\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism word32_byte_list_prism_le\<close>
    by (rule word_byte_array_prism_validity)
next
  fix a show \<open>length (prism_embed word32_byte_list_prism_le a) = 4\<close>
    by (simp add: word_byte_array_prism_defs word_byte_array_iso_prism_defs prism_compose_def
        iso_prism_def list_fixlen_prism_def list_fixlen_embed_def)
next
  fix bs a assume \<open>prism_project word32_byte_list_prism_le bs = Some a\<close>
  then show \<open>length bs = 4\<close>
    by (auto simp add: word_byte_array_prism_defs prism_compose_def list_fixlen_prism_def
        list_fixlen_project_def bind_eq_Some_conv split: if_splits)
qed

lemma fixed_width_word64_le: \<open>fixed_width_prism 8 word64_byte_list_prism_le\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism word64_byte_list_prism_le\<close>
    by (rule word_byte_array_prism_validity)
next
  fix a show \<open>length (prism_embed word64_byte_list_prism_le a) = 8\<close>
    by (simp add: word_byte_array_prism_defs word_byte_array_iso_prism_defs prism_compose_def
        iso_prism_def list_fixlen_prism_def list_fixlen_embed_def)
next
  fix bs a assume \<open>prism_project word64_byte_list_prism_le bs = Some a\<close>
  then show \<open>length bs = 8\<close>
    by (auto simp add: word_byte_array_prism_defs prism_compose_def list_fixlen_prism_def
        list_fixlen_project_def bind_eq_Some_conv split: if_splits)
qed

lemma fixed_width_word128_le: \<open>fixed_width_prism 16 word128_byte_list_prism_le\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism word128_byte_list_prism_le\<close>
    by (rule word128_byte_array_prism_validity)
next
  fix a show \<open>length (prism_embed word128_byte_list_prism_le a) = 16\<close>
    by (simp add: word_byte_array_prism_defs word_byte_array_iso_prism_defs prism_compose_def
        iso_prism_def list_fixlen_prism_def list_fixlen_embed_def)
next
  fix bs a assume \<open>prism_project word128_byte_list_prism_le bs = Some a\<close>
  then show \<open>length bs = 16\<close>
    by (auto simp add: word_byte_array_prism_defs prism_compose_def list_fixlen_prism_def
        list_fixlen_project_def bind_eq_Some_conv split: if_splits)
qed

subsection\<open>Turning a fixed-width prism into a remaining-returning prism\<close>

text\<open>A consume-all byte prism decodes an entire byte list into one value.  A
parser instead peels off the bytes it needs and hands the rest back, so it can be
chained.  \<^verbatim>\<open>split_prism n p\<close> is that bridge: for a fixed-width prism \<^term>\<open>p\<close> of
width \<^term>\<open>n\<close>, it peels \<^term>\<open>n\<close> bytes, decodes them through \<^term>\<open>p\<close>, and
pairs the result with the remaining bytes.  Its validity is take/drop reasoning
only; no induction is involved.\<close>

definition split_prism :: \<open>nat \<Rightarrow> (byte list, 'x) prism \<Rightarrow> (byte list, 'x \<times> byte list) prism\<close> where
  \<open>split_prism n p \<equiv> make_prism
     (\<lambda>(x, rest). prism_embed p x @ rest)
     (\<lambda>bs. map_option (\<lambda>x. (x, drop n bs)) (prism_project p (take n bs)))\<close>

lemma split_prism_valid:
  assumes \<open>fixed_width_prism n p\<close>
    shows \<open>is_valid_prism (split_prism n p)\<close>
proof -
  from assms have vp: \<open>is_valid_prism p\<close>
    and wp: \<open>\<And>a. length (prism_embed p a) = n\<close>
    by (auto simp add: fixed_width_prism_def)
  have pe: \<open>prism_project p (prism_embed p x) = Some x\<close> for x
    using vp by (simp add: prism_laws)
  have pj: \<open>bs = prism_embed p x @ drop n bs\<close> if \<open>prism_project p (take n bs) = Some x\<close> for bs x
  proof -
    from that vp have \<open>take n bs = prism_embed p x\<close>
      by (simp add: prism_laws)
    then have \<open>prism_embed p x @ drop n bs = take n bs @ drop n bs\<close>
      by simp
    then show ?thesis
      by (simp add: append_take_drop_id)
  qed
  show ?thesis
    unfolding is_valid_prism_def split_prism_def
    by (auto simp add: wp pe pj split: prod.splits)
qed

subsection\<open>The single-byte identity prism\<close>

text\<open>A \<^verbatim>\<open>u8\<close> is a single byte carried unchanged.  \<^verbatim>\<open>byte_id_prism\<close> is the byte-list
prism for one raw byte: embedding wraps it in a singleton list, projecting reads
exactly one byte and fails otherwise.  It is the element prism of a pad field
\<^verbatim>\<open>[u8; N]\<close> (an array of raw bytes), and is fixed-width \<^term>\<open>1\<close>.\<close>

definition byte_id_prism :: \<open>(byte list, byte) prism\<close> where
  \<open>byte_id_prism \<equiv> make_prism (\<lambda>b. [b]) (\<lambda>bs. case bs of [b] \<Rightarrow> Some b | _ \<Rightarrow> None)\<close>

lemma fixed_width_byte_id: \<open>fixed_width_prism 1 byte_id_prism\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism byte_id_prism\<close>
    unfolding is_valid_prism_def byte_id_prism_def by (auto split: list.splits)
next
  fix a show \<open>length (prism_embed byte_id_prism a) = 1\<close>
    by (simp add: byte_id_prism_def)
next
  fix bs a assume \<open>prism_project byte_id_prism bs = Some a\<close>
  then show \<open>length bs = 1\<close>
    by (auto simp add: byte_id_prism_def split: list.splits)
qed

(*<*)
end
(*>*)
