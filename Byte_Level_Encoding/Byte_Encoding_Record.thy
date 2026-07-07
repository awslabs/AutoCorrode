(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Record
  imports Byte_Encoding_Prisms Byte_Encoding_Word_Nat Byte_Encoding_Bool Byte_Encoding_Array Byte_Encoding_Enum
    "HOL-Library.Datatype_Records"
  keywords "define_byte_record" :: thy_decl
begin
(*>*)

section\<open>Byte encoding for fixed-layout records\<close>

text\<open>A fixed-layout record lays its fields out contiguously: the byte encoding of
\<^verbatim>\<open>{ f0, f1, ... }\<close> is the concatenation of each field's byte encoding.  This
section provides the combinator \<^verbatim>\<open>prod_byte_prism\<close> that pairs two field
byte-prisms, placing the first field's bytes (of fixed width \<^term>\<open>nA\<close>) before
the second's.  Multi-field records are obtained by nesting the combinator and
relabelling the resulting nested tuple to a named record via \<^const>\<open>iso_prism\<close>.

The combinator needs to know where one field ends and the next begins, so the
\<^emph>\<open>first\<close> field must be \<^emph>\<open>fixed-width\<close>: its embedding always has the same
length \<^term>\<open>nA\<close>, which is the split point on decode.  (As with arrays, a plain
\<^const>\<open>concat\<close> loses the field boundary, so the width information — carried by
\<^verbatim>\<open>fixed_width_prism\<close> — is what makes the pair invertible.)\<close>

subsection\<open>Leaf fields: single-byte prisms (\<^verbatim>\<open>bool\<close>, enums)\<close>

text\<open>The boolean and enum encodings are single-\<^emph>\<open>byte\<close> prisms
(\<^typ>\<open>(byte, 'a) prism\<close>), whereas a record field is a \<^emph>\<open>byte-list\<close> prism
(\<^typ>\<open>(byte list, 'a) prism\<close>).  \<^verbatim>\<open>single_byte_prism\<close> lifts any single-byte
prism to a one-element byte list, so a \<^verbatim>\<open>bool\<close> or enum can appear as a field.\<close>

definition single_byte_prism :: \<open>(byte, 'a) prism \<Rightarrow> (byte list, 'a) prism\<close> where
  \<open>single_byte_prism p \<equiv> make_prism
     (\<lambda>a. [prism_embed p a])
     (\<lambda>bs. case bs of [b] \<Rightarrow> prism_project p b | _ \<Rightarrow> None)\<close>

lemma fixed_width_single_byte:
  assumes \<open>is_valid_prism p\<close>
    shows \<open>fixed_width_prism 1 (single_byte_prism p)\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism (single_byte_prism p)\<close>
    using assms
    unfolding is_valid_prism_def single_byte_prism_def
    by (auto split: list.splits)
next
  fix a show \<open>length (prism_embed (single_byte_prism p) a) = 1\<close>
    by (simp add: single_byte_prism_def)
next
  fix bs a assume \<open>prism_project (single_byte_prism p) bs = Some a\<close>
  then show \<open>length bs = 1\<close>
    by (auto simp add: single_byte_prism_def split: list.splits)
qed

text\<open>The boolean field prism, and its fixed width.\<close>

definition bool_byte_list_prism :: \<open>(byte list, bool) prism\<close> where
  \<open>bool_byte_list_prism \<equiv> single_byte_prism bool_byte_prism\<close>

lemma fixed_width_bool: \<open>fixed_width_prism 1 bool_byte_list_prism\<close>
  unfolding bool_byte_list_prism_def
  by (rule fixed_width_single_byte[OF bool_byte_prism_valid])

text\<open>A \<^verbatim>\<open>u8\<close> field is a single byte: the identity prism on \<^typ>\<open>byte\<close>, lifted to
a one-element byte list.\<close>

definition byte_byte_list_prism :: \<open>(byte list, byte) prism\<close> where
  \<open>byte_byte_list_prism \<equiv> single_byte_prism (iso_prism (\<lambda>b. b) (\<lambda>b. b))\<close>

lemma fixed_width_u8: \<open>fixed_width_prism 1 byte_byte_list_prism\<close>
  unfolding byte_byte_list_prism_def
  by (rule fixed_width_single_byte[OF iso_prism_valid]) simp_all

subsection\<open>The pair combinator\<close>

text\<open>\<^verbatim>\<open>prod_byte_prism\<close> places \<^term>\<open>pA\<close>'s bytes (width \<^term>\<open>nA\<close>) before
\<^term>\<open>pB\<close>'s.  Embedding concatenates; projecting splits at \<^term>\<open>nA\<close> and runs
each side's projector.\<close>

definition prod_byte_embed ::
    \<open>(byte list, 'a) prism \<Rightarrow> (byte list, 'b) prism \<Rightarrow> 'a \<times> 'b \<Rightarrow> byte list\<close> where
  \<open>prod_byte_embed pA pB \<equiv> \<lambda>(a, b). prism_embed pA a @ prism_embed pB b\<close>

definition prod_byte_project ::
    \<open>nat \<Rightarrow> (byte list, 'a) prism \<Rightarrow> (byte list, 'b) prism \<Rightarrow> byte list \<Rightarrow> ('a \<times> 'b) option\<close> where
  \<open>prod_byte_project nA pA pB bs \<equiv>
     Option.bind (prism_project pA (take nA bs)) (\<lambda>a.
     Option.bind (prism_project pB (drop nA bs)) (\<lambda>b. Some (a, b)))\<close>

definition prod_byte_prism ::
    \<open>nat \<Rightarrow> (byte list, 'a) prism \<Rightarrow> (byte list, 'b) prism \<Rightarrow> (byte list, 'a \<times> 'b) prism\<close> where
  \<open>prod_byte_prism nA pA pB \<equiv> make_prism (prod_byte_embed pA pB) (prod_byte_project nA pA pB)\<close>

text\<open>Validity of the pair: the round-trip law for the composite follows from each
field's law plus the fact that \<^term>\<open>pA\<close>'s embedding has the exact width
\<^term>\<open>nA\<close> at which we split.\<close>

lemma prod_byte_prism_valid:
  assumes \<open>fixed_width_prism nA pA\<close>
      and \<open>is_valid_prism pB\<close>
    shows \<open>is_valid_prism (prod_byte_prism nA pA pB)\<close>
proof -
  from assms(1) have vA: \<open>is_valid_prism pA\<close>
    and wA: \<open>\<And>a. length (prism_embed pA a) = nA\<close>
    by (auto simp add: fixed_width_prism_def)
  show ?thesis
    unfolding is_valid_prism_def
  proof (intro conjI allI impI)
    fix ab :: \<open>'a \<times> 'b\<close>
    obtain a b where ab: \<open>ab = (a, b)\<close>
      by (cases ab)
    have eA: \<open>prism_project pA (prism_embed pA a) = Some a\<close>
      using vA by (simp add: prism_laws)
    have eB: \<open>prism_project pB (prism_embed pB b) = Some b\<close>
      using assms(2) by (simp add: prism_laws)
    show \<open>prism_project (prod_byte_prism nA pA pB) (prism_embed (prod_byte_prism nA pA pB) ab) = Some ab\<close>
      by (simp add: ab prod_byte_prism_def prod_byte_embed_def prod_byte_project_def wA eA eB)
  next
    fix bs ab
    assume \<open>prism_project (prod_byte_prism nA pA pB) bs = Some ab\<close>
    then obtain a b where pa: \<open>prism_project pA (take nA bs) = Some a\<close>
                      and pb: \<open>prism_project pB (drop nA bs) = Some b\<close>
                      and ab: \<open>ab = (a, b)\<close>
      by (auto simp add: prod_byte_prism_def prod_byte_project_def bind_eq_Some_conv)
    from pa vA have ta: \<open>take nA bs = prism_embed pA a\<close>
      by (simp add: prism_laws)
    from pb assms(2) have da: \<open>drop nA bs = prism_embed pB b\<close>
      by (simp add: prism_laws)
    have \<open>bs = take nA bs @ drop nA bs\<close>
      by simp
    then show \<open>bs = prism_embed (prod_byte_prism nA pA pB) ab\<close>
      by (simp add: ab prod_byte_prism_def prod_byte_embed_def ta da)
  qed
qed

text\<open>The pair is itself fixed-width (\<^term>\<open>nA + nB\<close>).  This closure lets fields
chain — the result becomes the \<^term>\<open>pA\<close> of the next pair — and lets a whole
record nest as a field of another.\<close>

lemma prod_byte_prism_fixed_width:
  assumes \<open>fixed_width_prism nA pA\<close>
      and \<open>fixed_width_prism nB pB\<close>
    shows \<open>fixed_width_prism (nA + nB) (prod_byte_prism nA pA pB)\<close>
proof -
  from assms have vB: \<open>is_valid_prism pB\<close>
    and wA: \<open>\<And>a. length (prism_embed pA a) = nA\<close>
    and wB: \<open>\<And>b. length (prism_embed pB b) = nB\<close>
    and lA: \<open>\<And>bs a. prism_project pA bs = Some a \<Longrightarrow> length bs = nA\<close>
    and lB: \<open>\<And>bs b. prism_project pB bs = Some b \<Longrightarrow> length bs = nB\<close>
    by (auto simp add: fixed_width_prism_def)
  have valid: \<open>is_valid_prism (prod_byte_prism nA pA pB)\<close>
    using assms(1) vB by (rule prod_byte_prism_valid)
  moreover have \<open>length (prism_embed (prod_byte_prism nA pA pB) ab) = nA + nB\<close> for ab
    by (cases ab) (simp add: prod_byte_prism_def prod_byte_embed_def wA wB)
  moreover have \<open>length bs = nA + nB\<close>
    if \<open>prism_project (prod_byte_prism nA pA pB) bs = Some ab\<close> for bs ab
  proof -
    from that obtain a b where pa: \<open>prism_project pA (take nA bs) = Some a\<close>
                           and pb: \<open>prism_project pB (drop nA bs) = Some b\<close>
      by (auto simp add: prod_byte_prism_def prod_byte_project_def bind_eq_Some_conv)
    from pa lA have \<open>length (take nA bs) = nA\<close>
      by blast
    moreover from pb lB have \<open>length (drop nA bs) = nB\<close>
      by blast
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by (simp add: fixed_width_prism_def)
qed

subsection\<open>Relabelling a nested tuple as a named record\<close>

text\<open>Wrapping the raw pair (a nested tuple) in a record type is a pure
\<^const>\<open>iso_prism\<close>: it relabels the value without touching the bytes, so it
preserves both validity and the fixed width.  This is what turns a chain of
fields into a payload of a named \<^verbatim>\<open>datatype_record\<close>.\<close>

lemma fixed_width_compose_iso:
  assumes \<open>fixed_width_prism n pA\<close>
      and \<open>\<And>x. f (g x) = x\<close>
      and \<open>\<And>y. g (f y) = y\<close>
    shows \<open>fixed_width_prism n (prism_compose pA (iso_prism f g))\<close>
proof -
  from assms(1) have vA: \<open>is_valid_prism pA\<close>
    and wA: \<open>\<And>a. length (prism_embed pA a) = n\<close>
    and lA: \<open>\<And>bs a. prism_project pA bs = Some a \<Longrightarrow> length bs = n\<close>
    by (auto simp add: fixed_width_prism_def)
  have viso: \<open>is_valid_prism (iso_prism f g)\<close>
    using assms(2,3) by (rule iso_prism_valid)
  show ?thesis
    unfolding fixed_width_prism_def
  proof (intro conjI allI impI)
    show \<open>is_valid_prism (prism_compose pA (iso_prism f g))\<close>
      using vA viso by (rule prism_compose_valid)
  next
    fix a
    show \<open>length (prism_embed (prism_compose pA (iso_prism f g)) a) = n\<close>
      by (simp add: prism_compose_def iso_prism_def wA)
  next
    fix bs a
    assume \<open>prism_project (prism_compose pA (iso_prism f g)) bs = Some a\<close>
    then show \<open>length bs = n\<close>
      using lA by (auto simp add: prism_compose_def iso_prism_def bind_eq_Some_conv)
  qed
qed

subsection\<open>The \<^verbatim>\<open>define_byte_record\<close> command\<close>

text\<open>The \<^verbatim>\<open>define_byte_record\<close> command automates the per-record boilerplate.
Given a name and a field assignment

\<^verbatim>\<open>define_byte_record <T> = <f0>: <ty0> | <f1>: <ty1> | ...\<close>

it defines the record type (via \<^verbatim>\<open>datatype_record\<close>), builds \<^verbatim>\<open><T>_byte_prism\<close>
by nesting \<^const>\<open>prod_byte_prism\<close> over the per-field prisms and relabelling the
resulting tuple to the named record via \<^const>\<open>iso_prism\<close>, and proves the
round-trip law \<^verbatim>\<open><T>_byte_prism_valid\<close> automatically.  Field types may be
\<^verbatim>\<open>u8\<close>/\<^verbatim>\<open>u16\<close>/\<^verbatim>\<open>u32\<close>/\<^verbatim>\<open>u64\<close>/\<^verbatim>\<open>u128\<close>, \<^verbatim>\<open>bool\<close>, a pad \<^verbatim>\<open>[u8; N]\<close>, a word array
\<^verbatim>\<open>[uW; N]\<close>, an enum, or a nested record.\<close>

ML_file \<open>byte_encoding_record_cmd.ML\<close>

subsection\<open>Worked examples\<close>

text\<open>A two-field record, defined in one line by the command, with the type, byte
prism, and round-trip proof all generated.\<close>

define_byte_record pair_rec =
    pair_x: u32 | pair_y: u32

\<comment>\<open>The type, its fields, and the prism exist.\<close>
term \<open>pair_x\<close> term \<open>pair_y\<close>
term \<open>pair_rec_byte_prism :: (byte list, pair_rec) prism\<close>

\<comment>\<open>The round-trip law was proven automatically.\<close>
lemma \<open>is_valid_prism pair_rec_byte_prism\<close>
  by (rule pair_rec_byte_prism_valid)

text\<open>A record mixing word and boolean fields.\<close>

define_byte_record mixed_rec =
    mr_count: u16 | mr_flag: bool | mr_addr: u64

lemma \<open>is_valid_prism mixed_rec_byte_prism\<close>
  by (rule mixed_rec_byte_prism_valid)

text\<open>A record with pad and word-array fields.  Array/pad field types are written
in a cartouche.\<close>

define_byte_record padded_rec =
    pr_id: u32 | pr_pad: \<open>[u8; 4]\<close> | pr_vec: \<open>[u64; 3]\<close>

lemma \<open>is_valid_prism padded_rec_byte_prism\<close>
  by (rule padded_rec_byte_prism_valid)

text\<open>A record nested as a field of another record (naming convention: the field
type \<^verbatim>\<open>pair_rec\<close> resolves to \<^verbatim>\<open>pair_rec_byte_prism\<close> and
\<^verbatim>\<open>fixed_width_pair_rec\<close>, both generated above).\<close>

define_byte_record outer_rec =
    or_tag: u16 | or_inner: pair_rec

lemma \<open>is_valid_prism outer_rec_byte_prism\<close>
  by (rule outer_rec_byte_prism_valid)

text\<open>A record with an enum field (naming convention: the field type
\<^verbatim>\<open>demo_enum\<close> — defined by \<^verbatim>\<open>define_byte_enum\<close> — resolves to its single-byte
prism, lifted to a one-byte list field).\<close>

define_byte_record action_rec =
    ar_cpu: u16 | ar_action: demo_enum

lemma \<open>is_valid_prism action_rec_byte_prism\<close>
  by (rule action_rec_byte_prism_valid)

subsection\<open>Worked example: the command versus the same record by hand\<close>

text\<open>A 24-byte fixed-layout record
\<^verbatim>\<open>{ a: u64, b: u64, c: bool, d: u8, pad: [u8; 6] }\<close> mixing words, a boolean, a
single byte, and a pad run.  It illustrates what the command saves: first the
prism written \<^emph>\<open>by hand\<close> (record type, the nested field prism, and the
round-trip proof), then the \<^emph>\<open>same\<close> record in one line via
\<^verbatim>\<open>define_byte_record\<close>.\<close>

datatype_record demo_record_manual =
  drm_a   :: \<open>64 word\<close>
  drm_b   :: \<open>64 word\<close>
  drm_c   :: \<open>bool\<close>
  drm_d   :: \<open>byte\<close>
  drm_pad :: \<open>(byte, 6) array\<close>

definition demo_record_manual_byte_prism :: \<open>(byte list, demo_record_manual) prism\<close> where
  \<open>demo_record_manual_byte_prism \<equiv>
     prism_compose
       (prod_byte_prism 8 word64_byte_list_prism_le
         (prod_byte_prism 8 word64_byte_list_prism_le
           (prod_byte_prism 1 bool_byte_list_prism
             (prod_byte_prism 1 byte_byte_list_prism
               (list_fixlen_prism :: (byte list, (byte, 6) array) prism)))))
       (iso_prism
          (\<lambda>(a, b, c, d, pad). make_demo_record_manual a b c d pad)
          (\<lambda>r. (drm_a r, drm_b r, drm_c r, drm_d r, drm_pad r)))\<close>

lemma demo_record_manual_byte_prism_valid: \<open>is_valid_prism demo_record_manual_byte_prism\<close>
  unfolding demo_record_manual_byte_prism_def
  apply (rule prism_compose_valid)
   apply (rule prod_byte_prism_valid)
    apply (rule fixed_width_word64_le)
   apply (rule prod_byte_prism_valid)
    apply (rule fixed_width_word64_le)
   apply (rule prod_byte_prism_valid)
    apply (rule fixed_width_bool)
   apply (rule prod_byte_prism_valid)
    apply (rule fixed_width_u8)
   apply (rule fixed_width_prism_valid[OF fixed_width_pad])
  apply (rule iso_prism_valid)
   apply (simp_all split: prod.split)
  done

text\<open>The same record, in one line.\<close>

define_byte_record demo_record_auto =
    dra_a: u64 | dra_b: u64 | dra_c: bool
  | dra_d: u8 | dra_pad: \<open>[u8; 6]\<close>

lemma \<open>is_valid_prism demo_record_auto_byte_prism\<close>
  by (rule demo_record_auto_byte_prism_valid)


(*<*)
end
(*>*)
