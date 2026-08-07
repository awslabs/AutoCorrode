(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Array
  imports Byte_Encoding_Word_Nat Byte_Encoding_Prisms
begin
(*>*)

section\<open>Byte encoding for fixed-length arrays\<close>

text\<open>The word and boolean encodings turn a single value into a fixed run of
bytes.  A fixed-length array \<^verbatim>\<open>[T; N]\<close> instead lays out \<^term>\<open>N\<close> elements,
each itself encoded as a fixed-width byte run, contiguously.  This section
provides the generic combinator that turns an element byte-prism of constant
width \<^term>\<open>w\<close> into a byte-prism onto the fixed-length array type
\<^typ>\<open>('e, 'l::len) array\<close>, whose type-level length \<^verbatim>\<open>LENGTH('l)\<close> pins the
element count.

Unlike \<^const>\<open>list_fixlen_prism\<close> — which packages a byte list as a
\<^emph>\<open>byte\<close> array, one byte per element — here each element occupies \<^term>\<open>w\<close>
bytes and is decoded through its own prism, so the array decode is \<^emph>\<open>partial\<close>
(it fails if any element fails to decode, e.g. for an array of booleans).\<close>

subsection\<open>Decoding a byte list into elements\<close>

text\<open>\<^term>\<open>decode_chunks w dec n bs\<close> decodes \<^term>\<open>n\<close> consecutive \<^term>\<open>w\<close>-byte
chunks of \<^term>\<open>bs\<close> using the element decoder \<^term>\<open>dec\<close>, failing unless the
input is consumed exactly.  This is an internal helper for
\<^verbatim>\<open>array_byte_project\<close>; it is \<^emph>\<open>not\<close> a prism projection itself (it has no
paired embedding — the embedding side is plain \<^const>\<open>concat\<close>).\<close>

fun decode_chunks :: \<open>nat \<Rightarrow> (byte list \<Rightarrow> 'e option) \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> 'e list option\<close> where
  \<open>decode_chunks w dec 0 bs = (if bs = [] then Some [] else None)\<close>
| \<open>decode_chunks w dec (Suc n) bs =
     (case dec (take w bs) of None \<Rightarrow> None
      | Some e \<Rightarrow> (case decode_chunks w dec n (drop w bs) of None \<Rightarrow> None
                  | Some es \<Rightarrow> Some (e # es)))\<close>

text\<open>Decoding the concatenation of \<^term>\<open>n\<close> embedded elements recovers them
(the round-trip law, embedding side):\<close>

lemma decode_chunks_concat:
  assumes \<open>is_valid_prism p\<close>
      and \<open>\<And>e. length (prism_embed p e) = w\<close>
      and \<open>length es = n\<close>
    shows \<open>decode_chunks w (prism_project p) n (concat (map (prism_embed p) es)) = Some es\<close>
  using assms(3) proof (induction es arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then obtain m where m: \<open>n = Suc m\<close>
    by (cases n) auto
  have \<open>length es = m\<close>
    using Cons.prems m by simp
  then have IH: \<open>decode_chunks w (prism_project p) m (concat (map (prism_embed p) es)) = Some es\<close>
    by (rule Cons.IH)
  have tk: \<open>take w (prism_embed p e @ concat (map (prism_embed p) es)) = prism_embed p e\<close>
    using assms(2) by simp
  have dr: \<open>drop w (prism_embed p e @ concat (map (prism_embed p) es)) = concat (map (prism_embed p) es)\<close>
    using assms(2) by simp
  have pe: \<open>prism_project p (prism_embed p e) = Some e\<close>
    using assms(1) by (simp add: prism_laws)
  have \<open>decode_chunks w (prism_project p) (Suc m)
          (prism_embed p e @ concat (map (prism_embed p) es)) = Some (e # es)\<close>
    by (simp only: decode_chunks.simps tk dr pe IH option.case)
  then show ?case
    using m by simp
qed

text\<open>Conversely, a successful decode of a length-correct input is the embedding of
its result (the round-trip law, projection side):\<close>

lemma decode_chunks_inv:
  assumes \<open>is_valid_prism p\<close>
      and \<open>\<And>e. length (prism_embed p e) = w\<close>
      and \<open>length bs = w * n\<close>
      and \<open>decode_chunks w (prism_project p) n bs = Some es\<close>
    shows \<open>bs = concat (map (prism_embed p) es)\<close>
  using assms(3,4) proof (induction n arbitrary: bs es)
  case 0
  then show ?case by (simp split: if_splits)
next
  case (Suc n)
  from Suc.prems(2) obtain e es' where
        pe: \<open>prism_project p (take w bs) = Some e\<close>
    and rest: \<open>decode_chunks w (prism_project p) n (drop w bs) = Some es'\<close>
    and es: \<open>es = e # es'\<close>
    by (auto split: option.splits)
  from pe assms(1) have te: \<open>take w bs = prism_embed p e\<close>
    by (simp add: prism_laws)
  have \<open>length (drop w bs) = w * n\<close>
    using Suc.prems(1) by simp
  from this rest have \<open>drop w bs = concat (map (prism_embed p) es')\<close>
    by (rule Suc.IH)
  then have \<open>bs = prism_embed p e @ concat (map (prism_embed p) es')\<close>
    using te by (metis append_take_drop_id)
  then show ?case
    by (simp add: es)
qed

lemma decode_chunks_len:
  assumes \<open>decode_chunks w dec n bs = Some es\<close>
    shows \<open>length es = n\<close>
  using assms proof (induction n arbitrary: bs es)
  case 0
  then show ?case by (simp split: if_splits)
next
  case (Suc n)
  then show ?case by (auto split: option.splits)
qed

lemma concat_embed_len:
  assumes \<open>\<And>e. length (prism_embed p e) = w\<close>
    shows \<open>length (concat (map (prism_embed p) es)) = w * length es\<close>
  using assms by (induction es) (auto simp add: assms)

subsection\<open>The array byte-prism\<close>

text\<open>\<^verbatim>\<open>array_byte_embed\<close> embeds an array by concatenating each element's
\<^term>\<open>w\<close>-byte embedding; \<^verbatim>\<open>array_byte_project\<close> decodes by splitting the input
into \<^verbatim>\<open>LENGTH('l)\<close> pieces of width \<^term>\<open>w\<close> (via \<^verbatim>\<open>decode_chunks\<close>) and
decoding each.  These are the \<^emph>\<open>embed\<close> and \<^emph>\<open>project\<close> halves of
\<^verbatim>\<open>array_byte_prism\<close>.\<close>

definition array_byte_embed ::
    \<open>(byte list, 'e) prism \<Rightarrow> ('e, 'l::len) array \<Rightarrow> byte list\<close> where
  \<open>array_byte_embed p a \<equiv> concat (map (prism_embed p) (array_to_list a))\<close>

definition array_byte_project ::
    \<open>nat \<Rightarrow> (byte list, 'e) prism \<Rightarrow> byte list \<Rightarrow> ('e, 'l::len) array option\<close> where
  \<open>array_byte_project w p bs \<equiv>
     if length bs = w * LENGTH('l)
     then map_option array_of_list (decode_chunks w (prism_project p) (LENGTH('l)) bs)
     else None\<close>

definition array_byte_prism ::
    \<open>nat \<Rightarrow> (byte list, 'e) prism \<Rightarrow> (byte list, ('e, 'l::len) array) prism\<close> where
  \<open>array_byte_prism w p \<equiv> make_prism (array_byte_embed p) (array_byte_project w p)\<close>

text\<open>The round-trip law for the array follows from the element's law plus the fact
that each element embeds to exactly \<^term>\<open>w\<close> bytes.\<close>

lemma array_byte_prism_valid:
  assumes \<open>is_valid_prism p\<close>
      and \<open>\<And>e. length (prism_embed p e) = w\<close>
    shows \<open>is_valid_prism (array_byte_prism w p :: (byte list, ('e, 'l::len) array) prism)\<close>
  unfolding is_valid_prism_def
proof (intro conjI allI impI)
  have alen: \<open>\<And>a :: ('e, 'l) array. length (array_to_list a) = LENGTH('l)\<close>
    by simp
  fix a :: \<open>('e, 'l) array\<close>
  have cp: \<open>decode_chunks w (prism_project p) (LENGTH('l))
              (concat (map (prism_embed p) (array_to_list a))) = Some (array_to_list a)\<close>
    using assms alen by (rule decode_chunks_concat)
  have ln: \<open>length (concat (map (prism_embed p) (array_to_list a))) = w * LENGTH('l)\<close>
    using assms(2) by (simp add: concat_embed_len)
  show \<open>prism_project (array_byte_prism w p) (prism_embed (array_byte_prism w p) a) = Some a\<close>
    by (simp add: array_byte_prism_def array_byte_embed_def array_byte_project_def ln cp)
next
  fix bs and a :: \<open>('e, 'l) array\<close>
  assume \<open>prism_project (array_byte_prism w p) bs = Some a\<close>
  then have lbs: \<open>length bs = w * LENGTH('l)\<close>
        and cp: \<open>map_option array_of_list (decode_chunks w (prism_project p) (LENGTH('l)) bs) = Some a\<close>
    by (auto simp add: array_byte_prism_def array_byte_project_def split: if_splits)
  from cp obtain es where es: \<open>decode_chunks w (prism_project p) (LENGTH('l)) bs = Some es\<close>
                      and a: \<open>a = array_of_list es\<close>
    by auto
  from assms lbs es have bsc: \<open>bs = concat (map (prism_embed p) es)\<close>
    by (rule decode_chunks_inv)
  have \<open>length es = LENGTH('l)\<close>
    using es by (rule decode_chunks_len)
  then have \<open>array_to_list a = es\<close>
    using a by (simp add: list_to_array_to_list)
  then show \<open>bs = prism_embed (array_byte_prism w p) a\<close>
    using bsc by (simp add: array_byte_prism_def array_byte_embed_def)
qed

text\<open>The array prism is fixed-width: every array embeds to \<^verbatim>\<open>w * LENGTH('l)\<close>
bytes, and every successful projection consumes exactly that many.  These let an
array appear as a field of a larger fixed-layout record.\<close>

lemma array_byte_prism_embed_len:
  assumes \<open>\<And>e. length (prism_embed p e) = w\<close>
    shows \<open>length (prism_embed (array_byte_prism w p :: (byte list, ('e, 'l::len) array) prism) a)
             = w * LENGTH('l)\<close>
  using assms by (simp add: array_byte_prism_def array_byte_embed_def concat_embed_len)

lemma array_byte_prism_project_len:
  assumes \<open>prism_project (array_byte_prism w p :: (byte list, ('e, 'l::len) array) prism) bs = Some a\<close>
    shows \<open>length bs = w * LENGTH('l)\<close>
  using assms by (auto simp add: array_byte_prism_def array_byte_project_def split: if_splits)

text\<open>A concrete array encoding is obtained by instantiating the element prism
with a fixed-width element prism — for example \<^verbatim>\<open>array_byte_prism 8
word64_byte_list_prism_le\<close> for a \<^verbatim>\<open>[u64; N]\<close> field — whose validity follows
from \<^verbatim>\<open>array_byte_prism_valid\<close> and the element's embedding-length fact.\<close>

subsection\<open>Fixed-width facts for the array and pad leaves\<close>

text\<open>A pad field \<^verbatim>\<open>[u8; N]\<close> is exactly \<^const>\<open>list_fixlen_prism\<close> (a byte list to a
length-\<^term>\<open>N\<close> byte array), of fixed width \<^verbatim>\<open>LENGTH('l)\<close>.\<close>

lemma fixed_width_pad:
  \<open>fixed_width_prism (LENGTH('l::len)) (list_fixlen_prism :: (byte list, (byte, 'l) array) prism)\<close>
proof (rule fixed_width_prismI)
  show \<open>is_valid_prism (list_fixlen_prism :: (byte list, (byte, 'l) array) prism)\<close>
    by (rule list_fixlen_prism_valid)
next
  fix a show \<open>length (prism_embed (list_fixlen_prism :: (byte list, (byte, 'l) array) prism) a)
                = LENGTH('l)\<close>
    by (simp add: list_fixlen_prism_def list_fixlen_embed_def)
next
  fix bs and a :: \<open>(byte, 'l) array\<close>
  assume \<open>prism_project (list_fixlen_prism :: (byte list, (byte, 'l) array) prism) bs = Some a\<close>
  then show \<open>length bs = LENGTH('l)\<close>
    by (auto simp add: list_fixlen_prism_def list_fixlen_project_def split: if_splits)
qed

text\<open>A word-array field \<^verbatim>\<open>[uW; N]\<close> is \<^const>\<open>array_byte_prism\<close> over a fixed-width
element prism; the array is then fixed-width \<^verbatim>\<open>w * LENGTH('l)\<close>.\<close>

lemma fixed_width_array:
  assumes \<open>fixed_width_prism w p\<close>
    shows \<open>fixed_width_prism (w * LENGTH('l::len))
             (array_byte_prism w p :: (byte list, ('e, 'l) array) prism)\<close>
proof (rule fixed_width_prismI)
  from assms have vp: \<open>is_valid_prism p\<close>
    and wp: \<open>\<And>e. length (prism_embed p e) = w\<close>
    by (auto simp add: fixed_width_prism_def)
  show \<open>is_valid_prism (array_byte_prism w p :: (byte list, ('e, 'l) array) prism)\<close>
    using vp wp by (rule array_byte_prism_valid)
next
  from assms have wp: \<open>\<And>e. length (prism_embed p e) = w\<close>
    by (simp add: fixed_width_prism_def)
  fix a show \<open>length (prism_embed (array_byte_prism w p :: (byte list, ('e, 'l) array) prism) a)
                = w * LENGTH('l)\<close>
    using wp by (rule array_byte_prism_embed_len)
next
  fix bs and a :: \<open>('e, 'l) array\<close>
  assume \<open>prism_project (array_byte_prism w p :: (byte list, ('e, 'l) array) prism) bs = Some a\<close>
  then show \<open>length bs = w * LENGTH('l)\<close>
    by (rule array_byte_prism_project_len)
qed

subsection\<open>Remaining-returning array prism\<close>

text\<open>Bridging the consume-all \<^const>\<open>array_byte_prism\<close> to a remaining-returning prism
via \<^const>\<open>split_prism\<close>: it peels the \<^verbatim>\<open>w * LENGTH('l)\<close> bytes of the array off the
front and hands the rest back, so an array can be chained as a parser.  The one
array induction stays in \<^verbatim>\<open>array_byte_prism_valid\<close>; the bridge adds none.\<close>

definition array_split_prism ::
    \<open>nat \<Rightarrow> (byte list, 'e) prism \<Rightarrow> (byte list, ('e, 'l::len) array \<times> byte list) prism\<close> where
  \<open>array_split_prism w p \<equiv> split_prism (w * LENGTH('l)) (array_byte_prism w p)\<close>

lemma array_split_prism_valid:
  assumes \<open>fixed_width_prism w p\<close>
    shows \<open>is_valid_prism (array_split_prism w p :: (byte list, ('e, 'l::len) array \<times> byte list) prism)\<close>
  unfolding array_split_prism_def
  by (rule split_prism_valid) (rule fixed_width_array[OF assms])

(*<*)
end
(*>*)
