(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory WordAdditional
  imports "HOL-Library.Word"
    Word_Lib.Word_Lib_Sumo
    ListAdditional
begin
(*>*)

section \<open>Lemmas for reasoning about inequalities\<close>

text\<open>Our strategy for dealing with inequalities between instances \<^type>\<open>nat\<close> and
\<^type>\<open>word\<close> is to always reduce them to inequalities between natural numbers, and
to simplify any compound expressions involving word casts and word to nat conversion.\<close>

named_theorems word_nat_intros
named_theorems word_nat_elims
named_theorems word_nat_intros_weak
named_theorems word_nat_simps

lemma lt_word_to_natI [word_nat_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>unat a < unat b\<close>
    shows \<open>a < b\<close>
by (simp add: assms word_less_nat_alt)

text\<open>This is \<^verbatim>\<open>Word.unat_mono\<close> in another guise!\<close>
lemma lt_word_to_natE [elim_format, word_nat_elims]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>a < b\<close>
    shows \<open>unat a < unat b\<close>
using assms word_less_iff_unsigned by blast

lemma unat_ucast_up:
    fixes x :: \<open>'k::{len} word\<close>
  assumes \<open>LENGTH('k) \<le> LENGTH('l::{len})\<close>
    shows \<open>unat (ucast x :: 'l word) = unat x\<close>
by (metis assms unat_ucast_up_simp)

lemma unat_ucast_16_to_64 [word_nat_simps]:
  fixes x :: \<open>16 word\<close>
  shows \<open>unat x = unat (ucast x::64 word)\<close>
using unat_ucast_up[where 'k=16 and 'l=64] by auto

lemma unat_ucast_dec:
  fixes x :: \<open>'k::{len} word\<close>
  shows \<open>unat ((ucast x) :: 'l::{len} word) \<le> unat x\<close>
by (simp add: word_unat_less_le)

lemma unat_ucast_eq [word_nat_simps]:
    fixes x :: \<open>nat\<close>
  assumes \<open>x < 2^LENGTH('k :: len)\<close>
    shows \<open>unat (word_of_nat x :: 'k word) = x\<close>
by (simp add: assms of_nat_inverse)

lemma ucast_ucast_eq:
    fixes x :: \<open>'l::{len} word\<close>
  assumes \<open>unat x < 2^LENGTH('k::{len})\<close>
    shows \<open>ucast (ucast x::'k word) = x\<close>
by (metis assms bintr_uint take_bit_nat_eq_self unsigned_ucast_eq unsigned_word_eqI verit_comp_simplify1(2))

lemma ucast_ucast_16_64_eq [word_nat_simps]:
    fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 2^16\<close>
    shows \<open>ucast ((ucast x)::16 word) = x\<close>
using assms ucast_ucast_eq[where 'l=64 and 'k=16] by auto

section \<open>Some facts about words and nats\<close>

lemma min_unat [simp]:
  fixes a b :: \<open>'l::{len} word\<close>
  shows \<open>min (unat a) (unat b) = unat(min a b)\<close>
by (metis min_def word_less_eq_iff_unsigned)

lemma unat_lt_twice [simp]:
  fixes a b :: \<open>'l::{len} word\<close>
    and c :: nat
  shows \<open>c < unat a \<and> c < unat b \<longleftrightarrow> c < unat(min a b)\<close>
by (metis min_less_iff_conj min_unat)

lemma nat_upd_nth:
  assumes \<open>i < n\<close>
    shows \<open>[0..<n] ! i = i\<close>
using assms by simp

lemma word_unat_lt:
  assumes \<open>i < j\<close>
      and \<open>j < 2^LENGTH('l::{len})\<close>
    shows \<open>((word_of_nat i)::'l word) < word_of_nat j\<close>
by (metis assms dual_order.strict_trans2 nless_le of_nat_inverse word_less_iff_unsigned)

lemma ucast_ucast_le:
  fixes x :: \<open>'k::{len} word\<close>
  shows \<open>ucast ((ucast x)::'l::{len} word) \<le> x\<close>
by (simp add: le_ucast_ucast_le)

lemma unat_ucast_lt:
    fixes x :: \<open>'k::{len} word\<close>
      and y :: \<open>'k word\<close>
  assumes \<open>x < y\<close>
    shows \<open>unat ((ucast x)::'l::{len} word) < unat y\<close>
using unat_ucast_dec assms order_le_less_trans unat_mono by fast

lemma unat_lt_weakenI:
    fixes x  :: \<open>'k::{len} word\<close>
      and x' :: \<open>'k word\<close>
      and y :: \<open>nat\<close>
  assumes \<open>x < x'\<close>
      and \<open>unat x' \<le> y\<close>
    shows \<open>unat x < y\<close>
using assms by (meson order_less_le_trans unat_mono)

lemma unat_ucast_le:
    fixes x :: \<open>'k::{len} word\<close>
      and y :: \<open>'k word\<close>
  assumes \<open>x \<le> y\<close>
    shows \<open>unat ((ucast x)::'l::{len} word) \<le> unat y\<close>
using unat_ucast_dec assms le_trans word_le_nat_alt by fast

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma unat_le_weakenI:
    fixes x  :: \<open>'k::{len} word\<close>
      and x' :: \<open>'k word\<close>
      and y :: \<open>nat\<close>
  assumes \<open>x \<le> x'\<close>
      and \<open>unat x' \<le> y\<close>
    shows \<open>unat x \<le> y\<close>
using assms by (meson dual_order.trans word_less_eq_iff_unsigned)

lemma unat_lt_diff_len:
    fixes x :: \<open>'k::{len} word\<close>
      and y :: \<open>'l::{len} word\<close>
  assumes \<open>LENGTH('k) \<le> LENGTH('l)\<close>
    shows \<open>unat x < unat y \<longleftrightarrow> ucast x < y\<close>
using assms by (metis is_up.rep_eq linorder_not_le not_less_iff_gr_or_eq ucast_up_ucast_id
    unat_lt_weakenI unat_ucast_dec)

lemma unat_lt_16_64:
  fixes x :: \<open>16 word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>unat x < unat y \<longleftrightarrow> ucast x < y\<close>
using unat_lt_diff_len[where 'k=16 and 'l=64] by auto

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma unat_ucast_adjoint:
    fixes x  :: \<open>'k::{len} word\<close>
      and y :: \<open>nat\<close>
  assumes \<open>y < 2^LENGTH('k)\<close>
    shows \<open>unat x < y \<longleftrightarrow> x < word_of_nat y\<close>
by (metis assms of_nat_inverse word_less_iff_unsigned)

lemma word_range_sorted:
    fixes M N :: nat
  assumes \<open>0 \<le> M\<close>
      and \<open>M < N\<close>
      and \<open>N < 2^LENGTH('l::{len})\<close>
    shows \<open>sorted (List.map (Word.word_of_nat :: nat \<Rightarrow> 'l word) [M..<N])\<close>
using assms by (auto simp add: of_nat_inverse word_of_nat_le intro!: sorted_list_map_mono sorted_upt)

lemma set_of_wordlist:
    fixes M N :: \<open>nat\<close>
  assumes \<open>0 \<le> M\<close> and \<open>M < N\<close>
      and \<open>N < 2^LENGTH('l::{len})\<close>
    shows \<open>set (List.map Word.of_nat [M..<N]) = {v::'l word. Word.of_nat M \<le> v \<and> v < Word.of_nat N}\<close>
proof -
  have \<open>set (List.map Word.of_nat [M..<N]) = Word.of_nat ` (set [M..<N])\<close>
    by auto
  moreover have \<open>\<dots> = Word.of_nat ` {M..<N}\<close>
    by auto
  moreover have \<open>\<dots> = {v::'l word. Word.of_nat M \<le> v \<and> v < Word.of_nat N}\<close>
    using assms by (auto simp add: of_nat_inverse word_of_nat_le word_of_nat_less) (metis
      atLeastLessThan_iff image_iff le_eq_less_or_eq le_unat_uoi unat_less_helper unat_ucast_eq
      word_less_eq_iff_unsigned word_nat_cases)
 from this show ?thesis
   by auto
qed

lemma ucast_16_64_inj:
  assumes \<open>(ucast::16 word \<Rightarrow> 64 word) x = ucast y\<close>
    shows \<open>x = y\<close>
using assms by (rule ucast_up_inj, simp)

(*<*)
context
  includes bit_operations_syntax
begin
(*>*)

lemma word_cat_0 [simp]:
  fixes x :: \<open>2 word\<close>
  shows \<open>word_cat 0 x = (ucast x::64 word)\<close>
by (simp add: word_cat_eq)

lemma unat_word_comparison:
    fixes x :: \<open>'l::{len} word\<close>
  assumes \<open>unat x = y\<close>
    shows \<open>x = Word.of_nat y\<close> and \<open>y < 2^LENGTH('l)\<close>
using assms by (auto simp add: unat_arith_simps)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma unat_word_comparisonE:
    fixes x :: \<open>'l::{len} word\<close>
  assumes \<open>unat x = y\<close>
      and \<open>x = Word.of_nat y \<Longrightarrow> y < 2^LENGTH('l) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (blast intro: unat_word_comparison)

lemma word_int_bound:
    fixes v :: \<open>'l::{len} word\<close>
      and N :: \<open>int\<close>
  assumes \<open>v \<le> Word.of_int N\<close>
      and \<open>0 \<le> N\<close>
      and \<open>N < 2^LENGTH('l)\<close>
    shows \<open>v = Word.of_int (uint v)\<close> and \<open>uint v \<le> N\<close>
using assms by (transfer, force simp add: take_bit_int_eq_self)+

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word_int_bound':
    fixes v :: \<open>'l::{len} word\<close>
      and N :: \<open>int\<close>
  assumes \<open>0 \<le> N\<close>
      and \<open>N < 2^LENGTH('l)\<close>
    shows \<open>v \<le> Word.of_int N \<longleftrightarrow> uint v \<le> N\<close>
using assms by (transfer, force simp add: take_bit_int_eq_self)+

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word_int_boundE:
    fixes v :: \<open>'l::{len} word\<close>
      and N :: \<open>int\<close>
  assumes \<open>v \<le> Word.of_int N\<close>
      and \<open>0 \<le> N\<close>
      and \<open>N < 2^LENGTH('l)\<close>
      and \<open>uint v \<le> N \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (blast intro: word_int_bound)

lemma word64_bit_twiddle_technicalD1:
    fixes w :: \<open>64 word\<close>
  assumes \<open>w AND - 2 = 0\<close>
      and \<open>w AND 1 \<noteq> 1\<close>
    shows \<open>w = 0\<close>
using assms by (metis mask_eq_x_eq_0 not_one_eq word_and_1)

lemma word64_bit_twiddle_technicalD2:
    fixes w :: \<open>64 word\<close>
  assumes \<open>w AND - 2 = 0\<close>
      and \<open>w AND 1 = 0\<close>
    shows \<open>w = 0\<close>
using assms by (simp add: mask_eq_0_eq_x)

lemma word64_bit_twiddle_technicalD3:
    fixes w :: \<open>64 word\<close>
  assumes \<open>w AND - 2 = 0\<close>
      and \<open>w AND 1 = 1\<close>
    shows \<open>w = 1\<close>
using assms by (metis compl_of_1 mask_eq_x_eq_0)

lemma unat_word_of_nat64_le:
    fixes w :: \<open>64 word\<close>
  assumes \<open>unat w \<le> m\<close>
      and \<open>m < 2^64\<close>
    shows \<open>w \<le> word_of_nat m\<close>
using assms
  apply clarsimp
  apply (rule iffD2 [OF word_le_nat_alt])
  apply (subst of_nat_inverse; force)
  done

lemma word_div_mul_bound:
    fixes a b c :: \<open>'l::{len} word\<close>
  assumes \<open>a \<le> b\<close>
      and \<open>i < unat ((b - a) div c)\<close>
    shows \<open>i * unat c < 2^LENGTH('l)\<close>
using assms by (metis div_lt'' le_eq_less_or_eq le_unat_uoi word_of_nat_less)

lemma word_div_mul_bound':
    fixes a b c :: \<open>'l::{len} word\<close>
  assumes \<open>a \<le> b\<close>
      and \<open>i \<le> unat ((b - a) div c)\<close>
    shows \<open>i * unat c < 2^LENGTH('l)\<close>
using assms by (metis div_lt' le_eq_less_or_eq word_div_mul_bound word_le_less_eq)

lemma le_unat_uoi':
    fixes z :: \<open>'a::{len} word\<close>
  assumes \<open>y < unat z\<close>
    shows \<open>unat (word_of_nat y::'a word) = y\<close>
using assms by (meson le_unat_uoi less_or_eq_imp_le)

lemma nonoverflow_range:
    fixes a b :: \<open>'a::{len} word\<close>
  assumes \<open>a \<le> a + b\<close>
      and \<open>c \<le> b\<close>
    shows \<open>a \<le> a + c\<close>
using assms by unat_arith

lemma not_gr0_word:
  fixes n :: \<open>'a::{len} word\<close>
  shows \<open>\<not>0 < n \<longleftrightarrow> n = 0\<close>
by unat_arith

lemma lt_sub_left:
    fixes x y :: \<open>'a::{len} word\<close>
  assumes \<open>0 < x\<close>
      and \<open>x < y\<close>
    shows \<open>y - x < y\<close>
using assms by unat_arith

section \<open>Brute-force splitting of @{term\<open>w\<le>nn\<close>} or @{term\<open>w<nn\<close>} into cases\<close>

lemma word_le_numE:
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m \<le> numeral n\<close>
  obtains \<open>m = numeral n\<close> | \<open>m \<le> of_nat (pred_numeral n)\<close>
proof (cases \<open>m = numeral n\<close>)
  case False
  then have \<open>\<not> m \<ge> 1 + of_nat (pred_numeral n)\<close>
    by (metis assms nle_le numeral_eq_Suc of_nat_Suc of_nat_numeral)
  with that show thesis
    by (metis add.commute inc_le leI)
qed

lemma word_le_1E:
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m \<le> 1\<close>
  obtains \<open>m = 0\<close> | \<open>m = 1\<close>
using assms word_le_sub1 by fastforce

lemma word_less_numE:
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m < numeral n\<close>
  obtains \<open>m \<le> of_nat (pred_numeral n)\<close>
by (metis assms nless_le word_le_numE)

text \<open>Use with auto/force and the elim! modifiers\<close>
lemmas word_leE = word_le_numE word_le_1E word_less_numE

text \<open>A rewrite that replaces identity of words to identity of bits\<close>
lemma bit_word_eq_iff:
  fixes a b :: \<open>'a::{len} word\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>n < LENGTH('a). bit a n \<longleftrightarrow> bit b n)\<close>
using bit_word_eqI by auto

lemma nat_le_numeral_iff:
  shows \<open>n \<le> numeral v \<longleftrightarrow> n = numeral v \<or> n \<le> pred_numeral v\<close>
by (metis Suc_eq_numeral le_Suc_eq)

lemma nat_less_numeral_iff:
  shows \<open>m < numeral n \<longleftrightarrow> m \<le> pred_numeral n\<close>
using less_eq_Suc_le by force

text \<open>Rewrites to explode a bounded quantifier into individual cases\<close>
lemmas nat_le_numeral_iffs = nat_le_numeral_iff nat_less_numeral_iff le_Suc_eq[where n=0]

text \<open>Bitwise boolean ops. Negation doesn't fit this pattern: word length intrudes\<close>
lemmas word_op_nth = word_and_nth word_or_nth word_xor_nth

lemma push_bit_drop_bit:
  assumes \<open>k \<ge> m\<close>
      and \<open>m \<ge> n\<close>
    shows \<open>bit (push_bit m (drop_bit n a)) k = bit (push_bit (m-n) a) k\<close>
using assms unfolding bit_push_bit_iff by (auto simp add: bit_iff_odd_drop_bit possible_bit_def le_imp_diff_le)

lemma mod_eq_mask:
  shows \<open>x mod (2^n) = x AND mask n\<close>
by (metis take_bit_eq_mask take_bit_eq_mod)

lemma mod16_eq_mask:
  shows \<open>x mod 0x10 = x AND mask 4\<close>
using mod_eq_mask [of x 4] by simp

text \<open>Examples of use\<close>

lemma
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m \<le> 6\<close>  \<open>P 0\<close> \<open>P 1\<close> \<open>P 2\<close> \<open>P 3\<close> \<open>P 4\<close> \<open>P 5\<close> \<open>P 6\<close>
    shows \<open>P m\<close>
using assms by (force elim!: word_leE)

lemma
  fixes x :: \<open>64 word\<close>
  shows \<open>x AND (push_bit 2 (mask 4)) = 0xc \<longleftrightarrow> x AND mask 6 \<in> {0xc,0xd,0xe,0xf}\<close>
  \<comment> \<open>Note: two separate steps seem necessary\<close>
by safe (auto simp: mask_eq_exp_minus_1 bit_word_eq_iff nat_le_numeral_iffs word_op_nth)

abbreviation word_align_down :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 64 word\<close> where
  \<open>word_align_down a n \<equiv> a AND NOT (mask n)\<close>

definition page_range_word :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 64 word set\<close> where
  \<open>page_range_word start n \<equiv> {start..(start + 2 ^ n - 1)}\<close>

definition block_range :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 64 word set\<close> where
  \<open>block_range addr n \<equiv> { pa . word_align_down addr n = word_align_down pa n }\<close>

lemma aligned_word_range:
  assumes \<open>is_aligned start l\<close>
    shows \<open>a \<in> page_range_word start l \<longleftrightarrow> word_align_down a l = start\<close>
proof
  assume \<open>a \<in> page_range_word start l\<close>
  moreover from this have \<open>start \<le> a\<close> and \<open>a \<le> start + 2 ^ l - 1\<close>
    by (auto simp add: page_range_word_def)
  ultimately show \<open>word_align_down a l = start\<close>
    using assms by (clarsimp simp add: page_range_word_def add_mask_fold neg_mask_in_mask_range)
next
  assume \<open>word_align_down a l = start\<close>
  moreover from this have \<open>word_align_down a l \<le> a\<close>
    by (meson word_and_le2)
  moreover from calculation assms have \<open>a \<le> start + 2 ^ l - 1\<close>
    by (metis add_mask_fold and_neg_mask_plus_mask_mono)
  ultimately show \<open>a \<in> page_range_word start l\<close>
    by (clarsimp simp add: page_range_word_def)
qed

(*<*)
end (*bit_operations_syntax*)

lemma word_align_down_plus_pow2:
    fixes x :: \<open>64 word\<close>
  assumes \<open>is_aligned x (Suc n)\<close>
    shows \<open>word_align_down (x + (2^n)) n = word_align_down x n OR (2^n)\<close>
using assms by (simp add: neg_mask_add t2n_mask_eq_if) (metis (no_types, lifting) and_neq_0_is_nth
  is_aligned_neg_mask is_aligned_neg_mask_eq is_aligned_nth lessI less_or_eq_imp_le
  word_plus_and_or_coroll)

abbreviation word64_of_nat :: \<open>nat \<Rightarrow> 64 word\<close> where
  \<open>word64_of_nat \<equiv> word_of_nat\<close>

end
(*>*)