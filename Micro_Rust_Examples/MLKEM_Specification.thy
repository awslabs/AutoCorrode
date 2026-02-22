(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory MLKEM_Specification
  imports
    MLKEM_Parameters
begin

text\<open>
  Pure mathematical specification of MLKEM operations.
  All definitions are non-monadic HOL functions serving as reference specifications
  for the \<mu>Rust implementations proved correct in subsequent theories.
\<close>

section\<open>Utility: array\_map2\<close>

definition array_map2 ::
    \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'l::{len}) array \<Rightarrow> ('b, 'l) array \<Rightarrow> ('c, 'l) array\<close> where
  \<open>array_map2 f xs ys \<equiv>
     array_of_list (map2 f (array_to_list xs) (array_to_list ys))\<close>

lemma array_map2_nth:
  assumes \<open>i < LENGTH('l)\<close>
    shows \<open>array_nth (array_map2 f (xs :: ('a, 'l::len) array) ys) i =
           f (array_nth xs i) (array_nth ys i)\<close>
  using assms by (simp add: array_map2_def)

section\<open>Modular arithmetic in Z\_q\<close>

definition zq_add :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow> 16 word\<close> where
  \<open>zq_add a b \<equiv> (a + b) mod mlkem_q_word\<close>

definition zq_sub :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow> 16 word\<close> where
  \<open>zq_sub a b \<equiv> (a + mlkem_q_word - b) mod mlkem_q_word\<close>

definition zq_mul :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow> 16 word\<close> where
  \<open>zq_mul a b \<equiv> word_of_nat ((unat a * unat b) mod mlkem_q)\<close>

subsection\<open>Overflow and range lemmas\<close>

lemma zq_add_no_overflow:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>unat a + unat b < 2 ^ 16\<close>
proof -
  have \<open>unat a + unat b < 3329 + 3329\<close>
    using assms by (simp add: mlkem_q_def)
  also have \<open>\<dots> = 6658\<close> by simp
  also have \<open>\<dots> < 2 ^ 16\<close> by simp
  finally show ?thesis .
qed

lemma zq_sub_no_overflow:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>unat a + mlkem_q < 2 ^ 16\<close>
proof -
  have \<open>unat a + mlkem_q < 3329 + 3329\<close>
    using assms by (simp add: mlkem_q_def)
  also have \<open>\<dots> = 6658\<close> by simp
  also have \<open>\<dots> < 2 ^ 16\<close> by simp
  finally show ?thesis .
qed

lemma zq_mul_no_overflow_32:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>unat a * unat b < 2 ^ 32\<close>
proof -
  have \<open>unat a * unat b < 3329 * 3329\<close>
    using assms by (intro mult_strict_mono; simp add: mlkem_q_def)
  also have \<open>\<dots> = 11082241\<close> by simp
  also have \<open>\<dots> < 2 ^ 32\<close> by simp
  finally show ?thesis .
qed

lemma zq_mul_result_fits_16:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>(unat a * unat b) mod mlkem_q < 2 ^ 16\<close>
proof -
  have \<open>(unat a * unat b) mod mlkem_q < mlkem_q\<close>
    by (simp add: mlkem_q_def)
  also have \<open>mlkem_q < 2 ^ 16\<close>
    by (simp add: mlkem_q_def)
  finally show ?thesis .
qed

lemma zq_add_range:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>unat (zq_add a b) < mlkem_q\<close>
proof -
  have no_ov: \<open>unat a + unat b < 2 ^ 16\<close>
    using assms by (rule zq_add_no_overflow)
  have \<open>unat (zq_add a b) = unat ((a + b) mod mlkem_q_word)\<close>
    by (simp add: zq_add_def)
  also have \<open>\<dots> = unat (a + b) mod unat mlkem_q_word\<close>
    by (simp add: unat_mod)
  also have \<open>unat (a + b) = unat a + unat b\<close>
    using no_ov by (simp add: unat_add_lem[THEN iffD1])
  also have \<open>(unat a + unat b) mod unat mlkem_q_word < unat mlkem_q_word\<close>
    by (simp add: mlkem_q_word_def)
  finally show ?thesis
    by (simp add: mlkem_q_word_unat mlkem_q_def)
qed

lemma zq_sub_range:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>unat (zq_sub a b) < mlkem_q\<close>
proof -
  have a_bound: \<open>unat a + mlkem_q < 2 ^ 16\<close>
    using assms by (rule zq_sub_no_overflow)
  have b_le: \<open>unat b \<le> unat a + unat mlkem_q_word\<close>
    using assms by (simp add: mlkem_q_word_def mlkem_q_def)
  have \<open>unat (zq_sub a b) = unat ((a + mlkem_q_word - b) mod mlkem_q_word)\<close>
    by (simp add: zq_sub_def)
  also have \<open>\<dots> = unat (a + mlkem_q_word - b) mod unat mlkem_q_word\<close>
    by (simp add: unat_mod)
  also have \<open>\<dots> < unat mlkem_q_word\<close>
    by (simp add: mlkem_q_word_def)
  finally show ?thesis
    by (simp add: mlkem_q_word_unat)
qed

lemma zq_mul_range:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>unat (zq_mul a b) < mlkem_q\<close>
proof -
  have fits: \<open>(unat a * unat b) mod mlkem_q < 2 ^ 16\<close>
    using assms by (rule zq_mul_result_fits_16)
  have \<open>unat (zq_mul a b) = unat (word_of_nat ((unat a * unat b) mod mlkem_q) :: 16 word)\<close>
    by (simp add: zq_mul_def)
  also have \<open>\<dots> = (unat a * unat b) mod mlkem_q\<close>
    using fits by (simp add: unat_of_nat take_bit_nat_eq_self_iff)
  also have \<open>\<dots> < mlkem_q\<close>
    by (simp add: mlkem_q_def)
  finally show ?thesis .
qed

section\<open>Polynomial operations\<close>

definition poly_add :: \<open>mlkem_poly \<Rightarrow> mlkem_poly \<Rightarrow> mlkem_poly\<close> where
  \<open>poly_add a b \<equiv> array_map2 zq_add a b\<close>

definition poly_sub :: \<open>mlkem_poly \<Rightarrow> mlkem_poly \<Rightarrow> mlkem_poly\<close> where
  \<open>poly_sub a b \<equiv> array_map2 zq_sub a b\<close>

lemma poly_add_nth:
  assumes \<open>i < mlkem_n\<close>
    shows \<open>array_nth (poly_add a b) i = zq_add (array_nth a i) (array_nth b i)\<close>
  using assms by (simp add: poly_add_def array_map2_nth mlkem_n_def)

lemma poly_sub_nth:
  assumes \<open>i < mlkem_n\<close>
    shows \<open>array_nth (poly_sub a b) i = zq_sub (array_nth a i) (array_nth b i)\<close>
  using assms by (simp add: poly_sub_def array_map2_nth mlkem_n_def)

lemma poly_add_wf:
  assumes \<open>poly_wf a\<close>
      and \<open>poly_wf b\<close>
    shows \<open>poly_wf (poly_add a b)\<close>
  using assms by (auto simp add: poly_wf_def poly_add_nth intro: zq_add_range poly_wf_nth)

lemma poly_sub_wf:
  assumes \<open>poly_wf a\<close>
      and \<open>poly_wf b\<close>
    shows \<open>poly_wf (poly_sub a b)\<close>
  using assms by (auto simp add: poly_wf_def poly_sub_nth intro: zq_sub_range poly_wf_nth)

section\<open>NTT specification\<close>

definition ntt_butterfly ::
    \<open>16 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mlkem_poly \<Rightarrow> mlkem_poly\<close> where
  \<open>ntt_butterfly zeta j len p \<equiv>
     let t = zq_mul zeta (array_nth p (j + len)) in
     let p' = array_update p (j + len) (zq_sub (array_nth p j) t) in
     array_update p' j (zq_add (array_nth p j) t)\<close>

fun ntt_inner_loop ::
    \<open>16 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mlkem_poly \<Rightarrow> mlkem_poly\<close> where
  \<open>ntt_inner_loop zeta start len 0 p = p\<close>
| \<open>ntt_inner_loop zeta start len (Suc count) p =
     ntt_inner_loop zeta (Suc start) len count (ntt_butterfly zeta start len p)\<close>

fun ntt_middle_loop ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mlkem_poly \<Rightarrow> nat \<times> mlkem_poly\<close> where
  \<open>ntt_middle_loop k len 0 num_blocks p = (k, p)\<close>
| \<open>ntt_middle_loop k len (Suc remaining) num_blocks p =
     (let block = num_blocks - Suc remaining in
      let start = block * (2 * len) in
      let zeta = array_nth zetas_table k in
      let p' = ntt_inner_loop zeta start len len p in
      ntt_middle_loop (Suc k) len remaining num_blocks p')\<close>

fun ntt_outer_loop ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> mlkem_poly \<Rightarrow> mlkem_poly\<close> where
  \<open>ntt_outer_loop k 0 p = p\<close>
| \<open>ntt_outer_loop k (Suc layer_rem) p =
     (let len = 2 ^ (Suc layer_rem) in
      let num_blocks = 2 ^ (6 - layer_rem) in
      let (k', p') = ntt_middle_loop k len num_blocks num_blocks p in
      ntt_outer_loop k' layer_rem p')\<close>

definition ntt :: \<open>mlkem_poly \<Rightarrow> mlkem_poly\<close> where
  \<open>ntt p \<equiv> ntt_outer_loop 1 7 p\<close>

subsection\<open>NTT well-formedness\<close>

lemma ntt_butterfly_wf:
  assumes \<open>poly_wf p\<close>
      and \<open>unat zeta < mlkem_q\<close>
      and \<open>j + len < mlkem_n\<close>
    shows \<open>poly_wf (ntt_butterfly zeta j len p)\<close>
  using assms
  by (auto simp add: ntt_butterfly_def poly_wf_def Let_def mlkem_n_def
           intro!: zq_add_range zq_sub_range zq_mul_range)

lemma ntt_inner_loop_wf:
  assumes \<open>poly_wf p\<close>
      and \<open>unat zeta < mlkem_q\<close>
      and \<open>start + count + len \<le> mlkem_n\<close>
      and \<open>0 < len\<close>
    shows \<open>poly_wf (ntt_inner_loop zeta start len count p)\<close>
  using assms
proof (induction count arbitrary: start p)
  case 0
  then show ?case by simp
next
  case (Suc count)
  have jl: \<open>start + len < mlkem_n\<close>
    using Suc.prems(3) by linarith
  have bf_wf: \<open>poly_wf (ntt_butterfly zeta start len p)\<close>
    by (rule ntt_butterfly_wf[OF Suc.prems(1,2) jl])
  have bound': \<open>Suc start + count + len \<le> mlkem_n\<close>
    using Suc.prems(3) by linarith
  show ?case
    by (simp add: Suc.IH[OF bf_wf Suc.prems(2) bound' Suc.prems(4)])
qed

lemma ntt_middle_loop_wf:
  assumes \<open>poly_wf p\<close>
      and \<open>remaining \<le> num_blocks\<close>
      and \<open>num_blocks * (2 * len) \<le> mlkem_n\<close>
      and \<open>0 < len\<close>
      and \<open>\<And>i. i < remaining \<Longrightarrow> unat (array_nth zetas_table (k + i)) < mlkem_q\<close>
      and \<open>k + remaining \<le> 128\<close>
    shows \<open>poly_wf (snd (ntt_middle_loop k len remaining num_blocks p))\<close>
  using assms
proof (induction remaining arbitrary: k p)
  case 0
  then show ?case by simp
next
  case (Suc remaining)
  let ?block = \<open>num_blocks - Suc remaining\<close>
  let ?start = \<open>?block * (2 * len)\<close>
  let ?zeta = \<open>array_nth zetas_table k\<close>
  let ?p' = \<open>ntt_inner_loop ?zeta ?start len len p\<close>
  have zeta_range: \<open>unat ?zeta < mlkem_q\<close>
    using Suc.prems(5)[of 0] by simp
  have block_bound: \<open>?block + 1 \<le> num_blocks\<close>
    using Suc.prems(2) by linarith
  have start_bound: \<open>?start + len + len \<le> mlkem_n\<close>
  proof -
    have \<open>(?block + 1) * (2 * len) \<le> num_blocks * (2 * len)\<close>
      using block_bound by (intro mult_le_mono1)
    thus ?thesis using Suc.prems(3) by (simp add: algebra_simps)
  qed
  have p'_wf: \<open>poly_wf ?p'\<close>
    by (rule ntt_inner_loop_wf[OF Suc.prems(1) zeta_range start_bound Suc.prems(4)])
  have zeta_shift: \<open>\<And>i. i < remaining \<Longrightarrow> unat (array_nth zetas_table (Suc k + i)) < mlkem_q\<close>
    using Suc.prems(5)[of \<open>Suc _\<close>] by simp
  have k_bound: \<open>Suc k + remaining \<le> 128\<close>
    using Suc.prems(6) by linarith
  have rem_bound: \<open>remaining \<le> num_blocks\<close>
    using Suc.prems(2) by linarith
  show ?case
    by (simp add: Let_def)
       (rule Suc.IH[OF p'_wf rem_bound Suc.prems(3,4) zeta_shift k_bound])
qed

lemma ntt_middle_loop_fst:
  shows \<open>fst (ntt_middle_loop k len remaining num_blocks p) = k + remaining\<close>
  by (induction remaining arbitrary: k p) (simp_all add: Let_def)

lemma ntt_outer_loop_wf:
  assumes \<open>poly_wf p\<close>
      and \<open>layer_rem \<le> 7\<close>
      and \<open>k \<le> 2 ^ (7 - layer_rem)\<close>
    shows \<open>poly_wf (ntt_outer_loop k layer_rem p)\<close>
  using assms
proof (induction layer_rem arbitrary: k p)
  case 0
  then show ?case by simp
next
  case (Suc layer_rem)
  let ?len = \<open>2 ^ Suc layer_rem :: nat\<close>
  let ?nb = \<open>2 ^ (6 - layer_rem) :: nat\<close>
  have lr_le: \<open>layer_rem \<le> 6\<close>
    using Suc.prems(2) by linarith
  have nb_eq: \<open>?nb = 2 ^ (7 - Suc layer_rem)\<close>
    using lr_le by (simp add: Suc_diff_le)
  have size_eq: \<open>?nb * (2 * ?len) = mlkem_n\<close>
  proof -
    have \<open>?nb * (2 * ?len) = 2 ^ (6 - layer_rem) * 2 ^ (Suc (Suc layer_rem))\<close>
      by simp
    also have \<open>\<dots> = (2::nat) ^ (6 - layer_rem + Suc (Suc layer_rem))\<close>
      by (simp add: power_add)
    also have \<open>6 - layer_rem + Suc (Suc layer_rem) = 8\<close>
      using lr_le by linarith
    finally show ?thesis by (simp add: mlkem_n_def)
  qed
  have len_pos: \<open>0 < ?len\<close> by simp
  have k_le_nb: \<open>k \<le> ?nb\<close>
    unfolding nb_eq using Suc.prems(3) .
  have k_nb: \<open>k + ?nb \<le> 2 * ?nb\<close>
    using k_le_nb by linarith
  have nb_le_64: \<open>?nb \<le> 64\<close>
  proof -
    have \<open>?nb \<le> (2::nat) ^ 6\<close>
      by (intro power_increasing) simp_all
    thus ?thesis by simp
  qed
  have k_nb_128: \<open>k + ?nb \<le> 128\<close>
    using k_le_nb nb_le_64 by linarith
  have zeta_range: \<open>\<And>i. i < ?nb \<Longrightarrow> unat (array_nth zetas_table (k + i)) < mlkem_q\<close>
  proof -
    fix i assume \<open>i < ?nb\<close>
    then have \<open>k + i < k + ?nb\<close> by linarith
    also have \<open>\<dots> \<le> 128\<close> by (rule k_nb_128)
    finally show \<open>unat (array_nth zetas_table (k + i)) < mlkem_q\<close>
      by (rule zetas_table_wf)
  qed
  let ?res = \<open>ntt_middle_loop k ?len ?nb ?nb p\<close>
  have mid_wf: \<open>poly_wf (snd ?res)\<close>
    by (rule ntt_middle_loop_wf[OF Suc.prems(1) le_refl _ len_pos zeta_range k_nb_128])
       (use size_eq in linarith)
  have k'_eq: \<open>fst ?res = k + ?nb\<close>
    by (rule ntt_middle_loop_fst)
  have k'_bound: \<open>k + ?nb \<le> 2 ^ (7 - layer_rem)\<close>
  proof -
    have \<open>Suc (6 - layer_rem) = 7 - layer_rem\<close> using lr_le by linarith
    hence \<open>(2::nat) ^ (7 - layer_rem) = 2 * 2 ^ (6 - layer_rem)\<close>
      by (metis power_Suc)
    thus ?thesis using k_nb by linarith
  qed
  show ?case
    using Suc.prems(2)
    by (simp only: ntt_outer_loop.simps Let_def case_prod_beta k'_eq)
       (rule Suc.IH[OF mid_wf _ k'_bound]; linarith)
qed

lemma ntt_wf:
  assumes \<open>poly_wf p\<close>
    shows \<open>poly_wf (ntt p)\<close>
  unfolding ntt_def
  by (rule ntt_outer_loop_wf[OF assms]) simp_all

end
