(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory MLKEM_NTT
  imports
    MLKEM_Polynomial
begin

text\<open>
  NTT (Number Theoretic Transform) for MLKEM. This theory contains:
  \<^item> Pure properties of the NTT specification from @{theory Micro_Rust_Examples.MLKEM_Specification}
  \<^item> Array lens disjointness lemmas
  \<^item> \<mu>Rust NTT implementation with three nested loop invariants
\<close>

section\<open>NTT pure properties\<close>

lemma ntt_butterfly_updates_only:
    fixes len
  assumes \<open>j + len < mlkem_n\<close>
    shows \<open>\<forall>k < mlkem_n. k \<noteq> j \<and> k \<noteq> j + len \<longrightarrow>
            array_nth (ntt_butterfly zeta j len p) k = array_nth p k\<close>
using assms by (auto simp add: ntt_butterfly_def Let_def mlkem_n_def)

lemma ntt_inner_loop_bounds:
    fixes len start count
  assumes \<open>start + count + len \<le> mlkem_n\<close>
    shows \<open>\<forall>k < mlkem_n. k < start \<or> k \<ge> start + count + len \<longrightarrow>
            array_nth (ntt_inner_loop zeta start len count p) k = array_nth p k\<close>
using assms proof (induction count arbitrary: start p)
  case 0
  then show ?case by simp
next case (Suc count)
  have \<open>\<forall>k < mlkem_n. k < Suc start \<or> k \<ge> Suc start + count + len \<longrightarrow>
          array_nth (ntt_inner_loop zeta (Suc start) len count
            (ntt_butterfly zeta start len p)) k
          = array_nth (ntt_butterfly zeta start len p) k\<close>
    using Suc.IH Suc.prems by auto
  moreover have \<open>\<forall>k < mlkem_n. k < start \<or> k \<ge> start + Suc count + len \<longrightarrow>
                  k \<noteq> start \<and> k \<noteq> start + len\<close>
    using Suc.prems by auto
  moreover have \<open>\<forall>k < mlkem_n. k \<noteq> start \<and> k \<noteq> start + len \<longrightarrow>
                  array_nth (ntt_butterfly zeta start len p) k = array_nth p k\<close>
    using ntt_butterfly_updates_only Suc.prems by (auto simp add: mlkem_n_def)
  ultimately show ?case
    by auto
qed

text\<open>Key lemma: enables the inner loop inductive step by showing that applying
one more butterfly at the end is equivalent to extending the count.\<close>
lemma ntt_inner_loop_snoc:
  fixes start count len
  shows \<open>ntt_butterfly zeta (start + count) len
           (ntt_inner_loop zeta start len count p) =
         ntt_inner_loop zeta start len (Suc count) p\<close>
proof (induction count arbitrary: start p)
case 0
  show ?case
    by simp
next case (Suc count)
  have \<open>ntt_butterfly zeta (start + Suc count) len
          (ntt_inner_loop zeta start len (Suc count) p) =
        ntt_butterfly zeta (Suc start + count) len
          (ntt_inner_loop zeta (Suc start) len count (ntt_butterfly zeta start len p))\<close>
    by simp
  also have \<open>\<dots> = ntt_inner_loop zeta (Suc start) len (Suc count) (ntt_butterfly zeta start len p)\<close>
    by (rule Suc.IH)
  also have \<open>\<dots> = ntt_inner_loop zeta start len (Suc (Suc count)) p\<close>
    by simp
  finally show ?case
    .
qed

section\<open>Array lens disjointness\<close>

text\<open>Needed for the NTT butterfly which simultaneously holds focused references
to @{term \<open>f[j]\<close>} and @{term \<open>f[j+l]\<close>} where @{term \<open>l > 0\<close>}.\<close>

lemma nth_lens_array_disjoint:
  assumes \<open>i \<noteq> j\<close>
      and \<open>i < LENGTH('l)\<close>
      and \<open>j < LENGTH('l)\<close>
    shows \<open>disjoint_lenses
             (nth_lens_array i :: (('a,'l::len) array, 'a) lens)
             (nth_lens_array j)\<close>
using assms by (intro disjoint_lensesI)
   (simp add: nth_lens_array_def lens_modify_def array_update_swap)

section\<open>NTT index bounds\<close>

lemma ntt_j_plus_len_bound:
    fixes len :: \<open>nat\<close>
  assumes \<open>block < num_blocks\<close>
      and \<open>j_off < len\<close>
      and \<open>num_blocks * (2 * len) = 256\<close>
    shows \<open>block * (2 * len) + j_off + len < 256\<close>
proof -
  have \<open>block + 1 \<le> num_blocks\<close>
    using assms(1) by linarith
  then have \<open>(block + 1) * (2 * len) \<le> num_blocks * (2 * len)\<close>
    by (rule mult_le_mono1)
  then have \<open>block * (2 * len) + 2 * len \<le> 256\<close>
    using assms(3) by (simp add: algebra_simps)
  then show ?thesis
    using assms(2) by linarith
qed

lemma ntt_butterfly_disjoint_indices:
    fixes len :: \<open>nat\<close>
      and start :: \<open>nat\<close>
  assumes \<open>j_off < len\<close>
      and \<open>0 < len\<close>
    shows \<open>start + j_off \<noteq> start + j_off + len\<close>
using assms by linarith

lemma ntt_k_plus_pow2_bound:
  assumes \<open>k \<le> (2::nat) ^ n\<close>
      and \<open>n < 7\<close>
    shows \<open>k + 2 ^ n \<le> 128\<close>
proof -
  from assms(1) have \<open>k + 2 ^ n \<le> 2 * 2 ^ n\<close>
    by linarith
  also have \<open>\<dots> = 2 ^ Suc n\<close>
    by simp
  also from assms(2) have \<open>(2::nat) ^ Suc n \<le> 2 ^ 7\<close>
    by (intro power_increasing) simp_all
  finally show ?thesis
    by simp
qed

lemma ntt_k_block_bound:
  assumes \<open>k \<le> (2::nat) ^ n\<close>
      and \<open>b < 2 ^ n\<close>
      and \<open>n < 7\<close>
    shows \<open>k + b < 128\<close>
using assms ntt_k_plus_pow2_bound[OF assms(1) assms(3)] by linarith

lemma drop_bit_le_self_nat:
  shows \<open>drop_bit n (m::nat) \<le> m\<close>
by (simp add: drop_bit_eq_div)

section\<open>NTT locale and \<mu>Rust implementation\<close>

locale mlkem_ntt_context =
    mlkem_polynomial_context _ _ _ _ _ _ _ reference_types word16_prism word32_prism poly_prism
  + ref_word64: reference_allocatable reference_types _ _ _ _ _ _ _ word64_prism
  for
    reference_types ::
      \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and word16_prism :: \<open>('gv, 16 word) prism\<close>
  and word32_prism :: \<open>('gv, 32 word) prism\<close>
  and poly_prism :: \<open>('gv, mlkem_poly) prism\<close>
  and word64_prism :: \<open>('gv, 64 word) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word64.new

definition ntt :: \<open>('addr, 'gv, mlkem_poly) Global_Store.ref \<Rightarrow>
     ('s::{sepalg}, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>ntt f_ref \<equiv> FunctionBody \<lbrakk>
     let mut k = 1;

     for layer in 0..7 {
       let len = 128 >> layer;
       let num_blocks = 1 << layer;

       for block in 0..num_blocks {
         let start = block * (2_u64 * len);
         let zeta = zetas_table[*k];
         k = *k + 1_u64;

         for j_off in 0..len {
           let j = start + j_off;
           let fj_ref = f_ref[j];
           let fjl_ref = f_ref[j + len];

           let t = zq_mul(zeta, *fjl_ref);
           fjl_ref = zq_sub(*fj_ref, t);
           fj_ref = zq_add(*fj_ref, t)
         }
       }
     }
  \<rbrakk>\<close>

definition ntt_contract ::
    \<open>(('addr, 'gv) gref, 'gv, mlkem_poly) focused \<Rightarrow> 'gv \<Rightarrow> mlkem_poly \<Rightarrow>
     ('s::{sepalg}, unit, 'b) function_contract\<close> where
  [crush_contracts]: \<open>ntt_contract f_ref g p \<equiv>
     let pre  = f_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>p \<star>
                \<langle>poly_wf p\<rangle> \<star>
                can_alloc_reference;
         post = \<lambda>_. (\<Squnion> g'. f_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>(MLKEM_Specification.ntt p)) \<star>
                \<langle>poly_wf (MLKEM_Specification.ntt p)\<rangle> \<star>
                can_alloc_reference
      in make_function_contract pre post\<close>
ucincl_auto ntt_contract

text\<open>The NTT proof is the most involved verification in this development.
It requires three nested loop invariants, each using the ``backwards'' approach:
relating the remaining pure computation from the current state to the full
computation from the initial state.

The proof proceeds bottom-up: inner loop (butterfly), middle loop (blocks),
outer loop (layers). Each loop is verified using @{thm wp_raw_for_loop_framedI'}.

Key facts used:
\<^item> @{thm ntt_inner_loop_snoc}: enables the inner loop inductive step
\<^item> @{thm nth_lens_array_disjoint}: allows simultaneous focused refs to \<open>f[j]\<close> and \<open>f[j+len]\<close>
\<^item> @{thm ntt_butterfly_wf}: butterfly preserves well-formedness
\<close>

lemma ntt_outer_loop_step:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>ntt_middle_loop k (2 ^ (7 - layer)) (2 ^ layer) (2 ^ layer) pcur = (k', p')\<close>
    shows \<open>ntt_outer_loop k (7 - layer) pcur = ntt_outer_loop k' (7 - Suc layer) p'\<close>
proof (cases \<open>7 - layer\<close>)
  case 0 with assms show ?thesis by simp
next
  case (Suc n)
  with assms(1) have \<open>n = 6 - layer\<close> and \<open>6 - n = layer\<close>
    by simp_all
  with Suc assms show ?thesis
    by (simp add: ntt_outer_loop.simps Let_def case_prod_beta)
qed

lemma ntt_num_blocks_length:
  assumes \<open>layer < (7::nat)\<close>
    shows \<open>length (list.map word64_of_nat
           [0..<unat ((2::64 word) ^ unat (word64_of_nat layer))]) = 2 ^ layer\<close>
using assms by (simp add: unat_of_nat_eq unat_power_lower)

lemma ntt_middle_loop_terminal:
  assumes \<open>layer < (7::nat)\<close>
    shows \<open>MLKEM_Specification.ntt_middle_loop
            (k + unat ((2::64 word) ^ unat (word64_of_nat layer)))
            (2 ^ (7 - layer))
            (2 ^ layer - unat ((2::64 word) ^ unat (word64_of_nat layer)))
            (2 ^ layer) p
          = (k + 2 ^ layer, p)\<close>
using assms by (simp add: unat_of_nat_eq unat_power_lower)

lemma word64_of_nat_add_pow_layer:
  assumes \<open>layer < (7::nat)\<close>
    shows \<open>word64_of_nat k + ((2::64 word) ^ unat (word64_of_nat layer))
              = word64_of_nat (k + 2 ^ layer)\<close>
using assms by (simp add: unat_of_nat_eq unat_power_lower)

lemma word64_of_nat_add_pow_nat:
  shows \<open>word64_of_nat k + (2::64 word) ^ n = word64_of_nat (k + 2 ^ n)\<close>
  by (metis word_unat_power of_nat_add)

lemma ntt_inner_len_length:
  assumes \<open>layer < (7::nat)\<close>
    shows \<open>length (list.map word64_of_nat [0..<unat (drop_bit (unat (word64_of_nat layer)) (0x80::64 word))]) =
              2 ^ (7 - layer)\<close>
proof -
  have \<open>unat (drop_bit (unat (word64_of_nat layer)) (0x80::64 word)) =
          drop_bit layer (128::nat)\<close>
    using assms by (simp add: unat_of_nat_eq unat_drop_bit_eq)
  also have \<open>drop_bit layer (128::nat) = 2 ^ (7 - layer)\<close>
    using assms by (simp add: drop_bit_eq_div power_diff)
  finally show ?thesis
    by simp
qed

lemma ntt_inner_len_val:
  assumes \<open>layer < (7::nat)\<close>
    shows \<open>unat (drop_bit layer (0x80::64 word)) = 2 ^ (7 - layer)\<close>
using assms by (simp add: unat_drop_bit_eq drop_bit_eq_div power_diff unat_div unat_power_lower)

lemma ntt_middle_loop_step:
  assumes \<open>block < (2::nat) ^ layer\<close>
    shows \<open>MLKEM_Specification.ntt_middle_loop (k + block) ln (2 ^ layer - block) (2 ^ layer) p =
            MLKEM_Specification.ntt_middle_loop (k + Suc block) ln (2 ^ layer - Suc block) (2 ^ layer)
              (MLKEM_Specification.ntt_inner_loop (array_nth zetas_table (k + block)) (block * (2 * ln)) ln ln p)\<close>
proof -
  from assms have \<open>2 ^ layer - block = Suc (2 ^ layer - Suc block)\<close>
    by linarith
  moreover from assms have \<open>2 ^ layer - Suc (2 ^ layer - Suc block) = block\<close>
    by linarith
  ultimately show ?thesis
    by (simp add: MLKEM_Specification.ntt_middle_loop.simps(2) Let_def)
qed

text\<open>
  Word arithmetic side-conditions for the NTT inner loop step.
  These convert between \<^verbatim>\<open>word64\<close> operations and nat-level arithmetic,
  establishing index bounds needed by the VCG.
\<close>

lemma lt_7_cases:
  assumes \<open>layer < (7::nat)\<close>
    shows \<open>layer \<in> {0, 1, 2, 3, 4, 5, 6}\<close>
using assms by auto

lemma ntt_inner_j_bound:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
    shows \<open>unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) + word64_of_nat i) < 256\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div)

lemma ntt_inner_j_plus_len_bound:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
    shows \<open>unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) + word64_of_nat i + drop_bit layer (0x80::64 word)) < 256\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div)

lemma ntt_inner_zeta_wf:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>k_val \<le> 2 ^ layer\<close>
      and \<open>block < 2 ^ layer\<close>
    shows \<open>unat (array_nth zetas_table (unat (word64_of_nat k_val + word64_of_nat block))) < mlkem_q\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div zetas_table_wf)

lemma ntt_inner_entry_wf:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
      and \<open>poly_wf q\<close>
    shows \<open>unat (array_nth q (unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) + word64_of_nat i))) < mlkem_q\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div mlkem_q_def poly_wf_def mlkem_n_def)

lemma ntt_inner_entry_plus_len_wf:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
      and \<open>poly_wf q\<close>
    shows \<open>unat (array_nth q (unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) + word64_of_nat i + drop_bit layer (0x80::64 word)))) < mlkem_q\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div mlkem_q_def poly_wf_def mlkem_n_def)

lemma ntt_inner_j_add_len_no_overflow:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
    shows \<open>unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) + word64_of_nat i) + unat (drop_bit layer (0x80::64 word)) < 18446744073709551616\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div)

lemma ntt_inner_base_add_i_no_overflow:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
    shows \<open>unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word))) +
              unat (word64_of_nat i) < 18446744073709551616\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths
    unat_of_nat unat_drop_bit_eq drop_bit_eq_div)

lemma focus_modify_mlkem_poly:
    fixes arr :: mlkem_poly
  assumes \<open>idx < (256::nat)\<close>
    shows \<open>\<nabla>{nth_focus_array idx} f arr = array_update arr idx (f (array_nth arr idx))\<close>
using assms by (simp add: nth_focus_array_components)

lemma array_nth_update_mlkem:
    fixes arr :: mlkem_poly
  assumes \<open>j < (256::nat)\<close>
    shows \<open>array_nth (array_update arr i v) j = (if i = j then v else array_nth arr j)\<close>
using assms by (simp add: array_nth_update)

lemma poly_wf_update:
    fixes p :: mlkem_poly
  assumes \<open>poly_wf p\<close>
      and \<open>unat v < mlkem_q\<close>
      and \<open>idx < mlkem_n\<close>
    shows \<open>poly_wf (array_update p idx v)\<close>
using assms by (auto simp add: poly_wf_def array_nth_update mlkem_n_def)

lemma ntt_inner_j_unat:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
    shows \<open>unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) + word64_of_nat i) =
            block * (2 * 2 ^ (7 - layer)) + i\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths unat_of_nat unat_drop_bit_eq drop_bit_eq_div)

lemma ntt_inner_jl_unat:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
    shows \<open>unat (word64_of_nat block * (2 * drop_bit layer (0x80::64 word)) +
            word64_of_nat i + drop_bit layer (0x80::64 word)) =
          block * (2 * 2 ^ (7 - layer)) + i + 2 ^ (7 - layer)\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths unat_of_nat unat_drop_bit_eq drop_bit_eq_div)

lemma ntt_inner_k_unat:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>k_val \<le> 2 ^ layer\<close>
      and \<open>block < 2 ^ layer\<close>
    shows \<open>unat (word64_of_nat k_val + word64_of_nat block) = k_val + block\<close>
using assms by (auto dest!: lt_7_cases simp add: unat_word_ariths unat_of_nat)

lemma ntt_butterfly_fold:
  shows \<open>array_update (array_update p (j + half)
          (MLKEM_Specification.zq_sub (array_nth p j)
            (MLKEM_Specification.zq_mul zeta (array_nth p (j + half))))) j
          (MLKEM_Specification.zq_add (array_nth p j)
            (MLKEM_Specification.zq_mul zeta (array_nth p (j + half)))) =
         ntt_butterfly zeta j half p\<close>
by (simp add: ntt_butterfly_def Let_def)

lemma ntt_inner_step_wf:
  assumes \<open>layer < (7::nat)\<close>
      and \<open>block < 2 ^ layer\<close>
      and \<open>i < unat (drop_bit layer (0x80::64 word))\<close>
      and \<open>poly_wf p\<close>
      and \<open>k_val \<le> 2 ^ layer\<close>
    shows \<open>poly_wf (ntt_inner_loop (array_nth zetas_table (k_val + block))
            (Suc (block * (2 * 2 ^ (7 - layer)))) (2 ^ (7 - layer)) i
            (ntt_butterfly (array_nth zetas_table (k_val + block))
              (block * (2 * 2 ^ (7 - layer))) (2 ^ (7 - layer)) p))\<close>
proof -
  have zeta_wf: \<open>unat (array_nth zetas_table (k_val + block)) < mlkem_q\<close>
    using assms by (auto dest!: lt_7_cases simp add: zetas_table_wf)
  have bound1: \<open>block * (2 * 2 ^ (7 - layer)) + 2 ^ (7 - layer) < mlkem_n\<close>
    using assms by (auto dest!: lt_7_cases simp add: mlkem_n_def)
  have bound2: \<open>Suc (block * (2 * 2 ^ (7 - layer))) + i + 2 ^ (7 - layer) \<le> mlkem_n\<close>
    using assms by (auto dest!: lt_7_cases simp add: mlkem_n_def
      unat_drop_bit_eq drop_bit_eq_div unat_of_nat)
  have len_pos: \<open>(0::nat) < 2 ^ (7 - layer)\<close>
    by simp
  have \<open>poly_wf (ntt_butterfly (array_nth zetas_table (k_val + block))
    (block * (2 * 2 ^ (7 - layer))) (2 ^ (7 - layer)) p)\<close>
    using assms(4) zeta_wf bound1 by (rule ntt_butterfly_wf)
  then show ?thesis
    using zeta_wf bound2 len_pos by (rule ntt_inner_loop_wf)
qed

lemma ntt_spec:
  notes points_to_aentails_crule_focusedL[crush_aentails_cond_crules]
  shows \<open>\<Gamma>; ntt f_ref \<Turnstile>\<^sub>F ntt_contract f_ref g p\<close>
proof (crush_boot f: ntt_def contract: ntt_contract_def, goal_cases)
  case 1
  moreover note ntt_inner_loop_snoc ntt_butterfly_wf ntt_inner_loop_wf
                MLKEM_Specification.ntt_wf
                ntt_j_plus_len_bound ntt_butterfly_disjoint_indices
                nth_lens_array_disjoint zetas_table_wf poly_wf_nth
                MLKEM_Specification.ntt_middle_loop_fst
                ntt_outer_loop_step
                ntt_k_plus_pow2_bound ntt_k_block_bound
  ultimately show ?case
    apply crush_base
    subgoal for k_ref
      apply (ucincl_discharge\<open>rule_tac
        INV=\<open>\<lambda>_ layer. \<Squnion> k_val g_f g_k p_cur.
          f_ref \<mapsto> \<langle>\<top>\<rangle>g_f \<down> p_cur
          \<star> k_ref \<mapsto> \<langle>\<top>\<rangle>g_k \<down> (word_of_nat k_val :: 64 word)
          \<star> \<langle>MLKEM_Specification.ntt_outer_loop k_val (7 - layer) p_cur
             = MLKEM_Specification.ntt_outer_loop 1 7 p\<rangle>
          \<star> \<langle>poly_wf p_cur\<rangle>
          \<star> \<langle>k_val \<le> 2 ^ layer\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
       subgoal \<comment> \<open>Init/frame: establish INV[0] and frame INV[7] to postcondition\<close>
         apply (crush_base simp add: MLKEM_Specification.ntt_def)
         apply auto
         done
       subgoal for layer \<comment> \<open>Outer loop step: one NTT layer\<close>
         apply crush_base
         subgoal for k_val g_f g_k p_cur \<comment> \<open>middle loop WP\<close>
           apply (ucincl_discharge\<open>rule_tac
             INV=\<open>\<lambda>_ block. \<Squnion> g_f_m g_k_m p_mid.
               f_ref \<mapsto> \<langle>\<top>\<rangle>g_f_m \<down> p_mid
               \<star> k_ref \<mapsto> \<langle>\<top>\<rangle>g_k_m \<down> word64_of_nat (k_val + block)
               \<star> \<langle>MLKEM_Specification.ntt_middle_loop (k_val + block)
                    (2 ^ (7 - layer)) (2 ^ layer - block) (2 ^ layer) p_mid
                  = MLKEM_Specification.ntt_middle_loop k_val
                    (2 ^ (7 - layer)) (2 ^ layer) (2 ^ layer) p_cur\<rangle>
               \<star> \<langle>poly_wf p_mid\<rangle>
               \<star> \<langle>k_val + 2 ^ layer \<le> 128\<rangle>\<close>
             and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
             and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
           in wp_raw_for_loop_framedI'\<close>)
          subgoal \<comment> \<open>middle init/frame\<close>
            apply (crush_base no_schematics
                              simp add: ntt_num_blocks_length ntt_middle_loop.simps(1)
                                        ntt_middle_loop_terminal
                                        unat_of_nat_eq unat_power_lower
                              simp del: of_nat_add of_nat_power)
            \<comment> \<open>Instantiate init existentials (g_f_m=g_f, g_k_m=g_k, p_mid=p_cur)\<close>
            apply (rule_tac x=g_f in aexists_entailsR)
            apply (rule_tac x=g_k in aexists_entailsR)
            apply (rule_tac x=p_cur in aexists_entailsR)
            \<comment> \<open>Now crush can match init heap cells and handle the frame wand\<close>
            apply (crush_base no_schematics simp del: of_nat_add of_nat_power)
            \<comment> \<open>Instantiate outer loop next-iteration existentials\<close>
            apply (rule_tac x=\<open>k_val + 2 ^ layer\<close> in aexists_entailsR)
            apply (rule_tac x=x in aexists_entailsR)
            apply (rule_tac x=xa in aexists_entailsR)
            apply (rule_tac x=xb in aexists_entailsR)
            apply crush_base
            apply (metis ntt_outer_loop_step)
            done
          subgoal for block \<comment> \<open>middle step\<close>
            apply crush_base
            subgoal for g_f_m g_k_m p_mid \<comment> \<open>inner for loop\<close>
              apply (ucincl_discharge\<open>rule_tac
                INV=\<open>\<lambda>_ j_off. \<Squnion> g_f_inner.
                  f_ref \<mapsto> \<langle>\<top>\<rangle> g_f_inner \<down> (ntt_inner_loop
                    (array_nth zetas_table (k_val + block))
                    (block * (2 * 2 ^ (7 - layer)))
                    (2 ^ (7 - layer))
                    j_off
                    p_mid)
                  \<star> \<langle>poly_wf (ntt_inner_loop
                    (array_nth zetas_table (k_val + block))
                    (block * (2 * 2 ^ (7 - layer)))
                    (2 ^ (7 - layer))
                    j_off
                    p_mid)\<rangle>\<close>
                and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
              in wp_raw_for_loop_framedI'\<close>)
              subgoal \<comment> \<open>inner init/frame\<close>
                apply (crush_base simp add: simp add: ntt_inner_len_val unat_of_nat_eq unat_power_lower)
                apply (simp only: add_Suc_right[symmetric] ntt_middle_loop_step[symmetric])
                done
              subgoal for i \<comment> \<open>inner step\<close>
                apply (clarsimp simp add: ntt_inner_len_length unat_of_nat_eq unat_power_lower)
                apply (crush_base intro!: ntt_inner_entry_wf ntt_inner_j_bound ntt_inner_zeta_wf
                  ntt_inner_entry_plus_len_wf ntt_inner_j_plus_len_bound
                  ntt_inner_j_add_len_no_overflow ntt_inner_base_add_i_no_overflow)
                apply (all \<open>frule (2) ntt_inner_j_bound\<close>, all \<open>frule (2) ntt_inner_j_plus_len_bound\<close>)
                apply (simp_all only: focus_modify_mlkem_poly)
                subgoal by (rule ntt_inner_step_wf; assumption)
                subgoal by (simp add: ntt_inner_j_unat ntt_inner_jl_unat ntt_inner_k_unat
                              array_nth_update ntt_butterfly_fold)
                subgoal
                  apply (simp only: ntt_inner_jl_unat focus_modify_mlkem_poly)
                  by (rule poly_wf_update; (assumption | simp add: mlkem_n_def))
                done
            done
            subgoal
              apply (simp add: unat_of_nat_eq unat_power_lower)
              apply (frule (2) ntt_k_block_bound)
              apply (subgoal_tac \<open>k_val + block < 2 ^ 64\<close>)
              apply (subgoal_tac \<open>unat (word64_of_nat k_val + word64_of_nat block) = k_val + block\<close>)
              apply linarith
              apply (simp del: of_nat_add add: of_nat_add[symmetric] unat_of_nat_eq)
              apply (rule less_le_trans[of _ 128])
              apply assumption
              apply simp
              done
            subgoal
              apply (simp add: unat_of_nat_eq unat_power_lower)
              apply (frule (2) ntt_k_block_bound)
              apply (subgoal_tac \<open>k_val + block < 2 ^ 64\<close>)
              apply (subgoal_tac \<open>unat (word64_of_nat k_val + word64_of_nat block) = k_val + block\<close>)
              apply linarith
              apply (simp del: of_nat_add add: of_nat_add[symmetric] unat_of_nat_eq)
              apply (rule less_le_trans[of _ 128])
              apply assumption
              apply simp
              done
            subgoal
              apply unat_arith
              apply (clarsimp simp: unat_of_nat_eq unat_power_lower unat_drop_bit_eq
                                    drop_bit_eq_div unat_word_ariths)
              apply (subgoal_tac \<open>128 div 2 ^ layer \<le> 128\<close>)
              prefer 2
                apply (rule div_le_dividend)
              apply (subgoal_tac \<open>128 div 2 ^ layer mod 18446744073709551616 = 128 div 2 ^ layer\<close>)
              prefer 2
                apply (rule mod_less, linarith)
              apply (subgoal_tac \<open>2 * (128 div 2 ^ layer) mod 18446744073709551616
                                   = 2 * (128 div 2 ^ layer)\<close>)
              prefer 2
                apply (rule mod_less, linarith)
              apply simp
              apply (subgoal_tac \<open>block * (128 div 2 ^ layer) < 129\<close>)
              apply simp
              apply (rule le_less_trans[where y=\<open>2 ^ layer * (128 div 2 ^ layer)\<close>])
              apply (rule mult_le_mono1)
              apply linarith
              apply (rule le_less_trans[where y=128])
              apply (rule thd)
              apply simp
              done
            subgoal
              apply (auto simp: unat_of_nat_eq unat_power_lower unat_arith_simps
                             unat_drop_bit_eq drop_bit_eq_div
                        intro!: le_less_trans[OF div_le_dividend])
              done
            done
          done
        subgoal
          apply (auto simp: unat_of_nat_eq)
          done
        subgoal
          apply (auto simp: unat_of_nat_eq)
          done
      done
    done
  done
qed

end

end
