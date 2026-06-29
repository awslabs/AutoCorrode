(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Number_Theory
  imports Micro_Rust_Std_Lib.StdLib_All "HOL-Number_Theory.Totient"
begin

section\<open>Number Theory\<close>

locale number_theory =
  reference reference_types +
  ref_word: reference_allocatable reference_types _ _ _ _ _ _ _ word_prism +
  ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism +
  ref_int: reference_allocatable reference_types _ _ _ _ _ _ _ int_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and word_prism :: \<open>('gv, 'w::len word) prism\<close>
  and nat_prism :: \<open>('gv, nat) prism\<close>
  and int_prism :: \<open>('gv, int) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_int.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun
adhoc_overloading urust_add \<rightleftharpoons> \<open>bind2 (lift_exp2 (plus :: nat \<Rightarrow> nat \<Rightarrow> nat))\<close>

abbreviation fully_owns where \<open>fully_owns r v \<equiv> \<Squnion>g. r \<mapsto>\<langle>\<top>\<rangle> g\<down>v\<close>

subsection\<open>Fibonacci\<close>

fun fib :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>fib 0 = 0\<close>
| \<open>fib (Suc 0) = 1\<close>
| \<open>fib (Suc (Suc n)) = fib n + fib (Suc n)\<close>

definition fib_prog where
  \<open>fib_prog n \<equiv> FunctionBody \<lbrakk>
    let mut a = \<llangle>0 :: nat\<rrangle>;
    let mut b = \<llangle>1 :: nat\<rrangle>;
    for i in 0..n {
      let old_a = *a;
      let old_b = *b;
      a = old_b;
      b = old_a + old_b
    };
    *a
  \<rbrakk>\<close>

definition fib_contract where
  \<open>fib_contract n \<equiv>
    make_function_contract
      (can_alloc_reference)
      (\<lambda>ret. \<langle>ret = fib (unat n)\<rangle> \<star> can_alloc_reference)\<close>
ucincl_auto fib_contract

lemma fib_spec:
  shows \<open>\<Gamma>; fib_prog n \<Turnstile>\<^sub>F fib_contract n\<close>
  apply (crush_boot f: fib_prog_def contract: fib_contract_def)
  apply crush_base
  subgoal for a_ref b_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>_ i. fully_owns a_ref (fib i) \<star> fully_owns b_ref (fib (i + 1))\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'
    \<close>)
    apply (crush_base simp add: unat_of_nat_eq le_unat_uoi')
    done
  done

subsection\<open>GCD\<close>

definition gcd_prog where
  \<open>gcd_prog a b \<equiv> FunctionBody \<lbrakk>
    let mut x = \<llangle>a :: nat\<rrangle>;
    let mut y = \<llangle>b :: nat\<rrangle>;
    #[fuel(\<epsilon>\<open>a + b\<close>)] while (*y != 0) {
      let xv = *x;
      let yv = *y;
      x = yv;
      y = \<llangle>xv mod yv\<rrangle>
    };
    *x
  \<rbrakk>\<close>

definition gcd_contract where
  \<open>gcd_contract a b \<equiv>
    make_function_contract
      (can_alloc_reference)
      (\<lambda>ret. \<langle>ret = gcd a b\<rangle> \<star> can_alloc_reference)\<close>
ucincl_auto gcd_contract

lemma gcd_spec:
  shows \<open>\<Gamma>; gcd_prog a b \<Turnstile>\<^sub>F gcd_contract a b\<close>
  apply (crush_boot f: gcd_prog_def contract: gcd_contract_def)
  apply crush_base
  subgoal for x_ref y_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion> xv yv. fully_owns x_ref xv \<star> fully_owns y_ref yv \<star> \<langle>gcd xv yv = gcd a b \<and> yv \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion> xv yv. fully_owns x_ref xv \<star> fully_owns y_ref yv \<star> \<langle>gcd xv yv = gcd a b \<and> 0 < yv \<and> yv \<le> k + 1\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI
    \<close>)
    apply crush_base
    subgoal for k _ _ r ra
      using mod_less_divisor[of ra r] by linarith
    subgoal by (simp add: gcd.commute)
    done
  done

subsection\<open>Extended GCD\<close>

definition egcd_prog where
  \<open>egcd_prog (a :: int) b \<equiv> FunctionBody \<lbrakk>
    let mut old_remainder = \<llangle>a\<rrangle>;
    let mut remainder = \<llangle>b\<rrangle>;

    let mut old_a_coef = \<llangle>1 :: int\<rrangle>;
    let mut a_coef = \<llangle>0 :: int\<rrangle>;

    let mut old_b_coef = \<llangle>0 :: int\<rrangle>;
    let mut b_coef = \<llangle>1 :: int\<rrangle>;
    #[fuel(\<epsilon>\<open>nat a + nat b\<close>)] while (*remainder > \<llangle>0 :: int\<rrangle>) {
      let old_remainder_val = *old_remainder;
      let remainder_val = *remainder;
      let quotient = \<llangle>old_remainder_val div remainder_val\<rrangle>;
      old_remainder = remainder_val;
      remainder = \<llangle>old_remainder_val - quotient * remainder_val\<rrangle>;

      let old_a_coef_val = *old_a_coef;
      let a_coef_val = *a_coef;
      old_a_coef = a_coef_val;
      a_coef = \<llangle>old_a_coef_val - quotient * a_coef_val\<rrangle>;

      let old_b_coef_val = *old_b_coef;
      let b_coef_val = *b_coef;
      old_b_coef = b_coef_val;
      b_coef = \<llangle>old_b_coef_val - quotient * b_coef_val\<rrangle>
    };

    let final_remainder = *old_remainder;
    let final_a_coef = *old_a_coef;
    let final_b_coef = *old_b_coef;

    (final_remainder, final_a_coef, final_b_coef)
  \<rbrakk>\<close>

definition egcd_contract where
  \<open>egcd_contract (a :: int) b \<equiv>
    make_function_contract
      (\<langle>0 \<le> a \<and> 0 \<le> b\<rangle> \<star> can_alloc_reference)
      (\<lambda>(g, s, t, _). \<langle>g = gcd a b \<and> a * s + b * t = g\<rangle> \<star> can_alloc_reference)\<close>
ucincl_proof egcd_contract by (clarsimp split: prod.splits; ucincl_solve)

\<comment> \<open>Heap layout + Bezout identity + gcd preservation\<close>
abbreviation egcd_inv where
  \<open>egcd_inv a b old_remainder_ref remainder_ref old_a_coef_ref a_coef_ref old_b_coef_ref b_coef_ref
            old_remainder remainder old_a_coef a_coef old_b_coef b_coef \<equiv>
    fully_owns old_remainder_ref old_remainder \<star>
    fully_owns remainder_ref remainder \<star>
    fully_owns old_a_coef_ref old_a_coef \<star>
    fully_owns a_coef_ref a_coef \<star>
    fully_owns old_b_coef_ref old_b_coef \<star>
    fully_owns b_coef_ref b_coef \<star>
    \<langle>a * old_a_coef + b * old_b_coef = old_remainder \<and>
     a * a_coef + b * b_coef = remainder \<and>
     0 \<le> old_remainder \<and> 0 \<le> remainder \<and>
     gcd old_remainder remainder = gcd a b\<rangle>\<close>

lemma egcd_spec:
  shows \<open>\<Gamma>; egcd_prog a b \<Turnstile>\<^sub>F egcd_contract a b\<close>
  apply (crush_boot f: egcd_prog_def contract: egcd_contract_def)
  apply crush_base
  subgoal for old_remainder_ref remainder_ref old_a_coef_ref a_coef_ref old_b_coef_ref b_coef_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion> old_remainder remainder old_a_coef a_coef old_b_coef b_coef.
          egcd_inv a b old_remainder_ref remainder_ref old_a_coef_ref a_coef_ref old_b_coef_ref b_coef_ref old_remainder remainder old_a_coef a_coef old_b_coef b_coef \<star>
          \<langle>remainder \<le> int k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion> old_remainder remainder old_a_coef a_coef old_b_coef b_coef.
          egcd_inv a b old_remainder_ref remainder_ref old_a_coef_ref a_coef_ref old_b_coef_ref b_coef_ref old_remainder remainder old_a_coef a_coef old_b_coef b_coef \<star>
          \<langle>0 < remainder \<and> remainder \<le> int k + 1\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI
    \<close>)
      apply crush_base
      subgoal for k _ _ _ _ _ _ r ra rb rc
        apply (simp add: minus_div_mult_eq_mod)
        using pos_mod_bound[of \<open>a * ra + b * rc\<close> \<open>a * r + b * rb\<close>]
        by linarith
      subgoal
        by (simp add: minus_div_mult_eq_mod) (metis gcd.commute gcd_red_int)
      subgoal
        by (metis minus_div_mult_eq_mod pos_mod_sign diff_ge_0_iff_ge)
      subgoal
        by (simp add: algebra_simps)
    done
  done

subsection\<open>Euler's Totient\<close>

definition totient_prog where
  \<open>totient_prog n \<equiv> FunctionBody \<lbrakk>
    let mut count = \<llangle>0 :: nat\<rrangle>;
    for i in 0..n {
      let g = gcd_prog(\<llangle>unat i + 1\<rrangle>, \<llangle>unat n\<rrangle>);
      if (\<llangle>g = 1\<rrangle>) {
        count = *count + 1
      }
    };
    *count
  \<rbrakk>\<close>

definition totient_contract where
  \<open>totient_contract n \<equiv>
    make_function_contract
      (can_alloc_reference)
      (\<lambda>ret. \<langle>ret = totient (unat n)\<rangle> \<star> can_alloc_reference)\<close>
ucincl_auto totient_contract

\<comment> \<open>\<^verbatim>\<open>|{k in {1..i+1}. P(k)}| = |{k in {1..i}. P(k)}| + (if P(i+1) then 1 else 0)\<close>\<close>
lemma card_coprime_step:
  \<open>card {k. Suc 0 \<le> k \<and> k \<le> Suc i \<and> P k} =
   card {k. Suc 0 \<le> k \<and> k \<le> i \<and> P k} + (if P (Suc i) then 1 else 0)\<close>
proof -
  have \<open>{k. Suc 0 \<le> k \<and> k \<le> Suc i \<and> P k} =
        {k. Suc 0 \<le> k \<and> k \<le> i \<and> P k} \<union> (if P (Suc i) then {Suc i} else {})\<close>
    by (auto simp: le_Suc_eq)
  thus ?thesis by (simp add: card_insert_if finite_subset[of _ "{0..i}"])
qed

lemma totient_spec:
  shows \<open>\<Gamma>; totient_prog n \<Turnstile>\<^sub>F totient_contract n\<close>
  apply (simp only: totient_contract_def totient_def totatives_def
                    atLeastSucAtMost_greaterThanAtMost)
  apply (crush_boot f: totient_prog_def)
  apply crush_base
  subgoal for count_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>_ i. fully_owns count_ref (card {k \<in> {1..i}. coprime k (unat n)}) \<star> can_alloc_reference\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'
    \<close>)
    apply (crush_base specs add: gcd_spec contracts add: gcd_contract_def simp add: unat_of_nat_eq le_unat_uoi')
    subgoal by (auto simp: le_Suc_eq coprime_iff_gcd_eq_1 intro: arg_cong[of _ _ card])
    subgoal by (simp add: card_coprime_step coprime_iff_gcd_eq_1)
    subgoal by (auto intro: arg_cong[of _ _ card])
  done
done

subsection\<open>Modular Exponentiation\<close>

definition mod_exp_prog where
  \<open>mod_exp_prog base ex m \<equiv> FunctionBody \<lbrakk>
    let mut b = \<llangle>base :: nat\<rrangle>;
    let mut e = \<llangle>ex :: nat\<rrangle>;
    let mut acc = \<llangle>1 :: nat\<rrangle>;

    #[fuel(\<epsilon>\<open>ex\<close>)] while (*e != 0) {
      let ev = *e;
      let bv = *b;
      let av = *acc;

      if (\<llangle>ev mod 2 = 1\<rrangle>) {
        acc = \<llangle>av * bv mod m\<rrangle>
      };

      b = \<llangle>bv * bv mod m\<rrangle>;
      e = \<llangle>ev div 2\<rrangle>
    };

    *acc
  \<rbrakk>\<close>

definition mod_exp_contract where
  \<open>mod_exp_contract base ex m \<equiv>
    make_function_contract
      (\<langle>m \<noteq> 1\<rangle> \<star> can_alloc_reference)
      (\<lambda>ret. \<langle>ret = base ^ ex mod m\<rangle> \<star> can_alloc_reference)\<close>
ucincl_auto mod_exp_contract

lemma sq_pow_even: \<open>even n \<Longrightarrow> (x * x) ^ (n div 2) = x ^ n\<close>
  for x :: nat
proof (elim evenE)
  fix k assume \<open>n = 2 * k\<close>
  thus \<open>(x * x) ^ (n div 2) = x ^ n\<close>
    by (simp add: power_mult_distrib mult_2 flip: power_add)
qed

lemma sq_pow_odd: \<open>n mod 2 = Suc 0 \<Longrightarrow> x * (x * x) ^ (n div 2) = x ^ n\<close>
  for x :: nat
proof -
  assume \<open>n mod 2 = Suc 0\<close>
  hence nk: \<open>n = Suc (2 * (n div 2))\<close> by arith
  show ?thesis
    by (subst nk) (simp add: power_mult_distrib mult_2 power_add)
qed

lemma mod_exp_spec:
  shows \<open>\<Gamma>; mod_exp_prog base ex m \<Turnstile>\<^sub>F mod_exp_contract base ex m\<close>
  apply (crush_boot f: mod_exp_prog_def contract: mod_exp_contract_def)
  apply crush_base
  subgoal for b_ref e_ref acc_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion> bv ev av. fully_owns b_ref bv \<star> fully_owns e_ref ev \<star> fully_owns acc_ref av \<star> \<langle>(av * bv ^ ev) mod m = base ^ ex mod m \<and> (0 < m \<longrightarrow> av < m) \<and> ev \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion> bv ev av. fully_owns b_ref bv \<star> fully_owns e_ref ev \<star> fully_owns acc_ref av \<star> \<langle>(av * bv ^ ev) mod m = base ^ ex mod m \<and> (0 < m \<longrightarrow> av < m) \<and> 0 < ev \<and> ev \<le> k + 1\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI
    \<close>)
    apply crush_base
    subgoal by linarith
    subgoal for k _ _ _ ev bv av
      using sq_pow_even[of ev bv]
      by (metis mod_mult_right_eq power_mod)
    subgoal by linarith
    subgoal for k _ _ _ ev bv av
      using sq_pow_odd[of ev bv]
      by (simp add: mod_mult_left_eq mult.assoc) (metis mod_mult_right_eq power_mod)
    subgoal by auto
  done
done

subsection\<open>Primality Testing\<close>

definition is_prime_prog where
  \<open>is_prime_prog n \<equiv> FunctionBody \<lbrakk>
    if (\<llangle>unat n < 2\<rrangle>) {
      return False;
    };

    for i in 0..n {
      if (\<llangle>(unat i + 2) * (unat i + 2) \<le> unat n \<and> unat n mod (unat i + 2) = 0\<rrangle>) {
        return False;
      }
    };

    True
  \<rbrakk>\<close>

definition is_prime_contract where
  \<open>is_prime_contract n \<equiv>
    make_function_contract
      (can_alloc_reference)
      (\<lambda>ret. \<langle>ret = prime (unat n)\<rangle> \<star> can_alloc_reference)\<close>
ucincl_auto is_prime_contract

lemma primeI_no_small_divisor:
  assumes \<open>1 < (n :: nat)\<close> \<open>\<forall>d \<in> {2..n}. d\<^sup>2 \<le> n \<longrightarrow> \<not> d dvd n\<close>
  shows \<open>prime n\<close>
proof (rule ccontr)
  assume np: \<open>\<not> prime n\<close>
  from prime_factor_nat[of n] assms(1) obtain p where p: \<open>prime p\<close> \<open>p dvd n\<close> by auto
  let ?q = \<open>n div p\<close>
  have n_eq: \<open>n = p * ?q\<close> using p(2) by simp
  have p2: \<open>2 \<le> p\<close> using p(1) prime_ge_2_nat by simp
  have q_nz: \<open>?q \<noteq> 0\<close> using n_eq assms(1) by (cases ?q) auto
  have q_n1: \<open>?q \<noteq> 1\<close> using n_eq p(1) np by auto
  have q2: \<open>2 \<le> ?q\<close> using q_nz q_n1 by linarith
  define d where \<open>d = min p ?q\<close>
  have \<open>d\<^sup>2 \<le> p * ?q\<close> unfolding d_def power2_eq_square
    by (simp add: min_def mult_le_mono1 mult_le_mono2)
  moreover have \<open>d dvd n\<close> unfolding d_def using p(2) n_eq by (auto simp: min_def dvd_div_iff_mult)
  moreover have \<open>d \<in> {2..n}\<close>
    unfolding d_def using p2 q2 dvd_imp_le[OF p(2)] div_le_dividend[of n p] assms(1) by (auto simp: min_def)
  ultimately show False using assms(2) n_eq by auto
qed

lemmas prime_natD = prime_nat_iff[THEN iffD1, THEN conjunct2, rule_format]

\<comment> \<open>Extending the no-small-divisor range by one\<close>
lemma no_small_divisor_step:
  assumes inv: \<open>\<forall>d \<in> {2..i+1}. d\<^sup>2 \<le> n \<longrightarrow> \<not> d dvd n\<close>
    and body: \<open>\<not> ((i+2)\<^sup>2 \<le> n \<and> (i+2) dvd n)\<close>
  shows \<open>\<forall>d \<in> {2..i+2}. d\<^sup>2 \<le> n \<longrightarrow> \<not> d dvd (n :: nat)\<close>
proof (intro ballI impI notI)
  fix d assume \<open>d \<in> {2..i+2}\<close> \<open>d\<^sup>2 \<le> n\<close> \<open>d dvd n\<close>
  hence \<open>d \<in> {2..i+1} \<or> d = i+2\<close> by auto
  thus False
  proof
    assume \<open>d \<in> {2..i+1}\<close>
    with inv \<open>d\<^sup>2 \<le> n\<close> \<open>d dvd n\<close> show False by auto
  next
    assume \<open>d = i+2\<close>
    with body \<open>d\<^sup>2 \<le> n\<close> \<open>d dvd n\<close> show False by auto
  qed
qed

lemma is_prime_spec:
  shows \<open>\<Gamma>; is_prime_prog n \<Turnstile>\<^sub>F is_prime_contract n\<close>
  apply (crush_boot f: is_prime_prog_def contract: is_prime_contract_def)
  apply crush_base
  subgoal
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>_ i. \<langle>\<forall>d \<in> {2..i + 1}. d\<^sup>2 \<le> unat n \<longrightarrow> \<not> d dvd unat n\<rangle> \<star> can_alloc_reference\<close> and
        \<tau>=\<open>\<lambda>ret. \<langle>ret = False \<and> \<not> prime (unat n)\<rangle> \<star> can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'
    \<close>)
    apply crush_base
    subgoal for i d
      apply (frule le_unat_uoi', simp)
      apply (drule no_small_divisor_step[of i \<open>unat n\<close>, simplified])
      apply (simp add: power2_eq_square algebra_simps dvd_eq_mod_eq_0)
      by auto
    subgoal for i
      apply (frule le_unat_uoi')
      apply simp
      apply (drule(1) prime_natD)
      by (simp add: algebra_simps)
    subgoal using primeI_no_small_divisor by auto
    done
  subgoal using not_prime_0 not_prime_1 by (auto simp: less_2_cases_iff unat_eq_zero)
  done

end

end
