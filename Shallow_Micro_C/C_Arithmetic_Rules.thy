(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Arithmetic_Rules
  imports
    C_Numeric_Types
    "Shallow_Separation_Logic.Weakest_Precondition"
begin

section \<open>WP Rules for C Arithmetic Operations\<close>

text \<open>
  We provide weakest-precondition rules for the overflow-checked C arithmetic
  operations defined in @{theory "Shallow_Micro_C.C_Numeric_Types"}.  Each
  operation has:
  \<^enum> A simp rule tagged @{text "[micro_rust_wp_simps]"} giving the equational WP.
  \<^enum> An intro rule tagged @{text "[micro_rust_wp_intros]"} that assumes
    no overflow, suitable for use by Crush.

  The intro rules follow the pattern of @{thm wp_literalI}: they do not
  require @{const ucincl} and instead reduce to @{thm wp_literalI} in the
  success case.
\<close>

subsection \<open>Overflow Condition Abbreviation\<close>

abbreviation c_signed_in_range :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>c_signed_in_range v l \<equiv> -(2^(l - 1)) \<le> v \<and> v < 2^(l - 1)\<close>

subsection \<open>Addition\<close>

lemma wp_c_signed_add [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_add a b) \<psi> \<rho> \<theta> =
    (if c_signed_in_range (sint a + sint b) LENGTH('l)
     then \<psi> (word_of_int (sint a + sint b))
     else \<theta> (CustomAbort SignedOverflow) \<star> UNIV)\<close>
  using assms
  by (simp add: c_signed_add_def c_signed_overflow_def c_abort_def Let_def
                micro_rust_wp_simps)

lemma wp_c_signed_addI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>c_signed_in_range (sint a + sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a + sint b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_add a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1) have eq: \<open>c_signed_add a b = literal (word_of_int (sint a + sint b))\<close>
    by (simp add: c_signed_add_def c_signed_overflow_def Let_def)
  show ?thesis unfolding eq using assms(2) by (rule wp_literalI)
qed


subsection \<open>Subtraction\<close>

lemma wp_c_signed_sub [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_sub a b) \<psi> \<rho> \<theta> =
    (if c_signed_in_range (sint a - sint b) LENGTH('l)
     then \<psi> (word_of_int (sint a - sint b))
     else \<theta> (CustomAbort SignedOverflow) \<star> UNIV)\<close>
  using assms
  by (simp add: c_signed_sub_def c_signed_overflow_def c_abort_def Let_def
                micro_rust_wp_simps)

lemma wp_c_signed_subI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>c_signed_in_range (sint a - sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a - sint b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_sub a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1) have eq: \<open>c_signed_sub a b = literal (word_of_int (sint a - sint b))\<close>
    by (simp add: c_signed_sub_def c_signed_overflow_def Let_def)
  show ?thesis unfolding eq using assms(2) by (rule wp_literalI)
qed

subsection \<open>Multiplication\<close>

lemma wp_c_signed_mul [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_mul a b) \<psi> \<rho> \<theta> =
    (if c_signed_in_range (sint a * sint b) LENGTH('l)
     then \<psi> (word_of_int (sint a * sint b))
     else \<theta> (CustomAbort SignedOverflow) \<star> UNIV)\<close>
  using assms
  by (simp add: c_signed_mul_def c_signed_overflow_def c_abort_def Let_def
                micro_rust_wp_simps)

lemma wp_c_signed_mulI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>c_signed_in_range (sint a * sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a * sint b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_mul a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1) have eq: \<open>c_signed_mul a b = literal (word_of_int (sint a * sint b))\<close>
    by (simp add: c_signed_mul_def c_signed_overflow_def Let_def)
  show ?thesis unfolding eq using assms(2) by (rule wp_literalI)
qed

subsection \<open>Division\<close>

lemma wp_c_signed_div [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_div a b) \<psi> \<rho> \<theta> =
    (if b = 0 then \<theta> (CustomAbort DivisionByZero) \<star> UNIV
     else if c_signed_in_range (sint a div sint b) LENGTH('l)
     then \<psi> (word_of_int (sint a div sint b))
     else \<theta> (CustomAbort SignedOverflow) \<star> UNIV)\<close>
  using assms
  by (simp add: c_signed_div_def c_signed_overflow_def c_abort_def c_division_by_zero_def Let_def
                micro_rust_wp_simps)

lemma wp_c_signed_divI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>b \<noteq> 0\<close>
      and \<open>c_signed_in_range (sint a div sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a div sint b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_div a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1,2) have eq: \<open>c_signed_div a b = literal (word_of_int (sint a div sint b))\<close>
    by (simp add: c_signed_div_def c_signed_overflow_def c_division_by_zero_def Let_def)
  show ?thesis unfolding eq using assms(3) by (rule wp_literalI)
qed

subsection \<open>Modulo\<close>

lemma wp_c_signed_mod [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_mod a b) \<psi> \<rho> \<theta> =
    (if b = 0 then \<theta> (CustomAbort DivisionByZero) \<star> UNIV
     else \<psi> (word_of_int (sint a mod sint b)))\<close>
  using assms
  by (simp add: c_signed_mod_def c_abort_def c_division_by_zero_def Let_def
                micro_rust_wp_simps)

lemma wp_c_signed_modI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>b \<noteq> 0\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a mod sint b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_mod a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1) have eq: \<open>c_signed_mod a b = literal (word_of_int (sint a mod sint b))\<close>
    by (simp add: c_signed_mod_def c_division_by_zero_def Let_def)
  show ?thesis unfolding eq using assms(2) by (rule wp_literalI)
qed

subsection \<open>Comparison Operations\<close>

text \<open>Comparisons never overflow --- they always succeed.\<close>

lemma wp_c_signed_less [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_less a b) \<psi> \<rho> \<theta> = \<psi> (sint a < sint b)\<close>
  using assms
  by (simp add: c_signed_less_def micro_rust_wp_simps)

lemma wp_c_signed_lessI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (sint a < sint b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_less a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_less_def wp_literalI)

lemma wp_c_signed_le [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_le a b) \<psi> \<rho> \<theta> = \<psi> (sint a \<le> sint b)\<close>
  using assms
  by (simp add: c_signed_le_def micro_rust_wp_simps)

lemma wp_c_signed_leI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (sint a \<le> sint b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_le a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_le_def wp_literalI)

lemma wp_c_signed_eq [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_eq a b) \<psi> \<rho> \<theta> = \<psi> (a = b)\<close>
  using assms
  by (simp add: c_signed_eq_def micro_rust_wp_simps)

lemma wp_c_signed_eqI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a = b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_eq a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_eq_def wp_literalI)

lemma wp_c_signed_neq [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_neq a b) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> b)\<close>
  using assms
  by (simp add: c_signed_neq_def micro_rust_wp_simps)

lemma wp_c_signed_neqI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_neq a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_neq_def wp_literalI)

subsection \<open>Unsigned Addition\<close>

lemma wp_c_unsigned_add [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_add a b) \<psi> \<rho> \<theta> = \<psi> (a + b)\<close>
  using assms
  by (simp add: c_unsigned_add_def micro_rust_wp_simps)

lemma wp_c_unsigned_addI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a + b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_add a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_add_def wp_literalI)

subsection \<open>Unsigned Subtraction\<close>

lemma wp_c_unsigned_sub [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_sub a b) \<psi> \<rho> \<theta> = \<psi> (a - b)\<close>
  using assms
  by (simp add: c_unsigned_sub_def micro_rust_wp_simps)

lemma wp_c_unsigned_subI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a - b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_sub a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_sub_def wp_literalI)

subsection \<open>Unsigned Multiplication\<close>

lemma wp_c_unsigned_mul [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mul a b) \<psi> \<rho> \<theta> = \<psi> (a * b)\<close>
  using assms
  by (simp add: c_unsigned_mul_def micro_rust_wp_simps)

lemma wp_c_unsigned_mulI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a * b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_mul a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_mul_def wp_literalI)

subsection \<open>Unsigned Comparison Operations\<close>

lemma wp_c_unsigned_less [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_less a b) \<psi> \<rho> \<theta> = \<psi> (a < b)\<close>
  using assms
  by (simp add: c_unsigned_less_def micro_rust_wp_simps)

lemma wp_c_unsigned_lessI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a < b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_less a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_less_def wp_literalI)

lemma wp_c_unsigned_le [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_le a b) \<psi> \<rho> \<theta> = \<psi> (a \<le> b)\<close>
  using assms
  by (simp add: c_unsigned_le_def micro_rust_wp_simps)

lemma wp_c_unsigned_leI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a \<le> b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_le a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_le_def wp_literalI)

lemma wp_c_unsigned_eq [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_eq a b) \<psi> \<rho> \<theta> = \<psi> (a = b)\<close>
  using assms
  by (simp add: c_unsigned_eq_def micro_rust_wp_simps)

lemma wp_c_unsigned_eqI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a = b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_eq a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_eq_def wp_literalI)

lemma wp_c_unsigned_neq [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_neq a b) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> b)\<close>
  using assms
  by (simp add: c_unsigned_neq_def micro_rust_wp_simps)

lemma wp_c_unsigned_neqI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_neq a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_neq_def wp_literalI)

subsection \<open>Signed Bitwise Operations\<close>

lemma wp_c_signed_and [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_and a b) \<psi> \<rho> \<theta> = \<psi> (a AND b)\<close>
  using assms by (simp add: c_signed_and_def micro_rust_wp_simps)

lemma wp_c_signed_andI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a AND b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_and a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_and_def wp_literalI)

lemma wp_c_signed_or [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_or a b) \<psi> \<rho> \<theta> = \<psi> (a OR b)\<close>
  using assms by (simp add: c_signed_or_def micro_rust_wp_simps)

lemma wp_c_signed_orI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a OR b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_or a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_or_def wp_literalI)

lemma wp_c_signed_xor [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_xor a b) \<psi> \<rho> \<theta> = \<psi> (a XOR b)\<close>
  using assms by (simp add: c_signed_xor_def micro_rust_wp_simps)

lemma wp_c_signed_xorI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a XOR b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_xor a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_xor_def wp_literalI)

lemma wp_c_signed_not [micro_rust_wp_simps]:
  fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_not a) \<psi> \<rho> \<theta> = \<psi> (NOT a)\<close>
  using assms by (simp add: c_signed_not_def micro_rust_wp_simps)

lemma wp_c_signed_notI [micro_rust_wp_intros]:
  fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (NOT a) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_not a) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_signed_not_def wp_literalI)

subsection \<open>Unsigned Bitwise Operations\<close>

lemma wp_c_unsigned_and [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_and a b) \<psi> \<rho> \<theta> = \<psi> (a AND b)\<close>
  using assms by (simp add: c_unsigned_and_def micro_rust_wp_simps)

lemma wp_c_unsigned_andI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a AND b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_and a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_and_def wp_literalI)

lemma wp_c_unsigned_or [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_or a b) \<psi> \<rho> \<theta> = \<psi> (a OR b)\<close>
  using assms by (simp add: c_unsigned_or_def micro_rust_wp_simps)

lemma wp_c_unsigned_orI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a OR b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_or a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_or_def wp_literalI)

lemma wp_c_unsigned_xor [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_xor a b) \<psi> \<rho> \<theta> = \<psi> (a XOR b)\<close>
  using assms by (simp add: c_unsigned_xor_def micro_rust_wp_simps)

lemma wp_c_unsigned_xorI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (a XOR b) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_xor a b) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_xor_def wp_literalI)

lemma wp_c_unsigned_not [micro_rust_wp_simps]:
  fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_not a) \<psi> \<rho> \<theta> = \<psi> (NOT a)\<close>
  using assms by (simp add: c_unsigned_not_def micro_rust_wp_simps)

lemma wp_c_unsigned_notI [micro_rust_wp_intros]:
  fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> (NOT a) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_not a) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: c_unsigned_not_def wp_literalI)

subsection \<open>Unsigned Shift Operations\<close>

lemma wp_c_unsigned_shl [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shl a b) \<psi> \<rho> \<theta> =
    (if unat b < LENGTH('l)
     then \<psi> (push_bit (unat b) a)
     else \<theta> (CustomAbort ShiftOutOfRange) \<star> UNIV)\<close>
  using assms
  by (simp add: c_unsigned_shl_def c_shift_out_of_range_def c_abort_def micro_rust_wp_simps)

lemma wp_c_unsigned_shlI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (push_bit (unat b) a) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_shl a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1) have eq: \<open>c_unsigned_shl a b = literal (push_bit (unat b) a)\<close>
    by (simp add: c_unsigned_shl_def)
  show ?thesis unfolding eq using assms(2) by (rule wp_literalI)
qed

lemma wp_c_unsigned_shr [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shr a b) \<psi> \<rho> \<theta> =
    (if unat b < LENGTH('l)
     then \<psi> (drop_bit (unat b) a)
     else \<theta> (CustomAbort ShiftOutOfRange) \<star> UNIV)\<close>
  using assms
  by (simp add: c_unsigned_shr_def c_shift_out_of_range_def c_abort_def micro_rust_wp_simps)

lemma wp_c_unsigned_shrI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (drop_bit (unat b) a) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_shr a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1) have eq: \<open>c_unsigned_shr a b = literal (drop_bit (unat b) a)\<close>
    by (simp add: c_unsigned_shr_def)
  show ?thesis unfolding eq using assms(2) by (rule wp_literalI)
qed

subsection \<open>Signed Shift Operations\<close>

lemma wp_c_signed_shl [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_shl a b) \<psi> \<rho> \<theta> =
    (if unat b \<ge> LENGTH('l) then \<theta> (CustomAbort ShiftOutOfRange) \<star> UNIV
     else let result_int = sint a * 2 ^ unat b in
       if sint a < 0 \<or> \<not> c_signed_in_range result_int LENGTH('l) then
         \<theta> (CustomAbort SignedOverflow) \<star> UNIV
       else \<psi> (word_of_int result_int))\<close>
  using assms
  by (simp add: c_signed_shl_def c_shift_out_of_range_def c_signed_overflow_def
                c_abort_def Let_def micro_rust_wp_simps)

lemma wp_c_signed_shlI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>unat b < LENGTH('l)\<close>
      and \<open>sint a \<ge> 0\<close>
      and \<open>c_signed_in_range (sint a * 2 ^ unat b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a * 2 ^ unat b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shl a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1,2,3) have eq: \<open>c_signed_shl a b = literal (word_of_int (sint a * 2 ^ unat b))\<close>
    by (simp add: c_signed_shl_def c_shift_out_of_range_def c_signed_overflow_def Let_def)
  show ?thesis unfolding eq using assms(4) by (rule wp_literalI)
qed

lemma wp_c_signed_shr [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_signed_shr a b) \<psi> \<rho> \<theta> =
    (if unat b \<ge> LENGTH('l) then \<theta> (CustomAbort ShiftOutOfRange) \<star> UNIV
     else if sint a < 0 then \<theta> (CustomAbort SignedOverflow) \<star> UNIV
     else \<psi> (word_of_int (sint a div 2 ^ unat b)))\<close>
  using assms
  by (simp add: c_signed_shr_def c_shift_out_of_range_def c_signed_overflow_def
                c_abort_def micro_rust_wp_simps)

lemma wp_c_signed_shrI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>unat b < LENGTH('l)\<close>
      and \<open>sint a \<ge> 0\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a div 2 ^ unat b)) \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shr a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms(1,2) have eq: \<open>c_signed_shr a b = literal (word_of_int (sint a div 2 ^ unat b))\<close>
    by (simp add: c_signed_shr_def c_shift_out_of_range_def c_signed_overflow_def)
  show ?thesis unfolding eq using assms(3) by (rule wp_literalI)
qed

subsection \<open>Unsigned Division and Modulo\<close>

lemma wp_c_unsigned_div [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_div a b) \<psi> \<rho> \<theta> =
    (if b = 0 then \<theta> (CustomAbort DivisionByZero) \<star> UNIV
     else \<psi> (a div b))\<close>
  using assms
  by (simp add: c_unsigned_div_def c_abort_def c_division_by_zero_def micro_rust_wp_simps)

lemma wp_c_unsigned_mod [micro_rust_wp_simps]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mod a b) \<psi> \<rho> \<theta> =
    (if b = 0 then \<theta> (CustomAbort DivisionByZero) \<star> UNIV
     else \<psi> (a mod b))\<close>
  using assms
  by (simp add: c_unsigned_mod_def c_abort_def c_division_by_zero_def micro_rust_wp_simps)

end

