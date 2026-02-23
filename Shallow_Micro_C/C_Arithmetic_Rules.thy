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

