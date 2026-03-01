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
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_add a b) \<psi> \<rho> \<theta> =
             (if c_signed_in_range (sint a + sint b) LENGTH('l) then
                \<psi> (word_of_int (sint a + sint b))
              else
                \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (auto simp add: c_signed_add_def c_signed_overflow_def c_abort_def Let_def
  micro_rust_wp_simps asepconj_simp)

lemma wp_c_signed_addI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>c_signed_in_range (sint a + sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a + sint b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_add a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_add a b = literal (word_of_int (sint a + sint b))\<close>
    by (simp add: c_signed_add_def c_signed_overflow_def Let_def)
  from assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Subtraction\<close>

lemma wp_c_signed_sub [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_sub a b) \<psi> \<rho> \<theta> =
            (if c_signed_in_range (sint a - sint b) LENGTH('l) then
               \<psi> (word_of_int (sint a - sint b))
             else
               \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_sub_def c_signed_overflow_def c_abort_def Let_def
  micro_rust_wp_simps asepconj_simp)

lemma wp_c_signed_subI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>c_signed_in_range (sint a - sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a - sint b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_sub a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_sub a b = literal (word_of_int (sint a - sint b))\<close>
    by (simp add: c_signed_sub_def c_signed_overflow_def Let_def)
  from assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Multiplication\<close>

lemma wp_c_signed_mul [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_mul a b) \<psi> \<rho> \<theta> =
             (if c_signed_in_range (sint a * sint b) LENGTH('l) then
                \<psi> (word_of_int (sint a * sint b))
              else
                \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_mul_def c_signed_overflow_def c_abort_def Let_def
  micro_rust_wp_simps asepconj_simp)

lemma wp_c_signed_mulI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>c_signed_in_range (sint a * sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a * sint b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_mul a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_mul a b = literal (word_of_int (sint a * sint b))\<close>
    by (simp add: c_signed_mul_def c_signed_overflow_def Let_def)
  from assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Division\<close>

lemma wp_c_signed_div [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_div a b) \<psi> \<rho> \<theta> =
             (if b = 0 then
                \<theta> (CustomAbort DivisionByZero)
              else if c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l) then
                \<psi> (word_of_int (c_trunc_div_int (sint a) (sint b)))
              else
                \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_div_def c_signed_overflow_def c_abort_def c_division_by_zero_def
  Let_def micro_rust_wp_simps asepconj_simp)

lemma wp_c_signed_divI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>b \<noteq> 0\<close>
      and \<open>c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (c_trunc_div_int (sint a) (sint b)))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_div a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_div a b = literal (word_of_int (c_trunc_div_int (sint a) (sint b)))\<close>
    by (simp add: c_signed_div_def c_signed_overflow_def c_division_by_zero_def Let_def)
  from assms this show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Modulo\<close>

lemma wp_c_signed_mod [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_mod a b) \<psi> \<rho> \<theta> =
            (if b = 0 then
               \<theta> (CustomAbort DivisionByZero)
             else if c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l) then
               \<psi> (word_of_int (c_trunc_mod_int (sint a) (sint b)))
             else
               \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_mod_def c_signed_overflow_def c_abort_def
  c_division_by_zero_def Let_def micro_rust_wp_simps asepconj_simp)

lemma wp_c_signed_modI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>b \<noteq> 0\<close>
      and \<open>c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (c_trunc_mod_int (sint a) (sint b)))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_mod a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_mod a b = literal (word_of_int (c_trunc_mod_int (sint a) (sint b)))\<close>
    by (simp add: c_signed_mod_def c_signed_overflow_def c_division_by_zero_def Let_def)
  from this assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Comparison operations\<close>

text \<open>Comparisons never overflow --- they always succeed.\<close>

lemma wp_c_signed_less [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_less a b) \<psi> \<rho> \<theta> = \<psi> (sint a < sint b)\<close>
using assms by (simp add: c_signed_less_def micro_rust_wp_simps)

lemma wp_c_signed_lessI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (sint a < sint b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_less a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_less_def wp_literalI asepconj_simp)

lemma wp_c_signed_le [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_le a b) \<psi> \<rho> \<theta> = \<psi> (sint a \<le> sint b)\<close>
using assms by (simp add: c_signed_le_def micro_rust_wp_simps)

lemma wp_c_signed_leI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (sint a \<le> sint b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_le a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_le_def wp_literalI asepconj_simp)

lemma wp_c_signed_eq [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_eq a b) \<psi> \<rho> \<theta> = \<psi> (a = b)\<close>
using assms by (simp add: c_signed_eq_def micro_rust_wp_simps)

lemma wp_c_signed_eqI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a = b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_eq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_eq_def wp_literalI asepconj_simp)

lemma wp_c_signed_neq [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_neq a b) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> b)\<close>
using assms by (simp add: c_signed_neq_def micro_rust_wp_simps)

lemma wp_c_signed_neqI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_neq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_neq_def wp_literalI asepconj_simp)

subsection \<open>Unsigned addition\<close>

lemma wp_c_unsigned_add [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_add a b) \<psi> \<rho> \<theta> = \<psi> (a + b)\<close>
using assms by (simp add: c_unsigned_add_def micro_rust_wp_simps)

lemma wp_c_unsigned_addI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a + b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_add a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_add_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Subtraction\<close>

lemma wp_c_unsigned_sub [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_sub a b) \<psi> \<rho> \<theta> = \<psi> (a - b)\<close>
using assms by (simp add: c_unsigned_sub_def micro_rust_wp_simps)

lemma wp_c_unsigned_subI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a - b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_sub a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_sub_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Multiplication\<close>

lemma wp_c_unsigned_mul [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mul a b) \<psi> \<rho> \<theta> = \<psi> (a * b)\<close>
using assms by (simp add: c_unsigned_mul_def micro_rust_wp_simps)

lemma wp_c_unsigned_mulI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a * b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_mul a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_mul_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Comparison Operations\<close>

lemma wp_c_unsigned_less [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_less a b) \<psi> \<rho> \<theta> = \<psi> (a < b)\<close>
using assms by (simp add: c_unsigned_less_def micro_rust_wp_simps)

lemma wp_c_unsigned_lessI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a < b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_less a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_less_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_le [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_le a b) \<psi> \<rho> \<theta> = \<psi> (a \<le> b)\<close>
using assms by (simp add: c_unsigned_le_def micro_rust_wp_simps)

lemma wp_c_unsigned_leI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<le> b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_le a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_le_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_eq [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_eq a b) \<psi> \<rho> \<theta> = \<psi> (a = b)\<close>
using assms by (simp add: c_unsigned_eq_def micro_rust_wp_simps)

lemma wp_c_unsigned_eqI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a = b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_eq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_eq_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_neq [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_neq a b) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> b)\<close>
using assms by (simp add: c_unsigned_neq_def micro_rust_wp_simps)

lemma wp_c_unsigned_neqI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_neq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_neq_def wp_literalI asepconj_simp)

subsection \<open>C Truthiness\<close>

lemma wp_c_signed_truthy [micro_rust_wp_simps]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_truthy a) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> 0)\<close>
using assms by (simp add: c_signed_truthy_def micro_rust_wp_simps)

lemma wp_c_signed_truthyI [micro_rust_wp_intros]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> 0)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_truthy a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_truthy_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_truthy [micro_rust_wp_simps]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_truthy a) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> 0)\<close>
using assms by (simp add: c_unsigned_truthy_def micro_rust_wp_simps)

lemma wp_c_unsigned_truthyI [micro_rust_wp_intros]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> 0)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_truthy a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_truthy_def wp_literalI asepconj_simp)

subsection \<open>Signed bitwise operations\<close>

lemma wp_c_signed_and [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_and a b) \<psi> \<rho> \<theta> = \<psi> (a AND b)\<close>
using assms by (simp add: c_signed_and_def micro_rust_wp_simps)

lemma wp_c_signed_andI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a AND b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_and a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_and_def wp_literalI asepconj_simp)

lemma wp_c_signed_or [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_or a b) \<psi> \<rho> \<theta> = \<psi> (a OR b)\<close>
using assms by (simp add: c_signed_or_def micro_rust_wp_simps)

lemma wp_c_signed_orI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a OR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_or a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_or_def wp_literalI asepconj_simp)

lemma wp_c_signed_xor [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_xor a b) \<psi> \<rho> \<theta> = \<psi> (a XOR b)\<close>
using assms by (simp add: c_signed_xor_def micro_rust_wp_simps)

lemma wp_c_signed_xorI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a XOR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_xor a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_xor_def wp_literalI asepconj_simp)

lemma wp_c_signed_not [micro_rust_wp_simps]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_not a) \<psi> \<rho> \<theta> = \<psi> (NOT a)\<close>
using assms by (simp add: c_signed_not_def micro_rust_wp_simps)

lemma wp_c_signed_notI [micro_rust_wp_intros]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (NOT a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_not a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_not_def wp_literalI asepconj_simp)

subsection \<open>Unsigned bitwise operations\<close>

lemma wp_c_unsigned_and [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_and a b) \<psi> \<rho> \<theta> = \<psi> (a AND b)\<close>
using assms by (simp add: c_unsigned_and_def micro_rust_wp_simps asepconj_simp)

lemma wp_c_unsigned_andI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a AND b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_and a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_and_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_or [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_or a b) \<psi> \<rho> \<theta> = \<psi> (a OR b)\<close>
using assms by (simp add: c_unsigned_or_def micro_rust_wp_simps)

lemma wp_c_unsigned_orI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a OR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_or a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_or_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_xor [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_xor a b) \<psi> \<rho> \<theta> = \<psi> (a XOR b)\<close>
using assms by (simp add: c_unsigned_xor_def micro_rust_wp_simps)

lemma wp_c_unsigned_xorI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a XOR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_xor a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_xor_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_not [micro_rust_wp_simps]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_not a) \<psi> \<rho> \<theta> = \<psi> (NOT a)\<close>
using assms by (simp add: c_unsigned_not_def micro_rust_wp_simps)

lemma wp_c_unsigned_notI [micro_rust_wp_intros]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (NOT a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_not a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_not_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Shift Operations\<close>

lemma wp_c_unsigned_shl [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shl a b) \<psi> \<rho> \<theta> = 
            (if unat b < LENGTH('l) then
               \<psi> (push_bit (unat b) a)
             else
               \<theta> (CustomAbort ShiftOutOfRange))\<close>
using assms by (simp add: c_unsigned_shl_def c_shift_out_of_range_def c_abort_def micro_rust_wp_simps
  asepconj_simp)

lemma wp_c_unsigned_shlI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (push_bit (unat b) a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_shl a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_unsigned_shl a b = literal (push_bit (unat b) a)\<close>
    by (simp add: c_unsigned_shl_def)
  from this assms show ?thesis
    unfolding eq using assms by (auto intro: wp_literalI simp add: asepconj_simp)
qed

lemma wp_c_unsigned_shr [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shr a b) \<psi> \<rho> \<theta> =
             (if unat b < LENGTH('l) then
                \<psi> (drop_bit (unat b) a)
              else \<theta> (CustomAbort ShiftOutOfRange))\<close>
using assms by (simp add: c_unsigned_shr_def c_shift_out_of_range_def c_abort_def
  micro_rust_wp_simps asepconj_simp)

lemma wp_c_unsigned_shrI [micro_rust_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (drop_bit (unat b) a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_shr a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_unsigned_shr a b = literal (drop_bit (unat b) a)\<close>
    by (simp add: c_unsigned_shr_def)
  from this assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Signed shift operations\<close>

lemma wp_c_signed_shl [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shl a b) \<psi> \<rho> \<theta> =
            (if unat b \<ge> LENGTH('l) then
               \<theta> (CustomAbort ShiftOutOfRange)
             else
               let result_int = sint a * 2 ^ unat b in
                 if sint a < 0 \<or> \<not> c_signed_in_range result_int LENGTH('l) then
                   \<theta> (CustomAbort SignedOverflow)
                 else
                   \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_shl_def c_shift_out_of_range_def c_signed_overflow_def
                c_abort_def Let_def micro_rust_wp_simps asepconj_simp)

lemma wp_c_signed_shlI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>sint a \<ge> 0\<close>
      and \<open>c_signed_in_range (sint a * 2 ^ unat b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a * 2 ^ unat b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shl a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_shl a b = literal (word_of_int (sint a * 2 ^ unat b))\<close>
    by (simp add: c_signed_shl_def c_shift_out_of_range_def c_signed_overflow_def Let_def)
  from this assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

lemma wp_c_signed_shr [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shr a b) \<psi> \<rho> \<theta> =
             (if unat b \<ge> LENGTH('l) then
                \<theta> (CustomAbort ShiftOutOfRange)
              else
                \<psi> (word_of_int (sint a div 2 ^ unat b)))\<close>
using assms by (simp add: c_signed_shr_def c_shift_out_of_range_def c_abort_def micro_rust_wp_simps
  asepconj_simp)

lemma wp_c_signed_shrI [micro_rust_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a div 2 ^ unat b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shr a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_shr a b = literal (word_of_int (sint a div 2 ^ unat b))\<close>
    by (simp add: c_signed_shr_def c_shift_out_of_range_def)
  from assms this show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Type cast operations\<close>

lemma wp_c_ucast [micro_rust_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_ucast w) \<psi> \<rho> \<theta> = \<psi> (ucast w)\<close>
using assms by (simp add: c_ucast_def micro_rust_wp_simps)

lemma wp_c_ucastI [micro_rust_wp_intros]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (ucast w)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_ucast w) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_ucast_def wp_literalI asepconj_simp)

lemma wp_c_scast [micro_rust_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_scast w) \<psi> \<rho> \<theta> = \<psi> (scast w)\<close>
using assms by (simp add: c_scast_def micro_rust_wp_simps)

lemma wp_c_scastI [micro_rust_wp_intros]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (scast w)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_scast w) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_scast_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Division and Modulo\<close>

lemma wp_c_unsigned_div [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_div a b) \<psi> \<rho> \<theta> =
             (if b = 0 then
                \<theta> (CustomAbort DivisionByZero)
              else
                \<psi> (a div b))\<close>
using assms by (simp add: c_unsigned_div_def c_abort_def c_division_by_zero_def micro_rust_wp_simps
  asepconj_simp)

lemma wp_c_unsigned_mod [micro_rust_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mod a b) \<psi> \<rho> \<theta> =
             (if b = 0 then
                \<theta> (CustomAbort DivisionByZero)
              else
                \<psi> (a mod b))\<close>
using assms by (simp add: c_unsigned_mod_def c_abort_def c_division_by_zero_def micro_rust_wp_simps
  asepconj_simp)

section \<open>C Integer Promotion Lemmas\<close>

text \<open>
  C11 integer promotion widens sub-int types before arithmetic. These
  lemmas show that the widen-operate-narrow roundtrip equals direct
  operation, and that 32-bit signed overflow cannot occur for promoted
  16-bit operands.
\<close>

subsection \<open>Signed 16 to 32 promotion roundtrip\<close>

lemma scast_scast_add_roundtrip_16_32 [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16 signed) (SCAST(16 signed \<rightarrow> 32 signed) a + SCAST(16 signed \<rightarrow> 32 signed) b) = a + b\<close>
by (simp add: scast_down_add scast_up_scast_id is_up is_down)

lemma scast_scast_sub_roundtrip_16_32 [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16 signed) (SCAST(16 signed \<rightarrow> 32 signed) a - SCAST(16 signed \<rightarrow> 32 signed) b) = a - b\<close>
by (simp add: scast_down_minus scast_up_scast_id is_up is_down)

subsection \<open>32-bit signed overflow bounds for promoted 16-bit signed values\<close>

lemma sint_scast_16_32_add_upper [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) + sint (SCAST(16 signed \<rightarrow> 32 signed) b) < 2147483648\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<ge> -32768 \<and> sint a \<le> 32767\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<ge> -32768 \<and> sint b \<le> 32767\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_scast_16_32_add_lower [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>- 2147483648 \<le> sint (SCAST(16 signed \<rightarrow> 32 signed) a) + sint (SCAST(16 signed \<rightarrow> 32 signed) b)\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<ge> -32768\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<ge> -32768\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_scast_16_32_sub_upper [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) - sint (SCAST(16 signed \<rightarrow> 32 signed) b) < 2147483648\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<le> 32767\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<ge> -32768\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_scast_16_32_sub_lower [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>- 2147483648 \<le> sint (SCAST(16 signed \<rightarrow> 32 signed) a) - sint (SCAST(16 signed \<rightarrow> 32 signed) b)\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<ge> -32768\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<le> 32767\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

subsection \<open>Unsigned 16 to signed 32 promotion roundtrip\<close>

lemma scast_ucast_roundtrip_16_32:
  fixes a :: \<open>16 word\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16) (UCAST(16 \<rightarrow> 32 signed) a) = a\<close>
by (simp add: scast_def sint_ucast_eq_uint is_down word_of_int_uint)

lemma scast_ucast_add_roundtrip_16_32 [simp]:
  fixes a b :: \<open>16 word\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16) (UCAST(16 \<rightarrow> 32 signed) a + UCAST(16 \<rightarrow> 32 signed) b) = a + b\<close>
by (simp add: scast_down_add is_down scast_ucast_roundtrip_16_32)

lemma sint_ucast_16_32_add_upper [simp]:
  fixes a b :: \<open>16 word\<close>
  shows \<open>sint (UCAST(16 \<rightarrow> 32 signed) a) + sint (UCAST(16 \<rightarrow> 32 signed) b) < 2147483648\<close>
proof -
  have \<open>sint (UCAST(16 \<rightarrow> 32 signed) a) = uint a\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>sint (UCAST(16 \<rightarrow> 32 signed) b) = uint b\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>uint a < 65536\<close>
    using uint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>uint b < 65536\<close>
    using uint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_ucast_16_32_add_lower [simp]:
  fixes a b :: \<open>16 word\<close>
  shows \<open>- 2147483648 \<le> sint (UCAST(16 \<rightarrow> 32 signed) a) + sint (UCAST(16 \<rightarrow> 32 signed) b)\<close>
proof -
  have \<open>sint (UCAST(16 \<rightarrow> 32 signed) a) = uint a\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>sint (UCAST(16 \<rightarrow> 32 signed) b) = uint b\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>uint a \<ge> 0\<close>
    by simp
  moreover have \<open>uint b \<ge> 0\<close>
    by simp
  ultimately show ?thesis
    by linarith
qed

end
