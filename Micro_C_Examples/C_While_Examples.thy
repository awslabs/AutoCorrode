(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_While_Examples
  imports Simple_C_Functions
begin

section \<open>While Loop Verification Examples\<close>

text \<open>
  This theory demonstrates verification of C @{text while} loops using
  the @{const bounded_while} combinator with fuel-based termination.
  The C frontend translates @{text while} loops into @{const bounded_while}
  with a free @{typ nat} fuel parameter that becomes a function argument.
\<close>

context c_uint_verification_ctx begin

subsection \<open>Countdown\<close>

text \<open>A simple countdown loop that decrements a counter to zero.
  Uses unsigned int to keep the abort type polymorphic (unsigned arithmetic
  wraps and does not abort, unlike signed arithmetic which uses @{typ c_abort}).\<close>

micro_c_translate \<open>
void countdown(unsigned int *counter) {
  while (*counter > 0) {
    *counter = *counter - 1;
  }
}
\<close>

thm c_countdown_def

text \<open>Contract: counter starts at @{term v} and ends at 0. Fuel = @{term \<open>unat v\<close>}.\<close>

definition c_countdown_contract ::
    \<open>('addr, 'gv, c_uint) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_uint \<Rightarrow>
     ('s, 'a, 'b) function_contract\<close> where
  \<open>c_countdown_contract counter g v \<equiv>
    make_function_contract
      (counter \<mapsto>\<langle>\<top>\<rangle> g\<down>v)
      (\<lambda>_. \<Squnion>g'. counter \<mapsto>\<langle>\<top>\<rangle> g'\<down>(0 :: c_uint))\<close>

ucincl_auto c_countdown_contract

lemma c_countdown_correct:
  shows \<open>\<Gamma>; c_countdown (unat v) counter \<Turnstile>\<^sub>F c_countdown_contract counter g v\<close>
  apply (crush_boot f: c_countdown_def contract: c_countdown_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g. counter \<mapsto>\<langle>\<top>\<rangle> g\<down>(of_nat k :: c_uint)\<close>
        and INV'=\<open>\<lambda>k. \<Squnion>g. counter \<mapsto>\<langle>\<top>\<rangle> g\<down>(of_nat (Suc k) :: c_uint)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  apply (auto simp add: unat_of_nat_eq word_of_nat_eq_0_iff of_nat_diff)
  apply crush_base
  apply (simp add: linorder_not_less)
  done

subsection \<open>Break in Loop\<close>

text \<open>A loop that immediately breaks. Tests the break-flag mechanism:
  allocates a break ref, sets it to True on break, augments the condition
  to check the break flag.\<close>

micro_c_translate \<open>
unsigned int break_imm(void) {
  unsigned int x = 42;
  while (x < 100) {
    break;
  }
  return x;
}
\<close>

thm c_break_imm_def

text \<open>Contract: break fires immediately, so x stays 42. Needs fuel \<ge> 1.\<close>

definition c_break_imm_contract ::
    \<open>('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_break_imm_contract \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = 42\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_break_imm_contract

lemma c_break_imm_correct:
  assumes \<open>while_fuel \<ge> 1\<close>
  shows \<open>\<Gamma>; c_break_imm while_fuel \<Turnstile>\<^sub>F c_break_imm_contract\<close>
  apply (crush_boot f: c_break_imm_def contract: c_break_imm_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>g. x \<mapsto>\<langle>\<top>\<rangle> g\<down>(0x2A :: c_uint)) \<star> (\<Squnion>g bf. xa \<mapsto>\<langle>\<top>\<rangle> g\<down>bf)\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>g. x \<mapsto>\<langle>\<top>\<rangle> g\<down>(0x2A :: c_uint)) \<star> (\<Squnion>g. xa \<mapsto>\<langle>\<top>\<rangle> g\<down>(0 :: c_uint))\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  apply crush_base
  done

subsection \<open>Continue in Loop\<close>

text \<open>A loop that uses continue to skip an iteration. Tests the continue-flag
  mechanism: allocates a continue ref, resets it at iteration start, sets it
  to True on continue, guards subsequent statements.\<close>

micro_c_translate \<open>
unsigned int skip_three(unsigned int n) {
  unsigned int sum = 0;
  unsigned int i = 0;
  while (i < n) {
    i = i + 1;
    if (i == 3) continue;
    sum = sum + 1;
  }
  return sum;
}
\<close>

thm c_skip_three_def

text \<open>Contract: the loop sums 1 for each iteration except when @{term \<open>i = 3\<close>}.
  Result is @{term n} minus one if @{term \<open>n \<ge> 3\<close>}, otherwise @{term n}.\<close>

definition c_skip_three_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_skip_three_contract n \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (if 3 \<le> n then n - 1 else n)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_skip_three_contract

lemma c_skip_three_correct_small:
  assumes \<open>\<not> 3 \<le> n\<close>
    shows \<open>\<Gamma>; c_skip_three (unat n) n \<Turnstile>\<^sub>F c_skip_three_contract n\<close>
  apply (crush_boot f: c_skip_three_def contract: c_skip_three_contract_def)
  apply (insert assms)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>g. x \<mapsto>\<langle>\<top>\<rangle> g\<down>(n - word_of_nat k))
            \<star> (\<Squnion>g. xa \<mapsto>\<langle>\<top>\<rangle> g\<down>(n - word_of_nat k))
            \<star> (\<Squnion>g v. xb \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>g. x \<mapsto>\<langle>\<top>\<rangle> g\<down>(n - (1 + word_of_nat k)))
            \<star> (\<Squnion>g. xa \<mapsto>\<langle>\<top>\<rangle> g\<down>(n - (1 + word_of_nat k)))
            \<star> (\<Squnion>g v. xb \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  apply (auto simp add: unat_of_nat_eq word_of_nat_eq_0_iff of_nat_diff
                         word_le_nat_alt word_less_nat_alt not_le not_less
                         word_of_nat_less)
  apply crush_base
  apply (all \<open>frule word_of_nat_less, frule inc_le, frule less_is_non_zero_p1\<close>)
  apply (all \<open>frule word_diff_less[of "word_of_nat _ + 1", rotated 2],
    (assumption | simp add: word_neq_0_conv add.commute[where a="word_of_nat _" and b=1])+\<close>)
  apply (drule arg_cong[where f=unat])
  apply (simp add: unat_sub less_imp_le unat_of_nat_eq word_less_nat_alt)
  done

definition skip_count :: \<open>c_uint \<Rightarrow> c_uint\<close> where
  \<open>skip_count i = i - (if 3 \<le> i then 1 else 0)\<close>

lemma skip_count_0[simp]:
  shows \<open>skip_count 0 = 0\<close>
by (simp add: skip_count_def)

lemma skip_count_step:
  assumes \<open>i + 1 \<noteq> (0 :: c_uint)\<close>
    shows \<open>skip_count (i + 1) = skip_count i + (if i + 1 = 3 then 0 else 1)\<close>
using assms by (auto simp add: skip_count_def word_le_nat_alt word_less_nat_alt not_le not_less) unat_arith+

lemma skip_count_ge3[simp]:
  assumes \<open>3 \<le> n\<close>
    shows \<open>skip_count n = n - 1\<close>
using assms by (simp add: skip_count_def)

lemma skip_count_2[simp]:
  shows \<open>skip_count 2 = (2 :: c_uint)\<close>
by (simp add: skip_count_def)

lemma word_sub_add_1:
  shows \<open>(a :: 'a::len word) - (1 + b) = a - b - 1\<close>
by (simp add: algebra_simps)

lemma word_of_nat_sub_less:
  assumes \<open>k < unat (n :: c_uint)\<close>
    shows \<open>n - (1 + word_of_nat k) < n\<close>
using assms
  apply -
  apply (frule word_of_nat_less, frule inc_le, frule less_is_non_zero_p1)
  apply (auto simp add: word_less_nat_alt word_neq_0_conv word_less_nat_alt unat_sub less_imp_le
    add.commute[where a="word_of_nat _" and b=1])
  done

lemma word_of_nat_sub_ne_zero:
  assumes \<open>k < unat (n :: c_uint)\<close>
    shows \<open>n - word_of_nat k \<noteq> 0\<close>
using assms by (auto simp add: word_less_nat_alt unat_sub less_imp_le unat_eq_zero dest: word_of_nat_less)

lemma skip_count_step_down:
  assumes \<open>k < unat (n :: c_uint)\<close>
      and \<open>n - word_of_nat k \<noteq> 3\<close>
    shows \<open>skip_count (n - word_of_nat k) = skip_count (n - (1 + word_of_nat k)) + 1\<close>
proof -
  from assms have \<open>(n - (1 + word_of_nat k)) + 1 \<noteq> (0 :: c_uint)\<close>
    using word_of_nat_sub_ne_zero by (simp add: algebra_simps)
  from skip_count_step[OF this] assms show ?thesis
    by auto
qed

lemma skip_count_case_3:
  assumes \<open>n - word_of_nat k = (3 :: c_uint)\<close>
    shows \<open>skip_count (n - (1 + word_of_nat k)) = 2\<close>
using assms by (simp add: word_sub_add_1)

lemma c_skip_three_correct_large:
  assumes \<open>3 \<le> n\<close>
    shows \<open>\<Gamma>; c_skip_three (unat n) n \<Turnstile>\<^sub>F c_skip_three_contract n\<close>
using assms
  apply -
  apply (crush_boot f: c_skip_three_def contract: c_skip_three_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>g. x \<mapsto>\<langle>\<top>\<rangle> g\<down>(skip_count (n - word_of_nat k) :: c_uint))
            \<star> (\<Squnion>g. xa \<mapsto>\<langle>\<top>\<rangle> g\<down>(n - word_of_nat k :: c_uint))
            \<star> (\<Squnion>g v. xb \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>g. x \<mapsto>\<langle>\<top>\<rangle> g\<down>(skip_count (n - (1 + word_of_nat k)) :: c_uint))
            \<star> (\<Squnion>g. xa \<mapsto>\<langle>\<top>\<rangle> g\<down>(n - (1 + word_of_nat k) :: c_uint))
            \<star> (\<Squnion>g v. xb \<mapsto>\<langle>\<top>\<rangle> g\<down>v)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  apply (crush_base simp add: skip_count_step_down word_of_nat_sub_less skip_count_case_3)
  done

lemma c_skip_three_correct:
  shows \<open>\<Gamma>; c_skip_three (unat n) n \<Turnstile>\<^sub>F c_skip_three_contract n\<close>
using c_skip_three_correct_small c_skip_three_correct_large by (cases \<open>3 \<le> n\<close>) auto

end

end
