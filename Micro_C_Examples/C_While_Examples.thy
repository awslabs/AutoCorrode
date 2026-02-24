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

end

end
