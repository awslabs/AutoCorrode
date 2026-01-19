(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Function_Contract
  imports Triple
begin

subsection\<open>Function contracts\<close>

text\<open>It is sometimes useful to provide independent \<^emph>\<open>contracts\<close> for a function's behaviour which may
not be the most general such behavioural description.  We introduce some dedicated machinery, here,
for working with these contracts:\<close>

datatype_record ('a, 'r, 'abort) function_contract =
  function_contract_pre :: \<open>'a assert\<close> \<comment>\<open>Precondition\<close>
  function_contract_post :: \<open>'r \<Rightarrow> 'a assert\<close> \<comment>\<open>Success post-condition\<close>
  function_contract_abort :: \<open>'abort abort \<Rightarrow> 'a assert\<close> \<comment>\<open>Abort post-condition\<close>

abbreviation \<open>make_function_contract_with_abort \<equiv> make_function_contract\<close>
abbreviation make_function_contract where
  \<open>make_function_contract pre post \<equiv> make_function_contract_with_abort pre post \<bottom>\<close>

(*<*)
context sepalg begin
(*>*)

definition satisfies_function_contract :: \<open>('a, 'abort, 'i, 'o) striple_context \<Rightarrow>
      ('a, 'r, 'abort, 'i prompt, 'o prompt_output) function_body \<Rightarrow>
      ('a, 'r, 'abort) function_contract \<Rightarrow> bool\<close> (\<open>(_)/ ; (_) \<Turnstile>\<^sub>F (_)\<close> [50,50,50]50) where
  \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C> \<longleftrightarrow>
     ucincl (function_contract_pre \<C>) \<and>
     (\<forall>r. ucincl (function_contract_post \<C> r)) \<and>
     (\<forall>r. ucincl (function_contract_abort \<C> r)) \<and>
     \<Gamma> ; function_contract_pre \<C>
         \<turnstile> function_body f
         \<stileturn> function_contract_post \<C>
            \<bowtie> function_contract_post \<C>
            \<bowtie> function_contract_abort \<C>\<close>

lemma satisfies_function_contractI:
  assumes \<open>ucincl (function_contract_pre \<C>)\<close>
      and \<open>\<And>r. ucincl (function_contract_post \<C> r)\<close>
      and \<open>\<And>r. ucincl (function_contract_abort \<C> r)\<close>
      and \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> function_body f
                 \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
  using assms by (simp add: satisfies_function_contract_def)

lemma satisfies_function_contractE:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>(\<And>\<rho>. \<Gamma> ; function_contract_pre \<C> \<turnstile> call f
                \<stileturn> function_contract_post \<C> \<bowtie> \<rho> \<bowtie> function_contract_abort \<C>) \<Longrightarrow>
            ucincl (function_contract_pre \<C>) \<Longrightarrow>
              (\<And>r. ucincl (function_contract_post \<C> r)) \<Longrightarrow>
              (\<And>r. ucincl (function_contract_abort \<C> r)) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (cases f) (simp add: satisfies_function_contract_def sstriple_callI)

lemma satisfies_function_contractE':
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>(\<Gamma> ; function_contract_pre \<C> \<turnstile> function_body f
                \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>) \<Longrightarrow>
            ucincl (function_contract_pre \<C>) \<Longrightarrow>
              (\<And>r. ucincl (function_contract_post \<C> r)) \<Longrightarrow>
              (\<And>r. ucincl (function_contract_abort \<C> r)) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (cases f) (simp add: satisfies_function_contract_def sstriple_callI)

lemma satisfies_function_contract_tripleD:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>\<And>\<rho>. \<Gamma> ; function_contract_pre \<C> \<turnstile> call f
               \<stileturn> function_contract_post \<C> \<bowtie> \<rho> \<bowtie> function_contract_abort \<C>\<close>
using assms by (auto elim: satisfies_function_contractE)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma satisfies_function_contract_tripleD':
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> function_body f
               \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
  using assms by (auto elim: satisfies_function_contractE')

lemma function_contract_implies_is_local:
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>urust_is_local (yh \<Gamma>) (function_body f) (function_contract_pre \<C>)\<close>
  using assms by (elim satisfies_function_contractE', simp add: sstriple_implies_is_local)

text\<open>Weakening rules for contracts are proved in the standard library,
building on the separation logic automation.\<close>

end

text\<open>This contract requires that a function behaves precisely like the first argument (a 'pure'
function), and does so without requiring any state.\<close>
definition lift_pure_to_contract :: \<open>'b \<Rightarrow> ('s::sepalg, 'b, 'c) function_contract\<close> where
  \<open>lift_pure_to_contract pure \<equiv>
    let pre = \<top> in
    let post = \<lambda> ret. \<langle>ret = pure\<rangle> in
    make_function_contract pre post\<close>

end