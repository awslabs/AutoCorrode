(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Contracts
  imports Crush.Crush StdLib_References Misc.Result
begin
(*>*)

text\<open>The following rule reduces the validity of a function spec to a
WP call entailment, to which our \<^verbatim>\<open>crush\<close> automation applies.

The main use case is for proving weakening rules: In this case, the base
contract is passed to \<^verbatim>\<open>crush\<close> to discharge \<^verbatim>\<open>call f\<close>, and the locality is
typically a direct consequence of weakening. See the examples below.\<close>

lemma satisfies_function_contract_via_call:
  assumes U0: \<open>ucincl (function_contract_pre \<C>)\<close>
      and U1: \<open>\<And>r. ucincl (function_contract_post \<C> r)\<close>
      and U2: \<open>\<And>r. ucincl (function_contract_abort \<C> r)\<close>
      and LOC: \<open>urust_is_local (yh \<Gamma>) (function_body f) (function_contract_pre \<C>)\<close>
    and W: \<open>function_contract_pre \<C> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) (function_contract_post \<C>)
                                                     (function_contract_post \<C>) 
                                                     (function_contract_abort \<C>)\<close>
  shows \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
proof -
  from W have 
    \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> call f \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
    by (simp add: wp_to_sstriple[OF W])
  from this have 
    \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> call f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
    by (clarsimp simp add: sstriple_striple)
  from this have \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> (function_body f) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
    by (simp add: striple_call_inv)
  from this and LOC have  
    \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> (function_body f) \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
      by (simp add: sstriple_striple eval_abort_def eval_return_def eval_value_def)
  from this and U0 U1 U2 show ?thesis
    by (intro satisfies_function_contractI; simp)
qed

lemma satisfies_function_contract_weaken:
  assumes C: \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
    and \<open>ucincl (function_contract_pre \<C>')\<close>
      and \<open>\<And>r. ucincl (function_contract_post \<C>' r)\<close>
      and \<open>\<And>r. ucincl (function_contract_abort \<C>' r)\<close>
      and PRE: \<open>function_contract_pre \<C>' \<longlongrightarrow> function_contract_pre \<C>\<close>
      and \<open>\<And>r. function_contract_post \<C> r \<longlongrightarrow> function_contract_post \<C>' r\<close>
      and \<open>\<And>r. function_contract_abort \<C> r \<longlongrightarrow> function_contract_abort \<C>' r\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
  using assms
  apply (elim satisfies_function_contractE', intro satisfies_function_contract_via_call;
    simp add: sstriple_implies_is_local urust_is_local_weaken[OF PRE])
  apply (crush_base specs add: C seplog drule add: PRE)
  done

lemma satisfies_function_contract_weaken_wp:
  assumes C: \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and U0: \<open>ucincl (function_contract_pre \<C>')\<close>
      and U1: \<open>\<And>r. ucincl (function_contract_post \<C>' r)\<close>
      and U2: \<open>\<And>r. ucincl (function_contract_abort \<C>' r)\<close>
      and PRE: \<open>function_contract_pre \<C>' \<longlongrightarrow> function_contract_pre \<C> \<star>
              ((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> function_contract_post \<C>' r)
               \<sqinter> ((\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> function_contract_abort \<C>' r)))\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
proof -
  from PRE and C have 
    PRE': \<open>function_contract_pre \<C>' \<longlongrightarrow> function_contract_pre \<C>\<close>
    using aentails_cancel_r aentails_trans' satisfies_function_contractE' by blast
  from C PRE' U0 U1 U2 show ?thesis
    apply (elim satisfies_function_contractE', intro satisfies_function_contract_via_call;
    simp add: sstriple_implies_is_local urust_is_local_weaken[OF PRE'])
    apply (crush_base specs add: C seplog drule add: PRE)
    done
qed

lemma satisfies_function_contract_weaken_wp_lambda:
  assumes C: \<open>\<And>x. \<Gamma> ; f \<Turnstile>\<^sub>F \<C> x\<close>
      and U0: \<open>ucincl (function_contract_pre \<C>')\<close>
      and U1: \<open>\<And>r. ucincl (function_contract_post \<C>' r)\<close>
      and U2: \<open>\<And>r. ucincl (function_contract_abort \<C>' r)\<close>
      and PRE: \<open>function_contract_pre \<C>' \<longlongrightarrow> (\<Squnion>x. function_contract_pre (\<C> x) \<star>
              ((\<Sqinter>r. function_contract_post (\<C> x) r \<Zsurj> function_contract_post \<C>' r)
               \<sqinter> (\<Sqinter>r. function_contract_abort (\<C> x) r \<Zsurj> function_contract_abort \<C>' r)))\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
proof -
  from PRE and C have PRE': \<open>function_contract_pre \<C>' \<longlongrightarrow> (\<Squnion>x. function_contract_pre (\<C> x))\<close>
    by (meson aentails_cancel_r aentails_trans aexists_entailsL aexists_entailsR
      satisfies_function_contractE')
  have \<open>urust_is_local (yh \<Gamma>) (function_body f) (function_contract_pre \<C>')\<close>
    using urust_is_local_weaken[OF PRE'] urust_is_local_Union function_contract_implies_is_local[OF C]
    by metis
  from this and U0 U1 U2 show ?thesis
    apply (intro satisfies_function_contract_via_call; simp add: function_contract_implies_is_local
      urust_is_local_weaken urust_is_local_Union)
    apply (crush_base specs add: C seplog drule add: PRE)
    done
qed

lemma Union_split: \<open>(\<Union>(x :: 'a \<times> 'b). P x) = (\<Union>(x::'a). \<Union>(y :: 'b). P (x,y))\<close> by force
lemmas satisfies_function_contract_weaken_wp_lambda2  = satisfies_function_contract_weaken_wp_lambda  [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda3  = satisfies_function_contract_weaken_wp_lambda2 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda4  = satisfies_function_contract_weaken_wp_lambda3 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda5  = satisfies_function_contract_weaken_wp_lambda4 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda6  = satisfies_function_contract_weaken_wp_lambda5 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda7  = satisfies_function_contract_weaken_wp_lambda6 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda8  = satisfies_function_contract_weaken_wp_lambda7 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda9  = satisfies_function_contract_weaken_wp_lambda8 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda10 = satisfies_function_contract_weaken_wp_lambda9 [of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda11 = satisfies_function_contract_weaken_wp_lambda10[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda12 = satisfies_function_contract_weaken_wp_lambda11[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda13 = satisfies_function_contract_weaken_wp_lambda12[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda14 = satisfies_function_contract_weaken_wp_lambda13[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda15 = satisfies_function_contract_weaken_wp_lambda14[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda16 = satisfies_function_contract_weaken_wp_lambda15[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda17 = satisfies_function_contract_weaken_wp_lambda16[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda18 = satisfies_function_contract_weaken_wp_lambda17[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda19 = satisfies_function_contract_weaken_wp_lambda18[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda20 = satisfies_function_contract_weaken_wp_lambda19[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda21 = satisfies_function_contract_weaken_wp_lambda20[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]
lemmas satisfies_function_contract_weaken_wp_lambda22 = satisfies_function_contract_weaken_wp_lambda21[of _ _ \<open>\<lambda>(x0,x1). _ x0 x1\<close>, simplified split_tupled_all Union_split, simplified]

lemmas satisfies_function_contract_weaken_wp_lambda_many =
  satisfies_function_contract_weaken_wp_lambda
  satisfies_function_contract_weaken_wp_lambda2 
  satisfies_function_contract_weaken_wp_lambda3  
  satisfies_function_contract_weaken_wp_lambda4  
  satisfies_function_contract_weaken_wp_lambda5  
  satisfies_function_contract_weaken_wp_lambda6  
  satisfies_function_contract_weaken_wp_lambda7  
  satisfies_function_contract_weaken_wp_lambda8  
  satisfies_function_contract_weaken_wp_lambda9  
  satisfies_function_contract_weaken_wp_lambda10 
  satisfies_function_contract_weaken_wp_lambda11 
  satisfies_function_contract_weaken_wp_lambda12 
  satisfies_function_contract_weaken_wp_lambda13 
  satisfies_function_contract_weaken_wp_lambda14 
  satisfies_function_contract_weaken_wp_lambda15 
  satisfies_function_contract_weaken_wp_lambda16 
  satisfies_function_contract_weaken_wp_lambda17 
  satisfies_function_contract_weaken_wp_lambda18 
  satisfies_function_contract_weaken_wp_lambda19
  satisfies_function_contract_weaken_wp_lambda20
  satisfies_function_contract_weaken_wp_lambda21
  satisfies_function_contract_weaken_wp_lambda22

lemma satisfies_function_contract_assume_precondition:
  assumes \<open>is_sat (function_contract_pre \<C>) \<Longrightarrow> (\<Gamma> ; f \<Turnstile>\<^sub>F \<C>)\<close>
      and \<open>ucincl (function_contract_pre \<C>)\<close>
      and \<open>\<And>r. ucincl (function_contract_post \<C> r)\<close>
      and \<open>\<And>r. ucincl (function_contract_abort \<C> r)\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
using assms by (metis sstriple_assume_is_sat satisfies_function_contractI)
-
lemma satisfies_function_contract_weaken':
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>ucincl (function_contract_pre \<C>')\<close>
      and \<open>\<And>r. ucincl (function_contract_post \<C>' r)\<close>
      and \<open>\<And>r. ucincl (function_contract_abort \<C>' r)\<close>
      and \<open>function_contract_pre \<C>' \<longlongrightarrow> function_contract_pre \<C>\<close>
      and \<open>\<And>r. is_sat (function_contract_pre \<C>') \<Longrightarrow>
                function_contract_post \<C> r \<longlongrightarrow> function_contract_post \<C>' r\<close>
      and \<open>\<And>r. is_sat (function_contract_pre \<C>') \<Longrightarrow>
                function_contract_abort \<C> r \<longlongrightarrow> function_contract_abort \<C>' r\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
using assms
  apply (clarsimp simp add: satisfies_function_contract_def split!: function_body.splits)
  using sstriple_consequence apply (meson sstriple_assume_is_sat satisfies_function_contract_def 
    satisfies_function_contract_weaken)
  done

(*<*)
end
(*>*)