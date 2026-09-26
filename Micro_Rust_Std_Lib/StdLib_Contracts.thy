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

text\<open>Result-case post-conditions are upwards closed when both branches are, allowing
\<^verbatim>\<open>ucincl_solve\<close> to discharge fallible specifications:\<close>
lemma ucincl_case_result [ucincl_intros]:
  assumes \<open>\<And>x. ucincl (f x)\<close>
      and \<open>\<And>e. ucincl (g e)\<close>
    shows \<open>ucincl (case_result f g r)\<close>
  using assms by (cases r; simp)

lemma satisfies_function_contract_via_call:
  assumes LOC: \<open>urust_is_local (yh \<Gamma>) (function_body f) (function_contract_pre \<C>)\<close>
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
  from this show ?thesis
    by (intro satisfies_function_contractI; simp)
qed

lemma satisfies_function_contract_weaken:
  assumes C: \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and PRE: \<open>function_contract_pre \<C>' \<longlongrightarrow> function_contract_pre \<C>\<close>
      and \<open>\<And>r. function_contract_post \<C> r \<longlongrightarrow> function_contract_post \<C>' r\<close>
      and \<open>\<And>r. function_contract_abort \<C> r \<longlongrightarrow> function_contract_abort \<C>' r\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
proof (intro satisfies_function_contractI)
  show \<open>\<Gamma> ; function_contract_pre \<C>' \<turnstile> function_body f
      \<stileturn> function_contract_post \<C>' \<bowtie> function_contract_post \<C>'
      \<bowtie> function_contract_abort \<C>'\<close>
    by (rule sstriple_consequence[OF satisfies_function_contract_tripleD'[OF C]])
       (use assms in auto)
qed

lemma satisfies_function_contract_weaken_wp:
  assumes C: \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and PRE: \<open>function_contract_pre \<C>' \<longlongrightarrow> function_contract_pre \<C> \<star>
              ((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> function_contract_post \<C>' r)
               \<sqinter> ((\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> function_contract_abort \<C>' r)))\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
proof -
  let ?frame = \<open>((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> function_contract_post \<C>' r)
               \<sqinter> (\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> function_contract_abort \<C>' r))\<close>
  have framed: \<open>\<Gamma> ; function_contract_pre \<C> \<star> ?frame \<turnstile> function_body f
      \<stileturn> (\<lambda>r. function_contract_post \<C> r \<star> ?frame)
      \<bowtie> (\<lambda>r. function_contract_post \<C> r \<star> ?frame)
      \<bowtie> (\<lambda>r. function_contract_abort \<C> r \<star> ?frame)\<close>
    by (rule sstriple_frame_rule[OF satisfies_function_contract_tripleD'[OF C]])
  \<comment>\<open>The frame stores the post- and abort-wands consumed by
  \<^verbatim>\<open>awand_forall_inter_counit\<close>.\<close>
  have post: \<open>\<And>r. function_contract_post \<C> r \<star> ?frame
      \<longlongrightarrow> function_contract_post \<C>' r\<close>
    by (rule awand_forall_inter_counit)
  have abort: \<open>\<And>r. function_contract_abort \<C> r \<star> ?frame
      \<longlongrightarrow> function_contract_abort \<C>' r\<close>
    by (rule awand_forall_inter_counit)
  show ?thesis
    by (intro satisfies_function_contractI sstriple_consequence[OF framed PRE post post abort])
qed

lemma satisfies_function_contract_weaken_wp_lambda:
  assumes C: \<open>\<And>x. \<Gamma> ; f \<Turnstile>\<^sub>F \<C> x\<close>
      and PRE: \<open>function_contract_pre \<C>' \<longlongrightarrow> (\<Squnion>x. function_contract_pre (\<C> x) \<star>
              ((\<Sqinter>r. function_contract_post (\<C> x) r \<Zsurj> function_contract_post \<C>' r)
               \<sqinter> (\<Sqinter>r. function_contract_abort (\<C> x) r \<Zsurj> function_contract_abort \<C>' r)))\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>'\<close>
proof -
  let ?frame = \<open>\<lambda>x. ((\<Sqinter>r. function_contract_post (\<C> x) r \<Zsurj> function_contract_post \<C>' r)
               \<sqinter> (\<Sqinter>r. function_contract_abort (\<C> x) r \<Zsurj> function_contract_abort \<C>' r))\<close>
  have framed: \<open>\<Gamma> ; function_contract_pre (\<C> x) \<star> ?frame x \<turnstile> function_body f
      \<stileturn> function_contract_post \<C>' \<bowtie> function_contract_post \<C>'
      \<bowtie> function_contract_abort \<C>'\<close> for x
  proof -
    have base: \<open>\<Gamma> ; function_contract_pre (\<C> x) \<star> ?frame x \<turnstile> function_body f
        \<stileturn> (\<lambda>r. function_contract_post (\<C> x) r \<star> ?frame x)
        \<bowtie> (\<lambda>r. function_contract_post (\<C> x) r \<star> ?frame x)
        \<bowtie> (\<lambda>r. function_contract_abort (\<C> x) r \<star> ?frame x)\<close>
      by (rule sstriple_frame_rule[OF satisfies_function_contract_tripleD'[OF C]])
    have post: \<open>\<And>r. function_contract_post (\<C> x) r \<star> ?frame x
        \<longlongrightarrow> function_contract_post \<C>' r\<close>
      by (rule awand_forall_inter_counit)
    have abort: \<open>\<And>r. function_contract_abort (\<C> x) r \<star> ?frame x
        \<longlongrightarrow> function_contract_abort \<C>' r\<close>
      by (rule awand_forall_inter_counit)
    show ?thesis
      by (rule sstriple_consequence[OF base aentails_refl post post abort])
  qed
  have union: \<open>\<Gamma> ; (\<Squnion>x. function_contract_pre (\<C> x) \<star> ?frame x)
      \<turnstile> function_body f \<stileturn> function_contract_post \<C>'
      \<bowtie> function_contract_post \<C>' \<bowtie> function_contract_abort \<C>'\<close>
    by (rule sstriple_existsI) (rule framed)
  show ?thesis
    by (intro satisfies_function_contractI sstriple_consequence[OF union PRE];
        rule aentails_refl)
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
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
using assms by (metis sstriple_assume_is_sat satisfies_function_contractI)
-
lemma satisfies_function_contract_weaken':
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
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
