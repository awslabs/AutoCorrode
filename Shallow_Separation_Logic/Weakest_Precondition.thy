(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Weakest_Precondition
  imports Assertion_Language Triple Function_Contract "Shallow_Micro_Rust.Micro_Rust" Representability
begin
(*>*)

section\<open>A weakest precondition calculus\<close>

(*<*)
context sepalg begin
(*>*)

text\<open>For solving goals related to Separation Logic triples, we introduce a Weakest Precondition (WP)
calculus: A means to convert questions about triples \<^term>\<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close> into questions of
ordinary entailment \<^term>\<open>(\<longlongrightarrow>)\<close>: For \<^emph>\<open>fixed\<close> \<^term>\<open>\<Gamma>\<close>, \<^term>\<open>e\<close>, \<^term>\<open>\<psi>\<close> and \<^term>\<open>\<rho>\<close>, we seek
to find an assertion \<^verbatim>\<open>\<W>\<P> \<Gamma> e \<psi> \<rho>\<close> so that for any \<^term>\<open>\<phi>\<close>, \<^term>\<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close> is equivalent to
 \<^verbatim>\<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho>\<close>.

First, we show that the weakest precondition exists, without explicitly computing it. This is a
consequence of basic triple properties and the abstract representability theorem proved in
\<^file>\<open>Representability.thy\<close>.

Second, we develop rules for computing or approximating the weakest precondition for various language
constructs, proceeding on a case by case basis. Ultimately, this provides the
\<^emph>\<open>weakest precondition calculus\<close> as a syntax-directed way of reasoning about triples.\<close>

subsection\<open>Representability of sstriples\<close>

text\<open>In this section, we show that for fixed \<^term>\<open>\<Gamma>\<close>, \<^term>\<open>e\<close>, \<^term>\<open>\<psi>\<close> and \<^term>\<open>\<rho>\<close>, the functor
 \<^verbatim>\<open>\<Gamma> ; _ \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho>\<close> is representable. The representing object is, by definition, the weakest
precondition for \<^verbatim>\<open>\<Gamma>,e,\<psi>,\<rho>\<close>.\<close>

text\<open>First, the definition of the sstriple as a functor on assertions:\<close>

definition sstriple_functor :: \<open>('a, 'abort, 'i, 'o) striple_context \<Rightarrow>
                  ('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow> \<comment> \<open>The expression to compute the WP for\<close>
                  ('v \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The success postcondition to compute the WP relative to\<close>
                  ('r \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The return postcondition to compute the WP relative to\<close>
                  ('abort abort \<Rightarrow> 'a assert) \<Rightarrow>
                  'a assert \<Rightarrow> bool\<close> where
  \<open>sstriple_functor \<Gamma> e \<psi> \<rho> \<theta> \<equiv> (\<lambda>\<phi>. (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>))\<close>

text \<open>From \<^file>\<open>Representability.thy\<close> we know that if the sstriple is representable, the representing
object must be given by \<^term>\<open>afunctor_sup\<close>. Let's give this a name.

Note: It should not be necessary to unfold this definition! Instead, work purely with the
universal property \<^verbatim>\<open>wp_sstriple_iff\<close> established below to reduce properties of \<^verbatim>\<open>\<W>\<P>\<close>
to properties of sstriples. There are plenty of examples below.\<close>

definition wp :: \<open>('a, 'abort, 'i, 'o) striple_context \<Rightarrow>
                  ('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow> \<comment> \<open>The expression to compute the WP for\<close>
                  ('v \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The success postcondition to compute the WP relative to\<close>
                  ('r \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The return postcondition to compute the WP relative to\<close>
                  ('abort abort \<Rightarrow> 'a assert) \<Rightarrow>
                  'a assert\<close> ("\<W>\<P>") where
  \<open>\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta> \<equiv> afunctor_sup (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>

text \<open>Next, we check the representability conditions for the sstriple functor.
First, contravariance:\<close>

lemma sstriple_contravariant:
  shows \<open>is_contravariant (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>
by (simp add: aentails_refl is_contravariant_def sstriple_consequence sstriple_functor_def)

text\<open>Second, sup-stability:\<close>

lemma sstriple_is_sup_stable:
  shows \<open>is_sup_stable (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>
by (simp add: aentails_refl is_sup_stable_def sstriple_functor_def aentails_def asat_def
  sstriple_existsI')

text\<open>As a consequence of contravariance and sup-stability, we obtain the representability
of the sstriple functor.\<close>

lemma sstriple_is_representable:
  shows \<open>is_representable (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>
using sstriple_is_sup_stable sstriple_contravariant afunctor_representability_criterion by blast

text\<open>Since we have already spelled out the representability candidate as \<^verbatim>\<open>\<W>\<P>\<close>, representability
can concretely be stated as follows:\<close>

lemma sstriple_wp_iff:
  shows \<open>(\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
proof -
  from afunctor_representability_iff[OF sstriple_is_representable] have
     \<open>(\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) \<longleftrightarrow> sstriple_functor \<Gamma> e \<psi> \<rho> \<theta> \<phi>\<close>
    by (force simp add: wp_def)
  from this show ?thesis
    unfolding sstriple_functor_def by simp
qed

lemma wp_sstriple_iff:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>)\<close>
  by (simp add: sstriple_wp_iff)

corollary wp_to_sstriple:
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    shows \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms wp_sstriple_iff by blast

corollary wp_is_precondition:
    shows \<open>\<Gamma> ; \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (simp add: aentails_refl wp_to_sstriple)

corollary wp_is_weakest_precondition:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
  using assms wp_sstriple_iff by blast

subsection\<open>Transporting general triple properties to WP-rules\<close>

text \<open>In this section, we demonstrate how to transport properties of sstriples to properties
of the weakest precondition. The proofs are purely formal and solely rely on the universal property
of the weakest precondition,  but not its concrete definition.\<close>

text \<open>First, the weakest precondition is always upwards closed:\<close>
lemma ucincl_wp'I [ucincl_intros]:
  shows \<open>ucincl (\<W>\<P> \<Gamma> e \<phi> \<psi> \<theta>)\<close>
  \<comment>\<open>For sake of demonstration, we go through this proof in small steps:\<close>
  \<comment>\<open>First, we need to use a definition of \<^term>\<open>ucincl\<close> which only uses \<^verbatim>\<open>_ \<longlongrightarrow> \<phi>\<close>,
  but not \<^verbatim>\<open>\<phi>\<close> itself. Luckily, \<^verbatim>\<open>ucincl_alt'\<close> provides such:\<close>
  apply (simp add: ucincl_alt')
  \<comment>\<open>Next, we apply the universal property of \<^verbatim>\<open>\<W>\<P>\<close> on both sides:\<close>
  apply (simp add: sstriple_wp_iff)
  \<comment>\<open>This has transformed the goal to an assertion about sstriples that we have proved before.\<close>
  apply (simp flip: sstriple_upwards_closure)
  done

text \<open>The weakest precondition is unchanged when passing to the upwards closure of the
post-conditions:\<close>
lemma wp_upwards_closure:
  shows \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e \<psi> (\<lambda>r. (\<rho> r \<star> \<top>)) \<theta>\<close>
    and \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e (\<lambda>r. (\<psi> r \<star> \<top>)) \<rho> \<theta>\<close>
    and \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e \<psi> \<rho> (\<lambda>a. \<theta> a \<star> \<top>)\<close>
    and \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e (\<lambda>r. (\<psi> r \<star> \<top>)) (\<lambda>r. (\<rho> r \<star> \<top>)) (\<lambda>a. (\<theta> a \<star> \<top>))\<close>
  \<comment>\<open>Here we use \<^verbatim>\<open>aentails_yonedaI\<close> to transform the goals into statements involving only
  \<^verbatim>\<open>_ \<longlongrightarrow> \<W>\<P> _\<close>. This allows us to apply the universal property \<^verbatim>\<open>sstriple_wp_iff\<close>, thereby
  reducing the statement to known upwards closure properties of sstriple:\<close>
  by (auto
    intro!: aentails_yonedaI
    simp add: sstriple_wp_iff
    simp flip: sstriple_upwards_closure)

text\<open>The transitivity/consequence rule for triples yields a similar rule for weakest preconditions.
It allows us to strengthen preconditions and weaken postconditions:\<close>

lemma wp_consequence:
  assumes \<open>\<phi>' \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi>' \<rho>' \<theta>'\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<And>r. \<psi>' r \<longlongrightarrow> \<psi> r\<close>
      and \<open>\<And>r. \<rho>' r \<longlongrightarrow> \<rho> r\<close>
      and \<open>\<And>r. \<theta>' r \<longlongrightarrow> \<theta> r\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
  using assms sstriple_consequence wp_is_weakest_precondition wp_to_sstriple by metis

text\<open>Using \<^term>\<open>wp_striple_iff\<close>, we can transport some frame rules into the weakest precondition setting:\<close>

theorem wp_frame_ruleI:
  assumes \<open>\<phi>' \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<psi> r) (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<rho> r) (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<theta> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> (\<phi>' \<Zsurj> \<phi>)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
using assms sstriple_frame_ruleI' wp_sstriple_iff by blast

theorem wp_frame_rule_asepconj_multi_singleI:
  assumes \<open>\<xi> (lst ! i) \<star> \<phi> \<longlongrightarrow>
              \<W>\<P> \<Gamma> e (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<psi> r)
                      (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<rho> r)
                      (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<theta> r)\<close>
      and \<open>ucincl \<phi>\<close>
      and \<open>i < length lst\<close>
    shows \<open>\<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
using assms sstriple_frame_rule_asepconj_multi_singleI' wp_sstriple_iff by blast

lemma sstriple_pure_to_wp':
    notes asat_simp [simp]
      and asepconj_simp [simp]
  assumes \<open>ucincl (\<psi> x)\<close>
      and \<open>\<Gamma>; \<top> \<turnstile> e \<stileturn> (\<lambda>v. \<langle>v = x\<rangle>) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
    shows \<open>\<psi> x \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; \<top> \<star> \<psi> x \<turnstile> e \<stileturn> (\<lambda>v. \<langle>v = x\<rangle> \<star> \<psi> x) \<bowtie> (\<lambda>_. \<bottom> \<star> \<psi> x) \<bowtie> (\<lambda>_. \<bottom> \<star> \<psi> x)\<close>
    by (intro sstriple_frame_rule, auto simp add: bot_fun_def)
  from assms and this show \<open>\<psi> x \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    by (intro wp_is_weakest_precondition; clarsimp)
      (rule sstriple_consequence, auto simp add: aentails_def)
qed

text \<open>This is a useful lemma for transporting Hoare triple facts of straight-line code (guaranteed
not to return) directly into WP facts using a standard pattern.\<close>
lemma sstriple_straightline_to_wp:
  notes asepconj_simp [simp]
  assumes \<open>\<Gamma>; pre \<turnstile> e \<stileturn> post \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
  shows \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn>
                          (\<lambda>v. post v \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))
                       \<bowtie> (\<lambda>_. \<bottom> \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))
                       \<bowtie> (\<lambda>_. \<bottom> \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))\<close>
    by (intro sstriple_frame_rule; clarsimp simp add: bot_fun_def ucincl_intros intro!:ucincl_Int)
  moreover have \<open>\<And>r. post r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl aforall_entailsL asepconj_comm awand_adjoint)
  ultimately have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (simp add: aentails_refl local.bot_aentails_all local.sstriple_consequence)
  from this and assms show \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    using wp_sstriple_iff by blast
qed

lemma sstriple_straightline_to_wp_with_abort:
    notes asepconj_simp [simp]
  assumes \<open>\<Gamma>; pre \<turnstile> e \<stileturn> post \<bowtie> \<bottom> \<bowtie> ab\<close>
    shows \<open>pre \<star> ((\<Sqinter>v. post v \<Zsurj> \<psi> v)\<sqinter>(\<Sqinter>v. ab v \<Zsurj> \<theta> v)) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  let ?frame = \<open>((\<Sqinter>v. post v \<Zsurj> \<psi> v)\<sqinter>(\<Sqinter>v. ab v \<Zsurj> \<theta> v))\<close>
  from assms have A: \<open>\<Gamma>; pre \<star> ?frame \<turnstile> e \<stileturn>
                          (\<lambda>v. post v \<star> ?frame)
                       \<bowtie> (\<lambda>_. \<bottom> \<star> ?frame)
                       \<bowtie> (\<lambda>r. ab r \<star> ?frame)\<close>
    by (intro sstriple_frame_rule; clarsimp simp add: bot_fun_def ucincl_intros intro!:ucincl_Int)
  moreover have B: \<open>\<And>r. ab r \<star> ?frame \<longlongrightarrow> \<theta> r\<close>
    by (metis (no_types, lifting) aentails_refl_eq inf_commute aentails_fold_def
      aentails_inter_weaken2 aforall_entailsL asepconj_mono3)
  moreover have C: \<open>\<And>r. post r \<star> ?frame \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl_eq aentails_fold_def
      aentails_inter_weaken2 aforall_entailsL asepconj_mono3)
  have \<open>\<Gamma>; pre \<star> ?frame \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using sstriple_consequence [OF A]
    by (simp add: B C aentails_refl local.bot_aentails_all)
  from this and assms show \<open>pre \<star> ?frame \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    using wp_sstriple_iff by blast
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_to_wp_frame:
  assumes \<open>\<Gamma>; pre \<turnstile> e \<stileturn> post
                        \<bowtie> (\<lambda>r. (\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<rho> r)
                        \<bowtie> (\<lambda>r. (\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<theta> r)\<close>
    shows \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn> (\<lambda>v. post v \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v')) \<bowtie>
                        (\<lambda>r. ((\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<rho> r) \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v')) \<bowtie>
                        (\<lambda>r. ((\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<theta> r) \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))\<close>
    by (intro sstriple_frame_rule; clarsimp simp add: ucincl_intros intro!: ucincl_Int)
  moreover have \<open>pre \<star> (\<Inter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> pre \<star> (\<Inter>v. post v \<Zsurj> \<psi> v)\<close>
    by (intro aentails_refl)
  moreover have \<open>\<And>r. post r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<psi> r\<close>
    by (meson aentails_refl local.aentails_forward local.aforall_entailsL local.asepconj_mono)
  moreover have \<open>\<And>r. (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<rho> r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<rho> r\<close>
    by (blast intro: awand_mp)
  moreover have \<open>\<And>r. (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<theta> r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<theta> r\<close>
    by (blast intro: awand_mp)
  ultimately have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (rule sstriple_consequence)
  then show \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    using assms by (auto intro!: wp_is_weakest_precondition ucincl_asepconj ucincl_Int ucincl_awand)
qed

subsection\<open>Local axioms for Micro Rust expressions\<close>

text\<open>In this section, we reason on a case-by-case basis, computing the Weakest Precondition for the
expressions of Core Micro Rust.  Note that, as many expressions are defined as abbreviations,
written in terms of a small set of core expressions that others elaborate into, we need only
consider this core set here.

First, we introduce some named collections of theorem that will be useful later, when defining
automation tactics.  We have theorem collections relating to simplification and introduction rules
for the Weakest Precondition calculus:\<close>

named_theorems micro_rust_wp_simps
named_theorems micro_rust_wp_elims
named_theorems micro_rust_wp_intros
named_theorems micro_rust_wp_case_splits

text\<open>Introduction rules introducing schematic variables. Those should be attempted after
destructing quantified assumptions, as only then the schematic may depend on the quantifiers
in the assumptions:\<close>
named_theorems micro_rust_wp_ex_intros

lemma wp_pause:
    notes asepconj_simp [simp]
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk> \<psi> \<rho> \<theta> = \<psi> ()\<close>
  using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_pause')

text\<open>The following is deliberately not marked as \<^verbatim>\<open>micro_rust_wp_intros\<close> so automation does not
silently go over it.\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_pauseI:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_pause)

lemma wp_log:
    notes asepconj_simp [simp]
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> \<lbrakk> \<l>\<o>\<g> \<llangle>p\<rrangle> \<llangle>l\<rrangle> \<rbrakk> \<psi> \<rho> \<theta> = \<psi> ()\<close>
using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_log')

lemma wp_logI [micro_rust_wp_intros]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> \<l>\<o>\<g> \<llangle>p\<rrangle> \<llangle>l\<rrangle> \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_log)

lemma wp_fatalI [micro_rust_wp_intros]:
    notes asepconj_simp [simp]
  assumes \<open>is_aborting_striple_context \<Gamma>\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> fatal!(msg) \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_fatal)

lemma wp_literal [micro_rust_wp_simps]:
    notes asepconj_simp [simp]
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (\<up>v) \<psi> \<rho>  \<theta> = \<psi> v\<close>
  using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_literal)

lemma wp_literal_coreI:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> v\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (\<up>v) \<psi> \<rho> \<theta>\<close>
using assms by (subst wp_literal)

lemma wp_literalI[micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> v \<star> \<top>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (\<up>v) \<psi> \<rho> \<theta>\<close>
  by (simp add: assms local.sstriple_literal local.sstriple_wp_iff)

text\<open>As immediate corollaries of the result above we have analogous results for all of our literal
values for Core Micro Rust:\<close>
corollary wp_core_rust_literals [micro_rust_wp_simps]:
  shows \<open>\<And>\<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> `True \<psi> \<rho>  \<theta>= \<psi> True\<close>
    and \<open>\<And>\<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> `False \<psi> \<rho>  \<theta>= \<psi> False\<close>
    and \<open>\<And>\<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> `None \<psi> \<rho>  \<theta>= \<psi> None\<close>
    and \<open>\<And>x \<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> (`Some (\<up>x)) \<psi> \<rho>  \<theta>= \<psi> (Some x)\<close>
by (auto simp add: true_def false_def none_def some_def wp_literal micro_rust_simps)

lemma wp_abort [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (abort a) \<psi> \<rho> \<theta> = \<theta> a \<star> UNIV\<close>
  by (clarsimp intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_abort)

corollary wp_panic [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> panic!(m) \<rbrakk> \<psi> \<rho> \<theta> = \<theta> (Panic m) \<star> UNIV\<close>
  by (intro wp_abort)

lemma wp_abortI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> a \<star> UNIV\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (abort a) \<psi> \<rho> \<theta>\<close>
using assms by (subst wp_abort)

lemma wp_panicI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (Panic m) \<star> UNIV\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> panic!(m) \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (subst wp_panic)

lemma wp_return [micro_rust_wp_simps]:
    shows \<open>\<W>\<P> \<Gamma> \<lbrakk> return v; \<rbrakk> \<psi> \<rho> \<theta> = \<rho> v \<star> \<top>\<close>
by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_return)

lemma wp_returnI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<rho> v \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> return v; \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_return)

lemma wp_assert [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> assert!(x) \<rbrakk> \<psi> \<rho> \<theta> = (\<langle>x\<rangle> \<Zsurj> (UNIV \<star> \<psi> ())) \<sqinter> (\<langle>\<not>x\<rangle> \<Zsurj> (UNIV \<star> \<theta> AssertionFailed))\<close>
  apply (intro aentails_yonedaI)
  apply (clarsimp simp add: sstriple_wp_iff aentails_simp sstriple_assert apure_def asepconj_simp
    bot_aentails_all)
  apply (meson aentails_refl_eq aentails_trans aentails_top_R' aentails_uc'
    ucincl_UNIV ucincl_asepconjL)
  done

lemma wp_assert_eq [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> assert_eq!(x, y) \<rbrakk> \<psi> \<rho> \<theta> =
     (\<langle>x=y\<rangle> \<Zsurj> (UNIV \<star> \<psi> ())) \<sqinter> (\<langle>x\<noteq>y\<rangle> \<Zsurj> (UNIV \<star> \<theta> AssertionFailed))\<close>
  by (clarsimp simp add: wp_assert[simplified assert_def micro_rust_simps]
    assert_eq_def assert_eq_val_def micro_rust_simps)

thm aentails_frulify_pure

lemma wp_assertI[micro_rust_wp_intros]:
    notes aentails_intro [intro]
  assumes \<open>\<phi> \<longlongrightarrow> (\<langle>x\<rangle> \<star> \<psi> ())\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> assert!(x) \<rbrakk> \<psi> \<rho> \<theta>\<close>
proof -
  have \<open>\<langle>x\<rangle> \<star> \<psi> () \<star> \<langle>x\<rangle> \<longlongrightarrow> UNIV \<star> \<psi> ()\<close>
    by (simp add: aentails_refl apure_entailsL' asepconj_comm asepconj_pure2)
  moreover
  have \<open>\<langle>x\<rangle> \<star> \<psi> () \<star> \<langle>\<not> x\<rangle> \<longlongrightarrow> UNIV \<star> \<theta> AssertionFailed\<close>
    by (metis local.aentails_is_sat local.is_sat_pure local.is_sat_splitE)
  ultimately show ?thesis
    using aentails_trans[OF assms]
    by (simp add: wp_assert aentails_intI asepconj_assoc awand_adjoint)
qed

lemma wp_assert_eqI[micro_rust_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>\<phi> \<longlongrightarrow> (\<langle>x=y\<rangle> \<star> \<psi> ())\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> assert_eq!(x,y) \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp intro!: wp_assertI[simplified assert_def micro_rust_simps]
     simp add: assert_eq_def assert_eq_val_def micro_rust_simps)

lemma wp_assert_neI[micro_rust_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>\<phi> \<longlongrightarrow> (\<langle>x\<noteq>y\<rangle> \<star> \<psi> ())\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> assert_ne!(x,y) \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp intro!: wp_assertI[simplified assert_def micro_rust_simps]
     simp add: assert_ne_def assert_ne_val_def micro_rust_simps)

lemma wp_bind_core:
  shows \<open>\<W>\<P> \<Gamma> e (\<lambda>r. \<W>\<P> \<Gamma> (f r) \<xi> \<rho> \<theta>) \<rho> \<theta> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> let v = \<epsilon>\<open>e\<close>; \<epsilon>\<open>f v\<close> \<rbrakk> \<xi> \<rho> \<theta>\<close>
  by (meson sstriple_bindI wp_is_precondition wp_sstriple_iff)

lemma aentails_cong_only_rhs:
  assumes \<open>\<psi> = \<psi>'\<close>
    shows \<open>(\<phi> \<longlongrightarrow> \<psi>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi>')\<close>
using assms by auto

lemma wp_bindI [micro_rust_wp_intros]:
    notes aentails_intro [intro]
    fixes e :: \<open>('a, 'b, 'c, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda>r. \<W>\<P> \<Gamma> (f r) \<xi> \<rho> \<theta>) \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> let v = \<epsilon>\<open>e\<close>; \<epsilon>\<open>f v\<close> \<rbrakk>  \<xi> \<rho> \<theta>\<close>
using assms by (blast intro: wp_bind_core)

corollary wp_sequence_core:
  shows \<open>\<W>\<P> \<Gamma> e (\<lambda>x. \<W>\<P> \<Gamma> f \<xi> \<rho> \<theta>) \<rho> \<theta> \<longlongrightarrow> \<W>\<P> \<Gamma> (sequence e f) \<xi> \<rho> \<theta>\<close>
by (auto simp add: sequence_def intro!: wp_bind_core)

lemma wp_sequenceI [micro_rust_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda>x. \<W>\<P> \<Gamma> f \<xi> \<rho> \<theta>) \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (sequence e f) \<xi> \<rho> \<theta>\<close>
using assms wp_sequence_core by blast

lemma wp_two_armed_conditional:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> if x { \<epsilon>\<open>t\<close> } else { \<epsilon>\<open>f\<close> } \<rbrakk> \<psi> \<rho> \<theta>
     = (if x then \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta> else \<W>\<P> \<Gamma> f \<psi> \<rho> \<theta>)\<close>
by (cases x) (auto simp add: micro_rust_simps)

lemma wp_two_armed_conditionalI[micro_rust_wp_case_splits]:
  assumes \<open>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta>\<close>
      and \<open>\<not>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> f \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> if x { \<epsilon>\<open>t\<close> } else { \<epsilon>\<open>f\<close> }\<rbrakk> \<psi> \<rho> \<theta>\<close>
by (simp add: assms wp_two_armed_conditional)

corollary wp_one_armed_conditional:
  assumes \<open>\<And>s. ucincl (\<psi> s)\<close>
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> if x { \<epsilon>\<open>t\<close> } \<rbrakk> \<psi> \<rho> \<theta> = (if x then \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta> else \<psi> ())\<close>
using assms by (simp add: micro_rust_wp_simps wp_two_armed_conditional)

lemma wp_one_armed_conditionalI[micro_rust_wp_case_splits]:
  assumes \<open>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta>\<close>
      and \<open>\<not>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi> () \<star> \<top>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> if x { \<epsilon>\<open>t\<close> } \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_literalI wp_two_armed_conditional)

lemma wp_two_armed_conditional_thenI:
  assumes \<open>x\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> if x { \<epsilon>\<open>t\<close> } else { \<epsilon>\<open>f\<close> }\<rbrakk> \<psi> \<rho> \<theta>\<close>
  by (simp add: assms wp_two_armed_conditional)

lemma wp_two_armed_conditional_elseI:
  assumes \<open>\<not>x\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> f \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> if x { \<epsilon>\<open>t\<close> } else { \<epsilon>\<open>f\<close> }\<rbrakk> \<psi> \<rho> \<theta>\<close>
  by (simp add: assms wp_two_armed_conditional)

\<comment>\<open>TODO: This is not uniform with the treatment of conditionals
which are discharged using \<^verbatim>\<open>micro_rust_wp_intros\<close> rather than
\<^verbatim>\<open>micro_rust_wp_simps\<close>.\<close>
lemma wp_option_cases: (* [micro_rust_wp_simps]: *)
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> match x { None \<Rightarrow> \<epsilon>\<open>nn\<close>, Some(s) \<Rightarrow> \<epsilon>\<open>sm s\<close> } \<rbrakk> \<psi> \<rho> \<theta> =
          (case x of
             None   \<Rightarrow> \<W>\<P> \<Gamma> nn \<psi> \<rho> \<theta>
           | Some s \<Rightarrow> \<W>\<P> \<Gamma> (sm s) \<psi> \<rho> \<theta>)\<close>
by (rule asat_semequivI; cases \<open>x\<close>) (auto simp add: micro_rust_simps)

lemma wp_option_cases_none[micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> match None { Some(s) \<Rightarrow> \<epsilon>\<open>sm s\<close>, None \<Rightarrow> \<epsilon>\<open>nn\<close> } \<rbrakk> \<psi> \<rho> \<theta> = \<W>\<P> \<Gamma> nn \<psi> \<rho> \<theta>\<close>
  by (simp add: wp_option_cases)

lemma wp_option_cases_some[micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> match \<llangle>Some s\<rrangle> { Some(s) \<Rightarrow> \<epsilon>\<open>sm s\<close>, None \<Rightarrow> \<epsilon>\<open>nn\<close> } \<rbrakk> \<psi> \<rho> \<theta> = \<W>\<P> \<Gamma> (sm s) \<psi> \<rho> \<theta>\<close>
  by (simp add: wp_option_cases)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_option_casesI:
  assumes \<open>x = None \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> nn \<psi> \<rho> \<theta>\<close>
     and \<open>\<And>s. x = Some s \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (sm s) \<psi> \<rho> \<theta>\<close>
   shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> match x { None \<Rightarrow> \<epsilon>\<open>nn\<close>, Some(s) \<Rightarrow> \<epsilon>\<open>sm s\<close> } \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp simp add: wp_option_cases split!: option.splits)

lemma wp_result_cases: (* [micro_rust_wp_simps]: *)
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> match x { Ok(k) \<Rightarrow> \<epsilon>\<open>ok k\<close>, Err(e) \<Rightarrow> \<epsilon>\<open>err e\<close> } \<rbrakk> \<psi> \<rho> \<theta> =
           (case x of
              Ok k  \<Rightarrow> \<W>\<P> \<Gamma> (ok k) \<psi> \<rho> \<theta>
            | Err e \<Rightarrow> \<W>\<P> \<Gamma> (err e) \<psi> \<rho> \<theta>)\<close>
by (rule asat_semequivI; cases \<open>x\<close>) (auto simp add:micro_rust_simps)

lemma wp_result_cases_ok[micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> match \<llangle>Ok k\<rrangle> { Ok(k) \<Rightarrow> \<epsilon>\<open>ok k\<close>, Err(e) \<Rightarrow> \<epsilon>\<open>err e\<close> } \<rbrakk> \<psi> \<rho> \<theta> = \<W>\<P> \<Gamma> (ok k) \<psi> \<rho> \<theta>\<close>
  by (simp add: wp_result_cases)

lemma wp_result_cases_err[micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> \<lbrakk> match \<llangle>Err e\<rrangle> { Ok(k) \<Rightarrow> \<epsilon>\<open>ok k\<close>, Err(e) \<Rightarrow> \<epsilon>\<open>err e\<close> } \<rbrakk> \<psi> \<rho> \<theta> = \<W>\<P> \<Gamma> (err e) \<psi> \<rho> \<theta>\<close>
  by (simp add: wp_result_cases)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_result_casesI:
  assumes \<open>\<And>k. x = Ok k \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (ok k) \<psi> \<rho> \<theta>\<close>
     and \<open>\<And>e. x = Err e \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (err e) \<psi> \<rho> \<theta>\<close>
   shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> match x { Ok(k) \<Rightarrow> \<epsilon>\<open>ok k\<close>, Err(e) \<Rightarrow> \<epsilon>\<open>err e\<close> } \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp simp add: wp_result_cases split!: result.splits)

lemma wp_get:
    notes asat_simp [simp]
  assumes \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
    shows \<open>has f v \<star> (has f v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> (get f) \<psi> \<rho> \<theta>\<close>
proof -
  have \<open>has f v \<star> (\<Sqinter>x. (\<langle>x=v\<rangle> \<star> has f v) \<Zsurj> \<psi> x) \<longlongrightarrow> \<W>\<P> \<Gamma> (get f) \<psi> \<rho> \<theta>\<close>
    using assms by (auto intro!: sstriple_straightline_to_wp sstriple_getI)
  moreover from assms have \<open>has f v \<star> (has f v \<Zsurj> \<psi> v) \<longlongrightarrow> has f v \<star> (\<Sqinter>x. (\<langle>x=v\<rangle> \<star> has f v) \<Zsurj> \<psi> x)\<close>
    by (clarsimp simp add: aentails_def elim!: awandE asepconjE) (force intro: asepconjI awandI)
  ultimately show ?thesis
    using aentails_trans by force
qed

lemma wp_put:
  assumes \<open>\<And>x. x \<Turnstile> has f v \<Longrightarrow> g x \<Turnstile> has f v'\<close>
      and \<open>\<And>x y. x\<sharp>y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> g (x+y) = g x + y \<and> g x \<sharp> y\<close>
      and \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
    shows \<open>has f v \<star> (has f v' \<Zsurj> \<psi> ()) \<longlongrightarrow> \<W>\<P> \<Gamma> (put g) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>has f v \<star> (\<Sqinter>u. has f v' \<Zsurj> \<psi> u) \<longlongrightarrow> \<W>\<P> \<Gamma> (put g) \<psi> \<rho> \<theta>\<close>
    by (auto intro!: sstriple_straightline_to_wp sstriple_putI)
  moreover from assms have \<open>has f v \<star> (has f v' \<Zsurj> \<psi> ()) \<longlongrightarrow> has f v \<star> (\<Sqinter>u. has f v' \<Zsurj> \<psi> u)\<close>
    by (auto simp add: aentails_def elim!: asepconjE awandE intro!: asepconjI awandI)
  ultimately show ?thesis
    using aentails_trans by force
qed

lemma wp_getI [micro_rust_wp_intros]:
  assumes \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
      and  \<open>\<phi> \<longlongrightarrow> has f v \<star> (has f v \<Zsurj> \<psi> v)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (get f) \<psi> \<rho> \<theta>\<close>
using assms by (force intro: aentails_trans' wp_get)

lemma wp_putI:
  assumes \<open>\<And>x. x \<Turnstile> has f v \<Longrightarrow> g x \<Turnstile> has f v'\<close>
      and \<open>\<And>x y. x\<sharp>y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> g (x+y) = g x + y \<and> g x \<sharp> y\<close>
      and \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
      and \<open>\<phi> \<longlongrightarrow> has f v \<star> (has f v' \<Zsurj> \<psi> ())\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (put g) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_put, auto)

lemma wp_fun [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (f\<langle>\<rangle>) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (call f) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f1(a0) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f1 a0\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f2(a0, a1) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f2 a0 a1\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f3(a0, a1, a2) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f3 a0 a1 a2\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f4(a0, a1, a2, a3) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f4 a0 a1 a2 a3\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f5(a0, a1, a2, a3, a4) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f5 a0 a1 a2 a3 a4\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f6(a0, a1, a2, a3, a4, a5) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f6 a0 a1 a2 a3 a4 a5\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f7(a0, a1, a2, a3, a4, a5, a6) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f7 a0 a1 a2 a3 a4 a5 a6\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f8(a0, a1, a2, a3, a4, a5, a6, a7) \<rbrakk> \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f8 a0 a1 a2 a3 a4 a5 a6 a7\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f9(a0, a1, a2, a3, a4, a5, a6, a7, a8) \<rbrakk> \<phi> \<rho> \<theta> =
           \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f9 a0 a1 a2 a3 a4 a5 a6 a7 a8\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> \<lbrakk> f10(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) \<rbrakk> \<phi> \<rho> \<theta> =
           \<W>\<P> \<Gamma> \<lbrakk> \<epsilon>\<open>f10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9\<close> () \<rbrakk> \<phi> \<rho> \<theta>\<close>
by (simp only:micro_rust_simps)+

text\<open>This rule is useful for unfolding the definition of a called function and reasoning about it
directly.\<close>
lemma wp_call_function_body:
  shows \<open>\<W>\<P> \<Gamma> f \<psi> \<psi> \<theta> \<longlongrightarrow> \<W>\<P> \<Gamma> (call (FunctionBody f)) \<psi> \<rho> \<theta>\<close>
  by (clarsimp intro!: aentails_yonedaI sstriple_callI simp add: sstriple_wp_iff
    wp_is_precondition)

\<comment> \<open>NB We don't mark this as an introduction rule because for some functions
we want to invoke a function contract rather than unfolding their definition.\<close>
corollary wp_call_function_bodyI:
    notes aentails_intro [intro]
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (function_body f) \<psi> \<psi> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms wp_call_function_body by (cases f; clarsimp) blast

\<comment>\<open>The following formulation is useful in the presence of a list of definitions for functions
to be inlined, one of which will discharge the first generated assumption.\<close>
corollary wp_call_inlineI:
  assumes \<open>f \<equiv> FunctionBody b\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> b \<psi> \<psi> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp intro!: wp_call_function_bodyI)

corollary wp_call_inline'I:
  assumes \<open>f \<equiv> g\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call g) \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by clarsimp

corollary wp_call_function_bodyI2 [micro_rust_wp_intros]:
    notes aentails_intro [intro]
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> f \<psi> \<psi> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call (FunctionBody f)) \<psi> \<rho> \<theta>\<close>
using assms wp_call_function_body by (cases f; clarsimp) blast

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_satisfies_function_contract_direct:
    notes asat_simp [simp]
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
      and pre: \<open>\<phi> \<longlongrightarrow> function_contract_pre \<C>\<close>
      and post: \<open>\<And>r. function_contract_post \<C> r \<longlongrightarrow> \<psi> r\<close>
      and abort: \<open>\<And>r. function_contract_abort \<C> r \<longlongrightarrow> \<theta> r\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; function_contract_pre \<C> \<turnstile> call f \<stileturn> function_contract_post \<C> \<bowtie> \<rho> \<bowtie> function_contract_abort \<C>\<close>
    by (auto elim!: satisfies_function_contractE)
  note X = this
  have \<open>\<Gamma>; \<phi> \<turnstile> call f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using sstriple_consequence[OF X pre post aentails_refl abort] by simp
  from this show ?thesis
    by (simp add: wp_sstriple_iff)
qed

lemma wp_satisfies_function_contract:
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>function_contract_pre \<C> \<star> ((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> \<psi> r)
                                   \<sqinter>(\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> \<theta> r))
           \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by (elim satisfies_function_contractE,
   intro sstriple_straightline_to_wp_with_abort, auto)

lemma wp_call_with_abortI:
  assumes A: \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
      and B: \<open>\<phi> \<longlongrightarrow> function_contract_pre \<C> \<star>
           ((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> \<psi> r)
           \<sqinter>(\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> \<theta> r))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  by (intro aentails_trans[OF _ wp_satisfies_function_contract[OF A]], simp add: B)

lemma wp_callI:
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>function_contract_abort \<C> = \<bottom>\<close>
      and \<open>\<phi> \<longlongrightarrow> function_contract_pre \<C> \<star> (\<Sqinter>r. function_contract_post \<C> r \<Zsurj> \<psi> r)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by - (intro wp_call_with_abortI, assumption, simp add: awand_bot)

lemma wp_funliteral:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f1\<rrangle>\<^sub>1 (v0) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f1 v0)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f2\<rrangle>\<^sub>2 (v0, v1) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f2 v0 v1)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f3\<rrangle>\<^sub>3 (v0, v1, v2) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f3 v0 v1 v2)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f4\<rrangle>\<^sub>4 (v0, v1, v2, v3) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f4 v0 v1 v2 v3)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f5\<rrangle>\<^sub>5 (v0, v1, v2, v3, v4) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f5 v0 v1 v2 v3 v4)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f6\<rrangle>\<^sub>6 (v0, v1, v2, v3, v4, v5) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f6 v0 v1 v2 v3 v4 v5)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f7\<rrangle>\<^sub>7 (v0, v1, v2, v3, v4, v5, v6) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f7 v0 v1 v2 v3 v4 v5 v6)\<close>
      and \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>f8\<rrangle>\<^sub>8 (v0, v1, v2, v3, v4, v5, v6, v7) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (f8 v0 v1 v2 v3 v4 v5 v6 v7)\<close>
  using assms by (clarsimp intro!: aentails_yonedaI simp add: sstriple_wp_iff
    sstriple_call_funliteral asepconj_simp)+

lemma wp_range_new [micro_rust_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<phi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (\<langle>\<up>b\<dots>\<up>e\<rangle>) \<phi> \<rho> \<theta> = \<phi> (make_range b e)\<close>
using assms by (clarsimp simp add: range_new_def wp_funliteral)

lemma wp_op_eq [micro_rust_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> \<lbrakk> \<llangle>\<lambda>a b. a=b\<rrangle>\<^sub>2(e,f) \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (e = f)\<close>
using assms by (clarsimp simp add: wp_funliteral)

lemma wp_op_eqs [micro_rust_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> \<lbrakk> e == f \<rbrakk> \<psi> \<rho> \<theta> = \<psi> (e = f)\<close>
using assms by (clarsimp simp add: urust_eq_def micro_rust_wp_simps micro_rust_simps)

lemma wp_word_add_no_wrap [micro_rust_wp_intros]:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x+y))\<close>
    shows \<open>\<langle>unat x + unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x + y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x + y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>(unat x) + (unat y) < 2^(LENGTH('l))\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x + y\<rangle> \<star> \<psi> (x+y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return; simp add: sstriple_word_add_no_wrapI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_add_no_wrapI [micro_rust_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x + y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat x + unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x + y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x + y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_add_no_wrap, auto)

lemma wp_word_mul_no_wrap [micro_rust_wp_intros]:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x*y))\<close>
    shows \<open>\<langle>unat x * unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x * y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x * y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>(unat x) * (unat y) < 2^(LENGTH('l))\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x * y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x * y\<rangle> \<star> \<psi> (x*y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_mul_no_wrapI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x * y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]; auto)
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_mul_no_wrapI [micro_rust_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x * y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat x * unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x * y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x * y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_mul_no_wrap, auto)

lemma wp_word_sub_no_wrap:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x - y))\<close>
    shows \<open>\<langle>y \<le> x\<rangle> \<star> \<psi> (x - y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x - y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>y \<le> x\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x - y\<rangle> \<star> \<psi> (x - y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_sub_no_wrapI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_sub_no_wrapI [micro_rust_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x - y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>y \<le> x\<rangle> \<star> \<psi> (x - y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x - y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_sub_no_wrap, auto)

lemma wp_word_udiv:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x div y))\<close>
  shows \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x div y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x / y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>y \<noteq> 0\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x div y\<rangle> \<star> \<psi> (x div y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_udivI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_udivI [micro_rust_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x div y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x div y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x / y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_udiv, auto)

lemma wp_word_umod:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x mod y))\<close>
    shows \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x mod y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x % y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>y \<noteq> 0\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x % y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x mod y\<rangle> \<star> \<psi> (x mod y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_umodI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x % y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_umodI [micro_rust_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x mod y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x mod y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x % y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_umod, auto)

lemma wp_bitwise_or:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (x OR y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x | y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_orI)

lemma wp_bitwise_and:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (x AND y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x & y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_andI)

lemma wp_bitwise_xor:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (x XOR y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x ^ y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_xorI)

lemma wp_bitwise_not:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (NOT x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> !x \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_notI)

lemma wp_bitwise_orI [micro_rust_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (x OR y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x | y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_or aentails_trans' by blast

lemma wp_bitwise_andI [micro_rust_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (x AND y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x & y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_and aentails_trans' by blast

lemma wp_bitwise_xorI [micro_rust_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (x XOR y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x ^ y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_xor aentails_trans' by blast

lemma wp_bitwise_notI [micro_rust_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (NOT x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> !x \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_not aentails_trans' by blast

lemma wp_word_shift_left:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp[simp]
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (push_bit (unat y) x))\<close>
    shows \<open>\<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (push_bit (unat y) x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x << y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>unat y < LENGTH('l0)\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have
         I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x << y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = push_bit (unat y) x\<rangle> \<star> \<psi> (push_bit (unat y) x)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_shift_leftI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x << y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_shift_leftI [micro_rust_wp_intros]:
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (push_bit (unat y) x))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (push_bit (unat y) x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x << y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms wp_word_shift_left aentails_trans' by blast

lemma wp_word_shift_right:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (drop_bit (unat y) x))\<close>
    shows \<open>\<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (drop_bit (unat y) x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x >> y \<rbrakk> \<psi> \<rho> \<theta>\<close> (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>unat y < LENGTH('l0)\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have
         I: \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x >> y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = drop_bit (unat y) x\<rangle> \<star> \<psi> (drop_bit (unat y) x)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_shift_rightI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile> \<lbrakk> x >> y \<rbrakk> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_shift_rightI [micro_rust_wp_intros]:
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (drop_bit (unat y) x))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (drop_bit (unat y) x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x >> y \<rbrakk> \<psi> \<rho> \<theta>\<close>
using assms wp_word_shift_right aentails_trans' by blast

declare aexists_entailsL aexists_entailsR aforall_entailsL aforall_entailsR apure_entails_iff
  apure_entailsR [micro_rust_wp_intros]

subsection\<open>Loops\<close>

text\<open>Note that this is not added to \<^verbatim>\<open>micro_rust_wp_intros\<close>. The invariant pretty much always needs
to be provided, so there is not much point.\<close>
lemma wp_raw_for_loopI:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
  assumes \<open>\<And>past todo. ucincl (INV past todo)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV [] xs\<close>
      and \<open>\<And>past cur todo. xs = past@(cur#todo) \<Longrightarrow> INV past (cur#todo) \<longlongrightarrow> \<W>\<P> \<Gamma> (f cur) (\<lambda>_. INV (past@[cur]) todo) \<rho> \<theta>\<close>
      and \<open>INV xs [] \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have H: \<open>\<Gamma> ; \<langle>xs = []@xs\<rangle> \<star> INV [] xs \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. \<langle>xs = xs@[]\<rangle> \<star> INV xs []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_raw_for_loop) (force intro: ucincl_intros wp_to_sstriple)
  from assms have \<open>INV [] xs \<longlongrightarrow>  \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<theta>\<close>
    by (intro wp_is_weakest_precondition; clarsimp intro: ucincl_intros)
      (rule sstriple_consequence[OF H]; clarsimp simp add: aentails_refl)
  from this and assms show ?thesis
    by blast
qed

text\<open>The following is a framed version of \<^text>\<open>wp_raw_for_loopI\<close> recovering the latter if
\<^term>\<open>\<xi> = UNIV\<close>.\<close>
lemma wp_raw_for_loop_framedI:
  assumes \<open>\<And>past todo. ucincl (INV past todo)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>ucincl (\<psi> ())\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV [] xs \<star> ((INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>past cur todo. INV past (cur#todo) \<longlongrightarrow> \<W>\<P> \<Gamma> (f cur) (\<lambda>_. INV (past@[cur]) todo) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV [] xs \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_raw_for_loop_framed) (auto simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV [] xs \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
    using local.ucincl_asepconj wp_is_weakest_precondition by (metis (mono_tags, lifting)
      ucincl_Int local.ucincl_IntE local.ucincl_awand local.ucincl_inter)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

text\<open>Alternative loop rule which might be easier to use in some situations. Passing the list to the
invariant may seem redundant because it's part of the context, but we don't always know what the
list will be named in the current proof state.\<close>
lemma wp_raw_for_loop_framedI':
    fixes xs :: \<open>'e list\<close>
      and INV :: \<open>'e list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>ls i. ucincl (INV ls i)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>ucincl (\<psi> ())\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV xs 0 \<star> ((INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>i. i < length xs \<Longrightarrow> INV xs i \<longlongrightarrow> \<W>\<P> \<Gamma> (f (xs ! i)) (\<lambda>_. INV xs (i+1)) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV xs 0 \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_raw_for_loop_framed') (auto simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV xs 0 \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
    by (intro wp_is_weakest_precondition) (auto intro!: ucincl_Int ucincl_awand ucincl_inter
      ucincl_asepconj)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

lemma wp_gather_framedI:
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and \<xi> :: \<open>nat \<Rightarrow> 'v \<Rightarrow> bool\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<And>ls i. ucincl (INV i ls)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow>
              \<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn> (\<lambda>v. INV (i+1) (res @ [v])) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (gather thunks) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_gather_framed; simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV 0 [] \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (gather thunks) \<psi> \<rho> \<chi>\<close>
    by (intro wp_is_weakest_precondition) (auto intro!: ucincl_asepconj ucincl_inter ucincl_Int
      ucincl_awand)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

lemma wp_gather_framedI':
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and \<xi> :: \<open>nat \<Rightarrow> 'v \<Rightarrow> bool\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<And>ls i. ucincl (INV i ls)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow>
              INV i res \<longlongrightarrow> \<W>\<P> \<Gamma> (thunks ! i) (\<lambda>v. INV (i+1) (res @ [v])) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (gather thunks) \<psi> \<rho> \<chi>\<close>
  using assms by (blast intro: wp_gather_framedI wp_to_sstriple)

(*<*)
end
(*>*)

(*<*)
end
(*>*)