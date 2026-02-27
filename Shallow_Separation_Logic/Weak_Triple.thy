(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Weak_Triple
  imports
    Assertion_Language
    Assertion_Triple
    Precision
    Locality
    Shallow_Micro_Rust.Shallow_Micro_Rust
begin

text\<open>This type captures logical context that is necessary to specify the full program logic, but
that changes rarely or never during verification.  This will encode things like rely/guarantee
relations and contextual assumptions.\<close>
datatype_record ('st, 'abort, 'i, 'o) striple_context_raw =
  yield_handler_raw :: \<open>('st, 'abort, 'i, 'o) yield_handler_nondet_basic\<close>

text\<open>The following class of yield handlers is sufficient for functions which can never
throw \<^verbatim>\<open>FatalError\<close>s. If \<^verbatim>\<open>FatalError\<close> can occur, specifications are likely only true
for \<^term>\<open>standard_yield_handler\<close>.\<close>
definition is_valid_striple_context :: \<open>('st, 'abort, 'i prompt, 'o prompt_output) striple_context_raw \<Rightarrow> bool\<close> where
  \<open>is_valid_striple_context \<Gamma> \<equiv>
      is_log_transparent_yield_handler (yield_handler_raw \<Gamma>) \<and>
      is_nondet_order_yield_handler (yield_handler_raw \<Gamma>)\<close>

text\<open>Until the context is properly integrated, offer a dummy context\<close>
definition striple_context_raw_no_yield :: \<open>('st, 'abort, 'i prompt, 'o prompt_output) striple_context_raw\<close> where
  \<open>striple_context_raw_no_yield \<equiv> make_striple_context_raw yield_handler_no_yield\<close>

lemma striple_context_raw_no_yield_is_valid:
  shows \<open>is_valid_striple_context striple_context_raw_no_yield\<close>
by (auto simp add: is_valid_striple_context_def striple_context_raw_no_yield_def
  intro: yield_handler_no_yield_is_log_transparent yield_handler_no_yield_is_nondet_order)

typedef (overloaded) ('st, 'abort, 'i, 'o) striple_context =
  \<open>{ ctxt :: ('st, 'abort, 'i prompt, 'o prompt_output) striple_context_raw . is_valid_striple_context ctxt }\<close>
using striple_context_raw_no_yield_is_valid by blast

setup_lifting type_definition_striple_context

lift_definition striple_context_no_yield :: \<open>('st, 'abort, 'i, 'o) striple_context\<close>
  is \<open>striple_context_raw_no_yield\<close>
  using striple_context_raw_no_yield_is_valid by simp

lift_definition yield_handler :: \<open>('st, 'abort, 'i, 'o) striple_context \<Rightarrow> ('st, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic\<close>
  is \<open>yield_handler_raw\<close> .
abbreviation \<open>yh \<equiv> yield_handler\<close>

lemma striple_context_yh_is_log_transparaent[simp]:
  shows \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
  by  (transfer, simp add: is_valid_striple_context_def)

lemma striple_context_yh_is_nondet_order[simp]:
  shows \<open>is_nondet_order_yield_handler (yh \<Gamma>)\<close>
  by (transfer, simp add: is_valid_striple_context_def)

definition is_aborting_striple_context where
  \<open>is_aborting_striple_context \<Gamma> \<equiv> is_aborting_yield_handler (yh \<Gamma>)\<close>

lemma striple_context_no_yield_yh[simp]:
  shows \<open>yh striple_context_no_yield = yield_handler_no_yield\<close>
  by (transfer, simp add: striple_context_raw_no_yield_def)

lift_definition striple_context_refines :: \<open>('st, 'abort, 'i, 'o) striple_context \<Rightarrow> ('st, 'abort, 'i, 'o) striple_context \<Rightarrow> bool\<close> ("_ \<lesssim> _"[100,100]100)
  is \<open>\<lambda>\<Theta> \<Gamma>. yield_handler_nondet_basic_refines (yield_handler_raw \<Theta>) (yield_handler_raw \<Gamma>)\<close> .

lemma striple_context_refines_alt[simp]:
  shows \<open>\<Gamma> \<lesssim> \<Theta> \<longleftrightarrow> yield_handler_nondet_basic_refines (yh \<Gamma>) (yh \<Theta>)\<close>
  by (transfer, simp)

lemma striple_context_refines_top[simp]:
  shows \<open>\<Gamma> \<lesssim> striple_context_no_yield\<close>
  by (transfer, simp add: is_valid_striple_context_def striple_context_raw_no_yield_def
    yield_handler_nondet_basic_refines_top)

(*<*)
context sepalg begin
(*>*)

subsection\<open>S-triples\<close>

text\<open>The following definition is central to our development: It describes the effect of evaluating
an expression on a state as replacing a sub-state satisfying a given precondition by a sub-state
satisfying one of two post-conditions, depending on how the evaluation terminates.\<close>

definition striple ::
     \<open>('a, 'abort, 'i, 'o) striple_context \<Rightarrow> \<comment> \<open>Fixed context for this verification\<close>
      'a assert \<Rightarrow> \<comment> \<open>The property of the pre-state\<close>
      ('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow> \<comment> \<open>Expanded out our expression type\<close>
      ('v \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The property of the post-state after successful execution\<close>
      ('r \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The property of the post-state after successful early return\<close>
      ('abort abort \<Rightarrow> 'a assert) \<Rightarrow>
      bool\<close> ("(_) ; (_) /\<turnstile>/ (_) /\<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k/ (_) /\<bowtie>/ (_)/ \<bowtie>/ (_)" [50,50,50,50,50,50]50) where
  \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho> \<equiv> (\<forall>\<sigma>.
      (\<forall>(a,\<sigma>') \<in> (yh \<Gamma>,e) \<diamondop>\<^sub>a \<sigma>. \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<rho> a) \<and> \<comment>\<open>Post-condition for aborting evaluations\<close>
      (\<forall>(v,\<sigma>') \<in> (yh \<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v) \<and> \<comment>\<open>Post-condition for value-evaluations\<close>
      (\<forall>(r,\<sigma>') \<in> (yh \<Gamma>,e) \<diamondop>\<^sub>r \<sigma>. \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> r))\<close> \<comment>\<open>Post-condition for return-evaluations\<close>

text\<open>The striple is invariant under passage to upward closure:\<close>
lemma striple_upwards_closure:
  shows \<open>(\<Gamma> ; \<phi> \<star> \<top> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. \<psi> v \<star> \<top>) \<bowtie> (\<lambda>v. \<xi> v \<star> \<top>) \<bowtie> (\<lambda>a. \<rho> a \<star> \<top>)) \<longleftrightarrow>
         (\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho>)\<close>
by (auto simp add: atriple_upwards_closure striple_def local.asepconj_UNIV_idempotent
  local.asepconj_assoc)

lemma stripleI:
  assumes \<open>\<And>v s s'. s \<leadsto>\<^sub>v\<langle>yh \<Gamma>,e\<rangle> (v, s') \<Longrightarrow> \<phi> \<tturnstile> (s, s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v\<close>
      and \<open>\<And>r s s'. s \<leadsto>\<^sub>r\<langle>yh \<Gamma>,e\<rangle> (r, s') \<Longrightarrow> \<phi> \<tturnstile> (s, s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> r\<close>
      and \<open>\<And>a s s'. s \<leadsto>\<^sub>a\<langle>yh \<Gamma>,e\<rangle> (a, s') \<Longrightarrow> \<phi> \<tturnstile> (s, s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<rho> a\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho>\<close>
using assms by (clarsimp simp add: striple_def return_evaluations_def value_evaluations_def
  abort_evaluations_def)

lemma striple_hoist_pure:
  shows \<open>(\<Gamma> ; \<phi> \<star> \<langle>P\<rangle> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho>) \<longleftrightarrow> (P \<longrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho>))\<close>
by (auto simp add: striple_def atriple_hoist_pure asepconj_simp asepconj_False_True
  asepconj_pure_UNIV asat_simp asat_apure_distrib')

lemma striple_localI:
  assumes \<open>is_local (\<lambda>\<sigma> (v,\<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,e\<rangle> (v,\<sigma>')) \<phi>\<close>
      and \<open>is_local (\<lambda>\<sigma> (r,\<sigma>'). \<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,e\<rangle> (r,\<sigma>')) \<phi>\<close>
      and \<open>is_local (\<lambda>\<sigma> (a,\<sigma>'). \<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,e\<rangle> (a,\<sigma>')) \<phi>\<close>
      and \<open>\<And>\<sigma> \<sigma>' v. \<sigma> \<leadsto>\<^sub>v\<langle>yh \<Gamma>,e\<rangle> (v, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<psi> v\<close>
      and \<open>\<And>\<sigma> \<sigma>' r. \<sigma> \<leadsto>\<^sub>r\<langle>yh \<Gamma>,e\<rangle> (r, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<xi> r\<close>
      and \<open>\<And>\<sigma> \<sigma>' a. \<sigma> \<leadsto>\<^sub>a\<langle>yh \<Gamma>,e\<rangle> (a, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<rho> a\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho>\<close>
using assms
  by (intro stripleI; metis (mono_tags, lifting) atriple_local prod.case)

lemma striple_localI':
  assumes \<open>is_local (\<lambda>\<sigma> (v,\<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,e\<rangle> (v,\<sigma>')) \<phi>\<close>
      and \<open>is_local (\<lambda>\<sigma> (r,\<sigma>'). \<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,e\<rangle> (r,\<sigma>')) \<phi>\<close>
      and \<open>is_local (\<lambda>\<sigma> (a,\<sigma>'). \<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,e\<rangle> (a,\<sigma>')) \<phi>\<close>
      and \<open>\<And>\<sigma> \<sigma>' v. \<sigma> \<leadsto>\<^sub>v\<langle>yh \<Gamma>,e\<rangle> (v, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<psi> v \<star> \<top>\<close>
      and \<open>\<And>\<sigma> \<sigma>' r. \<sigma> \<leadsto>\<^sub>r\<langle>yh \<Gamma>,e\<rangle> (r, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<xi> r \<star> \<top>\<close>
      and \<open>\<And>\<sigma> \<sigma>' a. \<sigma> \<leadsto>\<^sub>a\<langle>yh \<Gamma>,e\<rangle> (a, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<rho> a \<star> \<top>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<rho>\<close>
using assms
  by (intro stripleI; metis (mono_tags, lifting) atriple_local' prod.case)

text\<open>Weak triples are preserved under refinement of yield handlers:\<close>

lemma striple_yield_handler_refine:
  assumes \<open>\<Theta> \<lesssim> \<Gamma>\<close>
      and \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    shows \<open>\<Theta> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
proof -
  have \<open>deep_evaluates_nondet_basic (yh \<Theta>) e \<sigma> \<subseteq> deep_evaluates_nondet_basic (yh \<Gamma>) e \<sigma>\<close>
    if \<open>\<sigma> \<Turnstile> \<phi> \<star> \<pi>\<close> for \<sigma> \<pi>
  proof -
    have \<open>\<sigma> \<Turnstile> \<phi> \<star> \<top>\<close>
      using that by (meson aentails_def aentails_true asepconj_mono3)
    with \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    have \<open>\<forall>a \<sigma>'. Abort a \<sigma>' \<notin> deep_evaluates_nondet_basic (yh \<Gamma>) e \<sigma>\<close>
      using asepconj_bot_zero 
      by (fastforce simp: striple_def evaluates_to_return_def atriple_def
          evaluates_to_value_def evaluates_to_abort_def urust_eval_action_via_predicate)
    with \<open>\<Theta> \<lesssim> \<Gamma>\<close> show ?thesis
      by (metis deep_evaluate_basic_nondet_refine striple_context_refines_alt subsetI)
  qed
  with \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close> show ?thesis
    by (auto simp add: striple_def atriple_def evaluates_to_return_def
        evaluates_to_value_def evaluates_to_abort_def urust_eval_action_via_predicate) blast+
qed

corollary striple_yield_handler_no_yield_implies_all:
  assumes \<open>striple_context_no_yield ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  using assms striple_context_refines_top striple_yield_handler_refine by blast

end

section\<open>Example\<close>

text\<open>At this point, we pause and study the locality properties implied by the above definition
of the separating triple.

Intuitively, there are two properties one would expect to hold for the 'footprint' of an operation:
The footprint's 'complement' should (a) not be affected, and (b) not affect, the operation.

It is important to note that the above definition of the separating triple only guarantees (a),
but not (b). The following is a simple example: We work in the context of the separation algebra
with two naturals, \<^verbatim>\<open>high\<close> and \<^verbatim>\<open>low\<close>, and consider the 'program' which leaks \<^verbatim>\<open>high\<close> into \<^verbatim>\<open>low\<close>
\<^emph>\<open>if \<^verbatim>\<open>high\<close> is present\<close>; if \<^verbatim>\<open>high\<close> is not present, it does nothing.\<close>

datatype high_low_sa_component = High | Low
datatype high_low_sa = HighLowSA \<open>high_low_sa_component \<rightharpoonup> nat\<close>

definition high_low_components :: \<open>high_low_sa \<Rightarrow> high_low_sa_component \<rightharpoonup> nat\<close> where
  \<open>high_low_components x \<equiv> case x of HighLowSA y \<Rightarrow> y\<close>

definition get_low :: \<open>high_low_sa \<Rightarrow> nat option\<close> where
  \<open>get_low x \<equiv> high_low_components x Low\<close>

definition get_high :: \<open>high_low_sa \<Rightarrow> nat option\<close> where
  \<open>get_high x \<equiv> high_low_components x High\<close>

definition has_low :: \<open>high_low_sa assert\<close> where
  \<open>has_low \<equiv> {\<sigma>. \<exists>v. get_low \<sigma> = Some v}\<close>

definition has_high :: \<open>high_low_sa assert\<close> where
  \<open>has_high \<equiv> {\<sigma>. \<exists>v. get_high \<sigma> = Some v}\<close>

definition put_low :: \<open>nat \<Rightarrow> high_low_sa \<Rightarrow> high_low_sa\<close> where
  \<open>put_low v \<sigma> \<equiv> HighLowSA ((high_low_components \<sigma>)(Low \<mapsto> v))\<close>

definition put_high :: \<open>nat \<Rightarrow> high_low_sa \<Rightarrow> high_low_sa\<close> where
  \<open>put_high v \<sigma> \<equiv> HighLowSA ((high_low_components \<sigma>)(High \<mapsto> v))\<close>

instantiation high_low_sa :: sepalg
begin

definition plus_high_low_sa :: \<open>high_low_sa \<Rightarrow> high_low_sa \<Rightarrow> high_low_sa\<close> where
  \<open>plus_high_low_sa x y \<equiv> HighLowSA ((high_low_components x) + (high_low_components y))\<close>

definition disjoint_high_low_sa :: \<open>high_low_sa \<Rightarrow> high_low_sa \<Rightarrow> bool\<close> where
  \<open>disjoint_high_low_sa x y \<equiv> (high_low_components x) \<sharp> (high_low_components y)\<close>

definition zero_high_low_sa :: \<open>high_low_sa\<close> where
  \<open>zero_high_low_sa \<equiv> HighLowSA 0\<close>

instance
proof
  fix x :: \<open>high_low_sa\<close>
  show \<open>x \<sharp> 0\<close>
    by (simp add: disjoint_high_low_sa_def high_low_components_def zero_high_low_sa_def)
next
  fix x y :: \<open>high_low_sa\<close>
  show \<open>x \<sharp> y = y \<sharp> x\<close>
    by (simp add: disjoint_high_low_sa_def)
next
  fix x :: \<open>high_low_sa\<close>
  assume \<open>x \<sharp> x\<close>
  from this show \<open>x = 0\<close>
    by (metis (mono_tags) disjoint_high_low_sa_def high_low_components_def high_low_sa.case
      high_low_sa.exhaust unique zero_high_low_sa_def)
next
  fix x :: \<open>high_low_sa\<close>
  show \<open>x + 0 = x\<close>
    by (clarsimp simp add: zero_high_low_sa_def plus_high_low_sa_def high_low_components_def split:
      high_low_sa.splits)
next
  fix x y :: \<open>high_low_sa\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (simp add: disjoint_high_low_sa_def plus_high_low_sa_def)
next
  fix x y z :: \<open>high_low_sa\<close>
  assume \<open>x \<sharp> y\<close>
     and \<open>y \<sharp> z\<close>
     and \<open>x \<sharp> z\<close>
  from this show \<open>x + (y + z) = x + y + z\<close>
    by (clarsimp simp add: zero_high_low_sa_def plus_high_low_sa_def high_low_components_def split:
      high_low_sa.splits) (metis disjoint_high_low_sa_def high_low_components_def high_low_sa.case
      sepalg_assoc)
next
  fix x y z :: \<open>high_low_sa\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x \<sharp> y\<close>
    by (simp add: disjoint_high_low_sa_def high_low_components_def plus_high_low_sa_def)
next
  fix x y z :: \<open>high_low_sa\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x + y \<sharp> z\<close>
    by (metis (mono_tags, lifting) disjoint_high_low_sa_def high_low_components_def high_low_sa.case
      plus_high_low_sa_def sepalg_apart_assoc2)
qed

end

text\<open>The following "program" changes the low value based on the presence of the high value,
but leaves the low-value unchanged. Despite clearly not being low-local, it does satisfy the
above triple definition:\<close>
definition leak_high :: \<open>(high_low_sa, unit, unit, 'abort, 'i, 'o) expression\<close> where
  \<open>leak_high \<equiv> \<lbrakk>
     if let Some(high) = \<epsilon>\<open>get get_high\<close> {
        \<epsilon>\<open>put (put_low high)\<close>
     }
  \<rbrakk>\<close>

text\<open>The program \<^term>\<open>leak_high\<close> is 'pathological' in that it inspects the partiality of the
state to make runtime decisions -- no real program would be able to do that. Yet, it does fit
our formal framework. Moreover, strongly counter-intuitively, \<^verbatim>\<open>high\<close> is outside of its
'footprint' in the sense of \<^term>\<open>striple\<close>:\<close>

lemma put_low_is_local:
  shows \<open>is_local (\<lambda>\<sigma> (v', \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>,put (put_low v)\<rangle> (v',\<sigma>')) has_low\<close>
proof -
  have \<open>\<sigma>_1 \<sharp> HighLowSA \<sigma> \<Longrightarrow> \<sigma> Low = Some v' \<Longrightarrow> \<sigma>_1 \<sharp> HighLowSA (\<sigma>(Low \<mapsto> v))\<close> for \<sigma> \<sigma>_1 v'
    by (force simp: disjoint_high_low_sa_def high_low_components_def disjoint_map_iff split!: high_low_sa.splits)
  then show ?thesis
    by (auto simp add: is_local_def urust_eval_predicate_simps asat_def has_low_def get_low_def 
        disjoint_high_low_sa_def domI  plus_high_low_sa_def put_low_def high_low_components_def split!: high_low_sa.splits)
qed

lemma put_low_triple:
  shows \<open>\<Gamma>; has_low \<turnstile> put (put_low v) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. has_low) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
  apply (intro striple_localI put_low_is_local)
  apply (auto simp add: urust_eval_predicate_simps is_local_def asat_def get_low_def has_low_def
    high_low_components_def put_low_def)
  done

lemma put_low_atriple:
  shows \<open>has_low \<tturnstile> (\<sigma>,put_low v \<sigma>) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k has_low\<close>
proof (rule atriple_local [OF put_low_is_local])
  show \<open>case (undefined, put_low v \<sigma>) of (v', \<sigma>') \<Rightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>undefined,put (put_low v)\<rangle> (v',\<sigma>')\<close>
    by (simp add: urust_eval_predicate_put(1))
qed (auto simp add: urust_eval_predicate_simps is_local_def asat_def get_low_def has_low_def
    high_low_components_def put_low_def)

lemma leak_high_triple:
  shows \<open>\<Gamma> ; has_low \<turnstile> leak_high \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. has_low) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
by (intro stripleI; clarsimp simp add: leak_high_def urust_eval_predicate_simps atriple_refl
  put_low_atriple split!: option.splits)

text\<open>This shows that for \<^term>\<open>striple\<close>, it is indeed not generally true that state outside of
the footprint has no influence on the program's execution. For that, one would need to explicitly
assume locality of the program, leading to a stroner notion of separating triple which we study
below.

We end the example by noting that \<^term>\<open>leak_high\<close> is indeed not local:\<close>

lemma leak_high_is_not_local:
  shows \<open>\<not> (is_local (\<lambda>\<sigma> (v', \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>,leak_high\<rangle> (v',\<sigma>')) has_low)\<close>
proof -
  let ?\<sigma>0 = \<open>HighLowSA (0(Low \<mapsto> 0))\<close>
  let ?\<sigma>1 = \<open>HighLowSA ((high_low_components ?\<sigma>0)(High \<mapsto> 1))\<close>
  let ?\<sigma>0' = \<open>HighLowSA (0(Low \<mapsto> 0))\<close>
  let ?\<sigma>1' = \<open>HighLowSA ((high_low_components ?\<sigma>1)(Low \<mapsto> 1))\<close>
  let ?\<tau> = \<open>HighLowSA (0(High \<mapsto> 1))\<close>
  show ?thesis
  proof -
    have 1: \<open>(\<Gamma>, leak_high) \<diamondop>\<^sub>v ?\<sigma>0 = {((), ?\<sigma>0')}\<close> and \<open>(\<Gamma>, leak_high) \<diamondop>\<^sub>v ?\<sigma>1 = {((), ?\<sigma>1')}\<close>
      by (auto simp add: urust_eval_action_simps leak_high_def get_high_def high_low_components_def
          put_low_def zero_fun_def zero_option_def split: option.splits)
    then have 2: \<open>?\<sigma>0 \<leadsto>\<^sub>v \<langle>\<Gamma>, leak_high\<rangle> ((), ?\<sigma>0')\<close> \<open>?\<sigma>1 \<leadsto>\<^sub>v \<langle>\<Gamma>, leak_high\<rangle> ((), ?\<sigma>1')\<close>
      by (simp add: evaluates_to_value_eq)+
    have 3: \<open>?\<sigma>0 \<sharp> ?\<tau>\<close> \<open>?\<sigma>1 = ?\<sigma>0 + ?\<tau>\<close>
      by (fastforce simp: disjoint_fun_def disjoint_option_def disjoint_high_low_sa_def
          high_low_components_def zero_fun_def zero_option_def plus_option_def plus_fun_def
          plus_high_low_sa_def)+
    then have \<open>HighLowSA (0(Low \<mapsto> 0)) \<sharp> HighLowSA (0(High \<mapsto> Suc 0))\<close>
      by simp
    moreover have \<open>HighLowSA (0(Low \<mapsto> 0)) \<Turnstile> has_low\<close>
      by (simp add: asat_def get_low_def has_low_def high_low_components_def)
    ultimately show ?thesis
      using 1 2 3
      apply (clarsimp simp add: is_local_def)
      apply (rule exI [where x=\<open>?\<sigma>0\<close>])
      apply (rule exI [where x=\<open>?\<tau>\<close>])
      apply (auto simp: is_local_def evaluates_to_value_eq high_low_components_def)
      by (metis One_nat_def fun_upd_eqD fun_upd_twist high_low_sa.inject high_low_sa_component.simps(2) option.inject zero_neq_one)
  qed
qed

context sepalg
begin

lemma stripleE_value:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>s \<leadsto>\<^sub>v\<langle>yh \<Gamma>,e\<rangle> (v,s')\<close>
      and \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (simp add: striple_def value_evaluations_def)

lemma stripleE_return:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>s \<leadsto>\<^sub>r\<langle>yh \<Gamma>,e\<rangle> (r, s')\<close>
      and \<open>\<phi> \<tturnstile> (s, s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> r \<Longrightarrow> R\<close>
    shows \<open>R\<close>
  using assms by (simp add: striple_def return_evaluations_def)

lemma stripleE_abort:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>s \<leadsto>\<^sub>a\<langle>yh \<Gamma>,e\<rangle> (a, s')\<close>
      and \<open>\<phi> \<tturnstile> (s, s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (simp add: striple_def abort_evaluations_def)

lemma striple_satisfiable:
  assumes \<open>striple_context_no_yield ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>is_sat \<phi>\<close>
      and \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<And>r. ucincl (\<xi> r)\<close>
      and \<open>\<And>a. ucincl (\<theta> a)\<close>
    shows \<open>(\<exists>v. is_sat (\<psi> v)) \<or> (\<exists>r. is_sat (\<xi> r)) \<or> (\<exists>a. is_sat (\<theta> a))\<close>
proof -
  from assms obtain s\<^sub>0 where \<open>s\<^sub>0 \<Turnstile> \<phi> \<star> UNIV\<close>
    unfolding is_sat_def
    by (meson asat_connectives_characterisation(1) asepconj_weakenI)
  moreover from this assms obtain k where \<open>k \<in> deep_evaluates_nondet_basic yield_handler_no_yield e s\<^sub>0\<close>
    using deep_evaluates_nondet_basic_nonempty yield_handler_no_yield_is_nonempty
    by (metis all_not_in_conv)
  moreover {
    fix v \<sigma>'
    assume \<open>k = Success v \<sigma>'\<close>
    from this and calculation and assms have \<open>\<sigma>' \<Turnstile> \<psi> v \<star> UNIV\<close>
      by (clarsimp simp add: ucincl_UNIV striple_def atriple_def is_sat_def value_evaluations_def
        evaluates_to_value_def)
  }
  moreover {
    fix r \<sigma>'
    assume \<open>k = Return r \<sigma>'\<close>
    from this and calculation and assms have \<open>\<sigma>' \<Turnstile> \<xi> r \<star> UNIV\<close>
      by (clarsimp simp add: ucincl_UNIV striple_def atriple_def is_sat_def return_evaluations_def
        evaluates_to_return_def)
  }
  moreover {
    fix a \<sigma>'
    assume \<open>k = Abort a \<sigma>'\<close>
    from this and calculation and assms have \<open>\<sigma>' \<Turnstile> \<theta> a \<star> UNIV\<close>
      by (clarsimp simp add: ucincl_UNIV striple_def atriple_def is_sat_def abort_evaluations_def
        evaluates_to_abort_def)
  }
  ultimately show ?thesis
    using assms by (auto simp add: ucincl_alt striple_def atriple_def is_sat_def dest!:
      deep_evaluate_basic_no_yield)
qed

subsection \<open>Basic properties of \<^term>\<open>striple\<close>\<close>

text\<open>When proving a triple, one can without loss of generality assume that the spatial
precondition of the triple is satisfiable.\<close>
lemma striple_assume_is_sat:
  assumes \<open>is_sat \<phi> \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (metis aentails_eq assms local.aentails_is_sat local.awand_mp local.striple_hoist_pure)

lemma striple_existsI':
  assumes \<open>(\<And>\<phi>. \<phi> \<in> \<Phi> \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
  shows \<open>\<Gamma> ; (\<Union>\<Phi>) \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (intro stripleI; meson atriple_union asepconj_simp stripleE_value stripleE_return stripleE_abort)

lemma striple_existsI:
  assumes \<open>\<And>x. \<Gamma> ; \<phi> x \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; (\<Union>x. \<phi> x) \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms by (intro striple_existsI') auto

lemma striple_bexistsI:
  assumes \<open>\<And>x. x\<in>S \<Longrightarrow> \<Gamma> ; \<phi> x \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  shows \<open>\<Gamma> ; (\<Union>x\<in>S. \<phi> x) \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms by (intro striple_existsI') auto

subsection\<open>Structural rules\<close>


text\<open>This is the rule of consequence, which allows you to strengthen the preconditions of an
expression's execution and strengthen the postcondition:\<close>
lemma striple_consequence:
  assumes \<open>\<Gamma> ; \<phi>' \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>' \<bowtie> \<rho>' \<bowtie> \<theta>'\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<And>r. \<psi>' r \<longlongrightarrow> \<psi> r\<close>
      and \<open>\<And>r. \<rho>' r \<longlongrightarrow> \<rho> r\<close>
      and \<open>\<And>r. \<theta>' r \<longlongrightarrow> \<theta> r\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof (intro stripleI)
  fix v s s'
  assume \<open>s \<leadsto>\<^sub>v \<langle>yh \<Gamma>,e\<rangle> (v,s')\<close>
  with assms show \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v\<close>
    by (meson atriple_consequence stripleE_value)
next
  fix r s s'
  assume \<open>s \<leadsto>\<^sub>r \<langle>yh \<Gamma>,e\<rangle> (r,s')\<close>
  with assms show \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<rho> r\<close>
    by (metis atriple_consequence stripleE_return)
next
  fix a s s'
  assume \<open>s \<leadsto>\<^sub>a \<langle>yh \<Gamma>,e\<rangle> (a,s')\<close>
  with assms show \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a\<close>
    by (meson atriple_consequence stripleE_abort)
qed

text\<open>NB: this is expressed in a non-standard form as it's used to derive other results below by
unifying against the premiss of another theorem.\<close>
lemma striple_consequence_wrap:
  shows \<open>\<forall>\<phi> \<psi> \<rho> \<theta> \<psi>' \<rho>' \<theta>' \<phi>' e \<Gamma>.
      striple \<Gamma> \<phi>' e \<psi>' \<rho>' \<theta>' \<longrightarrow> \<phi> \<longlongrightarrow> \<phi>' \<longrightarrow> (\<forall>r. \<psi>' r \<longlongrightarrow> \<psi> r) \<longrightarrow>
            (\<forall>r. \<rho>' r \<longlongrightarrow> \<rho> r) \<longrightarrow> (\<forall>a. \<theta>' a \<longlongrightarrow> \<theta> a) \<longrightarrow> striple \<Gamma> \<phi> e \<psi> \<rho> \<theta>\<close>
using striple_consequence by blast

theorem striple_frame_rule:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<psi> r \<star> \<xi>) \<bowtie> (\<lambda>r. \<rho> r \<star> \<xi>) \<bowtie> (\<lambda>a. \<theta> a \<star> \<xi>)\<close>
using assms by (clarsimp simp add: striple_def return_evaluations_def abort_evaluations_def
  value_evaluations_def atriple_frame_rule)

text\<open>NB: this is expressed in a non-standard form as it's used to derive other results below by
unifying against the premiss of another theorem.\<close>
theorem striple_frame_rule_wrap:
  shows \<open>\<forall>\<phi> \<psi> \<rho> \<theta> \<xi> \<Gamma> e. striple \<Gamma> \<phi> e \<psi> \<rho> \<theta>
      \<longrightarrow> striple \<Gamma> (\<phi> \<star> \<xi>) e (\<lambda>v. \<psi> v \<star> \<xi>) (\<lambda>r. \<rho> r \<star> \<xi>) (\<lambda>a. \<theta> a \<star> \<xi>)\<close>
  by (simp add: striple_frame_rule)

text\<open>NB: this is expressed in a non-standard form as it's used to derive other results below by
being unifiable against the results phrased in a non-standard way above.\<close>
context
    fixes R :: \<open>('s, 'abort, 'i, 'o) striple_context \<Rightarrow> 'a assert \<Rightarrow> ('s, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow> ('v \<Rightarrow> 'a assert) \<Rightarrow>
                  ('r \<Rightarrow> 'a assert) \<Rightarrow> ('abort abort \<Rightarrow> 'a assert) \<Rightarrow> bool\<close>
  assumes WEAKEN: \<open>\<forall>\<phi> \<psi> \<rho> \<theta> \<psi>' \<rho>'  \<theta>' \<phi>' e \<Gamma>. R \<Gamma> \<phi>' e \<psi>' \<rho>' \<theta>' \<longrightarrow> \<phi> \<longlongrightarrow> \<phi>' \<longrightarrow>
        (\<forall>r. \<psi>' r \<longlongrightarrow> \<psi> r) \<longrightarrow> (\<forall>r. \<rho>' r \<longlongrightarrow> \<rho> r) \<longrightarrow> (\<forall>a. \<theta>' a \<longlongrightarrow> \<theta> a) \<longrightarrow> R \<Gamma> \<phi> e \<psi> \<rho> \<theta>\<close>
      and FRAME: \<open>\<forall>\<phi> \<psi> \<rho> \<theta> \<xi> \<Gamma> e. R \<Gamma> \<phi> e \<psi> \<rho> \<theta> \<longrightarrow> R \<Gamma> (\<phi> \<star> \<xi>) e (\<lambda>v. \<psi> v \<star> \<xi>) (\<lambda>r. \<rho> r \<star> \<xi>) (\<lambda>a. \<theta> a \<star> \<xi>)\<close>
begin

notation R ("(_) ; (_) /\<turnstile>/ (_) /\<stileturn>\<^sub>a\<^sub>b\<^sub>s/ (_) /\<bowtie>/ (_) /\<bowtie>/ (_)" [50,50,50,50,50,50]50)

theorem triple_frame_ruleI:
    notes aentails_simp [simp]
  assumes \<open>\<Gamma> ; \<phi>' \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi>' \<bowtie> \<rho>' \<bowtie> \<theta>'\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> \<phi>''\<close>
      and \<open>\<And>r. \<psi>' r \<longlongrightarrow> (\<phi>'' \<Zsurj> \<psi> r)\<close>
      and \<open>\<And>r. \<rho>' r \<longlongrightarrow> (\<phi>'' \<Zsurj> \<rho> r)\<close>
      and \<open>\<And>a. \<theta>' a \<longlongrightarrow> (\<phi>'' \<Zsurj> \<theta> a)\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  have \<open>\<Gamma> ; \<phi>' \<star> \<phi>'' \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<psi>' r \<star> \<phi>'') \<bowtie> (\<lambda>r. \<rho>' r \<star> \<phi>'') \<bowtie> (\<lambda>a. \<theta>' a \<star> \<phi>'')\<close>
    using assms FRAME by blast
  moreover have \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> \<phi>''\<close>
    using assms by blast
  moreover have \<open>\<And>r. \<psi>' r \<star> \<phi>'' \<longlongrightarrow> \<psi> r\<close>
    using assms awand_adjoint by blast
  moreover have \<open>\<And>r. \<rho>' r \<star> \<phi>'' \<longlongrightarrow> \<rho> r\<close>
    using assms by auto
  moreover have \<open>\<And>a. \<theta>' a \<star> \<phi>'' \<longlongrightarrow> \<theta> a\<close>
    using assms by auto
  ultimately show ?thesis
    using WEAKEN by blast
qed

text\<open>The following version of the reverse frame rule might be more useful because it uses less free
variables.\<close>
theorem triple_frame_ruleI':
  assumes \<open>\<Gamma> ; \<phi>' \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<psi> r) \<bowtie> (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<rho> r) \<bowtie> (\<lambda>a. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<theta> a)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> (\<phi>' \<Zsurj> \<phi>)\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma> ; \<phi>' \<star> (\<phi>' \<Zsurj> \<phi>) \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. ((\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<psi> r) \<star> (\<phi>' \<Zsurj> \<phi>))
                                             \<bowtie> (\<lambda>r. ((\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<rho> r) \<star> (\<phi>' \<Zsurj> \<phi>))
                                             \<bowtie> (\<lambda>a. ((\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<theta> a) \<star> (\<phi>' \<Zsurj> \<phi>))\<close>
    using ucincl_awand FRAME by blast
  from this and assms show ?thesis
    using WEAKEN local.awand_mp by blast
qed

theorem triple_frame_rule_asepconj_multi_singleI':
    notes asepconj_simp [simp]
      and aentails_intro [intro]
    assumes \<open>\<Gamma> ; (\<xi> (lst ! i)) \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s
               (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<psi> r)
            \<bowtie> (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<rho> r)
            \<bowtie> (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<theta> r)\<close>
      and \<open>i < length lst\<close>
    shows \<open>\<Gamma> ; \<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  have \<open>\<star>\<star> {# \<xi> \<Colon> lst #} \<star> \<phi> \<longlongrightarrow> \<xi> (lst ! i) \<star> \<phi> \<star> \<star>\<star> {# \<xi> \<Colon> drop_nth i lst #}\<close>
    using assms by (simp add: aentails_refl asepconj_comm asepconj_multi_mapped_pick asepconj_swap_top)
  moreover have \<open>\<And>r. \<star>\<star> {# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<psi> r \<star> \<star>\<star> {# \<xi> \<Colon> drop_nth i lst #} \<longlongrightarrow> \<psi> r\<close>
    using assms awand_mp by blast
  moreover have \<open>\<And>r. \<star>\<star> {# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<rho> r \<star> \<star>\<star> {# \<xi> \<Colon> drop_nth i lst #} \<longlongrightarrow> \<rho> r\<close>
    using assms awand_mp by blast
  ultimately show ?thesis
    using assms(1) triple_frame_ruleI by fastforce
qed

corollary triple_frame_rule':
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<xi> \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<xi> \<star> \<psi> r) \<bowtie> (\<lambda>r. \<xi> \<star> \<rho> r) \<bowtie> (\<lambda>a. \<xi> \<star> \<theta> a)\<close>
using assms FRAME asepconj_comm by auto

theorem triple_frame_rule_asepconj_multi:
  assumes \<open>\<Gamma> ; \<star>\<star>\<Psi> \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<star>\<star>\<Psi> \<star> \<psi> r) \<bowtie> (\<lambda>r. \<star>\<star>\<Psi> \<star> \<rho> r) \<bowtie> (\<lambda>a. \<star>\<star>\<Psi> \<star> \<theta> a)\<close>
      and \<open>\<forall>\<psi> \<in># \<Phi>. ucincl \<psi>\<close>
      and \<open>ucincl \<phi>\<close>
      and \<open>\<Psi> \<subseteq># \<Phi>\<close>
    shows \<open>\<Gamma> ; \<star>\<star>\<Phi> \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<star>\<star>\<Phi> \<star> \<psi> r) \<bowtie> (\<lambda>r. \<star>\<star>\<Phi> \<star> \<rho> r) \<bowtie> (\<lambda>a. \<star>\<star>\<Phi> \<star> \<theta> a)\<close>
proof -
  from \<open>\<Psi> \<subseteq># \<Phi>\<close> obtain \<Psi>' where \<open>\<Phi> = \<Psi>' + \<Psi>\<close>
    using mset_subset_eq_exists_conv union_commute by metis
  from this and \<open>\<Psi> \<subseteq># \<Phi>\<close> and \<open>\<forall>\<psi> \<in># \<Phi>. ucincl \<psi>\<close> have \<open>\<forall>\<psi> \<in># \<Psi>. ucincl \<psi>\<close>
    by auto
  from this and assms have \<open>ucincl (\<star>\<star>\<Psi> \<star> \<phi>)\<close>
    using asepconj_multi_ucincl ucincl_asepconj by auto
  from \<open>\<Phi> = \<Psi>' + \<Psi>\<close>  and \<open>\<forall>\<psi> \<in># \<Phi>. ucincl \<psi>\<close> have \<open>\<forall>\<psi> \<in># \<Psi>'. ucincl \<psi>\<close>
    by auto
  from this have \<open>ucincl (\<star>\<star>\<Psi>')\<close>
    using local.asepconj_multi_ucincl by auto
  from \<open>\<Phi> =  \<Psi>' + \<Psi>\<close> have \<open>\<star>\<star>\<Phi> = \<star>\<star>\<Psi>' \<star> \<star>\<star>\<Psi>\<close>
    using asepconj_multi_split' by auto
  from \<open>ucincl (\<star>\<star>\<Psi>')\<close> and \<open>ucincl (\<star>\<star>\<Psi> \<star> \<phi>)\<close>
       and \<open>\<Gamma> ; \<star>\<star>\<Psi> \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<star>\<star>\<Psi> \<star> \<psi> r) \<bowtie> (\<lambda>r. \<star>\<star>\<Psi> \<star> \<rho> r) \<bowtie> (\<lambda>a. \<star>\<star>\<Psi> \<star> \<theta> a)\<close>
  have \<open>\<Gamma> ; \<star>\<star>\<Psi>' \<star> (\<star>\<star>\<Psi> \<star> \<phi>) \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<star>\<star>\<Psi>' \<star> (\<star>\<star>\<Psi> \<star> \<psi> r))
                                    \<bowtie> (\<lambda>r. \<star>\<star>\<Psi>' \<star> (\<star>\<star>\<Psi> \<star> \<rho> r))
                                    \<bowtie> (\<lambda>r. \<star>\<star>\<Psi>' \<star> (\<star>\<star>\<Psi> \<star> \<theta> r))\<close>
      using triple_frame_rule' by blast
  from this and \<open>\<star>\<star>\<Phi> = \<star>\<star>\<Psi>' \<star> \<star>\<star>\<Psi>\<close> show ?thesis
    using local.asepconj_assoc by auto
qed

theorem triple_frame_rule_asepconj_multi_single:
    notes asepconj_simp [simp]
  assumes \<open>\<Gamma> ; \<tau> \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<tau> \<star> \<psi> r) \<bowtie> (\<lambda>r. \<tau> \<star> \<rho> r) \<bowtie> (\<lambda>a. \<tau> \<star> \<theta> a)\<close>
      and \<open>\<forall>\<psi> \<in># \<Phi>. ucincl \<psi>\<close>
      and \<open>ucincl \<phi>\<close>
      and \<open>\<tau> \<in># \<Phi>\<close>
    shows \<open>\<Gamma> ; \<star>\<star>\<Phi> \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<star>\<star>\<Phi> \<star> \<psi> r) \<bowtie> (\<lambda>r. \<star>\<star>\<Phi> \<star> \<rho> r) \<bowtie> (\<lambda>a. \<star>\<star>\<Phi> \<star> \<theta> a)\<close>
proof -
  from assms have  \<open>\<Gamma> ; \<star>\<star>{#\<tau>#} \<star> \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<star>\<star>{#\<tau>#} \<star> \<psi> r)
                                          \<bowtie> (\<lambda>r. \<star>\<star>{#\<tau>#} \<star> \<rho> r)
                                          \<bowtie> (\<lambda>a. \<star>\<star>{#\<tau>#} \<star> \<theta> a)\<close>
    by (simp add: local.asepconj_multi_def)
  moreover from \<open>\<tau> \<in># \<Phi>\<close> have \<open>{#\<tau>#} \<subseteq># \<Phi>\<close>
    by auto
  ultimately show ?thesis
    using assms triple_frame_rule_asepconj_multi by blast
qed

text\<open>Corollaries of the frame rule in case the return or success cases cannot happen.\<close>

corollary triple_frame_rule_no_return:
    notes asepconj_simp [simp]
      and aentails_intro [intro]
  assumes \<open>\<And>\<rho> \<theta>. (\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<And>\<rho> \<theta>.(\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<psi> r \<star> \<xi>) \<bowtie> \<rho> \<bowtie> \<theta>)\<close> (is \<open>\<And>\<rho> \<theta>. (?goal \<rho> \<theta>)\<close>)
proof -
  from assms have \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> (\<lambda>_. {}) \<bowtie> (\<lambda>_. {})\<close>
    by auto
  from assms this have \<open>\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<psi> r \<star> \<xi>) \<bowtie> (\<lambda>_. {} \<star> \<xi>) \<bowtie> (\<lambda>_. {} \<star> \<xi>)\<close>
    using FRAME by blast
  from this have I: \<open>(\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>r. \<psi> r \<star> \<xi>) \<bowtie> (\<lambda>_. {}) \<bowtie> (\<lambda>_. {}))\<close>
    by simp
  from this show \<open>\<And>\<rho> \<theta>. ?goal \<rho> \<theta>\<close> using bot_aentails_all
    by (simp add: WEAKEN aentails_def)
qed

corollary triple_frame_rule_no_value:
    notes asepconj_simp [simp]
      and aentails_intro[intro]
  assumes \<open>\<And>\<psi> \<theta>. (\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<And>\<psi> \<theta>. (\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s \<psi> \<bowtie> (\<lambda>r. \<rho> r \<star> \<xi>) \<bowtie> \<theta>)\<close> (is \<open>\<And>\<psi> \<theta>. (?goal \<psi> \<theta>)\<close>)
proof -
  from assms have \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>_. {}) \<bowtie> \<rho> \<bowtie> (\<lambda>_. {}))\<close>
    by auto
  from assms this have \<open>(\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>_. {} \<star> \<xi>) \<bowtie> (\<lambda>r. \<rho> r \<star> \<xi>) \<bowtie> (\<lambda>_. {} \<star> \<xi>))\<close>
    using FRAME by blast
  from this have I: \<open>(\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn>\<^sub>a\<^sub>b\<^sub>s (\<lambda>_. {}) \<bowtie> (\<lambda>r. \<rho> r \<star> \<xi>) \<bowtie> (\<lambda>_. {}))\<close>
    by simp
  from this show \<open>\<And>\<psi> \<theta>. ?goal \<psi> \<theta>\<close> using bot_aentails_all
    by (simp add: WEAKEN aentails_def)
qed

no_notation R ("(_) ; (_) /\<turnstile>/ (_) /\<stileturn>\<^sub>a\<^sub>b\<^sub>s/ (_) /\<bowtie>/ (_) /\<bowtie>/ (_)" [50,50,50,50,50,50]50)

end

lemmas striple_frame_rule' = triple_frame_rule'
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_ruleI = triple_frame_ruleI
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_ruleI' = triple_frame_ruleI'
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_rule_asepconj_multi_singleI' =
  triple_frame_rule_asepconj_multi_singleI'
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_rule_asepconj_multi =
  triple_frame_rule_asepconj_multi_singleI'
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_rule_asepconj_multi_single =
  triple_frame_rule_asepconj_multi_single
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_rule_no_value =
  triple_frame_rule_no_value
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]
lemmas striple_frame_rule_no_return =
  triple_frame_rule_no_return
  [OF striple_consequence_wrap, OF striple_frame_rule_wrap]

subsection\<open>Local axioms for Micro Rust expressions in SSA form:\<close>

text\<open>This is the ``fundamental result'' here, as most other Micro Rust constructs are defined in
terms of the monadic bind.  Note that this is the rule for \<^verbatim>\<open>let\<close> in disguise.\<close>
lemma striple_bindI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<And>x. \<Gamma> ; \<psi> x \<turnstile> f x \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>   \<comment> \<open>Case of continuation into \<^term>\<open>f\<close>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> Core_Expression.bind e f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof (intro stripleI)
  fix v s s'
  assume \<open>s \<leadsto>\<^sub>v \<langle>yh \<Gamma>,bind e f\<rangle> (v,s')\<close>
  with assms show \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> v\<close>
    by (meson atriple_trans urust_eval_predicate_bind stripleE_value)
next
  fix r s s'
  assume \<open>s \<leadsto>\<^sub>r \<langle>yh \<Gamma>,bind e f\<rangle> (r,s')\<close>
  with assms show \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<rho> r\<close>
    by (meson atriple_trans urust_eval_predicate_bind_return stripleE_return stripleE_value)
next
  fix a s s'
  assume \<open>s \<leadsto>\<^sub>a \<langle>yh \<Gamma>,bind e f\<rangle> (a,s')\<close>
  with assms show \<open>\<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a\<close>
    by (meson local.atriple_trans urust_eval_predicate_bind_abort stripleE_abort stripleE_value )
qed

text\<open>This is basically the \<^verbatim>\<open>striple_bindI\<close> theorem in a (thin) disguise:\<close>
corollary striple_sequenceI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<Gamma> ; \<psi> () \<turnstile> f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<And>r. \<rho> r = \<xi> r\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> sequence e f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms by (unfold sequence_def) (auto intro: striple_bindI)

text\<open>The \<^verbatim>\<open>skip\<close> command does not modify the state in any way, and always succeeds:\<close>
lemma striple_skipI:
  shows \<open>\<Gamma> ; \<psi> \<turnstile> skip \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. \<psi>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: stripleI simp add: atriple_def urust_eval_predicate_skip)

lemma aentails_after_all_asepconjs:
  shows \<open>(\<forall>\<pi>. ucincl \<pi> \<longrightarrow> (\<phi> \<star> \<pi> \<longlongrightarrow> \<psi> \<star> \<pi>)) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> \<star> \<top>)\<close>
  by (metis (no_types, lifting) local.asepconj_ident2 local.asepconj_mono local.asepconj_swap_top local.ucincl_UNIV 
      local.ucincl_alt' local.ucincl_asepconjR)

text\<open>Executing a literal does not modify the state in anyway way, but does return the literal value.
It also always succeeds:\<close>
lemma striple_literalI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> \<up>v \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = v\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: stripleI simp add: atriple_def urust_eval_predicate_literal asepconj_simp)

lemma striple_literal:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<up>v \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> v \<star> \<top>)\<close>
  apply (clarsimp simp add: striple_def atriple_def urust_eval_action_simps)
  using aentails_after_all_asepconjs aentails_def apply blast
  done

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma is_sat_upwards_closed:
  shows \<open>is_sat \<phi> \<longleftrightarrow> is_sat (\<phi> \<star> \<top>)\<close>
by (auto simp add: is_sat_def asat_def asepconj_def)

lemma striple_assert_val:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert_val v \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
     (v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (\<not>v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
proof (cases v)
  case True
  then show ?thesis
    by (simp add: assert_val_def local.asepconj_comm striple_literal)
next
  case False
  show ?thesis
  proof -
    have \<open>\<phi> \<longlongrightarrow> UNIV \<star> \<theta> AssertionFailed\<close>
      if \<open>\<forall>\<sigma> \<pi>. ucincl \<pi> \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<star> \<pi> \<longrightarrow> \<sigma> \<Turnstile> \<theta> AssertionFailed \<star> \<pi>\<close>
      by (metis aentails_after_all_asepconjs aentails_def local.asepconj_comm that)
    moreover have \<open>\<sigma> \<Turnstile> \<theta> AssertionFailed \<star> \<pi>\<close>
      if \<open>\<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed\<close>
        and \<open>ucincl \<pi>\<close> \<open>\<sigma> \<Turnstile> \<phi> \<star> \<pi>\<close>
      for \<sigma> \<pi>
      using that by (metis aentailsE aentails_after_all_asepconjs local.asepconj_comm)
    ultimately show ?thesis
      using False by (auto simp add: striple_def atriple_def urust_eval_action_simps asepconj_False_True asepconj_simp)
  qed
qed

lemma striple_assert:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> assert!(v) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
            (v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (\<not>v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
  by (simp add: assert_def micro_rust_simps striple_assert_val)

lemma striple_assert_eq:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> assert_eq!(v,w) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
            (v=w \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (v \<noteq> w \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
  by (simp add: assert_eq_def assert_eq_val_def micro_rust_simps striple_assert_val)

text\<open>The \<^verbatim>\<open>return_func\<close> command always succeeds and returns the given value:\<close>
lemma striple_return_valI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> return_val v \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> (\<lambda>rv. \<langle>rv = v\<rangle>) \<bowtie> \<theta>\<close>
by (auto intro!: stripleI simp add: atriple_def urust_eval_predicate_return asepconj_simp)

lemma striple_return_val:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> return_val v \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<rho> v \<star> \<top>)\<close>
  using aentails_after_all_asepconjs 
  by (force simp: aentails_def striple_def atriple_def urust_eval_action_simps)

lemma striple_returnI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> return_func (\<up>v) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> (\<lambda>rv. \<langle>rv = v\<rangle>) \<bowtie> \<theta>\<close>
by (intro stripleI; simp add: return_func_def urust_eval_predicate_bind urust_eval_predicate_return
  urust_eval_predicate_literal apure_def atriple_post_true)

lemma striple_return:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> return_func (\<up>v) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<rho> v \<star> \<top>)\<close>
  using aentails_after_all_asepconjs 
  by (force simp: aentails_def striple_def atriple_def return_func_def urust_eval_action_simps)

corollary striple_noneI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> `None \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = None\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (unfold none_def, rule striple_literalI)

corollary striple_trueI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> `True \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = True\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (unfold true_def, rule striple_literalI)

corollary striple_falseI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> `False \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = False\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (unfold false_def, rule striple_literalI)

corollary striple_someI:
  notes asepconj_simp [simp]
  shows \<open>\<Gamma> ; \<top> \<turnstile> `Some (\<up>x) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = Some x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; simp add: urust_eval_predicate_bind return_func_def micro_rust_simps some_def
  urust_eval_predicate_return urust_eval_predicate_literal apure_def atriple_post_true)

text\<open>Abort and panic terminate execution of the program:\<close>
lemma striple_abort:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> abort m \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<theta> m \<star> \<top>)\<close>
  using aentails_after_all_asepconjs
  by (force simp: aentails_def striple_def atriple_def return_func_def urust_eval_action_simps)

text\<open>Panic terminates execution of the program:\<close>
lemma striple_panic:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> panic msg \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<theta> (Panic msg) \<star> \<top>)\<close>
  by (simp add: striple_abort)

text\<open>Pause / Breakpoint\<close>

lemma striple_pause:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<top> \<turnstile> \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<top> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
using assms by (simp add: striple_def urust_eval_action_simps atriple_def)

lemma striple_pause':
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> ())\<close>
using assms unfolding is_valid_striple_context_def
  apply (clarsimp simp add: striple_def urust_eval_action_simps atriple_def)
  using aentails_after_all_asepconjs
  apply (metis aentails_def local.asepconj_strengthenE local.ucincl_UNIV)
  done

text\<open>Various types of log events:\<close>

lemma striple_log:
  shows \<open>\<Gamma> ; \<top> \<turnstile> \<lbrakk> \<l>\<o>\<g> \<llangle>p\<rrangle> \<llangle>l\<rrangle> \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<top> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (simp add: striple_def urust_eval_action_simps atriple_def is_valid_striple_context_def)

lemma striple_log':
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<l>\<o>\<g> \<llangle>p\<rrangle> \<llangle>l\<rrangle> \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> ())\<close>
using assms
  apply (clarsimp simp add: striple_def urust_eval_action_simps atriple_def
    is_valid_striple_context_def)
  using aentails_after_all_asepconjs
  apply (metis aentails_def local.asepconj_strengthenE local.ucincl_UNIV)
  done

text\<open>Fatal errors\<close>

lemma striple_fatal:
  assumes \<open>is_aborting_striple_context \<Gamma>\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> fatal!(msg) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
  using assms
  by (simp add: striple_def urust_eval_action_simps atriple_def is_aborting_striple_context_def)

lemma striple_two_armed_conditionalI:
  assumes \<open>x \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<not> x \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> two_armed_conditional (\<up>x) e f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  apply (intro stripleI)
    apply (force simp: urust_eval_predicate_two_armed_conditional
      urust_eval_predicate_literal elim: stripleE_value stripleE_return stripleE_abort)+
  done

text\<open>Generic yield\<close>

lemma striple_yield:
  shows \<open>\<Gamma>; \<phi> \<turnstile> yield \<omega> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta> \<longleftrightarrow>
           ((\<forall>\<sigma> \<sigma>' p . YieldContinue (p, \<sigma>') \<in> yh \<Gamma> \<omega> \<sigma> \<longrightarrow> \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> p) \<and>
            (\<forall>\<sigma> \<sigma>' a. YieldAbort a \<sigma>' \<in> yh \<Gamma> \<omega> \<sigma> \<longrightarrow> \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a))\<close>
  by (auto intro!: stripleI; clarsimp simp add: striple_def urust_eval_action_via_predicate
    urust_eval_predicate_simps)

lemma striple_nondet_choiceI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> l \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<Gamma> ; \<phi> \<turnstile> r \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> nondet_choice l r \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  have y: \<open>\<Gamma> ; \<phi> \<turnstile> yield NondetOrder \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. \<phi>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  proof (simp add: striple_yield, intro conjI allI impI)
    fix \<sigma> \<sigma>'
    assume hy: \<open>\<exists>p. YieldContinue (p, \<sigma>') \<in> yh \<Gamma> NondetOrder \<sigma>\<close>
    from striple_context_yh_is_nondet_order[of \<Gamma>] have hset:
      \<open>yh \<Gamma> NondetOrder \<sigma> = {YieldContinue (NondetLeft, \<sigma>), YieldContinue (NondetRight, \<sigma>)}\<close>
      by (simp add: is_nondet_order_yield_handler_def)
    from hy hset have eq: \<open>\<sigma>' = \<sigma>\<close> by auto
    from eq show \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<phi>\<close>
      by (simp add: atriple_refl)
  next
    fix \<sigma> \<sigma>' a
    assume hy: \<open>YieldAbort a \<sigma>' \<in> yh \<Gamma> NondetOrder \<sigma>\<close>
    from striple_context_yh_is_nondet_order[of \<Gamma>] have
      \<open>yh \<Gamma> NondetOrder \<sigma> = {YieldContinue (NondetLeft, \<sigma>), YieldContinue (NondetRight, \<sigma>)}\<close>
      by (simp add: is_nondet_order_yield_handler_def)
    with hy show \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a\<close> by auto
  qed
  have k: \<open>\<And>resp. \<Gamma> ; \<phi> \<turnstile> (if resp = NondetLeft then l else r) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using assms by (simp split: if_splits)
  from striple_bindI[OF y k] show ?thesis
    by (simp add: nondet_choice_def)
qed

text\<open>This rule does not hold for the strong striple: \<^verbatim>\<open>call f\<close> could be local without \<^verbatim>\<open>f\<close>
being local.\<close>
lemma striple_call:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> call (FunctionBody f) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<psi> \<bowtie> \<theta>)\<close>
  by (clarsimp simp add: striple_def urust_eval_action_simps atriple_def) blast

lemma striple_callI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<psi> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> call (FunctionBody f) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms by (simp add: striple_call)

lemma striple_call_inv:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> call (FunctionBody f) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<psi> \<bowtie> \<theta>\<close>
using assms by - (intro stripleI; elim stripleE_value stripleE_abort; simp add:
  urust_eval_predicate_call)

lemma striple_call_funliteral:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f1\<rrangle>\<^sub>1 (v0) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f1 v0) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f2\<rrangle>\<^sub>2 (v0, v1) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f2 v0 v1) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f3\<rrangle>\<^sub>3 (v0, v1, v2) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f3 v0 v1 v2) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f4\<rrangle>\<^sub>4 (v0, v1, v2, v3) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f4 v0 v1 v2 v3) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f5\<rrangle>\<^sub>5 (v0, v1, v2, v3, v4) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f5 v0 v1 v2 v3 v4) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f6\<rrangle>\<^sub>6 (v0, v1, v2, v3, v4, v5) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f6 v0 v1 v2 v3 v4 v5) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f7\<rrangle>\<^sub>7 (v0, v1, v2, v3, v4, v5, v6) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f7 v0 v1 v2 v3 v4 v5 v6) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> \<lbrakk> \<llangle>f8\<rrangle>\<^sub>8 (v0, v1, v2, v3, v4, v5, v6, v7) \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f8 v0 v1 v2 v3 v4 v5 v6 v7) \<star> \<top>)\<close>
using aentails_after_all_asepconjs by (auto simp add: striple_def urust_eval_action_simps
  micro_rust_simps atriple_def aentails_def) (blast, meson aentailsE aentails_after_all_asepconjs)+

lemma striple_getI:
  assumes \<open>ucincl (has f v)\<close>
    shows \<open>\<Gamma>; has f v \<turnstile> get f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>x. \<langle>x = v\<rangle> \<star> has f v) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms by (intro stripleI; clarsimp simp add: urust_eval_predicate_get urust_eval_predicate_literal
  atriple_def) (metis asat_def local.asat_apure_distrib local.asepconj_assoc
  local.asepconj_strengthenE local.has_def local.ucincl_asepconj mem_Collect_eq)

lemma striple_putI:
  assumes \<open>\<And>x. x \<Turnstile> has f v \<Longrightarrow> g x \<Turnstile> has f v'\<close>
      and \<open>\<And>x y. x\<sharp>y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> g (x+y) = g x + y \<and> g x \<sharp> y\<close>
    shows \<open>\<Gamma>; has f v \<turnstile> put g \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. has f v') \<bowtie> \<rho>  \<bowtie> \<theta>\<close>
using assms by (intro stripleI; clarsimp simp add: urust_eval_predicate_put
  urust_eval_predicate_literal atriple_def) (metis (full_types) assms(2) local.asepconjE
  local.asepconjI)

subsection\<open>Defining triples for numeric and bitwise operators\<close>

lemma striple_word_add_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x + unat y < 2^(LENGTH('l))\<rangle> \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_add_no_wrap apure_def asepconj_simp
    atriple_post_true atriple_pre_false)

lemma striple_word_mul_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x * unat y < 2^(LENGTH('l))\<rangle> \<turnstile> \<lbrakk> x * y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x * y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_mul_no_wrap apure_def asepconj_simp
    atriple_post_true atriple_pre_false)

lemma striple_word_sub_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<le> x\<rangle> \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_sub_no_wrap apure_def asepconj_simp
    atriple_post_true atriple_pre_false word_le_nat_alt)

lemma striple_word_udivI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x div y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_div apure_def asepconj_simp
    atriple_post_true unat_eq_zero atriple_pre_false)

lemma striple_word_umodI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> \<lbrakk> x % y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x mod y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_mod apure_def asepconj_simp
  atriple_post_true unat_eq_zero atriple_pre_false)

lemma striple_word_shift_leftI:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat y < LENGTH('l0)\<rangle> \<turnstile> \<lbrakk> x << y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = push_bit (unat y) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: asepconj_simp urust_eval_predicate_shift_left apure_def
  atriple_post_true atriple_pre_false)

lemma striple_word_shift_rightI:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat y < LENGTH('l0)\<rangle> \<turnstile> \<lbrakk> x >> y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = drop_bit (unat y) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_shift_right apure_def asepconj_simp
  atriple_post_true atriple_pre_false)

lemma striple_bitwise_orI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> \<lbrakk> x | y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x OR y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_or apure_def atriple_post_true)

lemma striple_bitwise_andI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> \<lbrakk> x & y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x AND y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_and apure_def atriple_post_true)

lemma striple_bitwise_xorI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> \<lbrakk> x ^ y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x XOR y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_xor apure_def atriple_post_true)

lemma striple_bitwise_notI:
  fixes x :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> \<lbrakk> !x \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = NOT x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_not apure_def atriple_post_true)

subsection\<open>Loops\<close>

lemma striple_raw_for_loop:
    fixes I :: \<open>'t list \<Rightarrow> 't list \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>past cur todo. \<Gamma> ; I past (cur # todo) \<turnstile> f cur \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (past @ [cur]) todo) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; I [] xs \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I xs []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms 
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by (simp add: raw_for_loop_nil striple_skipI)
next
  case (Cons x xs)
  then have \<open>\<Gamma> ; I [] (x # xs) \<turnstile> f x \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I [x] xs) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (metis append_Nil)
  moreover have \<open>\<Gamma> ; I [x] xs \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (x # xs) []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using Cons.prems Cons.IH[where I=\<open>\<lambda>past todo. I (x # past) todo\<close>] by (metis append_Cons)
  ultimately have \<open>\<Gamma> ; I [] (x # xs) \<turnstile> (bind (f x) (\<lambda>_. raw_for_loop xs f)) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (x # xs) []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (rule striple_bindI[where \<psi>=\<open>\<lambda> _. I [x] xs\<close>])
  then show ?case
    by (simp add: raw_for_loop_cons sequence_def)
qed

lemma striple_raw_for_loop_framed:
    notes aentails_intro [intro]
    fixes INV :: \<open>'t list \<Rightarrow> 't list \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>p t. ucincl (INV p t)\<close>
      and \<open>\<And>past cur todo. \<Gamma> ;  INV past (cur # todo) \<turnstile> f cur \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV (past @ [cur]) todo) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; INV [] xs \<star> ((INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a))
               \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)\<close>
  have \<open>\<Gamma> ; INV [] xs \<star> ?pc  \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV xs [] \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
  proof (intro striple_raw_for_loop)
    fix past cur todo
    have \<open>\<Gamma> ; INV past (cur # todo) \<turnstile> f cur \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV (past @ [cur]) todo) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms by auto
    moreover have \<open>\<Gamma> ; INV past (cur # todo) \<star> ?pc \<turnstile> f cur \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
        (\<lambda>_. INV (past @ [cur]) todo \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using assms by (intro striple_frame_rule; clarsimp)
    moreover have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
      by (meson aentails_refl_eq aentails_trans' local.aforall_entailsL local.asepconj_mono3 local.awand_counit)
    moreover from this have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
      by (metis (no_types, lifting) aentails_inter_weaken aentails_inter_weaken2 asepconj_comm awand_adjoint)
    moreover have \<open>\<And>a. \<theta> a \<star> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a) \<longlongrightarrow> \<chi> a\<close>
      by (meson aentails_refl_eq aentails_trans' local.aforall_entailsL local.asepconj_mono3 local.awand_counit)
    moreover from this have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
      by (metis (no_types, lifting) aentails_inter_weaken asepconj_comm local.awand_adjoint)
    ultimately show \<open>\<Gamma> ; INV past (cur # todo) \<star> ?pc \<turnstile> f cur \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV (past @ [cur]) todo \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      using assms by (meson aentails_refl striple_consequence)
  qed
  moreover have \<open>INV xs [] \<star> ?pc \<longlongrightarrow> \<psi> ()\<close>
    by (metis (no_types, lifting) aentails_refl local.asepconj_comm local.aentails_int local.awand_adjoint)
  ultimately have \<open>\<Gamma> ; INV [] xs \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using local.striple_consequence by (fastforce simp: aentails_refl)
  then show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.striple_consequence by fastforce
qed

text\<open>Alternative loop rule which might be easier to use in some situations. Passing the list to the
invariant may seem redundant because it's part of the context, but we don't always know what the
list will be named in the current proof state.\<close>
lemma striple_raw_for_loop':
    fixes I :: \<open>'t list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>i. i < length xs \<Longrightarrow> (\<Gamma> ; I xs i \<turnstile> f (xs ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I xs (i+1)) \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; I xs 0 \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I xs (length xs)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms 
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by (simp add: raw_for_loop_nil striple_skipI)
next
  case (Cons x xs)
  then have \<open>\<Gamma> ; I (x # xs) 0 \<turnstile> f x \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (x # xs) 1) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  moreover have \<open>\<And>i. i < length xs \<Longrightarrow> \<Gamma> ; I (x # xs) (Suc i) \<turnstile> f (xs ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (x # xs) (Suc (Suc i))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (metis Cons.prems Suc_eq_plus1 Suc_mono length_Cons nth_Cons_Suc)
  then have \<open>\<Gamma> ; I (x # xs) 1 \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (x # xs) (Suc (length xs))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using Cons.IH[where I=\<open>\<lambda>_ i. I (x # xs) (i+1)\<close>] by force
  ultimately have \<open>\<Gamma> ; I (x # xs) 0 \<turnstile> (bind (f x) (\<lambda>_. raw_for_loop xs f)) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. I (x # xs) (Suc (length xs))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (auto intro: striple_bindI[where \<psi>=\<open>\<lambda> _. I (x # xs) 1\<close>])
  then show ?case
    by (simp add: raw_for_loop_cons sequence_def)
qed

lemma striple_raw_for_loop_framed':
    notes aentails_intro [intro]
    fixes INV :: \<open>'t list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>i. (i < length xs) \<Longrightarrow> (\<Gamma> ; INV xs i \<turnstile> f (xs ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV xs (i+1)) \<bowtie> \<tau> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; INV xs 0 \<star> ((INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)) \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)\<close>
  have \<open>\<Gamma> ; INV xs 0 \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV xs (length xs) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
  proof (intro striple_raw_for_loop')
    fix i
    assume \<open>i < length xs\<close>
    then have \<open>\<Gamma> ; INV xs i \<turnstile> f (xs ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV xs (i+1)) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms by auto
    then have \<open>\<Gamma> ; INV xs i \<star> ?pc \<turnstile> f (xs ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
        (\<lambda>_. INV xs (i+1) \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using assms by (auto intro!: striple_frame_rule ucincl_Int ucincl_awand ucincl_inter)
    moreover have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
    proof -
      have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    moreover have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
    proof -
      have \<open>\<And>a. \<theta> a \<star> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a) \<longlongrightarrow> \<chi> a\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    ultimately show \<open>\<Gamma> ; INV xs i \<star> ?pc \<turnstile> f (xs ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. INV xs (i+1) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      by (meson aentails_refl striple_consequence)
  qed
  moreover have \<open>INV xs (length xs) \<star> ?pc \<longlongrightarrow> \<psi> ()\<close>
    by (metis (no_types, lifting) aentails_refl local.asepconj_comm local.aentails_int local.awand_adjoint)
  ultimately have \<open>\<Gamma> ; INV xs 0 \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using local.striple_consequence by (fastforce simp: aentails_refl)
  then show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.striple_consequence by fastforce
qed

lemma gather_spec':
    notes asepconj_simp [simp]
      and aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>i ls. i < length thunks \<Longrightarrow> length ls = i \<Longrightarrow> (\<Gamma> ; INV i ls \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV (i+1) (ls @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; INV 0 [] \<turnstile> gather' thunks acc \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. \<Squnion>rs'. \<langle>rs = acc @ rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms 
proof (induction thunks arbitrary: INV acc)
  case Nil
  have \<open>(\<Union>x. (if x = [] then UNIV else {}) \<star> INV 0 x) = (\<Union>x. (if x = [] then UNIV \<star> INV 0 x else {}))\<close>
    by (auto simp: split: if_splits)
  also have \<open>... = UNIV \<star> INV 0 []\<close> by auto
  finally show ?case
    by (auto simp: gather'_nil striple_def apure_def asepconj_swap_top urust_eval_action_literal atriple_refl')
next
  case (Cons t thunks)
  then have first: \<open>\<Gamma> ; INV 0 [] \<turnstile> t \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV 1 [v]) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  have \<open>\<Gamma> ; INV 1 [r0] \<turnstile> gather' thunks (acc @ [r0]) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
        (\<lambda>rs. \<Squnion>rs'. \<langle>rs = (acc @ rs')\<rangle> \<star> INV (length (t # thunks)) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close> for r0
  proof -
    have \<open>\<Gamma> ; INV (i+1) (r0 # ls) \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV ((i+1)+1) ((r0 # ls) @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      if \<open>i < length thunks\<close> \<open>length ls = i\<close> for i and ls :: \<open>'v list\<close>
         using that Cons.prems[where i=\<open>i+1\<close> and ls=\<open>r0 # ls\<close>] by fastforce
    with Cons.IH[where INV=\<open>\<lambda>i ls. INV (i+1) (r0 # ls)\<close> and acc=\<open>acc @ [r0]\<close>]
    have \<open>\<Gamma> ; INV 1 [r0] \<turnstile> gather' thunks (acc @ [r0]) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
          (\<lambda>rs. \<Squnion>rs'. \<langle>rs = (acc @ (r0 # rs'))\<rangle> \<star> INV (length (t # thunks)) (r0 # rs')) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      by simp
    moreover have \<open>\<And>rs. (\<Squnion>rs'. \<langle>rs = (acc @ (r0 # rs'))\<rangle> \<star> INV (Suc (length thunks)) (r0 # rs')) \<longlongrightarrow>
          (\<Squnion>rs'. \<langle>rs = (acc @ rs')\<rangle> \<star> INV (Suc (length thunks)) rs')\<close>
      by blast
    ultimately show ?thesis
      by (meson aentails_refl local.aexists_entailsL local.aexists_entailsR local.striple_consequence)
  qed
  with first
    show ?case by (simp add: gather'_cons local.striple_bindI)
  qed

lemma gather_spec:
    notes aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>i ls. ucincl (INV i ls)\<close>
      and \<open>\<And>i ls. i < length thunks \<Longrightarrow> length ls = i \<Longrightarrow>
            \<Gamma> ; INV i ls \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV (i+1) (ls @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. INV (length thunks) rs) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  from assms and gather_spec'[where INV=INV and thunks=thunks] have
        \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. \<Squnion>rs'. \<langle>rs = [] @ rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    unfolding gather_def by blast
  from this have \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. \<Squnion>rs'. \<langle>rs = rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  moreover have \<open>\<And>rs. (\<Squnion>rs'. \<langle>rs = rs'\<rangle> \<star> INV (length thunks) rs') \<longlongrightarrow> INV (length thunks) rs\<close>
    using assms by (simp add: asat_simp aentails_def)
  ultimately show ?thesis
    using striple_consequence by blast
qed

lemma striple_gather_framed:
    notes aentails_intro [intro]
    fixes thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>p r. ucincl (INV p r)\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow> \<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV (i+1) (res @ [v])) \<bowtie> \<tau>  \<bowtie> \<theta>\<close>
  shows \<open>\<Gamma> ; INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)) \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)\<close>
  {
    fix i and res :: \<open>'v list\<close>
    assume \<open>i < length thunks\<close>
       and \<open>length res = i\<close>
    from this have \<open>\<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (i+1) (res @ [r])) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms \<open>i < length thunks\<close> by auto
    moreover have \<open>\<Gamma> ; INV i res \<star> ?pc \<turnstile>
          (thunks ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (i+1) (res @ [r]) \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using assms calculation by (intro striple_frame_rule, force)
    moreover have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
    proof -
      have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    moreover have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
    proof -
      have \<open>\<And>a. \<theta> a \<star> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a) \<longlongrightarrow> \<chi> a\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    ultimately have \<open>\<Gamma> ; INV i res \<star> ?pc \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (i+1) (res @ [r]) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      by - (rule striple_consequence, assumption, rule aentails_refl, rule aentails_refl, force)
  }
  from this have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (length thunks) r \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using assms by (auto intro!: ucincl_intros gather_spec[where INV=\<open>\<lambda>i' res'. INV i' res' \<star> ?pc\<close> and thunks=thunks])
  moreover have \<open>\<And>r. INV (length thunks) r \<star> ?pc
                 \<longlongrightarrow> INV (length thunks) r \<star> (\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r))\<close>
    by (meson aentails_refl local.aentails_int local.asepconj_mono)
  moreover have \<open>\<And>r. INV (length thunks) r \<star> (\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r))  \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl local.aforall_entailsL local.asepconj_AC(1) local.awand_adjoint)
  moreover have \<open>\<And>r. INV (length thunks) r \<star> ?pc \<longlongrightarrow> \<psi> r\<close>
    using calculation by blast
  moreover have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using calculation local.striple_consequence by blast
  from this show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.striple_consequence by fastforce
qed


end

end
(*>*)
