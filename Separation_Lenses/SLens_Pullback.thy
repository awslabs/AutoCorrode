(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory SLens_Pullback
  imports
    Shallow_Separation_Logic.Assertion_Language 
    Shallow_Separation_Logic.Weak_Triple
    Shallow_Micro_Rust.Shallow_Micro_Rust
    Shallow_Separation_Logic.Triple
    Shallow_Separation_Logic.Function_Contract 
    SLens
begin

section \<open>Pullbacks along Separation lenses\<close>

text\<open>This is the central theory around separation lenses: We show that contracts and proofs
can be extended / 'pulled back' along a separation lens. While deceptively short, this theory
is very effective in capturing technical boilerplate involved in extending interface
implementations from smaller to larger separation algebras. For example, if a separation algebra
is needed that implements interfaces \<^verbatim>\<open>A\<close> and \<^verbatim>\<open>B\<close>, one can independently construct implementations
\<^verbatim>\<open>s\<^sub>A\<close> and \<^verbatim>\<open>s\<^sub>B\<close> of \<^verbatim>\<open>A\<close> and \<^verbatim>\<open>B\<close>, and then pull them back along \<^verbatim>\<open>s\<^sub>A \<times> s\<^sub>B\<close> to establish \<^verbatim>\<open>s\<^sub>A \<times> s\<^sub>B\<close>
as a separation algebra implementing \<^emph>\<open>both\<close> \<^verbatim>\<open>A\<close> and \<^verbatim>\<open>B\<close>. Writing the necessary boilerplate by
hand is not necessarily difficult, but tedious for complex interfaces or are large number of interfaces
that have to be composed as above.\<close>

text\<open>Assertion pullbacks differ in how they account for the lens complement. The precise
pullback embeds a satisfying viewed state into an empty complement and therefore preserves exact
ownership; it receives the \<^verbatim>\<open>l\<inverse>\<close> overload. The framed pullback constrains only the viewed
component and leaves the complement unconstrained, so it remains explicitly named.

The precise pullback preserves \<^term>\<open>emp\<close> and iterated separating conjunction. The framed
pullback is the precise pullback framed by \<^verbatim>\<open>slens_kernel\<close>; because it does not preserve
\<^term>\<open>emp\<close>, its iterated-conjunction law requires non-empty, upwards-closed factors. A non-empty
precise pullback is upwards closed only when the lens complement is trivial, so interface
assumptions that require upwards closure use the framed form.\<close>
definition pull_back_assertion :: \<open>('s::zero, 't) lens \<Rightarrow> 't assert \<Rightarrow> 's assert\<close>
  where \<open>pull_back_assertion l \<xi> = {lens_update l \<tau> 0 | \<tau>. \<tau> \<Turnstile> \<xi>}\<close>
adhoc_overloading pull_back_const \<rightleftharpoons> pull_back_assertion

definition pull_back_assertion_framed :: \<open>('s, 't) lens \<Rightarrow> 't assert \<Rightarrow> 's assert\<close>
  where \<open>pull_back_assertion_framed l \<xi> = {\<sigma>. lens_view l \<sigma> \<Turnstile> \<xi>}\<close>

lemma slens_view_zero:
    fixes l :: \<open>('s::sepalg, 't::sepalg) lens\<close>
  assumes \<open>is_valid_slens l\<close>
    shows \<open>lens_view l 0 = 0\<close>
proof -
  have \<open>0 \<sharp> (0 :: 's)\<close>
    by fast
  with assms have \<open>lens_view l 0 \<sharp> lens_view l 0\<close>
    by (simp add: is_valid_slens_def)
  then show \<open>lens_view l 0 = 0\<close>
    using unique by fast
qed

lemma slens_update_zero:
  assumes \<open>is_valid_slens l\<close>
    shows \<open>lens_update l 0 0 = 0\<close>
  by (simp add: assms slens.slens_update_alt(2) unique)

lemma pull_back_assertion_compose:
  assumes \<open>is_valid_slens l0\<close>
    shows \<open>pull_back_assertion (l0 \<circ>\<^sub>L l1) \<xi> =
      pull_back_assertion l0 (pull_back_assertion l1 \<xi>)\<close>
  using assms
  by (auto simp add: pull_back_assertion_def asat_def compose_lens_components slens_view_zero)

lemma pull_back_assertion_framed_compose:
  shows \<open>pull_back_assertion_framed (l0 \<circ>\<^sub>L l1) \<xi> =
      pull_back_assertion_framed l0 (pull_back_assertion_framed l1 \<xi>)\<close>
  by (clarsimp simp add: pull_back_assertion_framed_def asat_def compose_lens_components)

definition pull_back_relation :: \<open>('s, 't) lens \<Rightarrow> ('t \<Rightarrow> 'v \<times> 't \<Rightarrow> bool)
  \<Rightarrow> ('s \<Rightarrow> 'v \<times> 's \<Rightarrow> bool)\<close> where
  \<open>pull_back_relation l R \<equiv> \<lambda>\<sigma> (v, \<sigma>').
      (let \<tau> = lens_view l \<sigma> in
          \<exists>\<tau>'. R \<tau> (v, \<tau>') \<and> lens_update l \<tau>' \<sigma> = \<sigma>')\<close>
adhoc_overloading pull_back_const \<rightleftharpoons> pull_back_relation

definition is_lifted_striple_context where
  \<open>is_lifted_striple_context l \<Gamma> \<Theta> \<equiv>
      is_lifted_yield_handler l (yh \<Gamma>) (yh \<Theta>)\<close>

definition is_canonical_lifted_striple_context where
  \<open>is_canonical_lifted_striple_context l \<Gamma> \<Theta> \<equiv>
      (yh \<Theta> = canonical_pull_back_yield_handler l (yh \<Gamma>))\<close>

context slens
begin

lift_definition pull_back_striple_context :: \<open>('t, 'abort, 'i, 'o) striple_context \<Rightarrow> ('s, 'abort, 'i, 'o) striple_context\<close>
  is \<open>\<lambda>\<Gamma>. make_striple_context_raw (canonical_pull_back_yield_handler l (yield_handler_raw \<Gamma>))\<close>
   by (simp add: lens_valid canonical_pull_back_yield_handler_log_preserving
     canonical_pull_back_yield_handler_nondet_order_preserving
     is_valid_striple_context_def)

lemma pull_back_striple_context_yield_handler:
  shows \<open>yh (pull_back_striple_context \<Gamma>) = canonical_pull_back_yield_handler l (yh \<Gamma>)\<close>
  by (transfer, simp)

lemma pull_back_striple_context_no_yield[simp]:
  shows \<open>pull_back_striple_context striple_context_no_yield = striple_context_no_yield\<close>
  by (transfer, simp add: lens_valid striple_context_raw_no_yield_def)

end

adhoc_overloading pull_back_const \<rightleftharpoons> slens.pull_back_striple_context

definition pull_back_contract where
  \<open>pull_back_contract l \<CC> \<equiv> make_function_contract_with_abort
      (pull_back_assertion l (function_contract_pre \<CC>))
      (\<lambda>r. pull_back_assertion l (function_contract_post \<CC> r))
      (\<lambda>r. pull_back_assertion l (function_contract_abort \<CC> r))
  \<close>
adhoc_overloading pull_back_const \<rightleftharpoons> pull_back_contract

definition pull_back_contract_framed where
  \<open>pull_back_contract_framed l \<CC> \<equiv> make_function_contract_with_abort
      (pull_back_assertion_framed l (function_contract_pre \<CC>))
      (\<lambda>r. pull_back_assertion_framed l (function_contract_post \<CC> r))
      (\<lambda>r. pull_back_assertion_framed l (function_contract_abort \<CC> r))
  \<close>

\<comment>\<open>Precise and framed pullbacks use separate rule bundles because interface transfer also
consumes the framed rules backwards; combining them could rewrite a framed goal through a precise
pullback.\<close>
named_theorems slens_pull_back_simps
named_theorems slens_pull_back_intros

named_theorems slens_pull_back_precise_simps
named_theorems slens_pull_back_precise_intros

context slens
begin

subsection\<open>The precise pullback\<close>

lemma pull_back_assert_Union[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> (\<Union>x. \<xi> x) = (\<Union>x. l\<inverse> (\<xi> x))\<close>
  by (auto simp add: pull_back_assertion_def)

lemma pull_back_assertion_false[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> {} = {}\<close>
  by (simp add: pull_back_assertion_def)

lemma pull_back_assertion_emp[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> emp = emp\<close>
  using slens_lens_laws(2)[of 0] slens_view_zero[OF slens_valid]
  by (simp add: pull_back_assertion_def emp_def asat_def)

lemma pull_back_assertion_apure_precise[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> \<langle>P\<rangle> = \<langle>P\<rangle>\<close>
  by (simp add: apure_precise_def pull_back_assertion_def asat_def
      slens_update_zero[OF slens_valid])

text\<open>The precise pullback commutes with separating conjunction and its exact iteration.\<close>
lemma pull_back_asepconj[slens_pull_back_precise_simps]:
  fixes \<xi> \<tau> :: \<open>'t assert\<close>
  shows \<open>l\<inverse> (\<xi> \<star> \<tau>) = (l\<inverse> \<xi>) \<star> (l\<inverse> \<tau>)\<close>
  apply (clarsimp simp add: asepconj_def pull_back_assertion_def asat_def aentails_def; safe)
  apply (metis slens_embed_additive(1,2))
  apply (metis slens_embed_additive(2) slens_lens_laws(1) slens_view_local1)
  done

lemma pull_back_asepconj_multi'[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> (\<Phi> \<star>\<star>\<star> \<tau>) = {# l\<inverse> \<phi> . \<phi> \<leftarrow> \<Phi> #} \<star>\<star>\<star> l\<inverse> \<tau>\<close>
  by (induction \<Phi>) (simp_all add: asepconj_multi'_empty asepconj_multi'_add_mset
      pull_back_asepconj)

lemma pull_back_asepconj_multi[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> (\<star>\<star> \<Phi>) = \<star>\<star> {# l\<inverse> \<phi> . \<phi> \<leftarrow> \<Phi> #}\<close>
  by (simp add: asepconj_multi_def pull_back_asepconj_multi' pull_back_assertion_emp)

text\<open>The mapped form stays outside \<^verbatim>\<open>slens_pull_back_precise_simps\<close>: it introduces a
pullback while that bundle pushes pullbacks inward, so including both forms creates a rewrite
cycle.\<close>
lemma pull_back_asepconj_multi_map:
  shows \<open>\<star>\<star>{# l\<inverse> (\<xi> a) . a \<leftarrow> ms #} = l\<inverse> (\<star>\<star>{# \<xi> a . a \<leftarrow> ms #})\<close>
  by (induction ms) (simp_all add: slens_pull_back_precise_simps asepconj_simp)

corollary pull_back_asepconj_univ[slens_pull_back_precise_simps]:
  fixes \<xi> \<tau> :: \<open>'t assert\<close>
  shows \<open>l\<inverse> (\<xi> \<star> UNIV) = (l\<inverse> \<xi>) \<star> l\<inverse> UNIV\<close>
  by (simp add: slens_pull_back_precise_simps)

text\<open>The precise pullback is a full and faithful reading of the small algebra in the large one:\<close>
lemma pull_back_aentails[slens_pull_back_precise_simps]:
  shows \<open>(l\<inverse> \<alpha> \<longlongrightarrow> l\<inverse> \<beta>) \<longleftrightarrow> (\<alpha> \<longlongrightarrow> \<beta>)\<close>
proof (rule, goal_cases)
  case 1
  have embed_eq: \<open>\<And>y z. (slens_embed y = slens_embed z) \<longleftrightarrow> (y = z)\<close>
    using lens_valid by (metis slens_lens_laws(1))
  {
    fix x
    assume \<open>x \<in> \<alpha>\<close>
    then have \<open>lens_update l x 0 \<in> l\<inverse> \<alpha>\<close>
      by (force simp add: pull_back_assertion_def asat_def)
    with 1 have \<open>lens_update l x 0 \<in> l\<inverse> \<beta>\<close>
      by (force simp add: aentails_def asat_def)
    then have \<open>x \<in> \<beta>\<close>
      by (force simp add: pull_back_assertion_def asat_def embed_eq)
  }
  then show ?case
    by (simp add: aentails_def asat_def)
next
  case 2
  then show ?case
    by (auto simp add: aentails_def asat_def pull_back_assertion_def)
qed

lemma pull_back_asat_adjoint[slens_pull_back_precise_simps]:
  shows \<open>((lens_view l) \<sigma> \<Turnstile> \<xi> \<and> slens_proj1 \<sigma> = 0) \<longleftrightarrow> \<sigma> \<Turnstile> l\<inverse> \<xi>\<close>
proof
  assume left: \<open>(lens_view l) \<sigma> \<Turnstile> \<xi> \<and> slens_proj1 \<sigma> = 0\<close>
  have \<open>\<sigma> = lens_update l (lens_view l \<sigma>) 0 + slens_proj1 \<sigma>\<close>
    by (rule slens_decompose(1))
  also from left have \<open>\<dots> = lens_update l (lens_view l \<sigma>) 0\<close>
    by simp
  finally have \<open>\<sigma> = lens_update l (lens_view l \<sigma>) 0\<close> .
  with left show \<open>\<sigma> \<Turnstile> l\<inverse> \<xi>\<close>
    by (auto simp add: asat_def pull_back_assertion_def)
next
  assume \<open>\<sigma> \<Turnstile> l\<inverse> \<xi>\<close>
  then obtain \<tau> where \<open>\<sigma> = lens_update l \<tau> 0\<close> and \<open>\<tau> \<Turnstile> \<xi>\<close>
    by (auto simp add: asat_def pull_back_assertion_def)
  then show \<open>(lens_view l) \<sigma> \<Turnstile> \<xi> \<and> slens_proj1 \<sigma> = 0\<close>
    by (simp add: slens_lens_laws slens_update_zero[OF slens_valid])
qed

lemma pull_back_assertion_int[slens_pull_back_precise_simps]:
  shows \<open>l\<inverse> (\<phi> \<inter> \<psi>) = l\<inverse> \<phi> \<inter> l\<inverse> \<psi>\<close>
proof -
  have embed_eq: \<open>\<And>y z. (slens_embed y = slens_embed z) \<longleftrightarrow> (y = z)\<close>
    using lens_valid by (metis slens_lens_laws(1))
  show ?thesis
    by (auto simp add: pull_back_assertion_def asat_def embed_eq)
qed

lemma pull_back_contract_with_abort[slens_pull_back_precise_simps]:
  \<open>pull_back_contract l (make_function_contract_with_abort pre post ab) \<equiv>
      make_function_contract_with_abort
      (l\<inverse> pre) (\<lambda>r. l\<inverse> (post r)) (\<lambda>r. l\<inverse> (ab r))\<close>
  by (clarsimp simp add: pull_back_contract_def)

lemma pull_back_contract[slens_pull_back_precise_simps]:
  \<open>pull_back_contract l (make_function_contract pre post) \<equiv>
      make_function_contract (l\<inverse> pre) (\<lambda>r. l\<inverse> (post r))\<close>
  by (clarsimp simp add: bot_fun_def slens_pull_back_precise_simps)

lemma pull_back_aentailsI[slens_pull_back_precise_intros]:
  assumes \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>
    shows \<open>l\<inverse> \<alpha> \<longlongrightarrow> l\<inverse> \<beta>\<close>
  using assms pull_back_aentails by simp

lemmas pull_back_aentailsE = pull_back_aentails[elim_format]

text\<open>A non-empty precise pullback is upwards closed only when every lens complement is zero.\<close>
lemma precise_ucincl_forces_trivial:
  assumes \<open>ucincl (l\<inverse> \<phi>)\<close>
      and \<open>l\<inverse> \<phi> \<noteq> {}\<close>
    shows \<open>slens_proj1 \<sigma> = 0\<close>
proof -
  from assms(2) obtain \<tau> where t: \<open>lens_update l \<tau> 0 \<Turnstile> l\<inverse> \<phi>\<close>
    by (auto simp add: pull_back_assertion_def asat_def)
  have disj: \<open>lens_update l \<tau> 0 \<sharp> slens_proj1 \<sigma>\<close>
    by (metis disjoint_sym slens_complement_disj slens_lens_laws(1) zero_disjoint)
  from assms(1) t disj have grown: \<open>lens_update l \<tau> 0 + slens_proj1 \<sigma> \<Turnstile> l\<inverse> \<phi>\<close>
    using asat_weaken by blast
  from disj have comm: \<open>lens_update l \<tau> 0 + slens_proj1 \<sigma> = slens_proj1 \<sigma> + lens_update l \<tau> 0\<close>
    by (simp add: sepalg_comm)
  \<comment>\<open>Upwards closure keeps the grown state in the precise pullback, whose complement is zero.\<close>
  from grown comm have zero: \<open>slens_proj1 (slens_proj1 \<sigma> + lens_update l \<tau> 0) = 0\<close>
    using pull_back_asat_adjoint by metis
  have view0: \<open>lens_view l (slens_proj1 \<sigma>) = 0\<close>
    by (simp add: slens_lens_laws(1))
  from zero view0 show \<open>slens_proj1 \<sigma> = 0\<close>
    by (simp add: slens_complement_cancel_core)
qed

subsection\<open>The framed pullback\<close>

text\<open>The framed pullback of assertions along separation lenses commutes with separation
conjunction:\<close>

lemma pull_back_assertion_framed_Union[slens_pull_back_simps]:
  shows \<open>pull_back_assertion_framed l (\<Union>x. \<xi> x) =
      (\<Union>x. pull_back_assertion_framed l (\<xi> x))\<close>
  by (auto simp add: pull_back_assertion_framed_def)

lemma pull_back_assertion_framed_univ[slens_pull_back_simps]:
  shows \<open>pull_back_assertion_framed l UNIV = UNIV\<close>
  by (simp add: pull_back_assertion_framed_def)

lemma pull_back_assertion_framed_false[slens_pull_back_simps]:
  shows \<open>pull_back_assertion_framed l {} = {}\<close>
  by (simp add: pull_back_assertion_framed_def)

text\<open>A framed pullback enforces zero ownership only in the viewed component. Its complement is
therefore the lens kernel rather than \<^term>\<open>emp\<close>:\<close>
lemma pull_back_assertion_framed_apure_precise:
  shows \<open>pull_back_assertion_framed l \<langle>P\<rangle> =
      apure P \<inter> pull_back_assertion_framed l emp\<close>
  by (cases P; simp add: asepconj_simp pull_back_assertion_framed_false)

lemma pull_back_assertion_framed_asepconj[slens_pull_back_simps]:
  fixes \<xi> \<tau> :: \<open>'t assert\<close>
  shows \<open>pull_back_assertion_framed l (\<xi> \<star> \<tau>) =
      (pull_back_assertion_framed l \<xi>) \<star> (pull_back_assertion_framed l \<tau>)\<close>
  apply (clarsimp simp add: asepconj_def pull_back_assertion_framed_def asat_def aentails_def; safe)
  apply (metis slens_lift_decomposition slens_valid)
  apply (meson slens_valid slens_view_local1 slens_view_local2)
  done

text\<open>The framed pullback commutes with iteration over an explicit starting value.\<close>
lemma pull_back_assertion_framed_asepconj_multi'[slens_pull_back_simps]:
  shows \<open>pull_back_assertion_framed l (\<Phi> \<star>\<star>\<star> \<tau>) =
      {# pull_back_assertion_framed l \<phi> . \<phi> \<leftarrow> \<Phi> #} \<star>\<star>\<star>
        pull_back_assertion_framed l \<tau>\<close>
  by (induction \<Phi>) (simp_all add: asepconj_multi'_empty asepconj_multi'_add_mset
      pull_back_assertion_framed_asepconj)

corollary pull_back_assertion_framed_asepconj_univ[slens_pull_back_simps]:
  fixes \<xi> \<tau> :: \<open>'t assert\<close>
  shows \<open>pull_back_assertion_framed l (\<xi> \<star> UNIV) =
      (pull_back_assertion_framed l \<xi>) \<star> UNIV\<close>
  by (simp add: slens_pull_back_simps)

text\<open>As a separating-conjunction factor, \<^term>\<open>\<langle>P\<rangle>\<close> passes through unchanged:
according to \<^term>\<open>P\<close> it is the unit or annihilator, so the pullback acts only on the other
factor.\<close>
lemma pull_back_assertion_framed_apure_precise_asepconj:
  shows \<open>pull_back_assertion_framed l (\<langle>P\<rangle> \<star> \<xi>) =
      \<langle>P\<rangle> \<star> pull_back_assertion_framed l \<xi>\<close>
  by (cases P; simp add: asepconj_simp pull_back_assertion_framed_false)

lemma pull_back_assertion_framed_asepconj_apure_precise:
  shows \<open>pull_back_assertion_framed l (\<xi> \<star> \<langle>P\<rangle>) =
      pull_back_assertion_framed l \<xi> \<star> \<langle>P\<rangle>\<close>
  by (cases P; simp add: asepconj_simp pull_back_assertion_framed_false)

text\<open>The middle-factor form fixes the rewrite order for transfer goals with a precise-pure
condition between two spatial factors.\<close>
lemma pull_back_assertion_framed_asepconj_apure_precise_asepconj:
  shows \<open>pull_back_assertion_framed l (\<xi> \<star> \<langle>P\<rangle> \<star> \<tau>) =
      pull_back_assertion_framed l \<xi> \<star> \<langle>P\<rangle> \<star> pull_back_assertion_framed l \<tau>\<close>
  by (subst pull_back_assertion_framed_asepconj,
      subst pull_back_assertion_framed_apure_precise_asepconj, rule refl)

text\<open>These rules remain outside \<^verbatim>\<open>slens_pull_back_simps\<close>, which transfer proofs also use
in the reverse direction.\<close>

lemma pull_back_assertion_framed_ucincl[slens_pull_back_intros]:
  assumes \<open>ucincl \<pi>\<close>
  shows \<open>ucincl (pull_back_assertion_framed l \<pi>)\<close>
proof -
  have \<open>pull_back_assertion_framed l \<pi> = pull_back_assertion_framed l \<pi> \<star> UNIV\<close>
    using assms by (clarsimp simp add: ucincl_alt simp flip: slens_pull_back_simps)
  from this show ?thesis using ucincl_alt
    by auto
qed

text\<open>An upwards-closed assertion absorbs the framed pullback of \<^term>\<open>emp\<close>.\<close>
lemma pull_back_assertion_framed_emp_absorbed:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>\<phi> \<star> pull_back_assertion_framed l emp = \<phi>\<close>
proof (intro aentails_eq)
  show \<open>\<phi> \<star> pull_back_assertion_framed l emp \<longlongrightarrow> \<phi>\<close>
    using assms by (metis aentails_true asepconj_ident2 asepconj_mono)
next
  have \<open>emp \<longlongrightarrow> pull_back_assertion_framed l emp\<close>
    by (simp add: aentails_def asat_def emp_def pull_back_assertion_framed_def
      slens_view_zero[OF slens_valid])
  then show \<open>\<phi> \<longlongrightarrow> \<phi> \<star> pull_back_assertion_framed l emp\<close>
    by (rule asepconj_mono5)
qed

text\<open>The framed pullback commutes with a non-empty iteration of upwards-closed factors; both
side-conditions are determined by the rewrite target.\<close>
lemma pull_back_assertion_framed_asepconj_multi[slens_pull_back_simps]:
  assumes \<open>y \<noteq> {#}\<close>
      and \<open>\<And>x. ucincl (\<xi> x)\<close>
    shows \<open>pull_back_assertion_framed l (\<star>\<star>{# \<xi> x . x \<leftarrow> y #}) =
      \<star>\<star>{# pull_back_assertion_framed l (\<xi> x) . x \<leftarrow> y #}\<close>
proof -
  from assms have closed: \<open>ucincl (\<star>\<star>{# pull_back_assertion_framed l (\<xi> x) . x \<leftarrow> y #})\<close>
    by (intro asepconj_multi_mapped_ucincl) (auto intro: pull_back_assertion_framed_ucincl)
  have \<open>pull_back_assertion_framed l (\<star>\<star>{# \<xi> x . x \<leftarrow> y #}) =
      {# pull_back_assertion_framed l (\<xi> x) . x \<leftarrow> y #} \<star>\<star>\<star>
        pull_back_assertion_framed l emp\<close>
    by (simp only: asepconj_multi_def pull_back_assertion_framed_asepconj_multi'
        multiset.map_comp comp_def)
  also have \<open>\<dots> = \<star>\<star>{# pull_back_assertion_framed l (\<xi> x) . x \<leftarrow> y #} \<star>
      pull_back_assertion_framed l emp\<close>
    by (simp only: asepconj_multi_multi')
  finally show ?thesis
    by (simp only: pull_back_assertion_framed_emp_absorbed[OF closed])
qed

lemma pull_back_assertion_framed_aentails[slens_pull_back_simps]:
  shows \<open>(pull_back_assertion_framed l \<alpha> \<longlongrightarrow> pull_back_assertion_framed l \<beta>) \<longleftrightarrow>
      (\<alpha> \<longlongrightarrow> \<beta>)\<close>
proof -
  have \<open>\<And>x. lens_view l (lens_update l x 0) = x\<close>
    by (meson lens_laws lens_valid)
  from this have \<open>\<forall>x. \<exists>y. lens_view l y = x\<close>
    by blast
  from this show ?thesis
    by (auto simp add: asat_def aentails_def pull_back_assertion_framed_def) metis
qed

lemma pull_back_assertion_framed_asat_adjoint[slens_pull_back_simps]:
  shows \<open>(lens_view l) \<sigma> \<Turnstile> \<xi> \<longleftrightarrow> \<sigma> \<Turnstile> pull_back_assertion_framed l \<xi>\<close>
  by (clarsimp simp add: pull_back_assertion_framed_def asat_def)

lemma pull_back_assertion_framed_int[slens_pull_back_simps]:
  shows \<open>pull_back_assertion_framed l (\<phi> \<inter> \<psi>) =
      pull_back_assertion_framed l \<phi> \<inter> pull_back_assertion_framed l \<psi>\<close>
  by (auto simp add: pull_back_assertion_framed_def asat_def)

lemma pull_back_contract_framed_with_abort [slens_pull_back_simps]:
  \<open>pull_back_contract_framed l (make_function_contract_with_abort pre post ab) \<equiv>
      make_function_contract_with_abort
      (pull_back_assertion_framed l pre) (\<lambda>r. pull_back_assertion_framed l (post r))
      (\<lambda>r. pull_back_assertion_framed l (ab r))\<close>
  by (clarsimp simp add: pull_back_contract_framed_def)

lemma pull_back_contract_framed [slens_pull_back_simps]:
  \<open>pull_back_contract_framed l (make_function_contract pre post) \<equiv>
      make_function_contract
      (pull_back_assertion_framed l pre) (\<lambda>r. pull_back_assertion_framed l (post r))\<close>
  by (clarsimp simp add: bot_fun_def slens_pull_back_simps)

lemma pull_back_assertion_framed_aentailsI[slens_pull_back_intros]:
  assumes \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>
  shows \<open>pull_back_assertion_framed l \<alpha> \<longlongrightarrow> pull_back_assertion_framed l \<beta>\<close>
  using assms pull_back_assertion_framed_aentails by simp

lemmas pull_back_assertion_framed_aentailsE =
  pull_back_assertion_framed_aentails[elim_format]
subsection\<open>The lens kernel\<close>

text\<open>The lens kernel contains states with an empty viewed component. Framing a precise pullback
with the kernel yields the framed pullback.\<close>

definition slens_kernel :: \<open>'s assert\<close> where
  \<open>slens_kernel \<equiv> pull_back_assertion_framed l emp\<close>

lemma pull_back_assertion_precise_entails_framed:
  shows \<open>l\<inverse> \<xi> \<longlongrightarrow> pull_back_assertion_framed l \<xi>\<close>
  by (auto simp add: aentails_def asat_def pull_back_assertion_def
    pull_back_assertion_framed_def slens_lens_laws)

lemma pull_back_assertion_framed_as_precise_raw:
  shows \<open>pull_back_assertion_framed l \<xi> = l\<inverse> \<xi> \<star> pull_back_assertion_framed l emp\<close>
  apply (intro set_eqI iffI; clarsimp simp add: asepconj_def pull_back_assertion_def
    pull_back_assertion_framed_def asat_def emp_def)
  apply (metis slens_decompose(1) slens_decompose(2) slens_lens_laws(1))
  apply (clarsimp simp add: slens_view_local2 slens_lens_laws(1))
  done

text\<open>Naming the kernel makes the framed/precise equation a terminating left-to-right rewrite.\<close>
lemma pull_back_assertion_framed_as_precise:
  shows \<open>pull_back_assertion_framed l \<xi> = l\<inverse> \<xi> \<star> slens_kernel\<close>
  by (simp only: slens_kernel_def pull_back_assertion_framed_as_precise_raw[of \<xi>])

lemma slens_kernel_idem:
  shows \<open>slens_kernel \<star> slens_kernel = slens_kernel\<close>
  by (simp add: slens_kernel_def asepconj_simp flip: pull_back_assertion_framed_asepconj)

lemma slens_kernel_absorbed:
  shows \<open>slens_kernel \<star> pull_back_assertion_framed l \<psi> = pull_back_assertion_framed l \<psi>\<close>
  by (simp add: slens_kernel_def asepconj_simp flip: pull_back_assertion_framed_asepconj)

text\<open>A framed factor absorbs the kernel, allowing precise and framed factors in one separating
conjunction.\<close>
lemma pull_back_assertion_mixed_asepconj:
  shows \<open>l\<inverse> \<phi> \<star> pull_back_assertion_framed l \<psi> = pull_back_assertion_framed l (\<phi> \<star> \<psi>)\<close>
  apply (simp only: pull_back_assertion_framed_as_precise[of \<psi>]
     pull_back_assertion_framed_as_precise[of \<open>\<phi> \<star> \<psi>\<close>] pull_back_asepconj)
  apply (metis asepconj_assoc)
  done

lemma pull_back_assertion_mixed_asepconj':
  shows \<open>pull_back_assertion_framed l \<phi> \<star> l\<inverse> \<psi> = pull_back_assertion_framed l (\<phi> \<star> \<psi>)\<close>
  by (metis asepconj_comm pull_back_assertion_mixed_asepconj)

lemma pull_back_assertion_framed_absorbs_precise:
  shows \<open>l\<inverse> \<phi> \<star> \<rho> \<star> pull_back_assertion_framed l \<psi> =
      pull_back_assertion_framed l \<phi> \<star> \<rho> \<star> pull_back_assertion_framed l \<psi>\<close>
  by (metis asepconj_AC(1) asepconj_AC(3) pull_back_assertion_framed_as_precise
      slens_kernel_absorbed)

subsection\<open>Transport of triples and contracts\<close>

text\<open>Precise triple and contract transport is primitive. Framed transport follows by applying
the frame rules with \<^const>\<open>slens_kernel\<close>. Locality is antitone in its assertion, so precise
locality instead follows by weakening the framed law.\<close>

lemma pull_back_atriple_precise[slens_pull_back_precise_intros]:
  assumes \<open>\<phi> \<tturnstile> (lens_view l s, \<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
  shows \<open>l\<inverse> \<phi> \<tturnstile> (s, lens_update l \<tau>' s) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> \<psi>\<close>
proof (rule atripleI)
     fix \<xi>
  assume input: \<open>s \<Turnstile> l\<inverse> \<phi> \<star> \<xi>\<close>
  from input obtain a b where split:
      \<open>s = a + b\<close> \<open>a \<sharp> b\<close> \<open>a \<Turnstile> l\<inverse> \<phi>\<close> \<open>b \<Turnstile> \<xi>\<close>
    using asepconjE by blast
  \<comment>\<open>The precise left summand has zero complement, so the full lens complement lies in the
  frame.\<close>
  from split(3) obtain t where t: \<open>a = lens_update l t 0\<close> \<open>t \<Turnstile> \<phi>\<close>
    by (auto simp add: asat_def pull_back_assertion_def)
  from t have view_a: \<open>lens_view l a = t\<close>
    by (simp add: slens_lens_laws(1))
  from split(1,2) view_a have view_split: \<open>lens_view l s = t + lens_view l b\<close>
    by (simp add: slens_view_local2)
  from split(2) view_a have view_apart: \<open>t \<sharp> lens_view l b\<close>
    by (metis slens_view_local1)
  \<comment>\<open>The singleton viewed frame preserves that component exactly.\<close>
  from view_split view_apart t(2) have view_input: \<open>lens_view l s \<Turnstile> \<phi> \<star> {lens_view l b}\<close>
    by (simp add: asepconj_def asat_def) blast
  from assms view_input have output_sat: \<open>\<tau>' \<Turnstile> \<psi> \<star> {lens_view l b}\<close>
    using atriple_def by blast
  from output_sat obtain a' where out:
      \<open>\<tau>' = a' + lens_view l b\<close> \<open>a' \<sharp> lens_view l b\<close> \<open>a' \<Turnstile> \<psi>\<close>
    by (auto simp add: asepconj_def asat_def)
  from split(1,2) out(1,2) view_apart t view_a have update_split:
      \<open>lens_update l \<tau>' s = lens_update l a' a + lens_update l (lens_view l b) b\<close>
    using slens_update_general by (metis slens_view_local1)
  from t(1) have left_eq: \<open>lens_update l a' a = lens_update l a' 0\<close>
    by (simp add: slens_lens_laws)
  have right_eq: \<open>lens_update l (lens_view l b) b = b\<close>
    by (simp add: slens_lens_laws)
  from out(3) have left_sat: \<open>lens_update l a' 0 \<Turnstile> l\<inverse> \<psi>\<close>
    by (auto simp add: asat_def pull_back_assertion_def)
  from out(2) split(2) t(1) have update_apart: \<open>lens_update l a' 0 \<sharp> b\<close>
    by (metis slens_complement_disj disjoint_sym slens_lens_laws(1) slens_view_local1)
  show \<open>lens_update l \<tau>' s \<Turnstile> l\<inverse> \<psi> \<star> \<xi>\<close>
    using update_split left_eq right_eq left_sat update_apart split(4) by (metis asepconjI)
qed

lemma pull_back_atriple[slens_pull_back_intros]:
  assumes \<open>\<phi> \<tturnstile> (lens_view l s, \<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
  shows \<open>pull_back_assertion_framed l \<phi> \<tturnstile> (s,lens_update l \<tau>' s) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k pull_back_assertion_framed l \<psi>\<close>
  by (simp only: pull_back_assertion_framed_as_precise,
      rule atriple_frame_rule[OF pull_back_atriple_precise[OF assms]])

lemma pull_back_striple_precise[slens_pull_back_precise_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e  \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and C: \<open>is_canonical_lifted_striple_context l \<Gamma> \<Theta>\<close>
    shows \<open>\<Theta>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
      (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> (\<lambda>r. l\<inverse> (\<theta> r))\<close>
proof -
  from C have YH: \<open>yh \<Theta> = canonical_pull_back_yield_handler l (yh \<Gamma>)\<close>
    unfolding is_canonical_lifted_striple_context_def by simp
  show ?thesis
  proof (intro stripleI)
    fix v s s'
    assume \<open>s \<leadsto>\<^sub>v \<langle>yield_handler \<Theta>,l\<inverse> e\<rangle> (v,s')\<close>
    from this obtain \<tau>' where
       \<open>s' = lens_update l \<tau>' s\<close> and \<open>lens_view l s \<leadsto>\<^sub>v \<langle>yh \<Gamma>, e\<rangle> (v, \<tau>')\<close>
      using YH expression_pull_back_eval_value_canonical[OF lens_valid] by metis
    from this and T obtain \<open>\<phi> \<tturnstile> (lens_view l s,\<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v\<close>
      by (meson stripleE_value)
    from this and \<open>s' = lens_update l \<tau>' s\<close> and pull_back_atriple_precise
      show \<open>l\<inverse> \<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> (\<psi> v)\<close>
      by simp
  next
    fix r s s'
    assume \<open>s \<leadsto>\<^sub>r \<langle>yield_handler \<Theta>,l\<inverse> e\<rangle> (r,s')\<close>
    from this obtain \<tau>' where
       \<open>s' = lens_update l \<tau>' s\<close> and \<open>lens_view l s \<leadsto>\<^sub>r \<langle>yh \<Gamma>, e\<rangle> (r, \<tau>')\<close>
      using YH expression_pull_back_eval_return_canonical[OF lens_valid] by metis
    from this and T obtain \<open>\<phi> \<tturnstile> (lens_view l s,\<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> r\<close>
      by (meson stripleE_return)
    from this and \<open>s' = lens_update l \<tau>' s\<close> and pull_back_atriple_precise
      show \<open>l\<inverse> \<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> (\<xi> r)\<close>
      by simp
  next
    fix a s s'
    assume \<open>s \<leadsto>\<^sub>a \<langle>yield_handler \<Theta>,l\<inverse> e\<rangle> (a,s')\<close>
    from this obtain \<tau>' where
       \<open>s' = lens_update l \<tau>' s\<close> and \<open>lens_view l s \<leadsto>\<^sub>a \<langle>yh \<Gamma>, e\<rangle> (a, \<tau>')\<close>
      using YH expression_pull_back_eval_abort_canonical[OF lens_valid] by metis
    from this and T obtain \<open>\<phi> \<tturnstile> (lens_view l s,\<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a\<close>
      by (meson stripleE_abort)
    from this and \<open>s' = lens_update l \<tau>' s\<close> and pull_back_atriple_precise
      show \<open>l\<inverse> \<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> (\<theta> a)\<close>
      by simp
  qed
qed

lemma pull_back_striple[slens_pull_back_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e  \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and C: \<open>is_canonical_lifted_striple_context l \<Gamma> \<Theta>\<close>
    shows \<open>\<Theta>; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r))
      \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<theta> r))\<close>
  by (simp only: pull_back_assertion_framed_as_precise,
      rule striple_frame_rule[OF pull_back_striple_precise[OF T C]])

notation slens_embed ("\<iota>")
notation slens_view ("\<pi>")
notation slens_proj0 ("\<rho>\<^sub>0")
notation slens_proj1 ("\<rho>\<^sub>1")

lemma pull_back_local_relation_disj:
  assumes \<open>is_local R \<phi>\<close>
  shows \<open>\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v.
      \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi> \<Longrightarrow> l\<inverse> R \<sigma>_0 (v, \<sigma>_0') \<Longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1\<close>
proof -
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi>\<close>  and \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0')\<close>
  moreover from \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0')\<close> obtain \<tau>' where
     \<open>R (\<pi> \<sigma>_0) (v, \<tau>')\<close> and \<open>\<sigma>_0' = \<rho>\<^sub>1 \<sigma>_0 + \<iota> \<tau>'\<close>
    apply (clarsimp simp add: pull_back_relation_def)
    using slens_update_alt(1) slens_valid by blast
  moreover from \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi>\<close> have
    \<open>\<pi> \<sigma>_0 \<sharp> \<pi> \<sigma>_1\<close> and \<open>\<pi> \<sigma>_0 \<Turnstile> \<phi>\<close>
    apply (simp add: slens_view_local1)
    apply (metis \<open>\<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi>\<close> asat_def mem_Collect_eq pull_back_assertion_framed_def)
    done
  moreover from this and \<open>is_local R \<phi>\<close> have \<open>\<tau>' \<sharp> \<pi> \<sigma>_1\<close>
    by (meson calculation(4) is_localE)
  ultimately show \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
    by (metis slens_update_alt(1) slens_update_local4 slens_valid)
qed

lemma pull_back_local_relation[slens_pull_back_intros]:
  assumes \<open>is_local R \<phi>\<close>
  shows \<open>is_local (l\<inverse> R) (pull_back_assertion_framed l \<phi>)\<close>
proof (intro is_localI)
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi>\<close>  and \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0')\<close>
  from this show \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
    by (metis assms pull_back_local_relation_disj)
next
  fix \<sigma>_0 \<sigma>_1 \<sigma>' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi>\<close> and \<open>l\<inverse> R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')\<close>
  moreover from this obtain \<tau>' where
    \<open>R (\<pi> (\<sigma>_0 + \<sigma>_1)) (v, \<tau>')\<close> and \<open>lens_update l \<tau>' (\<sigma>_0 + \<sigma>_1) = \<sigma>'\<close>
    unfolding pull_back_relation_def by auto
  moreover from this have \<open>\<sigma>' = \<rho>\<^sub>1 \<sigma>_0 + \<rho>\<^sub>1 \<sigma>_1 + \<iota> \<tau>'\<close>
    using slens_valid by (metis calculation(1) slens_complement_additive(2) slens_update_alt(1))
  moreover from \<open>R (\<pi> (\<sigma>_0 + \<sigma>_1)) (v, \<tau>')\<close> have \<open>R (\<pi> \<sigma>_0 + \<pi> \<sigma>_1) (v, \<tau>')\<close>
    by (simp add: calculation(1) slens_view_local2)
  moreover from calculation obtain \<sigma>_0'' where
    \<open>R (\<pi> \<sigma>_0) (v, \<sigma>_0'')\<close> and \<open>\<tau>' = \<sigma>_0'' + \<pi> \<sigma>_1\<close>
    using slens_valid \<open>is_local R \<phi>\<close> unfolding is_local_def
    by (meson is_valid_slensE pull_back_assertion_framed_asat_adjoint)
  moreover from calculation have \<open>\<sigma>_0'' \<sharp> \<pi> \<sigma>_1\<close>
    using slens_valid by (meson assms is_localE pull_back_assertion_framed_asat_adjoint slens_view_local1)
  moreover note facts = calculation
  let ?\<sigma>_0' = \<open>\<rho>\<^sub>1 \<sigma>_0 + \<iota> \<sigma>_0''\<close>
  from facts have \<open>\<rho>\<^sub>1 \<sigma>' = \<rho>\<^sub>1 ?\<sigma>_0' + \<rho>\<^sub>1 \<sigma>_1\<close>
    using slens_valid by (metis slens_lens_laws(1) slens_complement_additive(2) slens_complement_cancel_core)
  moreover from facts have \<open>\<sigma>' = ?\<sigma>_0' + \<sigma>_1\<close>
    using slens_valid by (metis slens_update_alt(1) slens_update_local3)
  moreover have \<open>\<pi> ?\<sigma>_0' = \<sigma>_0''\<close>
    using slens_valid  by (metis slens_lens_laws(1) slens_update_alt(1))
  moreover from calculation have \<open>?\<sigma>_0' = lens_update l \<sigma>_0'' \<sigma>_0\<close>
    using slens_valid  by (metis slens_update_alt(1))
  moreover from calculation facts have \<open>l\<inverse> R \<sigma>_0 (v, ?\<sigma>_0')\<close>
    unfolding pull_back_relation_def by force
  ultimately show \<open>\<exists>\<sigma>_0'. l\<inverse> R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
    by blast
next
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v \<sigma>'
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
     and \<open>\<sigma>_0 \<Turnstile> pull_back_assertion_framed l \<phi>\<close>
     and \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
  moreover from this have \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
    by (meson assms pull_back_local_relation_disj)
  moreover from calculation obtain \<tau>' where \<open>R (\<pi> \<sigma>_0) (v, \<tau>')\<close> and \<open>\<sigma>_0' = lens_update l \<tau>' \<sigma>_0\<close>
    unfolding pull_back_relation_def by auto
  moreover have \<open>\<sigma>_0' = \<rho>\<^sub>1 \<sigma>_0 + \<iota> \<tau>'\<close>
    using slens_valid by (metis calculation(6) slens_update_alt(1))
  moreover from calculation have \<open>\<pi> \<sigma>' = \<pi> \<sigma>_0' + \<pi> \<sigma>_1\<close>
    using slens_valid  slens_view_local2 by blast
  moreover from calculation and \<open>is_local R \<phi>\<close> have \<open>R (\<pi> \<sigma>_0 + \<pi> \<sigma>_1) (v, \<tau>' + \<pi> \<sigma>_1)\<close>
    using slens_valid by (metis asat_def is_localE mem_Collect_eq pull_back_assertion_framed_def slens_view_local1)
  moreover from calculation have \<open>\<sigma>' = lens_update l (\<tau>' + \<pi> \<sigma>_1) (\<sigma>_0 + \<sigma>_1)\<close>
    using slens_valid by (metis slens_lens_laws(1) slens_update_local3 slens_view_local1)
  moreover have \<open>\<pi> (\<sigma>_0 + \<sigma>_1) = \<pi> \<sigma>_0 + \<pi> \<sigma>_1\<close>
    by (simp add: calculation(1) slens_view_local2)
  from this and \<open>\<sigma>' = lens_update l (\<tau>' + \<pi> \<sigma>_1) (\<sigma>_0 + \<sigma>_1)\<close> and
    \<open>R (\<pi> \<sigma>_0 + \<pi> \<sigma>_1) (v, \<tau>' + \<pi> \<sigma>_1)\<close> show \<open>l\<inverse> R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')\<close>
    unfolding pull_back_relation_def by auto
qed

lemma pull_back_local_urust:
  assumes \<open>urust_is_local y e \<phi>\<close>
    shows \<open>urust_is_local (l\<inverse> y) (l\<inverse> e) (pull_back_assertion_framed l \<phi>)\<close>
  using assms
  by (clarsimp simp add: pull_back_relation_def
    expression_pull_back_eval_value_canonical[OF lens_valid]
    expression_pull_back_eval_abort_canonical[OF lens_valid]
    expression_pull_back_eval_return_canonical[OF lens_valid]
    elim!: pull_back_local_relation[elim_format])

lemma pull_back_local_urust_precise:
  assumes \<open>urust_is_local y e \<phi>\<close>
    shows \<open>urust_is_local (l\<inverse> y) (l\<inverse> e) (l\<inverse> \<phi>)\<close>
  by (rule urust_is_local_weaken[OF pull_back_assertion_precise_entails_framed
        pull_back_local_urust[OF assms]])

lemma pull_back_sstriple_precise[slens_pull_back_precise_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
    shows \<open>l\<inverse> \<Gamma>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> (\<lambda>r. l\<inverse> (\<theta> r))\<close>
  using assms by (clarsimp simp add: sstriple_striple' is_canonical_lifted_striple_context_def
     pull_back_local_urust_precise pull_back_striple_precise
     pull_back_striple_context_yield_handler)

lemma pull_back_sstriple[slens_pull_back_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
    shows \<open>l\<inverse> \<Gamma>; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r))
      \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<theta> r))\<close>
  by (simp only: pull_back_assertion_framed_as_precise,
      rule sstriple_frame_rule[OF pull_back_sstriple_precise[OF T]])

lemma pull_back_sstriple_bot_precise[slens_pull_back_precise_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  shows \<open>l\<inverse> \<Gamma>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
proof -
  let ?bot = \<open>(\<lambda>_. \<bottom>) :: 'abort abort \<Rightarrow> 't assert\<close>
  have eq: \<open>\<bottom> = (\<lambda>r. (l\<inverse> (?bot r)))\<close>
    by (simp add: bot_fun_def pull_back_assertion_false)
  from this assms pull_back_sstriple_precise show ?thesis
    by fastforce
qed

\<comment>\<open>This is an artifact of the current use of \<^verbatim>\<open>\<bottom>\<close> as the abort-postcondition in function contracts.
 Once we generalize, this should no longer be necessary.\<close>
lemma pull_back_sstriple_bot[slens_pull_back_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  shows \<open>l\<inverse> \<Gamma>; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r)) \<bowtie> \<bottom>\<close>
proof -
  let ?bot = \<open>(\<lambda>_. \<bottom>) :: 'abort abort \<Rightarrow> 't assert\<close>
  have eq: \<open>\<bottom> = (\<lambda>r. (pull_back_assertion_framed l (?bot r)))\<close>
    by (simp add: bot_fun_def pull_back_assertion_framed_false)
  from this assms pull_back_sstriple show ?thesis
    by fastforce
qed

lemma pull_back_sstriple_universal_bot_precise[slens_pull_back_precise_intros]:
  assumes \<open>\<And>\<Gamma>. \<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  shows \<open>\<And>\<Gamma>. \<Gamma>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
proof -
  from assms have \<open>striple_context_no_yield; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    by simp
  from this have \<open>l\<inverse> striple_context_no_yield; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
    by (intro pull_back_sstriple_bot_precise; assumption)
  from this have \<open>striple_context_no_yield; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
    using lens_valid by force
  from this show \<open>\<And>\<Gamma>. \<Gamma> ; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
    using sstriple_yield_handler_no_yield_implies_all by blast
qed

lemma pull_back_sstriple_universal_bot[slens_pull_back_intros]:
  assumes \<open>\<And>\<Gamma>. \<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  shows \<open>\<And>\<Gamma>. \<Gamma>; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r)) \<bowtie> \<bottom>\<close>
proof -
  from assms have \<open>striple_context_no_yield; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    by simp
  from this have \<open>l\<inverse> striple_context_no_yield; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r)) \<bowtie> \<bottom>\<close>
    by (intro pull_back_sstriple_bot; assumption)
  from this have \<open>striple_context_no_yield; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r)) \<bowtie> \<bottom>\<close>
    using lens_valid by force
  from this show \<open>\<And>\<Gamma>. \<Gamma> ; pull_back_assertion_framed l \<phi> \<turnstile> l\<inverse> e \<stileturn>
      (\<lambda>v. pull_back_assertion_framed l (\<psi> v)) \<bowtie> (\<lambda>r. pull_back_assertion_framed l (\<xi> r)) \<bowtie> \<bottom>\<close>
    using sstriple_yield_handler_no_yield_implies_all by blast
qed

lemma pull_back_spec_precise[slens_pull_back_precise_intros]:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<CC>\<close>
  shows \<open>l\<inverse> \<Gamma>; l\<inverse> f \<Turnstile>\<^sub>F pull_back_contract l \<CC>\<close>
  using assms unfolding satisfies_function_contract_def pull_back_contract_def
  by (clarsimp simp add: function_pull_back_def pull_back_sstriple_precise)

lemma pull_back_spec[slens_pull_back_intros]:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<CC>\<close>
  shows \<open>l\<inverse> \<Gamma>; l\<inverse> f \<Turnstile>\<^sub>F pull_back_contract_framed l \<CC>\<close>
  using assms unfolding satisfies_function_contract_def pull_back_contract_framed_def
  by (clarsimp simp add: function_pull_back_def pull_back_sstriple)

lemma pull_back_spec_universal_precise:
  assumes \<open>\<And>\<Gamma>. \<Gamma>; f \<Turnstile>\<^sub>F \<CC>\<close>
      and \<open>function_contract_abort \<CC> = \<bottom>\<close>
  shows \<open>\<And>\<Gamma>. \<Gamma>; l\<inverse> f \<Turnstile>\<^sub>F pull_back_contract l \<CC>\<close>
  using assms unfolding satisfies_function_contract_def pull_back_contract_def
  by (simp add: function_pull_back_def pull_back_sstriple_universal_bot_precise
    slens_pull_back_precise_simps bot_fun_def[symmetric])

lemma pull_back_spec_universal:
  assumes \<open>\<And>\<Gamma>. \<Gamma>; f \<Turnstile>\<^sub>F \<CC>\<close>
      and \<open>function_contract_abort \<CC> = \<bottom>\<close>
  shows \<open>\<And>\<Gamma>. \<Gamma>; l\<inverse> f \<Turnstile>\<^sub>F pull_back_contract_framed l \<CC>\<close>
  using assms unfolding satisfies_function_contract_def pull_back_contract_framed_def
  by (simp add: function_pull_back_def pull_back_sstriple_universal_bot
    slens_pull_back_simps bot_fun_def[symmetric])

no_notation slens_embed ("\<iota>")
no_notation slens_view ("\<pi>")
no_notation slens_proj0 ("\<rho>\<^sub>0")
no_notation slens_proj1 ("\<rho>\<^sub>1")

\<comment>\<open>Give this a name so we can refer to it all simplification and introduction rules even
outside of the locale\<close>
lemmas slens_pull_back_simps_copy = slens_pull_back_simps
lemmas slens_pull_back_intros_copy = slens_pull_back_intros

end

\<comment>\<open>Simplifying to get rid of the wrapper \<^verbatim>\<open>lens l \<equiv> is_valid_slens l\<close> generated by the locale.\<close>
lemmas slens_pull_back_simps_generic = slens.slens_pull_back_simps_copy[simplified]
lemmas slens_pull_back_intros_generic = slens.slens_pull_back_intros_copy[simplified]

end
