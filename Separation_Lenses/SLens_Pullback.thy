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

definition pull_back_assertion :: \<open>('s, 't) lens \<Rightarrow> 't assert \<Rightarrow> 's assert\<close>
  where \<open>pull_back_assertion l \<xi> = {\<sigma>. lens_view l \<sigma> \<Turnstile> \<xi>}\<close>
adhoc_overloading pull_back_const \<rightleftharpoons> pull_back_assertion

lemma pull_back_assertion_compose:
  shows \<open>pull_back_assertion (l0 \<circ>\<^sub>L l1) \<xi> = pull_back_assertion l0 (pull_back_assertion l1 \<xi>)\<close>
  by (clarsimp simp add: pull_back_assertion_def asat_def compose_lens_components)

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
      (l\<inverse> (function_contract_pre \<CC>)) 
      (\<lambda>r. l\<inverse> (function_contract_post \<CC> r))
      (\<lambda>r. l\<inverse> (function_contract_abort \<CC> r))
  \<close>
adhoc_overloading pull_back_const \<rightleftharpoons> pull_back_contract

named_theorems slens_pull_back_simps
named_theorems slens_pull_back_intros

context slens
begin

text\<open>Pullback of assertions along separation lenses commutes with separation conjunction:\<close>

lemma pull_back_assert_Union[slens_pull_back_simps]:
  shows \<open>l\<inverse> (\<Union>x. \<xi> x) = (\<Union>x. l\<inverse> (\<xi> x))\<close>
  by (auto simp add: pull_back_assertion_def)

lemma pull_back_assertion_univ[slens_pull_back_simps]:
  shows \<open>l\<inverse> UNIV = UNIV\<close>
  by (simp add: pull_back_assertion_def)

lemma pull_back_assertion_false[slens_pull_back_simps]:
  shows \<open>l\<inverse> {} = {}\<close>
  by (simp add: pull_back_assertion_def)

lemma pull_back_assertion_pure[slens_pull_back_simps]:
  shows \<open>l\<inverse> \<langle>P\<rangle> = \<langle>P\<rangle>\<close>
  by (simp add: apure_def pull_back_assertion_def)

lemma pull_back_asepconj[slens_pull_back_simps]:
  fixes \<xi> \<tau> :: \<open>'t assert\<close>
  shows \<open>l\<inverse> (\<xi> \<star> \<tau>) = (l\<inverse> \<xi>) \<star> (l\<inverse> \<tau>)\<close>
  apply (clarsimp simp add: asepconj_def pull_back_assertion_def asat_def aentails_def; safe)
  apply (metis slens_lift_decomposition slens_valid)
  apply (meson slens_valid slens_view_local1 slens_view_local2)
  done

lemma pull_back_asepconj_multi[slens_pull_back_simps]:
  shows \<open> l\<inverse> (\<star>\<star>{# \<xi> x . x \<leftarrow> y #}) = \<star>\<star>{# l\<inverse> (\<xi> x) . x \<leftarrow> y #}\<close>
  by (induction y; clarsimp simp add: slens_pull_back_simps simp add: asepconj_simp)

corollary pull_back_asepconj_univ[slens_pull_back_simps]:
  fixes \<xi> \<tau> :: \<open>'t assert\<close>
  shows \<open>l\<inverse> (\<xi> \<star> UNIV) = (l\<inverse> \<xi>) \<star> UNIV\<close>
  by (simp add: slens_pull_back_simps)

lemma pull_back_ucincl[slens_pull_back_intros]:
  assumes \<open>ucincl \<pi>\<close>
  shows \<open>ucincl (l\<inverse> \<pi>)\<close>
proof -
  have \<open>l\<inverse> \<pi> = l\<inverse> \<pi> \<star> UNIV\<close>
    using assms by (clarsimp simp add: ucincl_alt simp flip: slens_pull_back_simps)
  from this show ?thesis using ucincl_alt
    by auto
qed

lemma pull_back_aentails[slens_pull_back_simps]:
  shows \<open>(l\<inverse> \<alpha> \<longlongrightarrow> l\<inverse> \<beta>) \<longleftrightarrow> (\<alpha> \<longlongrightarrow> \<beta>)\<close>
proof -
  have \<open>\<And>x. lens_view l (lens_update l x 0) = x\<close>
    by (meson lens_laws lens_valid)
  from this have \<open>\<forall>x. \<exists>y. lens_view l y = x\<close>
    by blast
  from this show ?thesis
    by (auto simp add: asat_def aentails_def pull_back_assertion_def) metis
qed

lemma pull_back_asat_adjoint[slens_pull_back_simps]:
  shows \<open>(lens_view l) \<sigma> \<Turnstile> \<xi> \<longleftrightarrow> \<sigma> \<Turnstile> l\<inverse> \<xi>\<close>
  by (clarsimp simp add: pull_back_assertion_def asat_def)

lemma pull_back_assertion_int[slens_pull_back_simps]:
  shows \<open>l\<inverse> (\<phi> \<inter> \<psi>) = l\<inverse> \<phi> \<inter> l\<inverse> \<psi>\<close>
  by (auto simp add: pull_back_assertion_def asat_def)

lemma pull_back_contract_with_abort [slens_pull_back_simps]:
  \<open>pull_back_contract l (make_function_contract_with_abort pre post ab) \<equiv>
      make_function_contract_with_abort
      (l\<inverse> pre) (\<lambda>r. l\<inverse> (post r)) (\<lambda>r. l\<inverse> (ab r))\<close>
  by (clarsimp simp add: pull_back_contract_def)

lemma pull_back_contract [slens_pull_back_simps]:
  \<open>pull_back_contract l (make_function_contract pre post) \<equiv>
      make_function_contract
      (l\<inverse> pre) (\<lambda>r. l\<inverse> (post r))\<close>
  by (clarsimp simp add: bot_fun_def slens_pull_back_simps)

lemma pull_back_aentailsI[slens_pull_back_intros]:
  assumes \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>
  shows \<open>l\<inverse> \<alpha> \<longlongrightarrow> l\<inverse> \<beta>\<close>
  using assms pull_back_aentails by simp

lemmas pull_back_aentailsE = pull_back_aentails[elim_format]

text\<open>The following is central: Assertion triples can be pulled back along separation lenses:\<close>

lemma pull_back_atriple[slens_pull_back_intros]:
  assumes \<open>\<phi> \<tturnstile> (lens_view l s, \<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
  shows \<open>l\<inverse> \<phi> \<tturnstile> (s,lens_update l \<tau>' s) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> \<psi>\<close>
  using assms
proof -
  assume \<open>\<phi> \<tturnstile> (lens_view l s, \<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
  let ?p = \<open>lens_view l\<close>
  { fix \<xi> assume \<open>ucincl \<xi>\<close> and \<open>s \<Turnstile> l\<inverse> \<phi> \<star> \<xi>\<close>
    then obtain a b where \<open>s = a + b\<close> and \<open>a \<sharp> b\<close> and \<open>a \<Turnstile> l\<inverse> \<phi>\<close> and \<open>b \<Turnstile> \<xi>\<close>
      using asepconjE by blast
    from this have \<open>?p s = ?p a + ?p b\<close> and \<open>?p a \<sharp> ?p b\<close>
      using slens_valid slens_view_local2 slens_view_local1 by blast+
    let ?pb = \<open>?p b\<close>
    let ?\<xi>' = \<open>{?pb} \<star> \<top>\<close>
    have \<open>ucincl ?\<xi>'\<close>
      by (simp add: ucincl_UNIV ucincl_asepconjR)
    moreover have \<open>?pb \<Turnstile> ?\<xi>'\<close>
      by (clarsimp simp add: asat_def asepconj_def) force
    moreover from this and \<open>?p s = ?p a + ?p b\<close> and \<open>?p a \<sharp> ?p b\<close> \<open>a \<Turnstile> l\<inverse> \<phi>\<close>
      have \<open>?p s \<Turnstile> \<phi> \<star> ?\<xi>'\<close>
      by (metis asat_def asepconjI mem_Collect_eq pull_back_assertion_def)
    moreover from this and \<open>ucincl ?\<xi>'\<close> and \<open>\<phi> \<tturnstile> (lens_view l s, \<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close> have
      \<open>\<tau>' \<Turnstile> \<psi> \<star> ?\<xi>'\<close>
      using atriple_def by blast
    moreover from this obtain a' b' where \<open>\<tau>' = a' + b'\<close> and \<open>a' \<sharp> b'\<close> and \<open>a' \<Turnstile> \<psi>\<close>
      and \<open>b' \<Turnstile> ?\<xi>'\<close>
      using asepconjE by blast
    moreover from this obtain b0 where \<open>b' = ?pb + b0\<close> and \<open>?pb \<sharp> b0\<close>
      by (metis asat_def asepconjE singletonD)
    moreover from calculation have \<open>lens_update l \<tau>' s = lens_update l a' a + lens_update l b' b\<close>
      using slens_valid slens_update_general by (metis \<open>a \<sharp> b\<close> \<open>s = a + b\<close>)
    moreover from calculation have \<open>lens_update l a' a \<sharp> lens_update l b' b\<close>
      by (metis \<open>a \<sharp> b\<close> disjoint_sym sepalg_apart_plus2 slens_lens_laws(1) slens_update_local4)
    moreover from calculation have \<open>lens_update l a' a \<Turnstile> l\<inverse> \<psi>\<close>
      by (metis lens_laws_update(1) local.lens_valid pull_back_asat_adjoint)
    moreover from calculation have \<open>lens_update l b' b = b + lens_update l b0 0\<close>
      by (metis slens_lens_laws(2) slens_update_disjoint)
    moreover from this have \<open>lens_update l b' b \<Turnstile> \<xi>\<close>
      by (metis \<open>b \<Turnstile> \<xi>\<close> \<open>ucincl \<xi>\<close> asat_weaken calculation(10) slens_complement_disj)
    ultimately have \<open>lens_update l \<tau>' s \<in> l\<inverse> \<psi> \<star> \<xi>\<close>
      by (metis asat_def asepconjI) }
  from this show \<open>l\<inverse> \<phi> \<tturnstile> (s,lens_update l \<tau>' s) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> \<psi>\<close>
    by (meson asat_def atripleI)
qed

lemma pull_back_striple[slens_pull_back_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e  \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>is_canonical_lifted_striple_context l \<Gamma> \<Theta>\<close>
    shows \<open>\<Theta>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> (\<lambda>r. l\<inverse> (\<theta> r))\<close>
proof -
  from \<open>is_canonical_lifted_striple_context l \<Gamma> \<Theta>\<close> have
    YH: \<open>yh \<Theta> = canonical_pull_back_yield_handler l (yh \<Gamma>)\<close>
    unfolding is_canonical_lifted_striple_context_def by simp
  note assms = YH T
  show ?thesis
proof (intro stripleI)
  fix v s s'
  assume \<open>s \<leadsto>\<^sub>v \<langle>yield_handler \<Theta>,l\<inverse> e\<rangle> (v,s')\<close>
  from this obtain \<tau>' where
     \<open>s' = lens_update l \<tau>' s\<close> and \<open>lens_view l s \<leadsto>\<^sub>v \<langle>yh \<Gamma>, e\<rangle> (v, \<tau>')\<close>
    using YH expression_pull_back_eval_value_canonical[OF lens_valid] by metis
  from this and \<open>\<Gamma>; \<phi> \<turnstile> e  \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close> obtain \<open>\<phi> \<tturnstile> (lens_view l s,\<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v\<close>
    by (meson stripleE_value)
  from this and \<open>s' = lens_update l \<tau>' s\<close> and pull_back_atriple
    show \<open>l\<inverse> \<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> (\<psi> v)\<close>
    by simp
next
  fix r s s'
  assume \<open>s \<leadsto>\<^sub>r \<langle>yield_handler \<Theta>,l\<inverse> e\<rangle> (r,s')\<close>
  from this obtain \<tau>' where
     \<open>s' = lens_update l \<tau>' s\<close> and \<open>lens_view l s \<leadsto>\<^sub>r \<langle>yh \<Gamma>, e\<rangle> (r, \<tau>')\<close>
    using YH expression_pull_back_eval_return_canonical[OF lens_valid] by metis
  from this and \<open>\<Gamma>; \<phi> \<turnstile> e  \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close> obtain \<open>\<phi> \<tturnstile> (lens_view l s,\<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi> r\<close>
    by (meson stripleE_return)
  from this and \<open>s' = lens_update l \<tau>' s\<close> and pull_back_atriple
    show \<open>l\<inverse> \<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> (\<xi> r)\<close>
    by simp
next
  fix a s s'
  assume \<open>s \<leadsto>\<^sub>a \<langle>yield_handler \<Theta>,l\<inverse> e\<rangle> (a,s')\<close>
  from this obtain \<tau>' where
     \<open>s' = lens_update l \<tau>' s\<close> and \<open>lens_view l s \<leadsto>\<^sub>a \<langle>yh \<Gamma>, e\<rangle> (a, \<tau>')\<close>
    using YH expression_pull_back_eval_abort_canonical[OF lens_valid] by metis
  from this and \<open>\<Gamma>; \<phi> \<turnstile> e  \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close> obtain \<open>\<phi> \<tturnstile> (lens_view l s,\<tau>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<theta> a\<close>
    by (meson stripleE_abort)
  from this and \<open>s' = lens_update l \<tau>' s\<close> and pull_back_atriple
    show \<open>l\<inverse> \<phi> \<tturnstile> (s,s') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k l\<inverse> (\<theta> a)\<close>
      by simp
  qed
qed

notation slens_embed ("\<iota>")
notation slens_view ("\<pi>")
notation slens_proj0 ("\<rho>\<^sub>0")
notation slens_proj1 ("\<rho>\<^sub>1")

lemma pull_back_local_relation_disj:
  assumes \<open>is_local R \<phi>\<close>
  shows \<open>\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v.
      \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> l\<inverse> \<phi> \<Longrightarrow> l\<inverse> R \<sigma>_0 (v, \<sigma>_0') \<Longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1\<close>
proof -
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> l\<inverse> \<phi>\<close>  and \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0')\<close>
  moreover from \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0')\<close> obtain \<tau>' where
     \<open>R (\<pi> \<sigma>_0) (v, \<tau>')\<close> and \<open>\<sigma>_0' = \<rho>\<^sub>1 \<sigma>_0 + \<iota> \<tau>'\<close>
    apply (clarsimp simp add: pull_back_relation_def)
    using slens_update_alt(1) slens_valid by blast
  moreover from \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> l\<inverse> \<phi>\<close> have
    \<open>\<pi> \<sigma>_0 \<sharp> \<pi> \<sigma>_1\<close> and \<open>\<pi> \<sigma>_0 \<Turnstile> \<phi>\<close>
    apply (simp add: slens_view_local1)
    apply (metis \<open>\<sigma>_0 \<Turnstile> l\<inverse> \<phi>\<close> asat_def mem_Collect_eq pull_back_assertion_def)
    done
  moreover from this and \<open>is_local R \<phi>\<close> have \<open>\<tau>' \<sharp> \<pi> \<sigma>_1\<close>
    by (meson calculation(4) is_localE)
  ultimately show \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
    by (metis slens_update_alt(1) slens_update_local4 slens_valid)
qed

lemma pull_back_local_relation[slens_pull_back_intros]:
  assumes \<open>is_local R \<phi>\<close>
  shows \<open>is_local (l\<inverse> R) (l\<inverse> \<phi>)\<close>
proof (intro is_localI)
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> l\<inverse> \<phi>\<close>  and \<open>l\<inverse> R \<sigma>_0 (v, \<sigma>_0')\<close>
  from this show \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
    by (metis assms pull_back_local_relation_disj)
next
  fix \<sigma>_0 \<sigma>_1 \<sigma>' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> l\<inverse> \<phi>\<close> and \<open>l\<inverse> R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')\<close>
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
    by (meson is_valid_slensE pull_back_asat_adjoint)
  moreover from calculation have \<open>\<sigma>_0'' \<sharp> \<pi> \<sigma>_1\<close>
    using slens_valid by (meson assms is_localE pull_back_asat_adjoint slens_view_local1)
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
     and \<open>\<sigma>_0 \<Turnstile> l\<inverse> \<phi>\<close>
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
    using slens_valid by (metis asat_def is_localE mem_Collect_eq pull_back_assertion_def slens_view_local1)
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
    shows \<open>urust_is_local (l\<inverse> y) (l\<inverse> e) (l\<inverse> \<phi>)\<close>
  using assms
  by (clarsimp simp add: pull_back_relation_def
    expression_pull_back_eval_value_canonical[OF lens_valid]
    expression_pull_back_eval_abort_canonical[OF lens_valid]
    expression_pull_back_eval_return_canonical[OF lens_valid]
    elim!: pull_back_local_relation[elim_format])

lemma pull_back_sstriple[slens_pull_back_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
    shows \<open>l\<inverse> \<Gamma>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> (\<lambda>r. l\<inverse> (\<theta> r))\<close>
  using assms by (clarsimp simp add: sstriple_striple' is_canonical_lifted_striple_context_def
     pull_back_local_urust pull_back_striple pull_back_striple_context_yield_handler)

\<comment>\<open>This is an artifact of the current use of \<^verbatim>\<open>\<bottom>\<close> as the abort-postcondition in function contracts.
 Once we generalize, this should no longer be necessary.\<close>
lemma pull_back_sstriple_bot[slens_pull_back_intros]:
  fixes e :: \<open>('t, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes T: \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  shows \<open>l\<inverse> \<Gamma>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
proof -
  let ?bot = \<open>(\<lambda>_. \<bottom>) :: 'abort abort \<Rightarrow> 't assert\<close>
  have eq: \<open>\<bottom> = (\<lambda>r. (l\<inverse> (?bot r)))\<close>
    by (simp add: bot_fun_def pull_back_assertion_false)
  from this assms pull_back_sstriple show ?thesis
    by fastforce
qed

lemma pull_back_sstriple_universal_bot[slens_pull_back_intros]:
  assumes \<open>\<And>\<Gamma>. \<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  shows \<open>\<And>\<Gamma>. \<Gamma>; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
proof -
  from assms have \<open>striple_context_no_yield; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    by simp
  from this have \<open>l\<inverse> striple_context_no_yield; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
    by (intro pull_back_sstriple_bot; assumption)
  from this have \<open>striple_context_no_yield; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
    using lens_valid by force
  from this show \<open>\<And>\<Gamma>. \<Gamma> ; l\<inverse> \<phi> \<turnstile> l\<inverse> e \<stileturn> (\<lambda>v. l\<inverse> (\<psi> v)) \<bowtie> (\<lambda>r. l\<inverse> (\<xi> r)) \<bowtie> \<bottom>\<close>
    using sstriple_yield_handler_no_yield_implies_all by blast
qed

lemma pull_back_spec[slens_pull_back_intros]:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<CC>\<close>
  shows \<open>l\<inverse> \<Gamma>; l\<inverse> f \<Turnstile>\<^sub>F l\<inverse> \<CC>\<close>
  using assms unfolding satisfies_function_contract_def pull_back_contract_def
  by (clarsimp simp add: pull_back_ucincl function_pull_back_def pull_back_sstriple)

lemma pull_back_spec_universal:
  assumes \<open>\<And>\<Gamma>. \<Gamma>; f \<Turnstile>\<^sub>F \<CC>\<close>
      and \<open>function_contract_abort \<CC> = \<bottom>\<close>
  shows \<open>\<And>\<Gamma>. \<Gamma>; l\<inverse> f \<Turnstile>\<^sub>F l\<inverse> \<CC>\<close>
  using assms unfolding satisfies_function_contract_def pull_back_contract_def
  by (simp add: function_pull_back_def pull_back_sstriple_universal_bot pull_back_ucincl
    slens_pull_back_simps bot_fun_def[symmetric] ucincl_intros)

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
