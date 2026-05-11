(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Assertion_Triple
  imports Shallow_Micro_Rust.Eval Assertion_Language Precision Locality "HOL-Library.Rewrite"
begin

context sepalg begin
(*>*)

subsubsection\<open>Assertion triples\<close>

text\<open>The following relation expresses that two states \<^term>\<open>\<sigma>\<close> and \<^term>\<open>\<sigma>'\<close> are related by
'swapping out' a sub-state satisfying assertion \<^term>\<open>\<phi>\<close> for a sub-state satisfying \<^term>\<open>\<psi>\<close>:\<close>
definition atriple :: \<open>'a assert \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a assert \<Rightarrow> bool\<close>
      ("(_) \<tturnstile>/ '(_,_')/ \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (_)" [50,50,50]50) where
  \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<equiv> \<forall>\<pi>. ucincl \<pi> \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<star> \<pi> \<longrightarrow> \<sigma>' \<Turnstile> \<psi> \<star> \<pi>\<close>

lemma atripleI:
  assumes \<open>\<And>\<pi>. ucincl \<pi> \<Longrightarrow> \<sigma> \<Turnstile> (\<phi> \<star> \<pi>) \<Longrightarrow> \<sigma>' \<Turnstile> (\<psi> \<star> \<pi>)\<close>
    shows \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
using assms by (auto simp add: atriple_def)

lemma atripleE:
  assumes \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
      and \<open>(\<And>\<pi>. ucincl \<pi> \<Longrightarrow> \<sigma> \<Turnstile> (\<phi> \<star> \<pi>) \<Longrightarrow> \<sigma>' \<Turnstile> (\<psi> \<star> \<pi>)) \<Longrightarrow> R\<close>
    shows R
using assms by (auto simp add: atriple_def)

lemma atriple_refl:
  shows \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<phi>\<close>
by (simp add: atriple_def)

lemma atriple_refl':
  shows \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<top> \<star> \<phi>\<close>
by (simp add: atriple_def) (metis local.asepconj_assoc local.asepconj_ident local.asepconj_swap_top)

lemma atriple_pre_false:
  shows \<open>{} \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
by (simp add: atriple_def local.asepconj_bot_zero)

lemma atriple_post_true:
  shows \<open>\<phi>  \<tturnstile> (\<sigma>, \<sigma>) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<top>\<close>
by (metis aentails_def atripleI local.aentails_cancel_l local.asepconj_ident)

lemma atriple_consequence:
  assumes \<open>\<phi>' \<longlongrightarrow> \<phi>\<close>
     and \<open>\<psi> \<longlongrightarrow> \<psi>'\<close>
     and \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
   shows \<open>\<phi>' \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>'\<close>
using assms by (auto elim!: atripleE intro!: atripleI) (meson aentailsE local.asepconj_mono2)

lemma atriple_trans:
  assumes \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
      and \<open>\<psi> \<tturnstile> (\<sigma>', \<sigma>'') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi>\<close>
    shows \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>'') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<xi>\<close>
using assms by (auto simp add: atriple_def)

lemma atriple_union:
  shows \<open>((\<Union>\<Phi>) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) = (\<forall>\<phi>\<in>\<Phi>. (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close>
    and \<open>((\<Squnion>x. \<phi> x) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) = (\<forall>x. (\<phi> x \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close>
    and \<open>((\<Squnion>x\<in>S. \<phi> x) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) = (\<forall>x\<in>S. (\<phi> x \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close>
by (auto simp add: atriple_def asepconj_Inf_distrib' asepconj_simp)

lemma atriple_frame_rule:
  assumes \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
    shows \<open>\<phi> \<star> \<xi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<star> \<xi>\<close>
using assms by (simp add: atriple_def local.asepconj_assoc local.ucincl_asepconjR)

lemma atriple_complement:
  assumes \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
      and \<open>is_splitting \<sigma> \<sigma>0 \<sigma>c\<close>
      and \<open>\<sigma>0 \<Turnstile> \<phi>\<close>
  obtains \<sigma>0' where \<open>\<sigma>0' \<Turnstile> \<psi> \<star> \<top>\<close> and \<open>\<sigma>0' \<sharp> \<sigma>c\<close> and \<open>\<sigma>' = \<sigma>0' + \<sigma>c\<close>
proof -
  let ?\<pi> = \<open>\<up>\<^sub>s \<sigma>c\<close>
  have \<open>ucincl ?\<pi>\<close>
    by (simp add: uc_state_ucincl)
  moreover have \<open>\<sigma> \<Turnstile> ?\<pi> \<star> \<phi>\<close>
    by (metis asat_def assms(2) assms(3) local.asepconjI local.asepconj_comm local.derived_order_refl
      local.is_splitting_def local.uc_state_def mem_Collect_eq)
  moreover from this have \<open>\<sigma>' \<Turnstile> ?\<pi> \<star> \<psi>\<close>
    using assms(1) atriple_def calculation local.asepconj_comm by auto
  moreover from this obtain \<sigma>0' \<sigma>c' where \<open>is_splitting \<sigma>' \<sigma>0' \<sigma>c'\<close> and \<open>\<sigma>0' \<Turnstile> \<psi>\<close> and \<open>\<sigma>c' \<Turnstile> \<up>\<^sub>s \<sigma>c\<close>
    by (metis local.asepconjE local.disjoint_sym local.is_splitting_def local.sepalg_comm)
  moreover from this obtain \<sigma>cc where \<open>\<sigma>c' = \<sigma>c + \<sigma>cc\<close> and \<open>\<sigma>c \<sharp> \<sigma>cc\<close>
    by (metis asat_def local.derived_order_def local.uc_state_def mem_Collect_eq)
  moreover from calculation obtain \<open>\<sigma>0' \<sharp> \<sigma>cc\<close> and \<open>(\<sigma>0' + \<sigma>cc) \<Turnstile> \<psi> \<star> \<top>\<close>
    by (meson asat_connectives_characterisation(1) local.asepconjI local.disjoint_sym local.is_splitting_def
        local.sepalg_apart_plus)
  ultimately show ?thesis
    by (metis local.disjoint_sym local.is_splitting_def local.sepalg_apart_plus2
      local.sepalg_apart_plus_distrib local.sepalg_assoc local.sepalg_comm that)
qed

lemma atriple_hoist_pure:
  shows \<open>(\<phi> \<star> \<langle>P\<rangle> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close>
    and \<open>(\<langle>P\<rangle> \<star> \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close> (is ?g2)
proof -
  show \<open>(\<phi> \<star> \<langle>P\<rangle> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close>
    by (clarsimp simp add: atriple_def apure_def asepconj_simp)
  from this show \<open>(\<langle>P\<rangle> \<star> \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>))\<close>
    by (simp add: asepconj_comm)
qed

lemma atriple_direct:
  assumes \<open>ucincl \<alpha>\<close>
      and \<open>ucincl \<beta>\<close>
      and \<open>\<alpha> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<beta>\<close>
      and \<open>\<sigma> \<Turnstile> \<alpha>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<beta>\<close>
by (metis assms atripleE ucincl_UNIV ucincl_alt)

text\<open>For minimal states, the atriple can be characterized in simpler terms:\<close>

lemma atriple_minimal:
  assumes \<open>is_minimal \<xi> \<sigma>\<close>
      and \<open>\<sigma>' \<Turnstile> \<psi>\<close>
    shows \<open>\<xi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
using assms by (clarsimp simp add: is_minimal_def asat_def atriple_def) (metis asat_def asepconjE
  asepconj_weakenI derived_order_def disjoint_sym reflE sepalg_apart_plus2 sepalg_comm)

text\<open>The assertion triple is invariant under passage to upward closure:\<close>
lemma atriple_upwards_closure:
  shows \<open>((\<phi> \<star> \<top>) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<psi> \<star> \<top>)) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>((\<top> \<star> \<phi>) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<top> \<star> \<psi>)) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>((\<phi> \<star> \<top>) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<top> \<star> \<psi>)) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>((\<top> \<star> \<phi>) \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<psi> \<star> \<top>)) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>(\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<psi> \<star> \<top>)) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>(\<phi> \<star> \<top> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>(\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<top> \<star> \<psi>)) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
    and \<open>(\<top> \<star> \<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>) \<longleftrightarrow> (\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>)\<close>
by (simp add: atriple_def local.asepconj_assoc local.asepconj_ident local.ucincl_asepconjR)+

(*<*)
end

context cancellative_sepalg begin
(*>*)

lemma atriple_minimal':
    notes sepalg_simps [simp del]
  assumes \<open>is_minimal \<xi> \<sigma>\<close>
      and \<open>has_minimal_splittings \<xi>\<close>
      and \<open>\<sigma>' \<Turnstile> \<psi>\<close>
      and \<open>\<sigma> \<sharp> \<sigma>C\<close>
      and \<open>\<sigma>' \<sharp> \<sigma>C\<close>
      and \<open>\<xi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
    shows \<open>\<xi> \<tturnstile> (\<sigma> + \<sigma>C, \<sigma>' + \<sigma>C) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi>\<close>
proof -
  have \<open>precise (minimal_states \<xi>)\<close> and \<open>\<xi> = (minimal_states \<xi>) \<star> \<top>\<close>
    using assms(2) local.has_minimal_splittings_via_minimal_states by blast+
  {
       fix \<pi>
    assume \<open>ucincl \<pi>\<close>
       and \<open>\<sigma> + \<sigma>C \<Turnstile> \<pi> \<star> \<xi>\<close>
    moreover from this obtain \<tau>0 \<tau>1 where \<open>\<tau>0 \<sharp> \<tau>1\<close> and \<open>\<tau>0 \<Turnstile> \<xi>\<close> \<open>\<tau>1 \<Turnstile> \<pi>\<close> and \<open>\<sigma> + \<sigma>C = \<tau>0 + \<tau>1\<close>
      by (metis local.asepconjE local.asepconj_comm)
    moreover from this obtain \<tau>0' \<tau>0'' where \<open>is_minimal_splitting \<tau>0 \<tau>0' \<tau>0'' \<xi>\<close>
      by (meson assms(2) local.has_minimal_splittingsE)
    moreover from this have \<open>\<tau>0' \<Turnstile> minimal_states \<xi>\<close>
      by (simp add: asat_def local.is_minimal_splitting_is_minimal local.minimal_states_def)
    moreover from calculation have \<open>\<sigma> + \<sigma>C = \<tau>0' + (\<tau>0'' + \<tau>1)\<close>
      using local.is_minimal_splitting_def local.is_splitting_def local.sepalg_assoc
        local.sepalg_pairwise by force
    moreover from calculation and \<open>precise (minimal_states \<xi>)\<close> have \<open>\<sigma> = \<tau>0'\<close>
      by (metis asat_def assms(1) assms(4) local.derived_orderI is_minimal_splitting_def
        is_splitting_def minimal_states_def preciseE local.sepalg_apart_assoc mem_Collect_eq)
    moreover from calculation have \<open>\<tau>0'' + \<tau>1 = \<sigma>C\<close>
      by (metis assms(4) local.disjoint_sym local.is_minimal_splitting_def local.is_splitting_def
        local.sepalg_apart_assoc local.sepalg_cancel local.sepalg_comm)
    ultimately have \<open>(\<sigma>' + \<sigma>C) \<Turnstile> \<pi> \<star> \<psi>\<close>
      by (metis assms(3) assms(5) local.asat_weaken local.asepconjI local.disjoint_sym
        local.is_minimal_splitting_def local.is_splitting_def local.sepalg_comm local.sepalg_pairwise2)
  }
  from this show ?thesis
    by (simp add: local.asepconj_comm local.atriple_def)
qed

(*<*)
end
(*>*)

context
    fixes \<alpha>  :: \<open>'a::{cancellative_sepalg} assert\<close>
      and \<alpha>' :: \<open>'a assert\<close>
      and \<beta>  :: \<open>'a assert\<close>
      and \<beta>' :: \<open>'a assert\<close>
  assumes preciseA:  \<open>has_minimal_splittings \<alpha>\<close>
      and preciseA': \<open>has_minimal_splittings \<alpha>'\<close>
      and preciseB:  \<open>has_minimal_splittings \<beta>\<close>
      and preciseB': \<open>has_minimal_splittings \<beta>'\<close>
    notes local_assms = preciseA preciseA' preciseB preciseB'
begin

lemma is_splitting_refine:
    notes sepalg_simps [simp del]
    fixes \<sigma> :: \<open>'a::{cancellative_sepalg}\<close>
  assumes \<open>is_splitting \<sigma> \<sigma>0 \<sigma>1\<close>
      and \<open>is_splitting \<sigma>0 \<sigma>00 \<sigma>01\<close>
      and \<open>is_splitting \<sigma>1 \<sigma>10 \<sigma>11\<close>
    shows \<open>\<sigma>00 \<sharp> \<sigma>10\<close>
      and \<open>\<sigma>01 \<sharp> \<sigma>11\<close>
      and \<open>is_splitting \<sigma> (\<sigma>00 + \<sigma>10) (\<sigma>01 + \<sigma>11)\<close>
proof -
  have \<open>\<sigma> = \<sigma>0 + \<sigma>1\<close> and \<open>\<sigma>0 = \<sigma>00 + \<sigma>01\<close> and \<open>\<sigma>1 = \<sigma>10 + \<sigma>11\<close>
    using assms is_splitting_def by auto
  moreover have \<open>\<sigma>00 \<sharp> \<sigma>01\<close> and \<open>\<sigma>10 \<sharp> \<sigma>11\<close>
    using assms is_splitting_def by blast+
  moreover show \<open>\<sigma>00 \<sharp> \<sigma>10\<close> and \<open>\<sigma>01 \<sharp> \<sigma>11\<close>
    using sepalg_apart_plus2 sepalg_apart_plus by (metis assms disjoint_sym is_splitting_def)+
  moreover have \<open>\<sigma>00 \<sharp> \<sigma>11\<close> and \<open>\<sigma>01 \<sharp> \<sigma>10\<close>
    using sepalg_apart_plus sepalg_apart_plus2 by (metis assms disjoint_sym is_splitting_def)+
  moreover from calculation have \<open>\<sigma>00 + \<sigma>10 \<sharp> \<sigma>01 + \<sigma>11\<close>
    by (meson disjoint_sym sepalg_pairwise_apart)
  ultimately show \<open>is_splitting \<sigma> (\<sigma>00 + \<sigma>10) (\<sigma>01 + \<sigma>11)\<close>
    by (clarsimp simp add: is_splitting_def; safe) (metis (no_types, opaque_lifting) disjoint_sym
      sepalg_assoc sepalg_comm sepalg_pairwise)
qed

lemma atriple_frame_rev:
    notes sepalg_simps [simp del]
  assumes \<open>assert_strong_disj \<alpha>' \<beta>\<close>
      and \<open>\<alpha> \<star> \<beta> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<alpha>' \<star> \<beta>'\<close>
      and \<open>\<sigma> \<Turnstile> \<alpha> \<star> \<beta>\<close>
  obtains \<sigma>'' where \<open>\<alpha> \<tturnstile> (\<sigma>, \<sigma>'') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<alpha>'\<close> and \<open>\<beta> \<tturnstile> (\<sigma>'', \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<beta>'\<close>
proof -
  from local_assms and assms have \<open>\<sigma>' \<Turnstile> \<alpha>' \<star> \<beta>'\<close>
    by (meson atriple_direct has_minimal_splittingsE ucincl_asepconjL)
  moreover from this and assms obtain \<sigma>A \<sigma>B where \<open>is_splitting \<sigma> \<sigma>A \<sigma>B\<close> and \<open>\<sigma>A \<Turnstile> \<alpha>\<close> and \<open>\<sigma>B \<Turnstile> \<beta>\<close>
    by (metis asepconjE is_splitting_def)
  moreover from this obtain \<sigma>A0 \<sigma>Ac \<sigma>B0 \<sigma>Bc where \<open>is_minimal_splitting \<sigma>A \<sigma>A0 \<sigma>Ac \<alpha>\<close> and
          \<open>is_minimal_splitting \<sigma>B \<sigma>B0 \<sigma>Bc \<beta>\<close>
    by (meson has_minimal_splittings_def preciseA preciseB)
  moreover from this have \<open>is_minimal \<alpha> \<sigma>A0\<close> and \<open>is_minimal \<beta> \<sigma>B0\<close>
    by (simp add: is_minimal_splitting_is_minimal)+
  moreover from calculation have \<open>\<sigma>Ac \<sharp> \<sigma>Bc\<close>
    by (metis disjoint_sym is_minimal_splitting_def is_splitting_def sepalg_apart_plus)
  moreover from calculation have \<open>is_splitting \<sigma> (\<sigma>A0 + \<sigma>B0) (\<sigma>Ac + \<sigma>Bc)\<close>
    by (simp add: is_minimal_splitting_def is_splitting_refine(3))
  moreover from calculation have \<open>\<sigma>A0 + \<sigma>B0 \<Turnstile> \<alpha> \<star> \<beta>\<close>
    by (meson asepconjI is_minimal_splitting_def is_splitting_refine(1))
  moreover from calculation and assms obtain \<sigma>AB0' where \<open>\<sigma>AB0' \<Turnstile> (\<alpha>' \<star> \<beta>') \<star> \<top>\<close> and \<open>\<sigma>AB0' \<sharp> (\<sigma>Ac + \<sigma>Bc)\<close>
        and \<open>\<sigma>' = \<sigma>AB0' + (\<sigma>Ac + \<sigma>Bc)\<close>
    using atriple_complement by blast
  moreover from this obtain \<sigma>A0' and \<sigma>B0' where \<open>\<sigma>A0' \<sharp> \<sigma>B0'\<close> and \<open>\<sigma>AB0' = \<sigma>A0' + \<sigma>B0'\<close> and \<open>\<sigma>A0' \<Turnstile> \<alpha>'\<close>
        and \<open>\<sigma>B0' \<Turnstile> \<beta>'\<close>
    by (metis asepconjE asepconj_strengthenE has_minimal_splittings_def preciseB' ucincl_UNIV ucincl_asepconjR)
  moreover from assms calculation obtain \<sigma>A0'' and C C' where \<open>\<sigma>A0' = \<sigma>A0'' + C\<close> and \<open>\<sigma>A0'' \<sharp> C\<close> and \<open>\<sigma>A0'' \<Turnstile> \<alpha>'\<close>
            and \<open>C' \<preceq> \<sigma>B0\<close> and \<open>C' \<Turnstile> \<beta>\<close> and \<open>\<sigma>A0'' \<sharp> C'\<close>
    using assert_strong_disj_def by (metis asat_def calculation(17) calculation(6) derived_orderE
      is_minimal_splitting_def)
  moreover from this and \<open>is_minimal \<beta> \<sigma>B0\<close> have \<open>C' = \<sigma>B0\<close>
    using is_minimal_def by blast
  moreover from calculation have \<open>\<sigma>A0'' \<sharp> \<sigma>B0'\<close> and \<open>C \<sharp> \<sigma>B0'\<close>
    using sepalg_pairwise by metis+
  moreover from calculation have \<open>\<sigma>B0' + C \<Turnstile> \<beta>'\<close>
    by (meson asat_weaken disjoint_sym has_minimal_splittings_ucincl preciseB')
  moreover have \<open>\<alpha> \<tturnstile> (\<sigma>A0, \<sigma>A0'') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<alpha>'\<close> and \<open>\<beta> \<tturnstile> (\<sigma>B0, \<sigma>B0' + C) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<beta>'\<close>
    by (auto simp add: atriple_minimal calculation)
  moreover from calculation have \<open>\<alpha> \<tturnstile> (\<sigma>A0 + (\<sigma>B0 + \<sigma>Ac + \<sigma>Bc), \<sigma>A0'' + (\<sigma>B0 + \<sigma>Ac + \<sigma>Bc)) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<alpha>'\<close>
    using preciseA by (auto intro!: atriple_minimal' simp add: is_minimal_splitting_def
      is_splitting_def sepalg_pairwise2)
  moreover have \<open>\<sigma>B0 \<sharp> (\<sigma>A0'' + \<sigma>Ac + \<sigma>Bc)\<close>
    using calculation by (metis (no_types, opaque_lifting) disjoint_sym is_minimal_splitting_def
      is_splitting_def sepalg_pairwise2)
  moreover from calculation have \<open>\<sigma>B0' + C \<sharp> (\<sigma>A0'' + \<sigma>Ac + \<sigma>Bc)\<close>
    by (metis (no_types, opaque_lifting) disjoint_sym sepalg_pairwise)
  moreover from calculation have \<open>\<beta> \<tturnstile> (\<sigma>B0 + (\<sigma>A0'' + \<sigma>Ac + \<sigma>Bc), \<sigma>B0' + C + (\<sigma>A0'' + \<sigma>Ac + \<sigma>Bc)) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<beta>'\<close>
    using preciseA by (auto simp add: preciseB is_minimal_splitting_def is_splitting_def
      sepalg_pairwise sepalg_pairwise2 intro!: atriple_minimal')
  moreover from calculation have \<open>\<sigma>B0' + C + (\<sigma>A0'' + \<sigma>Ac + \<sigma>Bc) = \<sigma>'\<close>
    by (metis (no_types, lifting) disjoint_sym sepalg_apart_plus sepalg_assoc sepalg_comm)
  moreover from calculation have \<open>\<sigma>A0'' + (\<sigma>B0 + \<sigma>Ac + \<sigma>Bc) = \<sigma>B0 + (\<sigma>A0'' + \<sigma>Ac + \<sigma>Bc)\<close> (is \<open>?a = ?b\<close>)
  proof -
    have \<open>?a = (\<sigma>A0'' + \<sigma>B0) + (\<sigma>Ac + \<sigma>Bc)\<close>
      using calculation by (metis disjoint_sym sepalg_assoc sepalg_pairwise2)
    also have \<open>... = (\<sigma>B0 + \<sigma>A0'') + (\<sigma>Ac + \<sigma>Bc)\<close>
      using \<open>C' = \<sigma>B0\<close> \<open>\<sigma>A0'' \<sharp> C'\<close> sepalg_comm by fastforce
    also from calculation have \<open>... = ?b\<close>
      by (metis (no_types, lifting) \<open>C \<sharp> \<sigma>B0'\<close> \<open>\<sigma>A0' = \<sigma>A0'' + C\<close> \<open>\<sigma>A0'' \<sharp> C\<close> \<open>\<sigma>A0'' \<sharp> \<sigma>B0'\<close>
        \<open>\<sigma>AB0' = \<sigma>A0' + \<sigma>B0'\<close> \<open>\<sigma>AB0' \<sharp> \<sigma>Ac + \<sigma>Bc\<close> \<open>\<sigma>Ac \<sharp> \<sigma>Bc\<close> \<open>\<sigma>B0 \<sharp> \<sigma>A0'' + \<sigma>Ac + \<sigma>Bc\<close>
        sepalg_assoc sepalg_pairwise sepalg_pairwise2)
    finally show ?thesis
      by auto
  qed
  moreover from calculation have \<open>\<sigma>A0 + (\<sigma>B0 + \<sigma>Ac + \<sigma>Bc) = \<sigma>\<close>
    by (simp add: is_minimal_splitting_def is_splitting_def sepalg_assoc sepalg_pairwise2)
  moreover from calculation have \<open>\<alpha> \<tturnstile> (\<sigma>, \<sigma>A0'' + (\<sigma>B0 + \<sigma>Ac + \<sigma>Bc)) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<alpha>'\<close> and
          \<open>\<beta> \<tturnstile> (\<sigma>A0'' + (\<sigma>B0 + \<sigma>Ac + \<sigma>Bc), \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<beta>'\<close>
    by fastforce+
  ultimately show ?thesis
    using that by blast
qed

(*<*)
end

context sepalg
begin
(*>*)

definition atriple_rel :: \<open>'a assert \<Rightarrow> ('a \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'a assert) \<Rightarrow> bool\<close>
      ("(_) \<turnstile>/ _/ \<stileturn>\<^sub>R (_)" [50,50,50]50) where
  \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi> \<equiv> is_local R \<phi> \<and> (\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<longrightarrow> \<sigma>' \<Turnstile> \<psi> v \<star> \<top>)\<close>

definition atriple_rel_id :: \<open>'a assert \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close> ("_\<sim>_") where
  \<open>\<xi>\<sim>P \<equiv> is_local0 P \<xi> \<and> (\<forall>\<sigma> \<sigma>'. \<sigma> \<Turnstile> \<xi> \<longrightarrow> P \<sigma> \<sigma>' \<longrightarrow> \<sigma>' \<Turnstile> \<xi>)\<close>

definition atriple_rel_ind :: \<open>'a assert \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool) \<Rightarrow>
      ('t \<Rightarrow> 'a assert) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close> ("(_:_) \<tturnstile>\<^sub>i/ _/ \<stileturn> (_:_)" [50,50,50]50) where
  \<open>(\<phi>:P \<tturnstile>\<^sub>i R \<stileturn> \<psi>:Q) \<equiv> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<and> (\<phi>\<sim>P) \<and> (\<forall>v. ((\<psi> v)\<sim>Q))
      \<and> (\<forall>\<sigma>0 \<sigma>1 \<sigma>0' \<sigma>1' v0 v1.
            P \<sigma>0 \<sigma>1 \<longrightarrow> R \<sigma>0 (v0, \<sigma>0') \<longrightarrow> R \<sigma>1 (v1, \<sigma>1') \<longrightarrow> v0 = v1 \<and> Q \<sigma>0' \<sigma>1')\<close>

lemma atriple_local:
  assumes \<open>is_local R \<phi>\<close>
      and  \<open>\<And>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<psi> v\<close>
      and \<open>R \<sigma> (v, \<sigma>')\<close>
    shows \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v\<close>
using assms by (clarsimp simp add: is_local_def atriple_def asat_def asepconj_def) (metis local.disjoint_sym)

lemma atriple_local':
  assumes \<open>is_local R \<phi>\<close>
      and  \<open>\<And>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<Longrightarrow> \<sigma> \<Turnstile> \<phi> \<Longrightarrow> \<sigma>' \<Turnstile> \<psi> v \<star> \<top>\<close>
      and \<open>R \<sigma> (v, \<sigma>')\<close>
    shows \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> v\<close>
proof -
  from assms have \<open>\<phi> \<tturnstile> (\<sigma>, \<sigma>') \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. \<psi> v \<star> \<top>) v\<close>
    by (intro atriple_local[where R=R]; simp)
  from this show ?thesis
    using atriple_upwards_closure(5) by blast
qed

lemma atriple_rel_upwards_closure:
  shows \<open>(\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<longleftrightarrow> (\<phi> \<star> \<top> \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<psi> v \<star> \<top>))\<close>
proof
  assume \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
  moreover {
       fix \<sigma> v \<sigma>'
    assume \<open>is_local R \<phi>\<close>
       and \<open>\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<longrightarrow> \<sigma>' \<Turnstile> \<psi> v \<star> UNIV\<close>
       and \<open>R \<sigma> (v, \<sigma>')\<close>
       and \<open>\<sigma> \<Turnstile> \<phi> \<star> UNIV\<close>
    from this calculation have \<open>\<sigma>' \<Turnstile> \<psi> v \<star> UNIV\<close>
      by (metis atriple_local' local.atripleE local.ucincl_UNIV)
  }
  ultimately show \<open>\<phi> \<star> \<top> \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<psi> v \<star> \<top>)\<close>
    by (auto simp add: atriple_rel_def is_local_upwards_closure asepconj_simp)
next
  assume \<open>\<phi> \<star> UNIV \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<psi> v \<star> UNIV)\<close>
  moreover {
       fix \<sigma> \<sigma>' v
    assume \<open>is_local R \<phi>\<close>
       and \<open>\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<star> UNIV \<longrightarrow> \<sigma>' \<Turnstile> \<psi> v \<star> UNIV\<close>
       and \<open>R \<sigma> (v, \<sigma>')\<close>
       and \<open>\<sigma> \<Turnstile> \<phi>\<close>
    from this have \<open>\<sigma>' \<Turnstile> \<psi> v \<star> UNIV\<close>
      by (simp add: local.asepconj_weakenI)
  }
  ultimately show \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
    by (clarsimp simp add: atriple_rel_def is_local_upwards_closure asepconj_simp)
qed

lemma atriple_rel_hoist_pure:
  shows \<open>(\<phi> \<star> \<langle>P\<rangle> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>))\<close>
    and \<open>(\<langle>P\<rangle> \<star> \<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>))\<close>
proof -
  {
    assume \<open>\<phi> \<star> \<langle>P\<rangle> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
       and \<open>P\<close>
    from this have \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
      by (simp add: atriple_rel_def local.asepconj_False_True(2) local.asepconj_comm
        local.asepconj_weaken2I local.is_local_upwards_closure(2))
  } moreover {
    assume \<open>\<not> P\<close>
    from this have \<open>\<phi> \<star> \<langle>P\<rangle> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
      by (simp add: atriple_rel_def local.asat_apure_distrib'(1) local.is_local_hoist_pure)
  } moreover {
    assume \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
    from this have \<open>\<phi> \<star> \<langle>P\<rangle> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
      by (clarsimp simp add: atriple_rel_def apure_def asepconj_simp)
        (metis atriple_local' local.atripleE local.is_local_empty local.is_local_frame local.ucincl_UNIV)
  }
  ultimately show \<open>(\<phi> \<star> \<langle>P\<rangle> \<turnstile> R \<stileturn>\<^sub>R \<psi>) = (P \<longrightarrow> \<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    by auto
  from this show \<open>(\<langle>P\<rangle> \<star> \<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<longleftrightarrow> (P \<longrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>))\<close>
    by (simp add: asepconj_comm)
qed

lemma atriple_rel_upwards_closure':
  shows \<open>((\<phi> \<star> \<top>) \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<psi> v \<star> \<top>)) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>((\<top> \<star> \<phi>) \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<top> \<star> \<psi> v)) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>((\<phi> \<star> \<top>) \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<top> \<star> \<psi> v)) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>((\<top> \<star> \<phi>) \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<psi> v \<star> \<top>)) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>(\<phi> \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<psi> v \<star> \<top>)) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>(\<phi> \<star> \<top> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>(\<phi> \<turnstile> R \<stileturn>\<^sub>R (\<lambda>v. \<top> \<star> \<psi> v)) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
    and \<open>(\<top> \<star> \<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>) \<longleftrightarrow> (\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>)\<close>
by (rewrite at "\<hole> \<longleftrightarrow> _" atriple_rel_upwards_closure, rewrite at "_ \<longleftrightarrow>  \<hole>"
  atriple_rel_upwards_closure, simp add: asepconj_simp asepconj_comm asepconj_UNIV_collapse_top)+

lemma atriple_rel_bind:
    fixes \<phi> :: \<open>'a assert\<close>
      and \<psi> :: \<open>'v \<Rightarrow> 'a assert\<close>
      and R :: \<open>'a \<Rightarrow> ('v \<times> 'a) \<Rightarrow> bool\<close>
      and S :: \<open>'v \<Rightarrow> 'a \<Rightarrow> ('w \<times> 'a) \<Rightarrow> bool\<close>
  assumes A: \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
      and B: \<open>\<And>v. (\<psi> v \<turnstile> S v \<stileturn>\<^sub>R \<tau>)\<close>
    shows \<open>\<phi> \<turnstile> R \<lozenge> S \<stileturn>\<^sub>R \<tau>\<close>
proof -
  from assms have \<open>\<And>v. (\<psi> v \<star> \<top> \<turnstile> S v \<stileturn>\<^sub>R \<tau>)\<close>
    by (metis atriple_rel_upwards_closure local.asepconj_UNIV_idempotent local.asepconj_assoc)
  moreover {
    assume \<section>: \<open>(\<And>v. is_local (S v) (\<psi> v \<star> UNIV) \<and> (\<forall>\<sigma> \<sigma>' va. S v \<sigma> (va, \<sigma>') \<longrightarrow> \<sigma> \<in> \<psi> v \<star> UNIV \<longrightarrow> \<sigma>' \<in> \<tau> va \<star> UNIV))\<close>
        and \<open>is_local R \<phi>\<close>
        and \<open>\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longrightarrow> \<sigma> \<in> \<phi> \<longrightarrow> \<sigma>' \<in> \<psi> v \<star> UNIV\<close>
    moreover {
         fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v
      assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
         and \<open>\<sigma>_0 \<Turnstile> \<phi>\<close>
         and \<open>(R \<lozenge> S) \<sigma>_0 (v, \<sigma>_0')\<close>
      with assms \<section> have \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close> 
        unfolding rel_compose_def atriple_rel_def is_local_def by meson
    } moreover {
         fix \<sigma>_0 \<sigma>_1 v \<sigma>'
      assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
         and \<open>\<sigma>_0 \<Turnstile> \<phi>\<close>
         and \<open>(R \<lozenge> S) (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')\<close>
      with assms \<section> have \<open>\<exists>\<sigma>_0'. (R \<lozenge> S) \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
        unfolding rel_compose_def atriple_rel_def is_local_def by (smt (verit, best))
    } moreover {
         fix \<sigma>_0 \<sigma>_1 v \<sigma>_0' \<sigma>'
      assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
         and \<open>\<sigma>_0 \<Turnstile> \<phi>\<close>
         and \<open>(R \<lozenge> S) \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
      with assms \<section> have \<open>(R \<lozenge> S) (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')\<close>
        unfolding rel_compose_def atriple_rel_def is_local_def  by (smt (verit, best))
    }
    ultimately have \<open>is_local (R \<lozenge> S) \<phi>\<close>
      by (intro is_localI) 
  } moreover {
       fix \<sigma> \<sigma>' v
    assume \<open>\<And>v. is_local (S v) (\<psi> v) \<and> (\<forall>\<sigma> \<sigma>' va. S v \<sigma> (va, \<sigma>') \<longrightarrow> \<sigma> \<in> \<psi> v \<longrightarrow> \<sigma>' \<in> \<tau> va \<star> UNIV)\<close>
       and \<open>is_local R \<phi>\<close>
       and \<open>\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longrightarrow> \<sigma> \<in> \<phi> \<longrightarrow> \<sigma>' \<in> \<psi> v \<star> UNIV\<close>
       and \<open>(R \<lozenge> S) \<sigma> (v, \<sigma>')\<close>
       and \<open>\<sigma> \<in> \<phi>\<close>
    from this calculation have \<open>\<sigma>' \<in> \<tau> v \<star> UNIV\<close>
      by (metis asat_def atriple_rel_def rel_compose_def)
  }
  ultimately show ?thesis
    using assms by (auto simp add: atriple_rel_def asat_def)
qed

lemma atriple_rel_disj:
  assumes \<open>\<phi> \<turnstile> R \<stileturn>\<^sub>R \<psi>\<close>
      and \<open>\<phi> \<turnstile> S \<stileturn>\<^sub>R \<psi>\<close>
    shows \<open>\<phi> \<turnstile> (\<lambda>a b. R a b \<or> S a b) \<stileturn>\<^sub>R \<psi>\<close>
using assms by (clarsimp simp add: atriple_rel_def is_local_disj)

(*<*)
end

end
(*>*)
