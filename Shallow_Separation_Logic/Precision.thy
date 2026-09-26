(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Precision
  imports Assertion_Language
begin

(*<*)
context sepalg begin
(*>*)

text\<open>Suppose \<^term>\<open>\<xi>\<close> is an upwards-closed assertion; intuitively, we will think of it as describing
all states owning a given resource, and potentially also prescribing the state of the resource.
In this situation, given a state \<^term>\<open>\<sigma>\<close>, one can ask whether there is a \<^emph>\<open>minimal\<close> substate \<^term>\<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n\<close>
of \<^term>\<open>\<sigma>\<close> still satisfying \<^term>\<open>\<xi>\<close>. If so, we think of \<^term>\<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n\<close> as the 'restriction' of
\<^term>\<open>\<sigma>\<close> to (the resource described by) \<^term>\<open>\<xi>\<close>, and if \<^term>\<open>\<sigma>\<close> decomposes as \<^term>\<open>\<sigma> = \<sigma>\<^sub>m\<^sub>i\<^sub>n + \<sigma>'\<close>,
we think of \<^term>\<open>\<sigma>'\<close> as the 'complement' of \<^term>\<open>\<sigma>\<close> with respect to \<^term>\<open>\<xi>\<close>.

Formally, given a term\<^term>\<open>\<sigma>\<close> satisfying \<^term>\<open>\<sigma> \<Turnstile> \<phi>\<close>, we consider decompositions
\<^term>\<open>\<sigma> = \<sigma>\<^sub>0 + \<sigma>\<^sub>1\<close> with \<^term>\<open>\<sigma>\<^sub>0 \<Turnstile> \<xi>\<close>, and ask whether there is a minimal one with respect to \<^term>\<open>(\<preceq>)\<close>:\<close>

definition is_splitting :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>is_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<equiv> \<sigma> = \<sigma>\<^sub>1 + \<sigma>\<^sub>2 \<and> \<sigma>\<^sub>1 \<sharp> \<sigma>\<^sub>2\<close>

definition is_minimal_splitting :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a assert \<Rightarrow> bool\<close> where
  \<open>is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi> \<equiv>
     is_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<and> \<sigma>\<^sub>1 \<Turnstile> \<xi> \<and>
     (\<forall>\<sigma>\<^sub>1' \<sigma>\<^sub>2'. is_splitting \<sigma> \<sigma>\<^sub>1' \<sigma>\<^sub>2' \<and> \<sigma>\<^sub>1' \<Turnstile> \<xi> \<longrightarrow> \<sigma>\<^sub>1 \<preceq> \<sigma>\<^sub>1' \<and> \<sigma>\<^sub>2' \<preceq> \<sigma>\<^sub>2)\<close>

text\<open>In general, a minimal splitting need not exist. Moreover, even if it exists, its components
are only unique up to \<^term>\<open>(\<preceq>)\<close>-equivalence.\<close>

definition has_minimal_splittings :: \<open>'a assert \<Rightarrow> bool\<close> where
  \<open>has_minimal_splittings \<xi> \<equiv> ucincl \<xi> \<and> (\<forall>\<sigma>. \<sigma> \<Turnstile> \<xi> \<longrightarrow> (\<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>))\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma has_minimal_splittingsI:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>\<And>\<sigma>. \<sigma> \<Turnstile> \<xi> \<Longrightarrow> \<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>\<close>
    shows \<open>has_minimal_splittings \<xi>\<close>
using assms by (auto simp add: has_minimal_splittings_def)

lemma has_minimal_splittingsE:
  assumes \<open>has_minimal_splittings \<xi>\<close>
      and \<open>ucincl \<xi> \<Longrightarrow> (\<And>\<sigma>. \<sigma> \<Turnstile> \<xi> \<Longrightarrow> \<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<xi>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: has_minimal_splittings_def)

subsection\<open>Precise assertions\<close>

text \<open>The existence of minimal splittings is closely related to the notion of \<^emph>\<open>precision\<close>
for assertions. An assertion is \<^emph>\<open>precise\<close> if every state has at most one substate satisfying it:\<close>

definition precise :: \<open>'a assert \<Rightarrow> bool\<close> where
  \<open>precise \<phi> \<longleftrightarrow> (\<forall>\<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>. \<sigma>\<^sub>1 \<preceq> \<sigma> \<longrightarrow> \<sigma>\<^sub>2 \<preceq> \<sigma> \<longrightarrow> \<sigma>\<^sub>1 \<Turnstile> \<phi> \<longrightarrow> \<sigma>\<^sub>2 \<Turnstile> \<phi> \<longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2)\<close>

theorem precise_alt:
  shows \<open>precise \<xi> \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2. \<sigma>1 \<Turnstile> \<xi> \<longrightarrow> \<sigma>2 \<Turnstile> \<xi> \<longrightarrow> \<sigma>1 \<noteq> \<sigma>2 \<longrightarrow> (\<up>\<^sub>s \<sigma>1) \<sqinter> (\<up>\<^sub>s \<sigma>2) = \<bottom>)\<close>
by (auto simp add: precise_def asat_def derived_order_def uc_state_def)

text \<open>Precision and upwards closure pull in opposite directions: a precise assertion in the above
sense is rarely upwards closed, and if it is, it can only consist of \<^verbatim>\<open>\<preceq>\<close>-maximal elements:\<close>

lemma precise_ucincl:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>precise \<phi> \<longleftrightarrow> (\<forall>\<sigma>. \<sigma> \<Turnstile> \<phi> \<longrightarrow> \<up>\<^sub>s \<sigma> = {\<sigma>})\<close>
using assms  by (clarsimp simp add: precise_def uc_state_def ucincl_def ucpred_def asat_def; safe)
  (metis (mono_tags) local.derived_order_refl CollectI singletonD)+

lemma preciseI:
  assumes \<open>\<And>\<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>. \<sigma>\<^sub>1 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>2 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>1 \<Turnstile> \<phi> \<Longrightarrow> \<sigma>\<^sub>2 \<Turnstile> \<phi> \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2\<close>
    shows \<open>precise \<phi>\<close>
using assms by (auto simp add: precise_def)

lemma preciseE:
  assumes \<open>precise \<phi>\<close>
      and \<open>(\<And>\<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>. \<sigma>\<^sub>1 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>2 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>1 \<Turnstile> \<phi> \<Longrightarrow> \<sigma>\<^sub>2 \<Turnstile> \<phi> \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: precise_def)

text \<open>Basic properties of precision:\<close>

lemma singleton_set_precise:
  shows \<open>precise {\<sigma>}\<close>
by (auto simp add: precise_def derived_order_def asat_def)

lemma empty_set_precise:
  shows \<open>precise {}\<close>
by (auto simp add: precise_def)

text \<open>The empty assertion has a unique satisfying substate.\<close>
corollary emp_precise:
  shows \<open>precise emp\<close>
by (simp add: emp_def singleton_set_precise)

text \<open>Semantic precision means uniqueness of satisfying substates and is
independent of the zero-ownership convention in \<^term>\<open>apure_precise\<close>.\<close>
corollary apure_precise_is_precise:
  shows \<open>precise \<langle>P\<rangle>\<close>
by (simp add: precise_def asat_apure_precise_characterisation)

lemma conjunction_preserves_precise:
  assumes \<open>precise \<phi>\<close>
      and \<open>precise \<psi>\<close>
    shows \<open>precise (\<phi> \<sqinter> \<psi>)\<close>
using assms by (clarsimp simp add: precise_def)

lemma asepconj_preserves_precise:
    fixes \<phi> :: \<open>'a assert\<close>
  assumes \<open>precise \<phi>\<close>
      and \<open>precise \<psi>\<close>
    shows \<open>precise (\<phi> \<star> \<psi>)\<close>
using assms by (clarsimp simp add: precise_def asepconj_def asat_def) (metis local.derived_orderI
  local.derived_order_trans local.disjoint_sym local.sepalg_comm)

(*<*)
end
(*>*)

(*<*)
context cancellative_sepalg begin
(*>*)

text \<open>In a cancellative separation algebra, \<^verbatim>\<open>\<preceq>\<close>-equivalent states are equal:\<close>

lemma cancellative_derived_order_equiv:
  assumes \<open>\<sigma>A \<preceq> \<sigma>B\<close>
      and \<open>\<sigma>B \<preceq> \<sigma>A\<close>
    shows \<open>\<sigma>A = \<sigma>B\<close>
proof -
  from assms obtain \<alpha> \<beta> where \<open>\<sigma>B = \<sigma>A + \<alpha>\<close> and \<open>\<sigma>A = \<sigma>B + \<beta>\<close> and \<open>\<sigma>A \<sharp> \<alpha>\<close> and \<open>\<sigma>B \<sharp> \<beta>\<close>
    by (metis local.derived_order_def)
  moreover from this have \<open>\<sigma>A = \<sigma>A + (\<alpha> + \<beta>)\<close>
    by (metis disjoint_sym reflE sepalg_apart_plus2 sepalg_comm sepalg_ident)
  moreover from calculation assms and sepalg_cancel have \<open>0 = \<alpha> + \<beta>\<close>
    by (metis local.sepalg_apart_assoc local.sepalg_apart_plus local.unique)
  moreover from calculation have \<open>\<alpha> = 0\<close> and \<open>\<beta> = 0\<close>
    by (metis local.disjoint_sym local.reflE local.sepalg_apart_plus2 local.sepalg_comm)+
  from \<open>\<sigma>A = \<sigma>B + \<beta>\<close> and \<open>\<beta> = 0\<close> show ?thesis
    by auto
qed

lemma cancellative_alt:
  assumes \<open>\<sigma>\<^sub>1 + \<sigma>\<^sub>2 = \<sigma>\<^sub>1' + \<sigma>\<^sub>2'\<close>
      and \<open>\<sigma>\<^sub>1 \<sharp> \<sigma>\<^sub>2\<close>
      and \<open>\<sigma>\<^sub>1' \<sharp> \<sigma>\<^sub>2'\<close>
      and \<open>\<sigma>\<^sub>1 \<preceq> \<sigma>\<^sub>1'\<close>
    shows \<open>\<sigma>\<^sub>2' \<preceq> \<sigma>\<^sub>2\<close>
proof -
  from assms obtain \<sigma>\<^sub>1'' where \<open>\<sigma>\<^sub>1' = \<sigma>\<^sub>1 + \<sigma>\<^sub>1''\<close> and \<open>\<sigma>\<^sub>1 \<sharp> \<sigma>\<^sub>1''\<close>
    by blast
  moreover from this and assms have \<open>\<sigma>\<^sub>1 + \<sigma>\<^sub>2 = \<sigma>\<^sub>1 + (\<sigma>\<^sub>1'' + \<sigma>\<^sub>2')\<close>
    by (metis local.disjoint_sym local.sepalg_apart_plus local.sepalg_assoc local.sepalg_comm)
  moreover from assms and calculation have \<open>\<sigma>\<^sub>2 = \<sigma>\<^sub>1'' + \<sigma>\<^sub>2'\<close>
    by (metis disjoint_sym sepalg_apart_assoc sepalg_cancel sepalg_comm)
  ultimately show ?thesis
    by (metis assms(3) derived_orderI disjoint_sym sepalg_apart_plus2 sepalg_comm)
qed

subsection \<open>Precision and intersection stability\<close>

text \<open>Next, we establish an alternative description of precision: An assertion is precise
if and only if its \<^verbatim>\<open>\<star>\<close> commutes with intersections:\<close>

lemma precise_asepconj_distrib1:
  assumes \<open>precise \<xi>\<close>
    shows \<open>(\<phi> \<sqinter> \<psi>) \<star> \<xi> = (\<phi> \<star> \<xi>) \<sqinter> (\<psi> \<star> \<xi>)\<close>
proof (intro equalityI subsetI)
  fix x
  assume \<open>x \<in> (\<phi> \<inter> \<psi>) \<star> \<xi>\<close>
  from this obtain t u where \<open>x = t + u\<close> and \<open>t \<sharp> u\<close> and \<open>t \<in> \<phi>\<close> and \<open>t \<in> \<psi>\<close> and \<open>u \<in> \<xi>\<close>
    by (auto simp add: asepconj_def asat_def)
  moreover from assms have \<open>\<And>\<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>. \<sigma>\<^sub>1 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>2 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>1 \<Turnstile> \<xi> \<Longrightarrow> \<sigma>\<^sub>2 \<Turnstile> \<xi> \<longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2\<close>
    by (auto simp add: precise_def)
  ultimately show \<open>x \<in> (\<phi> \<star> \<xi>) \<inter> (\<psi> \<star> \<xi>)\<close>
    by (auto simp add: precise_def asepconj_def asat_def)
next
  fix x
  assume \<open>x \<in> (\<phi> \<star> \<xi>) \<inter> (\<psi> \<star> \<xi>)\<close>
  from this have \<open>x \<in> \<phi> \<star> \<xi>\<close> and \<open>x \<in> \<psi> \<star> \<xi>\<close>
    by auto
  moreover from this obtain s t u v where \<open>x = s + t\<close> \<open>x = u + v\<close> and \<open>s \<sharp> t\<close> \<open>u \<sharp> v\<close> and \<open>s \<in> \<phi>\<close> \<open>t \<in> \<xi>\<close> and
        \<open>u \<in> \<psi>\<close> \<open>v \<in> \<xi>\<close>
    by (clarsimp simp add: asepconj_def asat_def) metis
  moreover from assms have \<open>\<And>\<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>. \<sigma>\<^sub>1 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>2 \<preceq> \<sigma> \<Longrightarrow> \<sigma>\<^sub>1 \<Turnstile> \<xi> \<Longrightarrow> \<sigma>\<^sub>2 \<Turnstile> \<xi> \<longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2\<close>
    by (auto simp add: precise_def)
  moreover from calculation have \<open>t = v\<close>
    by (metis asat_def local.derived_orderI local.disjoint_sym local.sepalg_comm)
  moreover from calculation have \<open>s = u\<close>
    using local.sepalg_cancel_iff by blast
  ultimately show \<open>x \<in> \<phi> \<inter> \<psi> \<star> \<xi>\<close>
    by (auto simp add: precise_def asepconj_def asat_def)
qed

lemma precise_asepconj_distrib2:
  assumes \<open>\<And>\<phi> \<psi>. (\<phi> \<sqinter> \<psi>) \<star> \<xi> = (\<phi> \<star> \<xi>) \<sqinter> (\<psi> \<star> \<xi>)\<close>
    shows \<open>precise \<xi>\<close>
proof (intro preciseI)
     fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>
  assume \<open>\<sigma>\<^sub>1 \<preceq> \<sigma>\<close>
     and \<open>\<sigma>\<^sub>2 \<preceq> \<sigma>\<close>
     and \<open>\<sigma>\<^sub>1 \<Turnstile> \<xi>\<close>
     and \<open>\<sigma>\<^sub>2 \<Turnstile> \<xi>\<close>
  moreover from this obtain \<sigma>\<^sub>1' \<sigma>\<^sub>2' where \<open>\<sigma>\<^sub>1 + \<sigma>\<^sub>1' = \<sigma>\<close> and \<open>\<sigma>\<^sub>2 + \<sigma>\<^sub>2' = \<sigma>\<close> and \<open>\<sigma>\<^sub>1 \<sharp> \<sigma>\<^sub>1'\<close> and \<open>\<sigma>\<^sub>2 \<sharp> \<sigma>\<^sub>2'\<close>
    by (auto simp add: derived_order_def)
  moreover from this and calculation have \<open>\<sigma>\<^sub>1' + \<sigma>\<^sub>1 \<Turnstile> {\<sigma>\<^sub>1'} \<star> \<xi>\<close> and \<open>\<sigma>\<^sub>2' + \<sigma>\<^sub>2 \<Turnstile> {\<sigma>\<^sub>2'} \<star> \<xi>\<close>
    by (meson asat_def local.asepconjI local.disjoint_sym singletonI)+
  moreover from this and calculation have \<open>\<sigma> \<Turnstile> ({\<sigma>\<^sub>1'} \<star> \<xi>) \<sqinter> ({\<sigma>\<^sub>2'} \<star> \<xi>)\<close>
    by auto
  moreover from this and assms have \<open>\<sigma> \<Turnstile> ({\<sigma>\<^sub>1'} \<sqinter> {\<sigma>\<^sub>2'}) \<star> \<xi>\<close>
    by auto
  ultimately show \<open>\<sigma>\<^sub>1 = \<sigma>\<^sub>2\<close>
    by (metis Int_insert_right_if0 asat_connectives_characterisation(2) inf_bot_right insertE
          insert_absorb local.asepconjE local.sepalg_cancel)
qed

theorem precise_asepconj_distrib:
  shows \<open>precise \<xi> \<longleftrightarrow> (\<forall>\<phi> \<psi>. (\<phi> \<sqinter> \<psi>) \<star> \<xi> = (\<phi> \<star> \<xi>) \<sqinter> (\<psi> \<star> \<xi>))\<close>
using precise_asepconj_distrib1 precise_asepconj_distrib2 by blast

subsection \<open>Precision and existence of minimal splittings\<close>

text \<open>The goal of this section is to connect the notion of precision to the existence of
minimal splittings: An assertion has minimal splittings if and only if it is the upwards
closure of a precise assertion. Moreover, the precise 'core' of an assertion with minimal
splittings can be obtained as the sub-assertion of \<^emph>\<open>minimal states\<close>, in the following sense:\<close>

(*<*)
end

context sepalg begin
(*>*)

definition is_minimal :: \<open>'a assert \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>is_minimal \<xi> \<sigma> \<equiv> \<sigma> \<Turnstile> \<xi> \<and> (\<forall>\<sigma>'. \<sigma>' \<preceq> \<sigma> \<longrightarrow> \<sigma>' \<Turnstile> \<xi> \<longrightarrow> \<sigma> = \<sigma>')\<close>

definition minimal_states :: \<open>'a assert \<Rightarrow> 'a assert\<close> where
  \<open>minimal_states \<xi> \<equiv> { \<sigma>. is_minimal \<xi> \<sigma> }\<close>

(*<*)
end

context cancellative_sepalg begin
(*>*)

lemma minimal_states_ucincl:
  shows \<open>minimal_states (\<xi> \<star> \<top>) = minimal_states \<xi>\<close>
proof (intro aentails_eq)
  show \<open>minimal_states \<xi> \<longlongrightarrow> minimal_states (\<xi> \<star> \<top>)\<close>
    by (clarsimp simp add: aentails_def minimal_states_def asepconj_def asat_def is_minimal_def)
        (metis cancellative_derived_order_equiv local.derived_orderI local.derived_order_trans
          local.sepalg_ident2 local.zero_disjoint)
next
  show \<open>minimal_states (\<xi> \<star> \<top>) \<longlongrightarrow> minimal_states \<xi>\<close>
    by (clarsimp simp add: aentails_def minimal_states_def asepconj_def asat_def is_minimal_def)
        (metis local.derived_order_def local.derived_order_refl)
qed

lemma is_minimal_precise:
  assumes \<open>precise \<xi>\<close>
    shows \<open>minimal_states \<xi> = \<xi>\<close>
using assms by (auto simp add: minimal_states_def is_minimal_def precise_def asat_def) (meson local.derived_order_refl)

lemma is_minimal_precise_ucincl:
  assumes \<open>precise \<xi>\<close>
    shows \<open>minimal_states (\<xi> \<star> \<top>) = \<xi>\<close>
by (simp add: assms is_minimal_precise minimal_states_ucincl)

lemma splitting_is_minimal_for_principal:
  assumes \<open>is_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2\<close>
    shows \<open>is_minimal_splitting \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 (\<up>\<^sub>s \<sigma>\<^sub>1)\<close>
using assms by (auto simp add: is_splitting_def is_minimal_splitting_def uc_state_def asat_def
  cancellative_alt)

lemma is_principal_implies_precise:
  assumes \<open>is_principal \<xi>\<close>
    shows \<open>has_minimal_splittings \<xi>\<close>
proof -
  from assms obtain \<sigma> where \<open>\<xi> = \<up>\<^sub>s \<sigma>\<close>
    using local.is_principal_def uc_state_def by auto
  moreover {
       fix \<sigma>'
    assume \<open>\<sigma>' \<Turnstile> \<xi>\<close>
    from this and \<open>\<xi> = \<up>\<^sub>s \<sigma>\<close> obtain \<sigma>'' where \<open>is_splitting \<sigma>' \<sigma> \<sigma>''\<close>
      by (metis asat_def local.derived_orderE local.is_splitting_def local.uc_state_def
        mem_Collect_eq)
    from this and calculation have \<open>is_minimal_splitting \<sigma>' \<sigma> \<sigma>'' \<xi>\<close>
      using splitting_is_minimal_for_principal by simp
    from this have \<open>\<exists>\<alpha> \<beta>. is_minimal_splitting \<sigma>' \<alpha> \<beta> \<xi>\<close>
      by blast
  }
  ultimately show ?thesis
    using assms has_minimal_splittings_def ucincl_principal by blast
qed

lemma is_minimal_splitting_lift_to_union:
  assumes \<open>is_minimal_splitting \<sigma> \<alpha> \<beta> \<xi>\<close>
      and \<open>\<xi> \<sqinter> \<psi> = \<bottom>\<close>
      and \<open>ucincl \<xi>\<close>
      and \<open>ucincl \<psi>\<close>
    shows \<open>is_minimal_splitting \<sigma> \<alpha> \<beta> (\<xi> \<squnion> \<psi>)\<close>
using assms by (clarsimp simp add: is_minimal_splitting_def) (metis
  asat_connectives_characterisation(2) asat_connectives_characterisation(3) local.asat_weaken
  local.is_splitting_def)

lemma has_minimal_splittings_ucincl:
  assumes \<open>has_minimal_splittings \<alpha>\<close>
    shows \<open>ucincl \<alpha>\<close>
using assms local.has_minimal_splittings_def by blast

corollary has_minimal_splittings_union:
  assumes \<open>has_minimal_splittings \<alpha>\<close>
      and \<open>has_minimal_splittings \<beta>\<close>
      and \<open>\<alpha> \<sqinter> \<beta> = \<bottom>\<close>
    shows \<open>has_minimal_splittings (\<alpha> \<squnion> \<beta>)\<close>
using assms is_minimal_splitting_lift_to_union by (clarsimp simp add: has_minimal_splittings_def ucincl_intros)
  (metis inf.commute sup.commute)+

corollary has_minimal_splittings_Union:
  assumes \<open>\<And>i. i\<in>S \<Longrightarrow> has_minimal_splittings (\<xi> i)\<close>
      and \<open>\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> i\<noteq>j \<Longrightarrow> \<xi> i \<sqinter> \<xi> j = \<bottom>\<close>
    shows \<open>has_minimal_splittings (\<Squnion>i\<in>S. \<xi> i)\<close>
proof -
  {
       fix \<sigma>
    assume \<open>\<sigma> \<Turnstile> (\<Squnion>i\<in>S. \<xi> i)\<close>
    from this obtain i where \<open>i\<in>S\<close> and \<open>\<sigma> \<Turnstile> \<xi> i\<close>
      by blast
    moreover from this assms have \<open>has_minimal_splittings (\<xi> i)\<close>
      by blast
    moreover from this calculation obtain \<sigma>A \<sigma>B where \<open>is_minimal_splitting \<sigma> \<sigma>A \<sigma>B (\<xi> i)\<close>
      unfolding has_minimal_splittings_def by blast
    moreover from assms calculation have \<open>\<xi> i \<sqinter> (\<Squnion>j\<in>S-{i}. \<xi> j) = \<bottom>\<close>
      by blast
    moreover have \<open>(\<Squnion>j\<in>S. \<xi> j) = \<xi> i \<squnion> (\<Squnion>j\<in>S-{i}. \<xi> j)\<close>
      using calculation(1) by blast
    ultimately have \<open>is_minimal_splitting \<sigma> \<sigma>A \<sigma>B (\<Squnion>i\<in>S. \<xi> i)\<close>
      by (auto intro!: is_minimal_splitting_lift_to_union ucincl_Un simp add: has_minimal_splittings_ucincl)
        (meson assms(1) has_minimal_splittings_ucincl)
    from this have \<open>\<exists>\<sigma>A \<sigma>B. is_minimal_splitting \<sigma> \<sigma>A \<sigma>B (\<Squnion>i\<in>S. \<xi> i)\<close> by blast
  }
  from this show ?thesis
    by (metis (mono_tags, lifting) assms(1) image_iff local.has_minimal_splittings_def local.ucincl_Un)
qed

corollary precise_to_has_minimal_splittings:
  assumes \<open>precise \<xi>\<close>
    shows \<open>has_minimal_splittings (\<xi> \<star> \<top>)\<close>
using assms uc_state_alt has_minimal_splittings_Union by (metis asat_def is_principal_implies_precise
  local.is_principal_def local.uc_state_def precise_alt)

lemma is_minimal_splitting_upwards_closure:
    notes disjoint_sym [simp del]
  assumes \<open>is_minimal_splitting \<sigma> \<sigma>' \<sigma>'' (\<xi> \<star> \<top>)\<close>
    shows \<open>is_minimal_splitting \<sigma> \<sigma>' \<sigma>'' \<xi>\<close>
proof -
  from assms have \<open>\<sigma> = \<sigma>' + \<sigma>''\<close> and \<open>\<sigma>' \<sharp> \<sigma>''\<close> and \<open>\<sigma>' \<Turnstile> \<xi> \<star> \<top>\<close> and \<open>\<And>\<sigma>\<^sub>1' \<sigma>\<^sub>2'. is_splitting \<sigma> \<sigma>\<^sub>1' \<sigma>\<^sub>2' \<Longrightarrow> \<sigma>\<^sub>1' \<Turnstile> \<xi> \<Longrightarrow> \<sigma>' \<preceq> \<sigma>\<^sub>1' \<and> \<sigma>\<^sub>2' \<preceq> \<sigma>''\<close>
    by - ((clarsimp simp add: asat_def is_minimal_splitting_def is_splitting_def)+,
      metis (full_types) CollectI UN_I local.derived_order_refl local.uc_state_alt local.uc_state_def)
  moreover from calculation obtain t u where \<open>\<sigma>' = t + u\<close> and \<open>t \<sharp> u\<close> and \<open>t \<in> \<xi>\<close> and \<open>u \<in> UNIV\<close>
    by (auto simp add: asepconj_def asat_def)
  moreover from calculation have \<open>t + u \<Turnstile> \<xi>\<close>
    by (clarsimp simp add: asat_def asepconj_def) (metis calculation(1)
      local.cancellative_derived_order_equiv local.derived_orderE local.derived_orderI
      local.derived_order_trans local.is_splitting_def)
  ultimately show ?thesis
    by (clarsimp simp add: is_minimal_splitting_def is_splitting_def)
qed

lemma minimal_states_aentails:
  shows \<open>minimal_states \<xi> \<longlongrightarrow> \<xi>\<close>
by (simp add: aentails_def asat_def is_minimal_def minimal_states_def)

lemma is_minimal_splitting_is_minimal:
    notes sepalg_simps[simp del]
  assumes \<open>is_minimal_splitting \<sigma> \<sigma>' \<sigma>'' \<xi>\<close>
    shows \<open>is_minimal \<xi> \<sigma>'\<close>
using assms by (auto simp add: is_minimal_splitting_def is_minimal_def is_splitting_def asat_def)
  (metis cancellative_derived_order_equiv local.derived_order_def local.derived_order_trans)

lemma has_minimal_splittings_to_precise:
  assumes \<open>has_minimal_splittings \<xi>\<close>
  obtains \<phi> where \<open>precise \<phi>\<close> and \<open>\<xi> = \<phi> \<star> \<top>\<close>
proof -
  let ?\<phi> = \<open>minimal_states \<xi>\<close>
  have \<open>precise ?\<phi>\<close>
  proof -
    {
         fix \<sigma>A \<sigma>B \<sigma>
      assume \<open>\<sigma>A \<preceq> \<sigma>\<close>
         and \<open>\<sigma>B \<preceq> \<sigma>\<close>
         and \<open>\<sigma>A \<Turnstile> ?\<phi>\<close>
         and \<open>\<sigma>B \<Turnstile> ?\<phi>\<close>
      moreover from this obtain \<sigma>A' \<sigma>B' where \<open>is_splitting \<sigma> \<sigma>A \<sigma>A'\<close> and \<open>is_splitting \<sigma> \<sigma>B \<sigma>B'\<close>
        by (metis local.derived_order_def local.is_splitting_def)
      moreover from calculation have \<open>\<sigma>A \<Turnstile> \<xi>\<close> and \<open>\<sigma>B \<Turnstile> \<xi>\<close>
        unfolding minimal_states_def is_minimal_def by (simp add: asat_def)+
      moreover from this and assms obtain \<sigma>' \<sigma>'' where \<open>is_minimal_splitting \<sigma> \<sigma>' \<sigma>'' \<xi>\<close>
        using local.has_minimal_splittings_def by (metis calculation(5) local.asat_weaken local.is_splitting_def)
      moreover from calculation have \<open>\<sigma>A \<preceq> \<sigma>'\<close> and \<open>\<sigma>B \<preceq> \<sigma>'\<close>
        by (metis asat_def is_minimal_def local.is_minimal_splitting_def mem_Collect_eq minimal_states_def)+
      ultimately have \<open>\<sigma>A = \<sigma>'\<close> and \<open>\<sigma>B = \<sigma>'\<close>
        by (simp add: cancellative_derived_order_equiv local.is_minimal_splitting_def)+
      from this have \<open>\<sigma>A = \<sigma>B\<close>
        by auto
    }
    from this show ?thesis
      unfolding precise_def by blast
  qed
  moreover have \<open>?\<phi> \<star> \<top> \<longlongrightarrow> \<xi>\<close>
    by (auto intro!: aentails_uc' minimal_states_aentails simp add: assms has_minimal_splittings_ucincl)
  moreover have \<open>\<xi> \<longlongrightarrow> ?\<phi> \<star> \<top>\<close>
  proof -
    {
         fix \<sigma>
      assume \<open>\<sigma> \<Turnstile> \<xi>\<close>
      then obtain \<sigma>' \<sigma>'' where \<open>is_minimal_splitting \<sigma> \<sigma>' \<sigma>'' \<xi>\<close>
        using assms local.has_minimal_splittings_def by blast
      moreover from this have \<open>is_minimal \<xi> \<sigma>'\<close>
        using is_minimal_splitting_is_minimal by auto
      ultimately have \<open>\<sigma> \<Turnstile> ?\<phi> \<star> \<top>\<close>
        by (auto simp add: uc_state_alt uc_state_def asat_def is_minimal_splitting_def
             is_splitting_def minimal_states_def)
           (metis local.derived_orderI local.disjoint_sym local.sepalg_comm)
    }
    from this show ?thesis
      by (simp add: aentailsI)
  qed
  ultimately show ?thesis
    by (simp add: aentails_eq that)
qed

text \<open>The following theorem summarizes the work of this section: An assertion has minimal splitings
if and only if it is the upwards closure of a precise assertion.\<close>

theorem precise_has_minimal_splittings:
  shows \<open>has_minimal_splittings \<xi> \<longleftrightarrow> (\<exists>\<tau>. precise \<tau> \<and> \<xi> = \<tau> \<star> \<top>)\<close>
by (meson has_minimal_splittings_to_precise precise_to_has_minimal_splittings)

lemma has_minimal_splittings_via_minimal_states:
  shows \<open>has_minimal_splittings \<xi> \<longleftrightarrow> (precise (minimal_states \<xi>) \<and> \<xi> = (minimal_states \<xi>) \<star> \<top>)\<close> (is ?g1)
    and \<open>has_minimal_splittings \<xi> \<longrightarrow> \<xi> = (minimal_states \<xi>) \<star> \<top>\<close> (is ?g2)
using is_minimal_precise_ucincl precise_has_minimal_splittings by auto

text \<open>As a corollary, we obtain that the existence of minimal splittings is stable under \<^verbatim>\<open>(\<star>)\<close>.
This does not appear to be easily proved directly.\<close>

corollary has_minimal_splittings_asepconj:
  assumes \<open>has_minimal_splittings \<xi>\<close>
      and \<open>has_minimal_splittings \<psi>\<close>
    shows \<open>has_minimal_splittings (\<xi> \<star> \<psi>)\<close>
proof -
  from assms obtain \<xi>' and \<psi>' where \<open>precise \<xi>'\<close> and \<open>precise \<psi>'\<close> and \<open>\<xi> = \<xi>' \<star> \<top>\<close>
    and \<open>\<psi> = \<psi>' \<star> \<top>\<close> using precise_has_minimal_splittings by auto
  moreover from this have \<open>precise (\<xi>' \<star> \<psi>')\<close>
    using asepconj_preserves_precise by force
  moreover from calculation have \<open>\<xi> \<star> \<psi> = (\<xi>' \<star> \<psi>') \<star> \<top>\<close>
    using local.asepconj_UNIV_idempotent local.asepconj_assoc local.asepconj_swap_top by auto
  ultimately show ?thesis
    using precise_has_minimal_splittings by blast
qed

lemma is_minimal_asepconj:
    notes sepalg_simps[simp del]
  assumes \<open>\<sigma> \<sharp> \<sigma>'\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>\<sigma>' \<Turnstile> \<psi>\<close>
      and \<open>has_minimal_splittings \<xi>\<close>
      and \<open>has_minimal_splittings \<psi>\<close>
    shows \<open>is_minimal (\<xi> \<star> \<psi>) (\<sigma> + \<sigma>') \<longleftrightarrow> (is_minimal \<xi> \<sigma> \<and> is_minimal \<psi> \<sigma>')\<close>
proof safe
  assume \<open>is_minimal (\<xi> \<star> \<psi>) (\<sigma> + \<sigma>')\<close>
  from this show \<open>is_minimal \<xi> \<sigma>\<close>
    using assms by (auto simp add: is_minimal_def asepconj_def asat_def)
      (metis local.derived_order_distinct_downward_closed local.derived_order_plus_monotone2
      local.disjoint_sym local.sepalg_cancel local.sepalg_comm)
next
  assume \<open>is_minimal (\<xi> \<star> \<psi>) (\<sigma> + \<sigma>')\<close>
  from this show \<open>is_minimal \<psi> \<sigma>'\<close>
    using assms by (auto simp add: is_minimal_def asepconj_def asat_def)
      (metis local.derived_order_distinct_downward_closed local.derived_order_plus_monotone2
      local.disjoint_sym local.sepalg_cancel local.sepalg_comm)
next
  assume \<open>is_minimal \<xi> \<sigma>\<close>
     and \<open>is_minimal \<psi> \<sigma>'\<close>
  moreover obtain \<xi>\<^sub>0 \<psi>\<^sub>0 where \<open>precise \<xi>\<^sub>0\<close> and \<open>precise \<psi>\<^sub>0\<close> and \<open>\<xi> = \<xi>\<^sub>0 \<star> \<top>\<close> and \<open>\<psi> = \<psi>\<^sub>0 \<star> \<top>\<close>
    using assms(4) assms(5) precise_has_minimal_splittings by auto
  moreover from this have \<open>minimal_states (\<xi> \<star> \<psi>) = \<xi>\<^sub>0 \<star> \<psi>\<^sub>0\<close>
    by (metis (full_types) asepconj_preserves_precise is_minimal_precise local.asepconj_assoc
      local.asepconj_comm minimal_states_ucincl)
  moreover from calculation have \<open>\<sigma> \<Turnstile> \<xi>\<^sub>0\<close> and \<open>\<sigma>' \<Turnstile> \<psi>\<^sub>0\<close>
    by (metis asat_def is_minimal_precise_ucincl mem_Collect_eq minimal_states_def)+
  ultimately show \<open>is_minimal (\<xi> \<star> \<psi>) (\<sigma> + \<sigma>')\<close>
    by (metis asat_def assms(1) local.asepconjI mem_Collect_eq minimal_states_def)
qed

corollary minimal_states_asepconj_sub:
  assumes \<open>has_minimal_splittings \<xi>\<close>
      and \<open>has_minimal_splittings \<psi>\<close>
    shows \<open>minimal_states (\<xi> \<star> \<psi>) = { \<sigma>0 + \<sigma>1 | \<sigma>0 \<sigma>1. \<sigma>0 \<Turnstile> minimal_states \<xi> \<and> \<sigma>1 \<Turnstile> minimal_states \<psi> \<and> \<sigma>0 \<sharp> \<sigma>1 }\<close> (is \<open>?a = ?b\<close>)
proof -
  {
       fix \<Sigma>
    assume \<open>\<Sigma> \<Turnstile> minimal_states (\<xi> \<star> \<psi>)\<close>
    moreover from this obtain \<sigma> \<sigma>' where \<open>\<sigma> \<sharp> \<sigma>'\<close> and \<open>\<sigma> \<Turnstile> \<xi>\<close> and \<open>\<sigma>' \<Turnstile> \<psi>\<close>
      and \<open>\<Sigma> = \<sigma> + \<sigma>'\<close>
      by (meson aentailsE local.asepconjE minimal_states_aentails)
    moreover from calculation have \<open>is_minimal \<xi> \<sigma>\<close> and \<open>is_minimal \<psi> \<sigma>'\<close>
      by (metis asat_def assms is_minimal_asepconj local.minimal_states_def mem_Collect_eq)+
    ultimately have \<open>\<Sigma> \<in> { \<sigma>0 + \<sigma>1 | \<sigma>0 \<sigma>1. \<sigma>0 \<Turnstile> minimal_states \<xi> \<and> \<sigma>1 \<Turnstile> minimal_states \<psi> \<and> \<sigma>0 \<sharp> \<sigma>1 }\<close>
      by (metis (mono_tags, lifting) asat_def local.minimal_states_def mem_Collect_eq)
  }
  from this have \<open>?a \<subseteq> ?b\<close>
    by (simp add: asat_def subset_eq)
  moreover have \<open>?b \<subseteq> ?a\<close>
    using assms is_minimal_asepconj by (auto simp add: minimal_states_def asat_def)
      (meson is_minimal_asepconj local.is_minimal_def)
  ultimately show ?thesis
    by auto
qed

lemma assert_strong_disj_has_minimal_splittings:
  assumes \<open>has_minimal_splittings \<xi>\<close>
      and \<open>has_minimal_splittings \<psi>\<close>
    shows \<open>assert_strong_disj \<xi> \<psi> \<longleftrightarrow>
            (\<forall>\<sigma> \<sigma>'. \<sigma> \<Turnstile> minimal_states \<xi> \<longrightarrow> \<sigma>' \<Turnstile> minimal_states \<psi> \<longrightarrow> \<sigma> \<sharp> \<sigma>')\<close> (is \<open>?a \<longleftrightarrow> ?b\<close>)
proof safe
  assume \<open>?b\<close>
  moreover from assms have \<open>\<xi> = (minimal_states \<xi>) \<star> \<top>\<close> and \<open>\<psi> = (minimal_states \<psi>) \<star> \<top>\<close>
    by (auto simp add: has_minimal_splittings_via_minimal_states(2))
  moreover from calculation assms have \<open>assert_strong_disj (minimal_states \<xi>) (minimal_states \<psi>)\<close>
      using assert_strong_disj_pairwise_disj by blast
  ultimately show \<open>assert_strong_disj \<xi> \<psi>\<close>
    by (metis local.assert_strong_disj_upward_closure)
next
     fix \<sigma> \<sigma>'
  assume \<open>?a\<close>
     and \<open>\<sigma> \<Turnstile> minimal_states \<xi>\<close>
     and \<open>\<sigma>' \<Turnstile> minimal_states \<psi>\<close>
  moreover from this obtain \<sigma>0 \<sigma>1 where \<open>\<sigma>0 \<preceq> \<sigma>\<close> and \<open>\<sigma>1 \<preceq> \<sigma>'\<close> and \<open>\<sigma>0 \<Turnstile> \<xi>\<close> and \<open>\<sigma>1 \<Turnstile> \<psi>\<close> and \<open>\<sigma>0 \<sharp> \<sigma>1\<close>
    by (metis aentailsE asat_def local.assert_strong_disj_def minimal_states_aentails)
  moreover from this and \<open>\<sigma> \<Turnstile> minimal_states \<xi>\<close> and \<open>\<sigma>' \<Turnstile> minimal_states \<psi>\<close> have \<open>\<sigma>0 = \<sigma>\<close> and \<open>\<sigma>1 = \<sigma>'\<close>
    by (metis asat_def local.is_minimal_def local.minimal_states_def mem_Collect_eq)+
  ultimately show \<open>\<sigma> \<sharp> \<sigma>'\<close> by auto
qed

lemma assert_strong_disj_asepconj:
  assumes \<open>has_minimal_splittings \<xi>\<close>
      and \<open>has_minimal_splittings \<psi>\<close>
      and \<open>has_minimal_splittings \<tau>\<close>
      and \<open>assert_strong_disj \<xi> \<psi>\<close>
      and \<open>assert_strong_disj \<xi> \<tau>\<close>
    shows \<open>assert_strong_disj \<xi> (\<psi> \<star> \<tau>)\<close>
proof -
  from assms have \<open>has_minimal_splittings (\<psi> \<star> \<tau>)\<close>
    using has_minimal_splittings_asepconj by blast
  from this and assms show ?thesis
    by (auto simp add: assert_strong_disj_has_minimal_splittings minimal_states_asepconj_sub asat_def simp del: sepalg_simps
      simp add: local.sepalg_pairwise2)
qed

(*<*)
end

end
(*>*)
