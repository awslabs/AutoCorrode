(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Assertion_Language
  imports Tree_Shares "HOL-Library.Multiset" Misc.MultisetAdditional
    Misc.SetAdditional "HOL-Eisbach.Eisbach"
begin
(*>*)

section\<open>Assertions as sets of states\<close>

(*<*)
named_theorems asepconj_simp
named_theorems aentails_simp
named_theorems asat_simp

named_theorems aentails_intro
named_theorems asat_intro
(*>*)

text\<open>We model assertions as \<^emph>\<open>sets\<close> of states.  This allows us to inherit a lot of the structure
inherent to HOL sets and reuse this as the basis of our Separation Logic:\<close>
type_synonym 'a assert = \<open>'a set\<close>

subsection\<open>Satisfiability\<close>

text \<open>A state \<^emph>\<open>satisfies\<close> an assertion when that state is within the set of states denoted by the
assertion:\<close>
definition asat :: \<open>'a \<Rightarrow> 'a assert \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) where
  \<open>S \<Turnstile> \<phi> \<longleftrightarrow> S \<in> \<phi>\<close>

text \<open>An assertion is \<^emph>\<open>satisfiable\<close> when there is at least one state that satisfies it:\<close>
definition is_sat :: \<open>'a assert \<Rightarrow> bool\<close> where
  \<open>is_sat \<phi> \<equiv> \<exists>s. s \<Turnstile> \<phi>\<close>

lemma non_is_sat_empty[iff]: "\<not> is_sat {}"
  by (simp add: asat_def is_sat_def)

text \<open>This is an introduction rule for establishing the semantic equivalence of assertions:\<close>
lemma asat_semequivI:
  assumes \<open>\<And>x. x \<Turnstile> \<phi> \<Longrightarrow> x \<Turnstile> \<psi>\<close>
      and \<open>\<And>x. x \<Turnstile> \<psi> \<Longrightarrow> x \<Turnstile> \<phi>\<close>
    shows \<open>\<phi> = \<psi>\<close>
  using assms by (auto simp add: asat_def)

lemma asat_insert [simp]: \<open>p \<Turnstile> insert p \<phi>\<close>
  by (simp add: asat_def)

(*<*)
context sepalg begin
(*>*)

text \<open>The following pair of lemmas capture the idea that, if a state satisfies an assertion, and
another state is completely disjoint from it, then the joined states also satisfy the assertion:\<close>
lemma asat_weaken:
    fixes x y :: \<open>'a\<close>
  assumes \<open>x \<Turnstile> \<phi>\<close>
      and \<open>x \<sharp> y\<close>
      and \<open>ucincl \<phi>\<close>
    shows \<open>x + y \<Turnstile> \<phi>\<close>
using assms by (clarsimp simp add: asat_def) (blast elim: ucinclE ucpredE)

lemma asat_weaken2:
  assumes \<open>x \<Turnstile> \<phi>\<close>
      and \<open>x \<sharp> y\<close>
      and \<open>ucincl \<phi>\<close>
    shows \<open>y + x \<Turnstile> \<phi>\<close>
proof -
  from assms have \<open>x + y \<Turnstile> \<phi>\<close>
    using asat_weaken by auto
  moreover from \<open>x \<sharp> y\<close> have \<open>x + y \<Turnstile> \<phi> \<longleftrightarrow> y + x \<Turnstile> \<phi>\<close>
    by simp
  ultimately show \<open>y + x \<Turnstile> \<phi>\<close>
    by auto
qed

text \<open>Note that satisfiability is \<^emph>\<open>monotone\<close> with respect to the derived order on states.  If a
state satisfies an assertion and another state \<^emph>\<open>dominates\<close> that state with respect to the order,
then the second, dominating state also satisfies the assertion too:\<close>
lemma asat_derived_order_monotone:
  assumes \<open>a \<Turnstile> v\<close>
      and \<open>a \<preceq> b\<close>
      and \<open>ucincl v\<close>
    shows \<open>b \<Turnstile> v\<close>
using assms and asat_weaken by blast

subsection\<open>The Boolean connectives preserve upwards-closure\<close>

text \<open>The following are technical results demonstrating that the standard Boolean connectives and
quantifiers are upwards-closed with respect to the derived ordering:\<close>

lemma ucpred_derived_orderI [intro!]:
  shows \<open>ucpred ((\<preceq>) a)\<close>
by (auto intro: ucpredI derived_order_trans)

lemma ucincl_empty [ucincl_intros, simp]:
  shows \<open>ucincl ({}::'a set)\<close>
by (auto intro: ucinclI ucpredI)

lemma ucincl_UNIV [ucincl_intros, simp]:
  shows \<open>ucincl (UNIV::'a set)\<close>
by (auto intro: ucinclI ucpredI)

lemma ucincl_inter [ucincl_intros]:
  assumes \<open>ucincl \<phi>\<close>
      and \<open>ucincl \<psi>\<close>
    shows \<open>ucincl (\<phi> \<inter> \<psi>)\<close>
using assms by (clarsimp elim!: ucinclE ucpredE intro!: ucinclI ucpredI)

lemma ucincl_un [ucincl_intros]:
  assumes \<open>ucincl \<phi>\<close>
      and \<open>ucincl \<psi>\<close>
    shows \<open>ucincl (\<phi> \<union> \<psi>)\<close>
using assms by (auto elim!: ucinclE ucpredE intro!: ucinclI ucpredI)

lemma ucincl_Un [ucincl_intros]:
  assumes \<open>\<And>\<phi>. \<phi> \<in> P \<Longrightarrow> ucincl \<phi>\<close>
    shows \<open>ucincl (\<Union>P)\<close>
using assms by (auto elim!: ucinclE ucpredE intro!: ucinclI ucpredI)

lemma ucincl_Int [ucincl_intros]:
  assumes \<open>\<And>\<phi>. \<phi> \<in> P \<Longrightarrow> ucincl \<phi>\<close>
    shows \<open>ucincl (\<Inter>P)\<close>
using assms by (auto elim!: ucinclE ucpredE intro!: ucinclI ucpredI)

lemma ucincl_IntE [ucincl_elims]:
  assumes \<open>\<phi> \<in> range P\<close>
      and \<open>\<And>x. ucincl (P x)\<close>
    shows \<open>ucincl \<phi>\<close>
using assms by (auto elim!: ucinclE ucpredE intro!: ucinclI ucpredI)

lemma ucincl_multiE [ucincl_elims]:
  assumes \<open>\<phi> \<in># {# e . m #}\<close>
      and \<open>\<And>x. ucincl (e x)\<close>
    shows \<open>ucincl \<phi>\<close>
using assms by (auto elim!: ucinclE ucpredE intro!: ucinclI ucpredI)

lemma ucincl_foldr [ucincl_intros]:
  assumes \<open>ucincl e\<close>
      and \<open>\<And>x acc. x \<in> set xs \<Longrightarrow> ucincl acc \<Longrightarrow> ucincl (f x acc)\<close>
    shows \<open>ucincl (foldr f xs e)\<close>
using assms by (induction xs, auto)

definition uc_state :: \<open>'a \<Rightarrow> 'a assert\<close> ("\<up>\<^sub>s") where
  \<open>uc_state \<sigma> \<equiv> {\<sigma>'. \<sigma> \<preceq> \<sigma>'}\<close>

text\<open>Downwards-closed assertions, analogous to upwards-closed ones.\<close>

definition dcpred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>dcpred P \<equiv> \<forall>x y. P y \<longrightarrow> x \<preceq> y \<longrightarrow> P x\<close>

definition dc_state :: \<open>'a \<Rightarrow> 'a assert\<close> ("\<down>\<^sub>s") where
  \<open>dc_state \<sigma> \<equiv> {\<sigma>'. \<sigma>' \<preceq> \<sigma>}\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma dcpredI:
  assumes \<open>\<And>x y. P y \<Longrightarrow> x \<preceq> y \<Longrightarrow> P x\<close>
    shows \<open>dcpred P\<close>
using assms by(auto simp add: dcpred_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma dcpredE:
  assumes \<open>dcpred P\<close>
      and \<open>(\<And>x y. P y \<Longrightarrow> x \<preceq> y \<Longrightarrow> P x) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by(clarsimp simp add: dcpred_def)

definition dcincl :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>dcincl S \<equiv> dcpred (\<lambda>x. x \<in> S)\<close>

lemma uc_state_ucincl:
  shows \<open>ucincl (\<up>\<^sub>s \<sigma>)\<close>
by (simp add: local.ucpred_derived_orderI local.ucpred_upward_closure uc_state_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma dc_state_dcincl:
  shows \<open>dcincl (\<down>\<^sub>s \<sigma>)\<close>
by (clarsimp simp add: dcincl_def dc_state_def derived_order_def dcpred_def) (metis
  local.disjoint_sym local.sepalg_apart_assoc local.sepalg_apart_plus2 local.sepalg_assoc
  local.sepalg_comm)

(*<*)
end
(*>*)

subsection\<open>Entailment\<close>

(*<*)
context begin

unbundle lattice_syntax
(*>*)

text \<open>We now introduce an \<^emph>\<open>entailment relation\<close> between Separation Logic assertions, capturing the
idea that one assertion follows from another.  Note that we may ``string together'' arbitrary
numbers of \<^emph>\<open>spatial\<close> and \<^emph>\<open>pure\<close> assumptions using separating- and/or Boolean-conjunction,
respectively.  However, as these two types of conjunction coincide for pure assertions we will, by
convention, only ever combine assumptions using the separating conjunction:\<close>
definition aentails :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> bool\<close> (infixr \<open>\<longlongrightarrow>\<close> 50) where
  \<open>aentails \<phi> \<psi> \<equiv> \<forall>x. x \<Turnstile> \<phi> \<longrightarrow> x \<Turnstile> \<psi>\<close>

text \<open>The following are introduction and elimination rules for the entailment relation:\<close>
lemma aentailsI:
  assumes \<open>\<And>x. x \<Turnstile> \<phi> \<Longrightarrow> x \<Turnstile> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
using assms by (simp add: aentails_def)

lemma aentailsE:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>(\<And>x. x \<Turnstile> \<phi> \<Longrightarrow> x \<Turnstile> \<psi>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: aentails_def)

text \<open>The entailment relation forms a \<^emph>\<open>preorder\<close> and is reflexive and transitive:\<close>
lemma aentails_refl [aentails_intro]:
  shows \<open>\<phi> \<longlongrightarrow> \<phi>\<close>
by (simp add: aentails_def)

lemma aentails_refl_eq:
  assumes \<open>\<phi> = \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
using aentails_refl assms by auto

lemma aentails_trans [trans, aentails_intro]:
  assumes \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<phi>' \<longlongrightarrow> \<phi>''\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<phi>''\<close>
using assms by (simp add: aentails_def)

text \<open>Restatement of the transitivity rule for entailment with the premises flipped.
      This makes certain proof patterns easier.\<close>
lemma aentails_trans':
  assumes \<open>P \<longlongrightarrow> Q\<close>
      and \<open>\<phi> \<longlongrightarrow> P\<close>
    shows \<open>\<phi> \<longlongrightarrow> Q\<close>
using aentails_trans assms by auto

text \<open>The relation is also antisymmetric, and if two assertions are entailments of each other then
they denote identical sets of states:\<close>
lemma aentails_eq:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>\<psi> \<longlongrightarrow> \<phi>\<close>
    shows \<open>\<phi> = \<psi>\<close>
using assms unfolding aentails_def by (auto intro!: asat_semequivI)

text \<open>The following lemma is crucial when working with an assertion \<^verbatim>\<open>\<phi>\<close> not in terms of its concrete
definition, but in terms of its associated functor \<^verbatim>\<open>_ \<longlongrightarrow> \<phi>\<close>. We will use it extensively to reason
about weakest preconditions without ever unfolding its definition, but only relying on its universal
property:\<close>
lemma aentails_yonedaI:
  assumes \<open>\<And>\<phi>. (\<phi> \<longlongrightarrow> \<alpha>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<beta>)\<close>
    shows \<open>\<alpha> = \<beta>\<close>
by (meson aentails_eq aentails_refl assms)

lemma aentails_uc:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
    shows \<open>\<up>\<^sub>s \<sigma> \<longlongrightarrow> \<xi>\<close>
by (metis aentails_def asat_def assms asat_derived_order_monotone mem_Collect_eq uc_state_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aentails_dc:
  assumes \<open>dcincl \<xi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
    shows \<open>\<down>\<^sub>s \<sigma> \<longlongrightarrow> \<xi>\<close>
using assms by (clarsimp simp add: dcincl_def dcpred_def dc_state_def aentails_def asat_def)

(*<*)
end

context sepalg begin
(*>*)

text \<open>The following technical lemma describes how the Boolean connectives and quantifiers of our
Separation Logic are characterised using the satisfaction relation:\<close>
lemma asat_connectives_characterisation [simp]:
  shows \<open>\<And>x. x \<Turnstile> \<top>\<close>
    and \<open>\<And>x. x \<Turnstile> \<bottom> \<longleftrightarrow> False\<close>
    and \<open>\<And>x \<phi> \<psi>. x \<Turnstile> \<phi> \<sqinter> \<psi> \<longleftrightarrow> x \<Turnstile> \<phi> \<and> x \<Turnstile> \<psi>\<close>
    and \<open>\<And>x \<phi> \<psi>. x \<Turnstile> \<phi> \<squnion> \<psi> \<longleftrightarrow> x \<Turnstile> \<phi> \<or> x \<Turnstile> \<psi>\<close>
    and \<open>\<And>x A \<phi>. x \<Turnstile> (\<Sqinter>y\<in>A. \<phi> y) \<longleftrightarrow> (\<forall>y\<in>A. x \<Turnstile> \<phi> y)\<close>
    and \<open>\<And>x A \<phi>. x \<Turnstile> (\<Squnion>y\<in>A. \<phi> y) \<longleftrightarrow> (\<exists>y\<in>A. x \<Turnstile> \<phi> y)\<close>
by (auto simp add: asat_def)

subsection\<open>Connectives of separation logic\<close>

subsubsection\<open>The separating conjunction\<close>

text \<open>The following assertion is one of the characteristic features of Separation Logic, the
\<^emph>\<open>separating conjunction\<close>.  A state satisfies the separating conjunction of two assertions if it
can be decomposed into two smaller, disjoint substates that each satisfy one of the two respective
assertions.  Note that this captures the idea of ``local reasoning'', allowing us two ``zoom in'' on
subparts of a machine state that satisfy a particular property, ignoring everything else:\<close>
definition asepconj :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> 'a assert\<close> (infixr \<open>\<star>\<close> 65) where
  \<open>\<phi> \<star> \<psi> \<equiv> {s. \<exists>t u. s = t + u \<and> t \<sharp> u \<and> t \<Turnstile> \<phi> \<and> u \<Turnstile> \<psi>}\<close>

text \<open>The following are technical introduction and elimination rules for separating conjunction:\<close>
lemma asepconjI:
  assumes \<open>x = y + z\<close>
      and \<open>y \<sharp> z\<close>
      and \<open>y \<Turnstile> \<phi>\<close>
      and \<open>z \<Turnstile> \<psi>\<close>
    shows \<open>x \<Turnstile> \<phi> \<star> \<psi>\<close>
using assms by (auto simp add: asepconj_def asat_def)

lemma asepconjE:
  assumes \<open>x \<Turnstile> \<phi> \<star> \<psi>\<close>
      and \<open>\<And>y z. x = y + z \<Longrightarrow> y \<sharp> z \<Longrightarrow> y \<Turnstile> \<phi> \<Longrightarrow> z \<Turnstile> \<psi> \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: asepconj_def asat_def)

text \<open>The Boolean truth value acts as a zero element for the separating conjunction:\<close>
lemma asepconj_bot_zero [asepconj_simp]:
  shows \<open>\<bottom> \<star> \<phi> = \<bottom>\<close>
by (auto simp add: asepconj_def)

lemma asepconj_bot_zero2 [asepconj_simp]:
  shows \<open>\<phi> \<star> \<bottom> = \<bottom>\<close>
by (auto simp add: asepconj_def)

text\<open>Separating conjunction with the always-true predicate is upwards closure:\<close>

lemma uc_state_alt:
  shows \<open>\<xi> \<star> \<top> = (\<Squnion> \<sigma>\<in>\<xi>. \<up>\<^sub>s \<sigma>)\<close>
by (auto simp add: uc_state_def asepconj_def asat_def) blast

corollary aentails_uc':
  assumes \<open>ucincl \<xi>\<close>
      and \<open>\<sigma> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<sigma> \<star> \<top> \<longlongrightarrow> \<xi>\<close>
using assms by (auto simp add: uc_state_alt uc_state_def aentails_def asat_def ucpred_def ucincl_def)

text\<open>In particular, the upwards closure of a single state can be described by its
separating conjunction with the always-true predicate:\<close>

corollary uc_state_single_alt:
  shows \<open>{\<sigma>} \<star> \<top> = \<up>\<^sub>s \<sigma>\<close>
by (simp add: uc_state_alt)

text\<open>For singleton sets, the separating conjunction essentially recovers the disjoint sum of states:\<close>

lemma asepconj_singleton:
  assumes \<open>y \<sharp> z\<close>
      and \<open>x = y + z\<close>
    shows \<open>{x} = {y} \<star> {z}\<close>
using assms by (auto simp add: asepconj_def asat_def)

text\<open>In fact, the separating conjunction of \<^emph>\<open>non-disjoint\<close> singletons is empty:\<close>

lemma asepconj_singleton_general:
  shows \<open>{x} \<star> {y} = (if x \<sharp> y then {x + y} else {})\<close>
by (auto simp add: asepconj_def asat_def)

text \<open>The result above can be used to provide an alternative characterisation of the notion of
upwards-closure.  Namely: an assertion is upwards-closed if it denotes the same set of states as
itself composed with the Boolean truth value using separating conjunction:\<close>
corollary ucincl_alt:
  shows \<open>ucincl \<phi> \<longleftrightarrow> (\<phi> = \<phi> \<star> \<top>)\<close>
by (clarsimp simp add: ucincl_def ucpred_def uc_state_alt uc_state_def asat_def)
  (blast intro!: local.derived_order_refl)

text \<open>One can also characterize upwards closure of an assertion \<^verbatim>\<open>\<phi>\<close> in terms of the functor
\<^verbatim>\<open>_ \<longlongrightarrow> \<phi>\<close>:\<close>

lemma ucincl_alt':
  shows \<open>ucincl \<phi> \<longleftrightarrow> (\<forall>\<psi>. (\<psi> \<longlongrightarrow> \<phi>) \<longleftrightarrow> (\<psi> \<star> \<top> \<longlongrightarrow> \<phi>))\<close>
by (force simp add: ucincl_def aentails_def asepconj_def ucpred_def asat_def)

named_theorems is_sat_elim
named_theorems is_sat_simp
named_theorems is_sat_destruct

text\<open>A helper method for the extraction of the 'pure content' of an assertion.\<close>
method is_sat_destruct uses simp = (
    elim is_sat_elim
  | drule is_sat_destruct
  | clarsimp simp add: is_sat_simp Let_def simp)+

lemma is_sat_splitE[is_sat_elim]:
  assumes \<open>is_sat (\<phi> \<star> \<psi>)\<close>
      and \<open>is_sat \<phi> \<Longrightarrow> is_sat \<psi> \<Longrightarrow> R\<close>
    shows R
by (meson asepconjE assms is_sat_def)

lemma is_sat_UnionD[is_sat_destruct]:
  assumes \<open>is_sat (\<Union>x. \<xi> x)\<close>
    shows \<open>\<exists>x. is_sat (\<xi> x)\<close>
using assms by (auto simp add: is_sat_def asat_def)

text \<open>When proving a separating entailment, one can without loss of generality
assume that the spatial premise is satisfiable.\<close>
lemma aentails_is_sat:
  assumes \<open>is_sat \<phi> \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
using aentails_def assms is_sat_def by blast

text \<open>The separating conjunction is commutative:\<close>
lemma asepconj_comm:
  shows \<open>\<phi> \<star> \<psi> = \<psi> \<star> \<phi>\<close>
proof(rule asat_semequivI)
     fix s :: \<open>'a\<close>
  assume \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
  from this obtain t u where \<open>s = t + u\<close> and \<open>t \<sharp> u\<close> and \<open>t \<Turnstile> \<phi>\<close> and \<open>u \<Turnstile> \<psi>\<close>
    by (auto elim: asepconjE)
  from this have \<open>u \<sharp> t\<close> and \<open>s = u + t\<close>
    by auto
  from this and \<open>t \<Turnstile> \<phi>\<close> and \<open>u \<Turnstile> \<psi>\<close> show \<open>s \<Turnstile> \<psi> \<star> \<phi>\<close>
    using asepconjI by blast
next
     fix s :: \<open>'a\<close>
  assume \<open>s \<Turnstile> \<psi> \<star> \<phi>\<close>
  from this obtain t u where \<open>s = t + u\<close> and \<open>t \<sharp> u\<close> and \<open>t \<Turnstile> \<psi>\<close> and \<open>u \<Turnstile> \<phi>\<close>
    by (auto elim: asepconjE)
  from this have \<open>u \<sharp> t\<close> and \<open>s = u + t\<close>
    by auto
  from this and \<open>t \<Turnstile> \<psi>\<close> and \<open>u \<Turnstile> \<phi>\<close> show \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
    using asepconjI by blast
qed

text \<open>It is also associative:\<close>
lemma asepconj_assoc [asepconj_simp]:
  shows \<open>(\<phi> \<star> \<psi>) \<star> \<xi> = \<phi> \<star> (\<psi> \<star> \<xi>)\<close>
proof(rule asat_semequivI)
     fix s :: \<open>'a\<close>
  assume \<open>s \<Turnstile> \<phi> \<star> (\<psi> \<star> \<xi>)\<close>
  from this obtain t u v where \<open>t \<sharp> (u + v)\<close> and \<open>u \<sharp> v\<close> and \<open>s = t + (u + v)\<close> and \<open>t \<Turnstile> \<phi>\<close>
      and \<open>u \<Turnstile> \<psi>\<close> and \<open>v \<Turnstile> \<xi>\<close>
    by (auto elim!: asepconjE)
  moreover from this have \<open>t \<sharp> u\<close> and \<open>t \<sharp> v\<close> and \<open>s = (t + u) + v\<close>
    by (meson disjoint_sym sepalg_apart_plus sepalg_apart_plus2 sepalg_assoc)+
  ultimately show \<open>s \<Turnstile> (\<phi> \<star> \<psi>) \<star> \<xi>\<close>
    by (metis asepconjI sepalg_apart_assoc2)
next
     fix s :: \<open>'a\<close>
  assume \<open>s \<Turnstile> (\<phi> \<star> \<psi>) \<star> \<xi>\<close>
  from this obtain t u v where \<open>t + u \<sharp> v\<close> and \<open>t \<sharp> u\<close> and \<open>s = (t + u) + v\<close> and \<open>t \<Turnstile> \<phi>\<close>
      and \<open>u \<Turnstile> \<psi>\<close> and \<open>v \<Turnstile> \<xi>\<close>
    by (auto elim!: asepconjE)
  moreover from this have \<open>t \<sharp> v\<close>
    by (meson disjoint_sym sepalg_apart_plus2)
  moreover from calculation have \<open>u \<sharp> v\<close>
    by blast
  moreover from calculation have \<open>s = t + (u + v)\<close>
    by (metis sepalg_assoc)
  ultimately show \<open>s \<Turnstile> \<phi> \<star> (\<psi> \<star> \<xi>)\<close>
    by (metis asepconjI sepalg_apart_assoc)
qed

lemma asepconj_swap_top:
  shows \<open>\<phi> \<star> (\<psi> \<star> \<xi>) = \<psi> \<star> (\<phi> \<star> \<xi>)\<close>
by (metis asepconj_assoc asepconj_comm)

lemmas asepconj_AC = asepconj_comm asepconj_assoc asepconj_swap_top

lemma assocL_entails:
  assumes \<open>\<phi> \<star> (\<psi> \<star> \<xi>) \<longlongrightarrow> \<gamma>\<close>
    shows \<open>(\<phi> \<star> \<psi>) \<star> \<xi> \<longlongrightarrow> \<gamma>\<close>
  by (simp add: asepconj_assoc assms)

text \<open>For upwards-closed assertions, the Boolean truth values acts as an identity.  Note that we
provide a full proof of this result here, but this is also an immediate corollary of our alternative
characterisation of upwards-closure, above:\<close>
lemma asepconj_ident [asepconj_simp]:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>\<top> \<star> \<phi> = \<phi>\<close>
using asepconj_comm assms ucincl_alt by simp

lemma asepconj_ident2 [asepconj_simp]:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>\<phi> \<star> \<top> = \<phi>\<close>
using assms ucincl_alt by simp

text \<open>The empty assertion owns exactly the empty machine state and is the
unconditional unit of separating conjunction.\<close>
definition emp :: \<open>'a assert\<close> where
  \<open>emp \<equiv> {0}\<close>

lemma asat_emp [asat_simp, simp]:
  shows \<open>x \<Turnstile> emp \<longleftrightarrow> x = 0\<close>
by (simp add: asat_def emp_def)

lemma asepconj_emp_unit [asepconj_simp]:
  shows \<open>\<phi> \<star> emp = \<phi>\<close> and \<open>emp \<star> \<phi> = \<phi>\<close>
proof -
  show \<open>\<phi> \<star> emp = \<phi>\<close>
    by (intro asat_semequivI) (auto simp add: asat_emp elim!: asepconjE
      intro!: asepconjI [where ?z=0])
  from this show \<open>emp \<star> \<phi> = \<phi>\<close>
    by (simp add: asepconj_comm)
qed

text \<open>The Boolean truth value is \<^emph>\<open>idempotent\<close> with respect to the separating conjunction:\<close>
lemma asepconj_UNIV_idempotent [asepconj_simp]:
  shows \<open>\<top> \<star> \<top> = \<top>\<close>
by (simp add: ucincl_intros asepconj_simp)

lemma asepconj_UNIV_collapse_top:
  shows \<open>\<top> \<star> \<top> \<star> \<phi> = \<top> \<star> \<phi>\<close>
by (simp flip: asepconj_assoc add: asepconj_UNIV_idempotent)

corollary asepconj_uc_state:
  assumes \<open>\<sigma> \<sharp> \<sigma>'\<close>
    shows \<open>\<up>\<^sub>s \<sigma> \<star> \<up>\<^sub>s \<sigma>' = \<up>\<^sub>s (\<sigma> + \<sigma>')\<close>
using assms  by (simp flip: uc_state_single_alt add: asepconj_simp asepconj_UNIV_collapse_top
  asepconj_singleton) (simp add: asepconj_UNIV_collapse_top asepconj_comm)

lemma asepconj_uc_state_general:
  shows \<open>\<up>\<^sub>s \<sigma> \<star> \<up>\<^sub>s \<sigma>' = (if \<sigma> \<sharp> \<sigma>' then \<up>\<^sub>s (\<sigma> + \<sigma>') else {})\<close>
proof (cases \<open>\<sigma> \<sharp> \<sigma>'\<close>)
  case True
  then show ?thesis
    by (simp add: asepconj_uc_state)
next
  case False
  then have \<open>{\<sigma>} \<star> UNIV \<star> {\<sigma>'} \<star> UNIV = {}\<close>
    using asepconj_comm asepconj_ident asepconj_swap_top local.asepconj_singleton_general by force
  then show ?thesis
    by (metis False asepconj_assoc local.uc_state_single_alt)
qed

text \<open>Separating conjunction also preserves upwards closure:\<close>

lemma ucincl_asepconjL [ucincl_intros]:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>ucincl (\<phi> \<star> \<psi>)\<close>
using assms by (simp only: ucincl_alt) (metis asepconj_assoc asepconj_comm)

\<comment>\<open>Both orientations participate in closure search. Each leaves a strictly smaller
\<^const>\<open>ucincl\<close> goal, and the left-oriented rule is tried first.\<close>
lemma ucincl_asepconjR [ucincl_intros]:
  assumes \<open>ucincl \<psi>\<close>
    shows \<open>ucincl (\<phi> \<star> \<psi>)\<close>
using assms asepconj_comm ucincl_asepconjL by force

notepad
begin
  \<comment>\<open>The theorem bundle closes a right-oriented conjunction.\<close>
  fix \<phi> \<psi> :: \<open>'a assert\<close>
  assume \<open>ucincl \<psi>\<close>
  then have \<open>ucincl (\<phi> \<star> \<psi>)\<close>
    by (intro ucincl_intros)
end

\<comment>\<open>TODO: Remove this\<close>
lemmas ucincl_asepconj = ucincl_asepconjL

text \<open>Separating conjunction \<^emph>\<open>distributes\<close> through the Boolean existential quantifier:\<close>
lemma asepconj_Inf_distrib [asepconj_simp]:
  fixes \<psi> :: \<open>'a assert\<close>
  shows \<open>(\<Squnion>x. \<phi> x) \<star> \<psi> = (\<Squnion>x. \<phi> x \<star> \<psi>)\<close>
by (auto simp add: asepconj_def)

lemma asepconj_Inf_distrib2 [asepconj_simp]:
  fixes \<psi> :: \<open>'a assert\<close>
  shows \<open>\<psi> \<star> (\<Squnion>x. \<phi> x) = (\<Squnion>x. \<phi> x \<star> \<psi>)\<close>
by (auto simp add: asepconj_comm asepconj_def)

lemma asepconj_Inf_distrib_right:
  fixes \<psi> :: \<open>'a assert\<close>
  shows \<open>\<psi> \<star> (\<Squnion>x. \<phi> x) = (\<Squnion>x. \<psi> \<star> \<phi> x)\<close>
  by (auto simp add: asepconj_comm asepconj_def)

lemma asepconj_Inf_distrib3_1:
  shows \<open>(\<Squnion>x. \<alpha> x) \<star> \<beta> \<star> \<gamma> = (\<Squnion>x. \<alpha> x \<star> \<beta> \<star> \<gamma>)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib3_2:
  shows \<open>\<alpha> \<star> (\<Squnion>x. \<beta> x) \<star> \<gamma> = (\<Squnion>x. \<alpha> \<star> \<beta> x \<star> \<gamma>)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib3_3:
  shows \<open>\<alpha> \<star> \<beta> \<star> (\<Squnion>x. \<gamma> x) = (\<Squnion>x. \<alpha> \<star> \<beta> \<star> \<gamma> x)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib4_1:
  shows \<open>(\<Squnion>x. \<alpha> x) \<star> \<beta> \<star> \<gamma> \<star> \<delta> = (\<Squnion>x. \<alpha> x \<star> \<beta> \<star> \<gamma> \<star> \<delta>)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib4_2:
  shows \<open>\<alpha> \<star> (\<Squnion>x. \<beta> x) \<star> \<gamma> \<star> \<delta> = (\<Squnion>x. \<alpha> \<star> \<beta> x \<star> \<gamma> \<star> \<delta>)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib4_3:
  shows \<open>\<alpha> \<star> \<beta> \<star> (\<Squnion>x. \<gamma> x) \<star> \<delta> = (\<Squnion>x. \<alpha> \<star> \<beta> \<star> \<gamma> x \<star> \<delta>)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib4_4:
  shows \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> (\<Squnion>x. \<delta> x) = (\<Squnion>x. \<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> x)\<close>
  by (auto simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)

lemma asepconj_Inf_distrib3 [asepconj_simp]:
  fixes \<psi> :: \<open>'a assert\<close>
  shows \<open>\<psi> \<star> (\<Squnion>x\<in>S. \<phi> x) = (\<Squnion>x\<in>S. \<phi> x \<star> \<psi>)\<close>
by (auto simp add: asepconj_comm asepconj_def)

lemma asepconj_Inf_distrib':
  shows \<open>(\<Union>\<Phi>) \<star> \<psi> = (\<Squnion>\<phi>\<in>\<Phi>. \<phi> \<star> \<psi>)\<close>
    and \<open>\<psi> \<star> (\<Union>\<Phi>) = (\<Squnion>\<phi>\<in>\<Phi>. \<psi> \<star> \<phi>)\<close>
by (auto simp add: asepconj_def asat_def)

text \<open>The following two elimination rules allow us to \<^emph>\<open>strengthen\<close>, or ``\<^emph>\<open>forget\<close>'' parts of a
separating conjunction:\<close>
lemma asepconj_strengthenE:
  assumes \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
      and \<open>ucincl \<phi>\<close>
      and \<open>ucincl \<psi>\<close>
      and \<open>s \<Turnstile> \<phi> \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto elim!: asepconjE) (meson asat_weaken)

lemma asepconj_strengthenE2:
  assumes \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
      and \<open>ucincl \<phi>\<close>
      and \<open>ucincl \<psi>\<close>
      and \<open>s \<Turnstile> \<psi> \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto elim!: asepconjE) (metis asepconj_comm asepconj_strengthenE assms)

text \<open>On the other hand, the following results allows us to \<^emph>\<open>weaken\<close> a separating conjunction with
an assertion that holds in an empty machine state:\<close>
lemma asepconj_weakenI:
  assumes \<open>s \<Turnstile> \<phi>\<close>
      and \<open>0 \<Turnstile> \<psi>\<close>
    shows \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
using assms by (auto intro!: asepconjI [where ?z=0])

lemma asepconj_weaken2I:
  assumes \<open>s \<Turnstile> \<phi>\<close>
      and \<open>0 \<Turnstile> \<psi>\<close>
    shows \<open>s \<Turnstile> \<psi> \<star> \<phi>\<close>
proof -
  from assms have \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
    using asepconj_weakenI by blast
  from this show \<open>s \<Turnstile> \<psi> \<star> \<phi>\<close>
    by (simp add: asepconj_comm)
qed

text \<open>Boolean truth follows from any and every set of assumptions:\<close>
lemma aentails_true [aentails_intro]:
  shows \<open>\<phi> \<longlongrightarrow> \<top>\<close>
by (simp add: aentails_def)

text \<open>Any assertion follows from the Boolean false assumption:\<close>
\<comment>\<open>TODO: Why is this not in \<^verbatim>\<open>aentails_simp\<close>? Try and see if anything breaks\<close>
lemma bot_aentails_all:
  shows \<open>\<bottom> \<longlongrightarrow> \<phi>\<close>
by (simp add: aentails_def asat_def)

text \<open>The following are \<^emph>\<open>monotonictity\<close> results for separating conjunction, allowing us to
decompose entailments between separating conjunctions in various ways:\<close>
lemma asepconj_mono4:
  assumes \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<psi> \<longlongrightarrow> \<psi>'\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi>' \<star> \<psi>'\<close>
proof (intro aentailsI)
  fix s assume \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>
  then obtain t u where \<open>s = t + u\<close> and \<open>t \<sharp> u\<close> and \<open>t \<Turnstile> \<phi>\<close> and \<open>u \<Turnstile> \<psi>\<close>
    by (auto elim: asepconjE)
  moreover from assms and \<open>t \<Turnstile> \<phi>\<close> and \<open>u \<Turnstile> \<psi>\<close> have \<open>t \<Turnstile> \<phi>'\<close> and \<open>u \<Turnstile> \<psi>'\<close>
    using assms by (auto simp add: aentails_def)
  ultimately show \<open>s \<Turnstile> \<phi>' \<star> \<psi>'\<close>
    by (auto intro: asepconjI)
qed

text \<open>Appending \<^term>\<open>\<psi>'\<close> without consuming resource requires it to hold on the
empty state:\<close>
lemma asepconj_mono6:
  assumes \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>emp \<longlongrightarrow> \<psi>'\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> \<psi>'\<close>
using assms by (simp add: aentails_def asepconj_weakenI)

\<comment>\<open>\<^verbatim>\<open>asepconj_mono7\<close> is stated with the disposal rules below.\<close>

lemma asepconj_mono:
  assumes \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi> \<star> \<xi>\<close>
using asepconj_mono4 aentails_refl assms by blast

text \<open>Weakening \<^term>\<open>\<phi>\<close> to \<^term>\<open>\<phi> \<star> \<xi>\<close> can append only a factor
satisfied by the empty state:\<close>
lemma asepconj_mono5:
  assumes \<open>emp \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<phi> \<star> \<xi>\<close>
using assms by (metis asepconj_emp_unit(1) asepconj_mono)

lemma asepconj_mono3:
  assumes \<open>\<phi> = \<phi>'\<close>
      and \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi>' \<star> \<xi>\<close>
using assms by (simp add: asepconj_mono)

lemma asepconj_mono2:
  assumes \<open>\<phi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<xi> \<star> \<psi>\<close>
proof -
  from assms have \<open>\<psi> \<star> \<phi> \<longlongrightarrow> \<psi> \<star> \<xi>\<close>
    by (metis asepconj_mono)
  then show ?thesis
    by (simp add: asepconj_comm)
qed

lemma asepconj_mono_sym:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>\<xi> \<longlongrightarrow> \<pi>\<close>
    shows \<open>\<phi> \<star> \<xi> \<longlongrightarrow> \<pi> \<star> \<psi>\<close>
using assms by (metis asepconj_comm asepconj_mono4)

text \<open>Discardability is the explicit licence required to forget a resource.\<close>
definition discardable_in :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> bool\<close> where
  \<open>discardable_in \<delta> \<rho> \<equiv> \<delta> \<star> \<rho> \<longlongrightarrow> \<rho>\<close>

named_theorems discardable_in_intros

text \<open>\<^term>\<open>discardable_in \<delta> \<rho>\<close> means that \<^term>\<open>\<delta>\<close> may be dropped
while \<^term>\<open>\<rho>\<close> is retained. The relation is contextual because the retained
assertion may absorb resource owned by the discarded one. Generic rules that
produce entailment or closure obligations stay outside
\<^verbatim>\<open>discardable_in_intros\<close>.\<close>
lemma discardable_in_aentails_empI:
  assumes \<open>\<delta> \<longlongrightarrow> emp\<close>
    shows \<open>discardable_in \<delta> \<rho>\<close>
proof -
  from assms have \<open>\<delta> \<star> \<rho> \<longlongrightarrow> emp \<star> \<rho>\<close>
    by (rule asepconj_mono2)
  then show ?thesis
    by (simp add: discardable_in_def asepconj_emp_unit(2))
qed

lemma discardable_in_empI [discardable_in_intros]:
  shows \<open>discardable_in emp \<rho>\<close>
by (rule discardable_in_aentails_empI[OF aentails_refl])

text \<open>Discardability composes over separating conjunction.\<close>
lemma discardable_in_conj [discardable_in_intros]:
  assumes \<open>discardable_in \<phi> \<rho>\<close>
      and \<open>discardable_in \<psi> \<rho>\<close>
    shows \<open>discardable_in (\<phi> \<star> \<psi>) \<rho>\<close>
proof -
  from assms(2) have \<open>\<phi> \<star> \<psi> \<star> \<rho> \<longlongrightarrow> \<phi> \<star> \<rho>\<close>
    by (simp add: discardable_in_def asepconj_mono)
  with assms(1) show ?thesis
    by (simp add: discardable_in_def asepconj_assoc aentails_trans')
qed

lemma discardable_in_ucinclI:
  assumes \<open>ucincl \<rho>\<close>
    shows \<open>discardable_in \<delta> \<rho>\<close>
proof -
  have \<open>\<delta> \<star> \<rho> \<longlongrightarrow> \<top> \<star> \<rho>\<close>
    by (intro asepconj_mono2 aentails_true)
  then show ?thesis
    by (simp add: discardable_in_def asepconj_ident assms)
qed

text \<open>Retaining an assertion while discarding arbitrary resource is exactly
upwards-closure.\<close>
lemma discardable_in_univ_iff_ucincl:
  shows \<open>discardable_in \<top> \<rho> \<longleftrightarrow> ucincl \<rho>\<close>
proof
  assume \<open>discardable_in \<top> \<rho>\<close>
  have \<open>\<rho> \<longlongrightarrow> \<rho> \<star> \<top>\<close>
    by (rule asepconj_mono6[OF aentails_refl aentails_true])
  moreover from \<open>discardable_in \<top> \<rho>\<close> have \<open>\<rho> \<star> \<top> \<longlongrightarrow> \<rho>\<close>
    by (simp add: discardable_in_def asepconj_comm)
  ultimately have \<open>\<rho> = \<rho> \<star> \<top>\<close>
    by (rule aentails_eq)
  then show \<open>ucincl \<rho>\<close>
    by (simp add: ucincl_alt)
next
  assume \<open>ucincl \<rho>\<close>
  then show \<open>discardable_in \<top> \<rho>\<close>
    by (rule discardable_in_ucinclI)
qed

text \<open>Cancellation consumes a discardability licence for the removed factor.\<close>
lemma aentails_cancel_r_discardable:
  assumes \<open>discardable_in \<psi> \<phi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi>\<close>
proof -
  from assms have \<open>\<psi> \<star> \<phi> \<longlongrightarrow> \<phi>\<close>
    by (simp add: discardable_in_def)
  then show ?thesis
    by (simp add: asepconj_comm)
qed

lemma aentails_cancel_l_discardable:
  assumes \<open>discardable_in \<phi> \<psi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<psi>\<close>
using assms by (simp add: discardable_in_def)

text \<open>Upwards-closed retention is the unrestricted disposal instance.\<close>
lemma aentails_cancel_r:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi>\<close>
using assms by (intro aentails_cancel_r_discardable discardable_in_ucinclI)

lemma aentails_cancel_l:
  assumes \<open>ucincl \<psi>\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<psi>\<close>
using assms by (intro aentails_cancel_l_discardable discardable_in_ucinclI)

text \<open>For an upwards-closed retained assertion, a leading \<^term>\<open>\<top>\<close> is semantically neutral
and gives cancellation an absorber independent of factor order.  The introduction form avoids
using \<^verbatim>\<open>asepconj_ident\<close> backwards, which would repeatedly insert \<^term>\<open>\<top>\<close>:\<close>
lemma aentails_insert_top:
  assumes \<open>ucincl \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<top> \<star> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
using assms by (simp add: asepconj_ident)

text \<open>Once an upwards-closed right-hand factor has been selected for
cancellation, \<^term>\<open>\<top>\<close> can be inserted immediately after that factor.
This needs upwards closure of the selected factor only, not of the remaining
right-hand conjunction.\<close>
lemma aentails_insert_top_after_ucincl:
  assumes \<open>ucincl \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> \<star> (\<top> \<star> \<xi>)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi> \<star> \<xi>\<close>
using assms by (simp only: asepconj_assoc[symmetric] asepconj_ident2)

text \<open>This rule weakens the retained factor and discards \<^term>\<open>\<psi>\<close>. The
\<^term>\<open>discardable_in \<psi> \<phi>'\<close> premise is the required disposal licence and remains
second so callers can compose a rule into the entailment premise.\<close>
lemma asepconj_mono7:
  assumes \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>discardable_in \<psi> \<phi>'\<close>
    shows \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi>'\<close>
proof -
  from assms(1) have \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<phi>' \<star> \<psi>\<close>
    by (rule asepconj_mono2)
  moreover from assms(2) have \<open>\<phi>' \<star> \<psi> \<longlongrightarrow> \<phi>'\<close>
    by (rule aentails_cancel_r_discardable)
  ultimately show ?thesis
    by (rule aentails_trans)
qed

text \<open>The following lemmas characterise how Boolean conjunction interacts with entailment:\<close>
lemma aentails_int [aentails_simp]:
  shows \<open>(\<phi> \<longlongrightarrow> \<psi> \<inter> \<xi>) = ((\<phi> \<longlongrightarrow> \<psi>) \<and> (\<phi> \<longlongrightarrow> \<xi>))\<close>
by (clarsimp simp add: aentails_def intro: aentailsI) blast

lemma aentails_intI [aentails_intro]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi> \<inter> \<xi>\<close>
using assms aentails_int by auto

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aentails_int_aentails:
  shows \<open>\<phi> \<star> (\<psi> \<sqinter> \<xi>) \<longlongrightarrow> (\<phi> \<star> \<psi>) \<sqinter> (\<phi> \<star> \<xi>)\<close>
by (meson aentails_refl local.aentails_int local.asepconj_mono)

lemma aentails_inter_weaken:
  assumes \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<sqinter> \<psi> \<longlongrightarrow> \<xi>\<close>
using assms by (metis aentails_refl aentails_trans local.aentails_int)

lemma aentails_inter_weaken2:
  assumes \<open>\<phi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<sqinter> \<psi> \<longlongrightarrow> \<xi>\<close>
using assms by (metis aentails_refl aentails_trans local.aentails_int)

subsection\<open>Separating implication\<close>

text\<open>The following is the implication constant which needs to be defined specially, as it does not
correspond to a natural operation on sets:\<close>
definition aimplies :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> 'a assert\<close> (infixr \<open>\<sqsubseteq>\<close> 60) where
  \<open>\<phi> \<sqsubseteq> \<psi> \<equiv> {s. \<forall>t. s \<preceq> t \<longrightarrow> t \<Turnstile> \<phi> \<longrightarrow> t \<Turnstile> \<psi> }\<close>

text \<open>The following are technical introduction and elimination rules for implication:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aimpliesI:
  assumes \<open>\<And>t. s \<preceq> t \<Longrightarrow> t \<Turnstile> \<phi> \<Longrightarrow> t \<Turnstile> \<psi>\<close>
    shows \<open>s \<Turnstile> \<phi> \<sqsubseteq> \<psi>\<close>
using assms by (clarsimp simp add: aimplies_def asat_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aimpliesE:
  assumes \<open>s \<Turnstile> \<phi> \<sqsubseteq> \<psi>\<close>
      and \<open>(\<And>t. s \<preceq> t \<Longrightarrow> t \<Turnstile> \<phi> \<Longrightarrow> t \<Turnstile> \<psi>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (clarsimp simp add: aimplies_def asat_def)

text \<open>Implication is upwards closed:\<close>
lemma ucincl_aimplies [ucincl_intros]:
  shows \<open>ucincl (\<phi> \<sqsubseteq> \<psi>)\<close>
by (clarsimp simp add: aimplies_def intro!: ucinclI ucpredI elim!: ucinclE ucpredE)
    (meson derived_order_trans)

text \<open>The following is a form of \<^emph>\<open>modus ponens\<close> describing how Boolean implication and separating
conjunction interact on upwards-closed assertion:\<close>
lemma aimplies_have:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>\<phi> \<star> (\<phi> \<sqsubseteq> \<psi>) \<longlongrightarrow> \<psi>\<close>
using assms by (clarsimp simp add: asepconj_def aimplies_def aentails_def asat_def) (metis
    asat_def local.asat_weaken local.derived_orderI local.disjoint_sym local.sepalg_comm)

subsection\<open>The magic wand\<close>

text \<open>The ``magic wand'' is another form of implication specific to Separation Logic and which
allows us to hypothesise the results of adding a disjoint piece of machine state:\<close>
definition awand :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> 'a assert\<close> (infixr \<open>\<Zsurj>\<close> 66) where
  \<open>\<phi> \<Zsurj> \<psi> \<equiv> { s. \<forall>y. s \<sharp> y \<longrightarrow> y \<Turnstile> \<phi> \<longrightarrow> s + y \<Turnstile> \<psi> }\<close>

text \<open>The following are technical introduction and elimination rules for the magic wand:\<close>
lemma awandI:
  assumes \<open>\<And>y. s \<sharp> y \<Longrightarrow> y \<Turnstile> \<phi> \<Longrightarrow> s + y \<Turnstile> \<psi>\<close>
    shows \<open>s \<Turnstile> \<phi> \<Zsurj> \<psi>\<close>
using assms by (auto simp add: awand_def asat_def)

lemma awandE:
  assumes \<open>s \<Turnstile> \<phi> \<Zsurj> \<psi>\<close>
      and \<open>(\<And>y. s \<sharp> y \<Longrightarrow> y \<Turnstile> \<phi> \<Longrightarrow> s + y \<Turnstile> \<psi>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: awand_def asat_def)

text \<open>The magic wand is \<^emph>\<open>adjoint\<close> to the entailment relation, in the following technical sense:\<close>
lemma awand_adjoint [aentails_simp]:
  shows \<open>(\<phi> \<longlongrightarrow> (\<psi> \<Zsurj> \<xi>)) = (\<phi> \<star> \<psi> \<longlongrightarrow> \<xi>)\<close>
  by (auto simp add: aentails_def awand_def asepconj_def asat_def)

text \<open>The adjunction alone determines the magic wand and can be used to proved its properties.
For example, the magic wand preserves upwards closure:\<close>
lemma ucincl_awand [ucincl_intros]:
  assumes \<open>ucincl \<psi>\<close>
    shows \<open>ucincl (\<phi> \<Zsurj> \<psi>)\<close>
using assms by (clarsimp simp add: ucincl_alt' awand_adjoint)
  (metis asepconj_assoc asepconj_comm)

\<comment>\<open>TODO: May this be the more efficient rule to use in automation, rather than
\<^verbatim>\<open>ucincl_awand\<close>? The LHS of the wand is usually the simpler one.\<close>
lemma ucincl_awand2:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>ucincl (\<phi> \<Zsurj> \<psi>)\<close>
using asepconj_assoc asepconj_ident assms awand_adjoint local.ucincl_alt' by auto

lemma awand_adjointI:
  assumes \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> (\<psi> \<Zsurj> \<xi>)\<close>
using assms awand_adjoint by auto

text \<open>A wand from the empty assertion needs no closure condition.\<close>
lemma awand_emp_adjointI:
  assumes \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>emp \<longlongrightarrow> (\<psi> \<Zsurj> \<xi>)\<close>
using assms by (simp add: awand_adjoint asepconj_emp_unit)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aimplies_implies_awand:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>\<phi> \<sqsubseteq> \<psi> \<longlongrightarrow> \<phi> \<Zsurj> \<psi>\<close>
using assms aimplies_have awand_adjoint asepconj_comm by force

text \<open>The separating conjunction and magic wand also satisfy a \<^emph>\<open>modus ponens\<close>-like relationship:\<close>
lemma awand_counit:
  shows \<open>\<psi> \<star> (\<psi> \<Zsurj> \<xi>) \<longlongrightarrow> \<xi>\<close>
by (metis awand_adjoint aentails_refl asepconj_comm)

lemma awand_counit2:
  assumes \<open>ucincl \<psi>\<close>
    shows \<open>\<psi> \<star> (\<psi> \<Zsurj> \<xi>) \<longlongrightarrow> \<psi> \<inter> \<xi>\<close>
using assms by (simp add: aentails_simp aentails_cancel_r awand_counit ucincl_awand)

lemma asepconj_frame_rev:
  assumes \<open>\<phi>' \<longlongrightarrow> (\<phi>'' \<Zsurj> \<psi>)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> \<phi>''\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_simp intro: aentails_intro)

lemma awand_bot:
  shows \<open>{} \<Zsurj> \<phi> = UNIV\<close>
  by (simp add: aentails_yonedaI aentails_true asepconj_bot_zero2 awand_adjoint bot_aentails_all)

lemma awand_univ:
  assumes \<open>ucincl \<phi>\<close>
    shows \<open>UNIV \<Zsurj> \<phi> = \<phi>\<close>
by (metis aentails_cancel_r aentails_eq asepconj_ident2 assms awand_adjoint ucincl_awand)

lemma aentails_conditional_crule_strong':
  assumes \<open>\<alpha> \<longlongrightarrow> (\<beta> \<Zsurj> \<gamma>) \<star> \<delta>\<close>
      and \<open>H \<star> \<delta> \<longlongrightarrow> \<beta> \<star> G\<close>
    shows \<open>H \<star> \<alpha> \<longlongrightarrow> \<gamma> \<star> G\<close>
proof -
  from \<open>\<alpha> \<longlongrightarrow> (\<beta> \<Zsurj> \<gamma>) \<star> \<delta>\<close>
    have \<open>H \<star> \<alpha> \<longlongrightarrow> H \<star> \<delta> \<star> (\<beta> \<Zsurj> \<gamma>)\<close>
      by (simp add: asepconj_comm asepconj_mono)
  also from \<open>H \<star> \<delta> \<longlongrightarrow> \<beta> \<star> G\<close> have \<open>\<dots> \<longlongrightarrow> \<beta> \<star> G \<star> (\<beta> \<Zsurj> \<gamma>)\<close>
    by (metis asepconj_assoc asepconj_mono2)
  also have \<open>\<dots>  \<longlongrightarrow> \<gamma> \<star> G\<close>
    by (simp add: asepconj_comm asepconj_mono asepconj_swap_top awand_counit)
  finally show ?thesis
    by simp
qed

lemma aentails_conditional_crule':
  assumes \<open>\<alpha> \<star> \<beta> \<longlongrightarrow> \<gamma> \<star> \<delta>\<close>
      and \<open>H \<longlongrightarrow> \<beta> \<star> (\<delta> \<Zsurj> G)\<close>
    shows \<open>H \<star> \<alpha> \<longlongrightarrow> \<gamma> \<star> G\<close>
proof -
  from \<open>H \<longlongrightarrow> \<beta> \<star> (\<delta> \<Zsurj> G)\<close> have \<open>H \<star> \<alpha> \<longlongrightarrow> \<alpha> \<star> \<beta> \<star> (\<delta> \<Zsurj> G)\<close>
    by (metis asepconj_comm asepconj_mono)
  also from \<open>\<alpha> \<star> \<beta> \<longlongrightarrow> \<gamma> \<star> \<delta>\<close> have \<open>\<dots> \<longlongrightarrow> \<gamma> \<star> \<delta> \<star> (\<delta> \<Zsurj> G)\<close>
    by (metis asepconj_assoc asepconj_mono2)
  also have \<open>\<dots>  \<longlongrightarrow> \<gamma> \<star> G\<close>
    by (simp add: aentails_refl asepconj_comm asepconj_mono_sym awand_counit)
  finally show ?thesis
    by simp
qed

text \<open>A conditional crule rewrites \<^term>\<open>\<alpha>\<close> into \<^term>\<open>\<beta>\<close> while
exchanging \<^term>\<open>C0\<close> for \<^term>\<open>C1\<close>. The strong form internalises consumption
of \<^term>\<open>C0\<close> in a wand. Closure is not part of either connective; derived
rules that discard an exchange residue carry their own disposal premise.\<close>
definition aentails_conditional_crule ("_ [_]\<longlongrightarrow>[_] _")
  where \<open>aentails_conditional_crule \<alpha> C0 C1 \<beta> \<equiv> C0 \<star> \<alpha> \<longlongrightarrow> C1 \<star> \<beta>\<close>
definition aentails_conditional_crule_strong ("_ [_]\<longlongrightarrow>\<^sub>s[_] _")
  where \<open>aentails_conditional_crule_strong \<alpha> C0 C1 \<beta> \<equiv> \<alpha> \<longlongrightarrow> C1 \<star> (C0 \<Zsurj> \<beta>)\<close>

lemma aentails_forallL:
  shows \<open>(\<Sqinter>x. \<alpha> x) \<longlongrightarrow> \<alpha> x\<close>
  by (simp add: aentails_def)

lemma awand_lambda_crule_any:
  shows \<open>(\<alpha> \<Zsurj> \<beta>) [\<alpha>]\<longlongrightarrow>[\<beta>] UNIV\<close>
        \<open>(\<Sqinter>x0. (\<alpha>0 x0 \<Zsurj> \<beta>0 x0)) [\<alpha>0 x0]\<longlongrightarrow>[\<beta>0 x0] UNIV\<close>
        \<open>(\<Sqinter>x0 x1. (\<alpha>1 x0 x1 \<Zsurj> \<beta>1 x0 x1)) [\<alpha>1 x0 x1]\<longlongrightarrow>[\<beta>1 x0 x1] UNIV\<close>
        \<open>(\<Sqinter>x0 x1 x2. (\<alpha>2 x0 x1 x2 \<Zsurj> \<beta>2 x0 x1 x2)) [\<alpha>2 x0 x1 x2]\<longlongrightarrow>[\<beta>2 x0 x1 x2] UNIV\<close>
        \<open>(\<Sqinter>x0 x1 x2 x3. (\<alpha>3 x0 x1 x2 x3 \<Zsurj> \<beta>3 x0 x1 x2 x3)) [\<alpha>3 x0 x1 x2 x3]\<longlongrightarrow>[\<beta>3 x0 x1 x2 x3] UNIV\<close>
        \<open>(\<Sqinter>x0 x1 x2 x3 x4. (\<alpha>4 x0 x1 x2 x3 x4 \<Zsurj> \<beta>4 x0 x1 x2 x3 x4)) [\<alpha>4 x0 x1 x2 x3 x4]\<longlongrightarrow>[\<beta>4 x0 x1 x2 x3 x4] UNIV\<close>
        \<open>(\<Sqinter>x0 x1 x2 x3 x4 x5. (\<alpha>5 x0 x1 x2 x3 x4 x5 \<Zsurj> \<beta>5 x0 x1 x2 x3 x4 x5)) [\<alpha>5 x0 x1 x2 x3 x4 x5]\<longlongrightarrow>[\<beta>5 x0 x1 x2 x3 x4 x5] UNIV\<close>
   unfolding aentails_conditional_crule_def
   apply (all \<open>rule asepconj_mono6[OF _ aentails_true]\<close>)
   by (all \<open>((rule aentails_trans, rule asepconj_mono[OF aentails_forallL])+)?, rule awand_counit\<close>)

lemma aentails_conditional_crule:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>[R] \<beta>\<close>
      and \<open>H \<longlongrightarrow> L \<star> R \<Zsurj> G\<close>
    shows \<open>\<alpha> \<star> H \<longlongrightarrow> \<beta> \<star> G\<close>
proof -
  from \<open>\<alpha> [L]\<longlongrightarrow>[R] \<beta>\<close> have \<open>\<alpha> \<star> L \<longlongrightarrow> \<beta> \<star> R\<close>
    unfolding aentails_conditional_crule_def by (simp add: asepconj_comm)
  from aentails_conditional_crule'[OF this] and assms show ?thesis
    by (simp add: asepconj_comm)
qed

lemma aentails_conditional_crule_L0:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>[R] \<beta>\<close>
      and \<open>UNIV \<longlongrightarrow> L \<star> R \<Zsurj> G\<close>
    shows \<open>\<alpha> \<longlongrightarrow> \<beta> \<star> G\<close>
  by (rule aentails_trans'[OF aentails_conditional_crule[OF assms]
        asepconj_mono6[OF aentails_refl aentails_true]])

text \<open>These rules collapse the exchange residue to \<^term>\<open>UNIV\<close>. Their
\<^term>\<open>ucincl \<beta>\<close> premise is exactly the licence
\<^term>\<open>discardable_in \<top> \<beta>\<close> for dropping that residue.\<close>
lemma aentails_conditional_crule_R0:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>[R] \<beta>\<close>
      and \<open>H \<longlongrightarrow> L \<star> R \<Zsurj> UNIV\<close>
      and \<open>ucincl \<beta>\<close>
    shows \<open>\<alpha> \<star> H \<longlongrightarrow> \<beta>\<close>
proof -
  from assms(1,2) have \<open>\<alpha> \<star> H \<longlongrightarrow> \<beta> \<star> UNIV\<close>
    by (rule aentails_conditional_crule)
  with \<open>ucincl \<beta>\<close> show ?thesis
    by (simp add: asepconj_ident2)
qed

lemma aentails_conditional_crule_LR0:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>[R] \<beta>\<close>
      and \<open>UNIV \<longlongrightarrow> L \<star> R \<Zsurj> UNIV\<close>
      and \<open>ucincl \<beta>\<close>
    shows \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>
proof -
  from assms(1,2) have \<open>\<alpha> \<longlongrightarrow> \<beta> \<star> UNIV\<close>
    by (rule aentails_conditional_crule_L0)
  with \<open>ucincl \<beta>\<close> show ?thesis
    by (simp add: asepconj_ident2)
qed

lemmas aentails_conditional_crules =
  aentails_conditional_crule
  aentails_conditional_crule_L0
  aentails_conditional_crule_R0
  aentails_conditional_crule_LR0

lemma aentails_conditional_crule_Runiv:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>[R] UNIV\<close>
      and \<open>ucincl G\<close>
      and \<open>H \<longlongrightarrow> L \<star> R \<Zsurj> G\<close>
    shows \<open>\<alpha> \<star> H \<longlongrightarrow> G\<close>
proof -
  from \<open>\<alpha> [L]\<longlongrightarrow>[R] UNIV\<close> have \<open>\<alpha> \<star> L \<longlongrightarrow> UNIV \<star> R\<close>
    unfolding aentails_conditional_crule_def by (simp add: asepconj_comm)
  from aentails_conditional_crule'[OF this] and assms show ?thesis
    by (metis asepconj_comm local.ucincl_alt)
qed

lemma aentails_conditional_crule_Luniv:
  assumes \<open>UNIV [L]\<longlongrightarrow>[R] \<beta>\<close>
      and \<open>H \<longlongrightarrow> L \<star> R \<Zsurj> G\<close>
    shows \<open>H \<longlongrightarrow> \<beta> \<star> G\<close>
proof -
  from \<open>UNIV [L]\<longlongrightarrow>[R] \<beta>\<close> have \<open>UNIV \<star> L \<longlongrightarrow> \<beta> \<star> R\<close>
    unfolding aentails_conditional_crule_def by (simp add: asepconj_comm)
  from aentails_conditional_crule'[OF this assms(2)] have \<open>H \<star> UNIV \<longlongrightarrow> \<beta> \<star> G\<close> .
  moreover have \<open>H \<longlongrightarrow> H \<star> UNIV\<close>
    by (rule asepconj_mono6[OF aentails_refl aentails_true])
  ultimately show ?thesis
    by (rule aentails_trans[rotated])
qed

lemma aentails_conditional_crule_L0_Runiv:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>[R] UNIV\<close>
      and \<open>ucincl G\<close>
      and \<open>UNIV \<longlongrightarrow> L \<star> R \<Zsurj> G\<close>
    shows \<open>\<alpha> \<longlongrightarrow> G\<close>
  by (metis aentails_conditional_crule_L0 asepconj_ident assms(1,2,3))

text \<open>This rule discards a \<^term>\<open>UNIV\<close> residue. The \<^verbatim>\<open>Runiv\<close>
variants use \<^term>\<open>ucincl G\<close> for the same disposal licence.\<close>
lemma aentails_conditional_crule_R0_Luniv:
  assumes \<open>UNIV [L]\<longlongrightarrow>[R] \<beta>\<close>
      and \<open>H \<longlongrightarrow> L \<star> R \<Zsurj> UNIV\<close>
      and \<open>ucincl \<beta>\<close>
    shows \<open>H \<longlongrightarrow> \<beta>\<close>
proof -
  from assms(1,2) have \<open>H \<longlongrightarrow> \<beta> \<star> UNIV\<close>
    by (rule aentails_conditional_crule_Luniv)
  with \<open>ucincl \<beta>\<close> show ?thesis
    by (simp add: asepconj_ident2)
qed

lemmas aentails_conditional_crules_univ =
  aentails_conditional_crule_Luniv
  aentails_conditional_crule_Runiv
  aentails_conditional_crule_L0_Runiv
  aentails_conditional_crule_R0_Luniv

lemma aentails_conditional_crule_strong:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>\<^sub>s[R] \<beta>\<close>
      and \<open>H \<star> R \<longlongrightarrow> L \<star> G\<close>
    shows \<open>\<alpha> \<star> H \<longlongrightarrow> \<beta> \<star> G\<close>
proof -
  from \<open>\<alpha> [L]\<longlongrightarrow>\<^sub>s[R] \<beta>\<close> have \<open>\<alpha> \<longlongrightarrow> (L\<Zsurj>\<beta>) \<star> R\<close>
    unfolding aentails_conditional_crule_strong_def by (simp add: asepconj_comm)
  from aentails_conditional_crule_strong'[OF this] and assms show ?thesis
    by (simp add: asepconj_comm)
qed

text \<open>Strong crules reconcile the exchange inside the wand. A degenerate
residue is therefore \<^term>\<open>emp\<close> and needs no disposal premise.\<close>
lemma aentails_conditional_crule_strong_L0:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>\<^sub>s[R] \<beta>\<close>
      and \<open>R \<longlongrightarrow> L \<star> G\<close>
    shows \<open>\<alpha> \<longlongrightarrow> \<beta> \<star> G\<close>
proof -
  from \<open>R \<longlongrightarrow> L \<star> G\<close> have \<open>emp \<star> R \<longlongrightarrow> L \<star> G\<close>
    by (simp add: asepconj_emp_unit)
  from aentails_conditional_crule_strong[OF assms(1) this] show ?thesis
    by (simp add: asepconj_emp_unit)
qed

lemma aentails_conditional_crule_strong_R0:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>\<^sub>s[R] \<beta>\<close>
      and \<open>H \<star> R \<longlongrightarrow> L\<close>
    shows \<open>\<alpha> \<star> H \<longlongrightarrow> \<beta>\<close>
proof -
  from \<open>H \<star> R \<longlongrightarrow> L\<close> have \<open>H \<star> R \<longlongrightarrow> L \<star> emp\<close>
    by (simp add: asepconj_emp_unit)
  from aentails_conditional_crule_strong[OF assms(1) this] show ?thesis
    by (simp add: asepconj_emp_unit)
qed

lemma aentails_conditional_crule_strong_LR0:
  assumes \<open>\<alpha> [L]\<longlongrightarrow>\<^sub>s[R] \<beta>\<close>
      and \<open>R \<longlongrightarrow> L\<close>
    shows \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>
  by (meson aentails_conditional_crule_strong_def aentails_trans assms(1,2) awand_adjoint awand_counit)

lemmas aentails_conditional_crules_strong = aentails_conditional_crule_strong
   aentails_conditional_crule_strong_L0
   aentails_conditional_crule_strong_R0
   aentails_conditional_crule_strong_LR0

text\<open>Note that the converse of \<^verbatim>\<open>awand_counit2\<close> does not seem to hold in general, but one can prove
the following weaker version:\<close>

definition is_principal :: \<open>'a assert \<Rightarrow> bool\<close> where
  \<open>is_principal \<phi> \<longleftrightarrow> (\<exists>s. \<phi> = {s'. s \<preceq> s'})\<close>

definition is_principal' :: \<open>'a assert \<Rightarrow> bool\<close> where
  \<open>is_principal' \<phi> \<equiv> \<exists>s. \<forall>s'. (s' \<Turnstile> \<phi>) \<longleftrightarrow> (s \<preceq> s')\<close>

lemma is_principal_alt:
  shows \<open>is_principal \<phi> \<longleftrightarrow> is_principal' \<phi>\<close>
  by (auto simp: is_principal'_def is_principal_def asat_def)

lemma ucincl_principal:
  assumes \<open>is_principal \<phi>\<close>
    shows \<open>ucincl \<phi>\<close>
using assms by (auto simp add: is_principal_def intro: ucpred_upward_closure)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma awand_counit_inv:
  assumes 1: \<open>is_principal \<psi>\<close>
      and \<open>ucincl \<xi>\<close>
    shows \<open>\<psi> \<inter> \<xi> \<longlongrightarrow> \<psi> \<star> (\<psi> \<Zsurj> \<xi>)\<close>
proof -
  from 1 obtain s0 where s_base: \<open>\<And>s. (s \<Turnstile> \<psi>) = (s0 \<preceq> s)\<close>
    by (fastforce simp add: is_principal'_def is_principal_alt)
  from this have \<open>s0 \<Turnstile> \<psi>\<close>
    by auto
  have \<open>s \<Turnstile> \<psi> \<star> (\<psi> \<Zsurj> \<xi>)\<close> if \<open>s \<Turnstile> \<psi> \<inter> \<xi>\<close> for s
  proof -
    have \<open>s \<Turnstile> \<psi>\<close> and \<open>s \<Turnstile> \<xi>\<close> and \<open>s0 \<preceq> s\<close>
      using that s_base by auto
    then obtain s1 where \<open>s = s0 + s1\<close> and \<open>s0 \<sharp> s1\<close>
      by (auto simp add: derived_order_def)
    have \<open>s1 + s' \<Turnstile> \<xi>\<close>
      if \<open>s' \<Turnstile> \<psi>\<close> and \<open>s1 \<sharp> s'\<close> for s'
    proof -
      from that and s_base obtain s1' where \<open>s' = s0 + s1'\<close> and \<open>s0 \<sharp> s1'\<close>
        by auto
      with \<open>s1 \<sharp> s'\<close> have \<open>s1 + s' = (s0 + s1) + s1'\<close>
        by (metis disjoint_sym sepalg_apart_plus sepalg_assoc sepalg_comm)
      from \<open>s' = s0 + s1'\<close> \<open>s0 \<sharp> s1'\<close> \<open>s1 \<sharp> s'\<close> have \<open>(s0 + s1) \<sharp> s1'\<close>
        by auto
      from this and \<open>s = s0 + s1\<close> \<open>s1 + s' = s0 + s1 + s1'\<close> have \<open>s \<preceq> s1 + s'\<close>
        by auto
      from this and \<open>s \<Turnstile> \<xi>\<close> and \<open>ucincl \<xi>\<close> show ?thesis
        by (auto intro: asat_derived_order_monotone)
    qed
    with \<open>s = s0 + s1\<close> \<open>s0 \<Turnstile> \<psi>\<close> \<open>s0 \<sharp> s1\<close> show ?thesis
      by (metis awandI local.asepconjI)
  qed
  from this show \<open>\<psi> \<inter> \<xi> \<longlongrightarrow> \<psi> \<star> (\<psi> \<Zsurj> \<xi>)\<close>
    by (intro aentailsI)
qed

subsubsection\<open>Notions of disjointness for assertions\<close>

subsection\<open>Notions of disjointness for assertions\<close>

text \<open>This definition is somewhat strange because it is not even assumed that the two states
share a common super state.\<close>
definition assert_strong_disj :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> bool\<close>
  where \<open>assert_strong_disj \<xi> \<psi> \<equiv> (\<forall>\<sigma>0 \<sigma>1.
    \<sigma>0 \<in> \<xi> \<longrightarrow> \<sigma>1 \<Turnstile> \<psi> \<longrightarrow> (\<exists>\<sigma>0' \<sigma>1'. \<sigma>0' \<preceq> \<sigma>0 \<and> \<sigma>1' \<Turnstile> \<psi> \<and> \<sigma>1' \<preceq> \<sigma>1 \<and> \<sigma>0' \<Turnstile> \<xi> \<and> \<sigma>0' \<sharp> \<sigma>1'))\<close>

text\<open>The following definition is more natural, but it is not sufficient to prove the lemma
\<^verbatim>\<open>atriple_frame_rev\<close> below.\<close>
definition assert_disj :: \<open>'a assert \<Rightarrow> 'a assert \<Rightarrow> bool\<close> where
  \<open>assert_disj \<xi> \<psi> \<equiv> \<xi> \<sqinter> \<psi> = \<xi> \<star> \<psi>\<close>

lemma assert_strong_disj_pairwise_disj:
  assumes \<open>\<And>\<sigma> \<sigma>'. \<sigma> \<Turnstile> \<xi> \<Longrightarrow> \<sigma>' \<Turnstile> \<psi> \<Longrightarrow> \<sigma> \<sharp> \<sigma>'\<close>
    shows \<open>assert_strong_disj \<xi> \<psi>\<close>
by (metis asat_def assert_strong_disj_def assms local.derived_order_refl)

lemma assert_strong_disj_upward_closure:
  shows \<open>assert_strong_disj (\<xi> \<star> \<top>) (\<psi> \<star> \<top>) \<longleftrightarrow> assert_strong_disj \<xi> \<psi>\<close>
proof safe
  assume DISJ: \<open>assert_strong_disj (\<xi> \<star> \<top>) (\<psi> \<star> \<top>)\<close>
  {
       fix \<sigma> \<sigma>'
    assume \<open>\<sigma> \<Turnstile> \<xi>\<close>
       and \<open>\<sigma>' \<Turnstile> \<psi>\<close>
    from this have \<open>\<sigma> \<Turnstile> \<xi> \<star> \<top>\<close> and \<open>\<sigma>' \<Turnstile> \<psi> \<star> \<top>\<close>
      by (simp add: asepconj_weakenI)+
    from this obtain \<sigma>0 and \<sigma>1 where \<open>\<sigma>0 \<preceq> \<sigma>\<close> and \<open>\<sigma>1 \<preceq> \<sigma>'\<close> and \<open>\<sigma>0 \<Turnstile> \<xi> \<star> \<top>\<close> and \<open>\<sigma>1 \<Turnstile> \<psi> \<star> \<top>\<close>
      and \<open>\<sigma>0 \<sharp> \<sigma>1\<close> by (meson DISJ asat_def assert_strong_disj_def)
    moreover from this obtain \<sigma>0' and \<sigma>1' where \<open>\<sigma>0' \<preceq> \<sigma>0\<close> and \<open>\<sigma>1' \<preceq> \<sigma>1\<close> and \<open>\<sigma>0' \<Turnstile> \<xi>\<close> and \<open>\<sigma>1' \<Turnstile> \<psi>\<close>
      by (metis local.asepconjE local.derived_orderI)
    moreover from calculation have \<open>\<sigma>0' \<sharp> \<sigma>1'\<close>
      by (meson local.derived_order_distinct_downward_closed local.disjoint_sym)
    ultimately have \<open>\<exists>\<sigma>0' \<sigma>1'. \<sigma>0' \<sharp> \<sigma>1' \<and> \<sigma>0' \<preceq> \<sigma> \<and> \<sigma>1' \<preceq> \<sigma>' \<and> \<sigma>0' \<Turnstile> \<xi> \<and> \<sigma>1' \<Turnstile> \<psi>\<close>
      by (meson local.derived_order_trans) }
  from this show \<open>assert_strong_disj \<xi> \<psi>\<close>
    by (metis asat_def assert_strong_disj_def)
next
  assume DISJ: \<open>assert_strong_disj \<xi> \<psi>\<close>
  {
       fix \<sigma> \<sigma>'
    assume \<open>\<sigma> \<Turnstile> \<xi> \<star> \<top>\<close>
       and \<open>\<sigma>' \<Turnstile> \<psi> \<star> \<top>\<close>
    from this obtain \<sigma>0 and \<sigma>1 where \<open>\<sigma>0 \<preceq> \<sigma>\<close> and \<open>\<sigma>1 \<preceq> \<sigma>'\<close> and \<open>\<sigma>0 \<Turnstile> \<xi>\<close> and \<open>\<sigma>1 \<Turnstile> \<psi>\<close>
      by (metis local.asepconjE local.derived_orderI)
    moreover from this obtain \<sigma>0' and \<sigma>1' where \<open>\<sigma>0' \<preceq> \<sigma>0\<close> and \<open>\<sigma>1' \<preceq> \<sigma>1\<close> and \<open>\<sigma>0' \<Turnstile> \<xi>\<close> and \<open>\<sigma>1' \<Turnstile> \<psi>\<close> and \<open>\<sigma>0' \<sharp> \<sigma>1'\<close>
      by (meson DISJ asat_def assert_strong_disj_def)
    moreover from this have \<open>\<sigma>0' \<Turnstile> \<xi> \<star> \<top>\<close> and \<open>\<sigma>1' \<Turnstile> \<psi> \<star> \<top>\<close>
      by (simp add: asepconj_weakenI)+
    ultimately have \<open>\<exists>\<sigma>0' \<sigma>1'. \<sigma>0' \<sharp> \<sigma>1' \<and> \<sigma>0' \<preceq> \<sigma> \<and> \<sigma>1' \<preceq> \<sigma>' \<and> \<sigma>0' \<Turnstile> \<xi> \<star> \<top> \<and> \<sigma>1' \<Turnstile> \<psi> \<star> \<top>\<close>
      by (meson local.derived_order_trans) }
  from this show \<open>assert_strong_disj (\<xi> \<star> \<top>) (\<psi> \<star> \<top>)\<close>
    by (metis asat_def assert_strong_disj_def)
qed

(*<*)
end

context cross_split_sepalg begin
(*>*)

lemma assert_disj_weak_strong:
  assumes \<open>ucincl \<xi>\<close>
      and \<open>ucincl \<psi>\<close>
      and \<open>assert_strong_disj \<xi> \<psi>\<close>
    shows \<open>assert_disj \<xi> \<psi>\<close>
proof -
  {
       fix \<sigma>
    assume \<open>\<sigma> \<Turnstile> \<xi>\<close>
       and \<open>\<sigma> \<Turnstile> \<psi>\<close>
    moreover from this and assms obtain \<sigma>0 and \<sigma>1 where \<open>\<sigma>0 \<preceq> \<sigma>\<close> and \<open>\<sigma>1 \<preceq> \<sigma>\<close>
      and \<open>\<sigma>0 \<sharp> \<sigma>1\<close> and \<open>\<sigma>0 \<Turnstile> \<xi>\<close> and \<open>\<sigma>1 \<Turnstile> \<psi>\<close>
      by (meson asat_def local.assert_strong_disj_def)
    moreover from this have \<open>\<sigma>0 + \<sigma>1 \<preceq> \<sigma>\<close>
      using local.sepalg_derived_order_plus by auto
    ultimately have \<open>\<sigma> \<Turnstile> \<xi> \<star> \<psi>\<close>
      by (meson assms(1) local.asat_derived_order_monotone local.asepconjI local.ucincl_asepconjL) }
  from this have \<open>\<xi> \<sqinter> \<psi> \<subseteq> \<xi> \<star> \<psi>\<close>
    by (simp add: asat_def subset_eq)
  moreover from assms have \<open>\<xi> \<star> \<psi> \<subseteq> \<xi> \<sqinter> \<psi>\<close>
    by (meson aentails_eq aentails_refl inf.orderI aentails_cancel_l aentails_cancel_r aentails_int)
  ultimately show ?thesis unfolding assert_disj_def by auto
qed

(*<*)
end

context sepalg begin
(*>*)

subsubsection\<open>State-querying operations\<close>

text \<open>All assertions have been largely-ambivalent about the underlying machine state, thus far,
aside from assuming a separation algebra structure on it.  Here, we start to introduce assertions
that assume more about the structure of the underlying machine.  In particular, we introduce the
following assertion that allows us to query directly the machine state:\<close>
definition has :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'a assert\<close> where
  \<open>has f v \<equiv> {s. f s = v}\<close>

text \<open>This assertion also preserves upwards closure for state-querying functions that are also
closed under upwards-closure:\<close>
lemma ucincl_has:
  assumes \<open>\<And>x y. x \<sharp> y \<Longrightarrow> f x = v \<Longrightarrow> f (x + y) = v\<close>
    shows \<open>ucincl (has f v)\<close>
using assms by (auto intro!: ucinclI ucpredI simp add: derived_order_def has_def)

subsubsection\<open>Pure assertions\<close>

text \<open>A precise pure assertion carries a HOL fact while owning exactly the empty machine state.\<close>
definition apure_precise :: \<open>bool \<Rightarrow> 'a assert\<close> (\<open>\<langle>_\<rangle>\<close> [0]1000) where
  \<open>\<langle>P\<rangle> \<equiv> {s. s = 0 \<and> P}\<close>

text \<open>The legacy spelling denotes a precise pure fact framed by arbitrary resource. It remains a
compatibility abbreviation rather than a second primitive assertion.\<close>
abbreviation apure :: \<open>bool \<Rightarrow> 'a assert\<close> where
  \<open>apure P \<equiv> UNIV \<star> \<langle>P\<rangle>\<close>

text \<open>This internal wrapper keeps Crush's generated pure conclusion opaque. It is needed to make
sure spatial drules trigger before the late introduction rule turns the separation-logic entailment
into a pure HOL goal.\<close>
definition apure_crush_obligation :: \<open>bool \<Rightarrow> 'a assert\<close> where
  \<open>apure_crush_obligation P \<equiv> apure P\<close>

text \<open>A precise pure assertion owns zero and is therefore discardable in
every context. A dedicated rule complements the syntactically distinct
\<^term>\<open>emp\<close> rule.\<close>
lemma discardable_in_apure_preciseI [discardable_in_intros]:
  shows \<open>discardable_in \<langle>P\<rangle> \<rho>\<close>
proof (rule discardable_in_aentails_empI)
  show \<open>\<langle>P\<rangle> \<longlongrightarrow> emp\<close>
    by (simp add: aentails_def asat_def apure_precise_def emp_def)
qed

text \<open>Precise pure factors combine without absorbing resource.\<close>
lemma asepconj_pure_precise [asepconj_simp]:
  shows \<open>\<langle>P\<rangle> \<star> \<langle>Q\<rangle> = \<langle>P \<and> Q\<rangle>\<close>
by (auto simp add: apure_precise_def asepconj_def asat_def)

lemma asepconj_pure2_precise [asepconj_simp]:
  shows \<open>\<langle>P\<rangle> \<star> (\<langle>Q\<rangle> \<star> \<phi>) = \<langle>P \<and> Q\<rangle> \<star> \<phi>\<close>
using asepconj_assoc asepconj_pure_precise by metis

text \<open>Satisfaction records both the pure fact and ownership of zero.\<close>
lemma asat_apure_precise_characterisation [asat_simp, simp]:
  shows \<open>x \<Turnstile> \<langle>P\<rangle> \<longleftrightarrow> x = 0 \<and> P\<close>
by (simp add: apure_precise_def asat_def)

corollary is_sat_pure_precise [is_sat_simp, simp]:
  shows \<open>is_sat \<langle>P\<rangle> = P\<close>
by (simp add: asat_apure_precise_characterisation is_sat_def)

text \<open>Precise-pure factors own zero, so satisfaction distributes unconditionally on either side.\<close>
lemma asat_apure_precise_distrib [asat_simp]:
  shows \<open>s \<Turnstile> \<langle>P\<rangle> \<star> \<phi> \<longleftrightarrow> P \<and> s \<Turnstile> \<phi>\<close>
by (simp add: apure_precise_def asepconj_def asat_def)

lemma asat_apure_precise_distrib2 [asat_simp]:
  shows \<open>s \<Turnstile> \<phi> \<star> \<langle>P\<rangle> \<longleftrightarrow> s \<Turnstile> \<phi> \<and> P\<close>
using asat_apure_precise_distrib local.asepconj_comm by force

text \<open>Truth yields the empty assertion; falsehood remains impossible.\<close>
lemma apure_precise_True [asepconj_simp]:
  shows \<open>\<langle>True\<rangle> = emp\<close>
by (simp add: apure_precise_def emp_def)

lemma apure_precise_False [asepconj_simp]:
  shows \<open>\<langle>False\<rangle> = \<bottom>\<close>
by (simp add: apure_precise_def)

text \<open>Pure assumptions can be hoisted without a closure premise; a standalone
factor leaves \<^term>\<open>emp\<close> behind.\<close>
lemma apure_precise_entailsL0:
  assumes \<open>P \<Longrightarrow> emp \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<langle>P\<rangle> \<longlongrightarrow> \<psi>\<close>
using assms by (simp add: asat_simp aentails_def)

lemma apure_precise_entailsL:
  assumes \<open>P \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<langle>P\<rangle> \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: asat_simp aentails_def elim!: asepconjE)

text \<open>Only empty resource can entail a standalone precise pure assertion.\<close>
lemma apure_precise_entailsR0:
  assumes \<open>P\<close>
    shows \<open>emp \<longlongrightarrow> \<langle>P\<rangle>\<close>
using assms by (simp add: asat_simp aentails_def)

text \<open>The following results describe how the Boolean quantifiers interact with respect to
satisfiability, and can be seen as restricted forms of our previous characterisation lemma, above:\<close>
lemma asat_existsE [elim]:
  assumes \<open>s \<Turnstile> (\<Squnion> x. P x)\<close>
     and \<open>\<And>x. s \<Turnstile> P x \<Longrightarrow> Q\<close>
   shows \<open>Q\<close>
using assms by auto

lemma asat_existsE' [elim]:
  assumes \<open>s \<Turnstile> (\<Union> x \<in> S. P x)\<close>
     and \<open>\<And>x. x \<in> S \<Longrightarrow> s \<Turnstile> P x \<Longrightarrow> Q\<close>
   shows \<open>Q\<close>
using assms by auto

lemma asat_existsI [asat_intro]:
  assumes \<open>x \<Turnstile> P a\<close>
    shows \<open>x \<Turnstile> (\<Squnion>a. P a)\<close>
using assms by auto

lemma asat_forallE [elim]:
  assumes \<open>x \<Turnstile> (\<Sqinter>a. P a)\<close>
      and \<open>(\<And>a. x \<Turnstile> P a) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by auto

lemma asat_forallI [asat_intro]:
  assumes \<open>\<And>a. x \<Turnstile> P a\<close>
    shows \<open>x \<Turnstile> (\<Sqinter>a. P a)\<close>
using assms by auto

lemma aexists_entailsL [aentails_intro]:
  assumes \<open>\<And>x. \<phi> x \<longlongrightarrow> \<psi>\<close>
    shows \<open>(\<Squnion>x. \<phi> x) \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_def)

lemma aexists_entailsL' [aentails_intro]:
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> \<phi> x \<longlongrightarrow> \<psi>\<close>
    shows \<open>(\<Squnion>x \<in> S. \<phi> x) \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_def)

lemma aexists_entailsR [aentails_intro]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> x\<close>
    shows \<open>\<phi> \<longlongrightarrow> (\<Squnion>x. \<psi> x)\<close>
using assms by (auto simp add: aentails_def)

lemma aexists_entailsR' [aentails_intro]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> x\<close> and \<open>x \<in> S\<close>
    shows \<open>\<phi> \<longlongrightarrow> (\<Squnion>x \<in> S. \<psi> x)\<close>
using assms by (auto simp add: aentails_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aentails_bUnion_pointwise:
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> \<phi> x \<longlongrightarrow> \<psi> x\<close>
    shows \<open>(\<Union>x\<in>S. \<phi> x) \<longlongrightarrow> (\<Union>x\<in>S. \<psi> x)\<close>
using assms by (meson local.aexists_entailsL' aexists_entailsR')

lemma aforall_entailsL [aentails_intro]:
  assumes \<open>\<phi> x \<longlongrightarrow> \<psi>\<close>
    shows \<open>(\<Sqinter>x. \<phi> x) \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_def)

lemma aforall_entailsR [aentails_intro]:
  assumes \<open>\<And>x. \<phi> \<longlongrightarrow> \<psi> x\<close>
    shows \<open>\<phi> \<longlongrightarrow> (\<Sqinter>x. \<psi> x)\<close>
using assms by (auto simp add: aentails_def)

lemma aentails_top_L [aentails_intro]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>ucincl \<phi>\<close>
    shows \<open>\<top> \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
using assms by (fastforce simp add: asepconj_simp)

lemma aentails_top_L':
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>ucincl \<phi>\<close>
    shows \<open>\<phi> \<star> \<top> \<longlongrightarrow> \<psi>\<close>
using assms aentails_top_L asepconj_comm by (auto intro: aentails_intro)

\<comment>\<open>An upwards-closed conclusion can absorb a trailing \<^term>\<open>\<top>\<close>. The rule stays outside
\<^verbatim>\<open>aentails_intro\<close> because the sibling and conclusion licences are ambiguous from the goal.\<close>
lemma aentails_drop_univ_ucincl:
  assumes \<open>ucincl \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<star> \<top> \<longlongrightarrow> \<psi>\<close>
using assms ucincl_alt' by blast

lemma aentails_top_R [aentails_intro]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<top> \<star> \<psi>\<close>
using assms by (metis asepconj_comm aentails_true asepconj_mono6)

lemma aentails_top_R_refl [simp]:
  shows \<open>\<phi> \<longlongrightarrow> \<top> \<star> \<phi>\<close>
by (rule aentails_top_R[OF aentails_refl])

lemma aentails_top_R':
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi> \<star> \<top>\<close>
using assms aentails_top_R asepconj_comm by (auto intro: aentails_intro)

text \<open>These rules are intended for backward use. They match a right-hand
intersection, universal, or wand preceded by \<^term>\<open>\<top>\<close> and reduce it to
the usual introduction premises without \<^term>\<open>\<top>\<close>. They are more
specific than using \<^verbatim>\<open>aentails_top_R\<close> as a generic final
fallback.\<close>
lemma aentails_intI_top:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<top> \<star> (\<psi> \<inter> \<xi>)\<close>
using assms by (intro aentails_top_R aentails_intI)

lemma aforall_entailsR_top:
  assumes \<open>\<And>x. \<phi> \<longlongrightarrow> \<psi> x\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<top> \<star> (\<Sqinter>x. \<psi> x)\<close>
using assms by (intro aentails_top_R aforall_entailsR)

lemma awand_adjointI_top:
  assumes \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<top> \<star> (\<psi> \<Zsurj> \<xi>)\<close>
using assms by (intro aentails_top_R awand_adjointI)

lemma awand_emp_adjointI_top:
  assumes \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
    shows \<open>emp \<longlongrightarrow> \<top> \<star> (\<psi> \<Zsurj> \<xi>)\<close>
using assms by (intro aentails_top_R awand_emp_adjointI)

lemma aentails_disj_distR [asepconj_simp]:
  shows \<open>(a \<squnion> b) \<star> \<phi> = (a \<star> \<phi>) \<squnion> (b \<star> \<phi>)\<close>
by (intro asat_semequivI) (auto elim!: asepconjE intro: asepconjI)

lemma aentails_disj_distL [asepconj_simp]:
  shows \<open>\<phi> \<star> (a \<squnion> b) = (\<phi> \<star> a) \<squnion> (\<phi> \<star> b)\<close>
by (intro asat_semequivI) (auto elim!: asepconjE intro: asepconjI)

lemma aentails_disj_L:
  assumes \<open>a \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
      and \<open>b \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>(a \<squnion> b) \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_def asepconj_simp)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aentails_disj_L':
  assumes \<open>\<phi> \<star> a \<longlongrightarrow> \<psi>\<close>
      and \<open>\<phi> \<star> b \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<star> (a \<squnion> b) \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_def asepconj_simp)

lemma aentails_disj_L0:
  assumes \<open>a  \<longlongrightarrow> \<psi>\<close>
      and \<open>b  \<longlongrightarrow> \<psi>\<close>
    shows \<open>(a \<squnion> b) \<longlongrightarrow> \<psi>\<close>
using assms by (auto simp add: aentails_def asepconj_simp)

lemma aentails_disj_R1:
  assumes \<open>\<phi> \<longlongrightarrow> a\<close>
    shows \<open>\<phi> \<longlongrightarrow> a \<squnion> b\<close>
using assms by (auto simp add: aentails_def)

lemma aentails_disj_R2:
  assumes \<open>\<phi> \<longlongrightarrow> b\<close>
    shows \<open>\<phi> \<longlongrightarrow> a \<squnion> b\<close>
using assms by (auto simp add: aentails_def)

lemma asepconj_Int_commute:
  shows \<open>(\<Sqinter>x. \<phi> x) \<star> \<psi> \<longlongrightarrow> (\<Sqinter>x. \<phi> x \<star> \<psi>)\<close>
by (auto simp add: aentails_def elim!: asepconjE intro!: asepconjI)

lemma awand_mp:
  shows \<open>(\<phi> \<Zsurj> \<psi>) \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
by (clarsimp elim!: asepconjE awandE simp add: aentails_def)

lemma awand_mp_strong_crule:
  shows \<open>(\<phi> \<Zsurj> \<psi>) [\<phi>]\<longlongrightarrow>\<^sub>s[emp] \<psi>\<close>
unfolding aentails_conditional_crule_strong_def
by (simp add: asepconj_emp_unit aentails_refl)

lemma awand_curry:
  shows \<open>(\<phi> \<star> \<psi>) \<Zsurj> \<chi> = \<phi> \<Zsurj> \<psi> \<Zsurj> \<chi>\<close>
by (metis (no_types, lifting) aentails_eq asepconj_AC(2) awand_adjoint awand_mp)

lemma awand_L0:
  assumes \<open>\<rho> \<longlongrightarrow> \<phi>\<close>
      and \<open>\<psi> \<longlongrightarrow> \<theta>\<close>
    shows \<open>(\<phi> \<Zsurj> \<psi>) \<star> \<rho> \<longlongrightarrow> \<theta>\<close>
using assms by (clarsimp simp add: aentails_def elim!: asepconjE awandE)

lemma awand_L:
  assumes \<open>\<rho> \<longlongrightarrow> \<phi> \<star> \<gamma>\<close>
      and \<open>\<psi> \<star> \<gamma> \<longlongrightarrow> \<theta>\<close>
    shows \<open>(\<phi> \<Zsurj> \<psi>) \<star> \<rho> \<longlongrightarrow> \<theta>\<close>
proof -
  from assms have \<open>(\<phi> \<Zsurj> \<psi>) \<star> \<rho> \<longlongrightarrow> (\<phi> \<Zsurj> \<psi> \<star> (\<phi> \<star> \<gamma>))\<close>
    by (simp add: local.asepconj_mono)
  also have \<open>\<dots> \<longlongrightarrow> \<psi> \<star> \<gamma>\<close>
    by (metis awand_mp local.asepconj_assoc local.asepconj_mono2)
  also have \<open>\<dots> \<longlongrightarrow> \<theta>\<close>
    by (rule assms)
  finally show \<open>(\<phi> \<Zsurj> \<psi>) \<star> \<rho> \<longlongrightarrow> \<theta>\<close>
    by blast
qed

text \<open>A quantified wand family discharges one matching assertion even when carried under an
intersection with unrelated resource.  Both intersection orders support symmetric call sites:\<close>
lemma awand_forall_inter_counit:
  shows \<open>\<phi> r \<star> ((\<Sqinter>v. \<phi> v \<Zsurj> \<psi> v) \<sqinter> \<chi>) \<longlongrightarrow> \<psi> r\<close>
    and \<open>\<phi> r \<star> (\<chi> \<sqinter> (\<Sqinter>v. \<phi> v \<Zsurj> \<psi> v)) \<longlongrightarrow> \<psi> r\<close>
proof -
  have wand: \<open>(\<Sqinter>v. \<phi> v \<Zsurj> \<psi> v) \<sqinter> \<chi> \<longlongrightarrow> \<phi> r \<Zsurj> \<psi> r\<close>
    by (intro aentails_inter_weaken2 aforall_entailsL) (rule aentails_refl)
  from wand have \<open>\<phi> r \<star> ((\<Sqinter>v. \<phi> v \<Zsurj> \<psi> v) \<sqinter> \<chi>) \<longlongrightarrow> \<phi> r \<star> (\<phi> r \<Zsurj> \<psi> r)\<close>
    by (rule asepconj_mono3[OF refl])
  from this show \<open>\<phi> r \<star> ((\<Sqinter>v. \<phi> v \<Zsurj> \<psi> v) \<sqinter> \<chi>) \<longlongrightarrow> \<psi> r\<close>
    using awand_counit by (rule aentails_trans)
  from this show \<open>\<phi> r \<star> (\<chi> \<sqinter> (\<Sqinter>v. \<phi> v \<Zsurj> \<psi> v)) \<longlongrightarrow> \<psi> r\<close>
    by (simp add: inf_commute)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma awand_int:
  shows \<open>\<phi> \<Zsurj> (\<xi> \<inter> \<psi>) = (\<phi> \<Zsurj> \<xi>) \<inter> (\<phi> \<Zsurj> \<psi>)\<close>
proof (intro asat_semequivI)
     fix x
  assume \<open>x \<Turnstile> \<phi> \<Zsurj> \<xi> \<inter> \<psi>\<close>
  from this show \<open>x \<Turnstile> (\<phi> \<Zsurj> \<xi>) \<inter> (\<phi> \<Zsurj> \<psi>)\<close>
    by (metis aentailsE aentails_int awand_adjoint awand_mp)
next
     fix x
  assume \<open>x \<Turnstile> (\<phi> \<Zsurj> \<xi>) \<inter> (\<phi> \<Zsurj> \<psi>)\<close>
  from this show \<open>x \<Turnstile> \<phi> \<Zsurj> \<xi> \<inter> \<psi>\<close>
    by (meson asat_connectives_characterisation(3) awandE awandI)
qed

lemma awand_curry_drule:
  shows \<open>(\<alpha> \<star> \<beta>) \<Zsurj> \<gamma> \<longlongrightarrow> \<alpha> \<Zsurj> (\<beta> \<Zsurj> \<gamma>)\<close>
  by (simp add: awand_adjointI awand_curry awand_mp)

lemma aentails_empty_R:
  assumes \<open>0 \<Turnstile> \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<rho>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi> \<star> \<rho>\<close>
using assms by (auto simp add: aentails_def intro!: asepconjI)

text \<open>A precise pure factor splits off without receiving any resource, so
this rule remains available to introduction search.\<close>
lemma apure_precise_entailsR [intro]:
  assumes \<open>is_sat \<phi> \<Longrightarrow> P\<close>
      and ent: \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<psi>\<close>
proof (rule aentails_is_sat)
  assume \<open>is_sat \<phi>\<close>
  with assms(1) have \<open>0 \<Turnstile> \<langle>P\<rangle>\<close>
    by simp
  from this and ent show \<open>\<phi> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<psi>\<close>
    by (rule aentails_empty_R)
qed

text \<open>Crush discharges its opaque pure obligation only after spatial proof search is complete.\<close>
lemma apure_crush_obligation_entailsR0:
  assumes \<open>is_sat \<phi> \<Longrightarrow> P\<close>
    shows \<open>\<phi> \<longlongrightarrow> apure_crush_obligation P\<close>
proof -
  have \<open>\<phi> \<longlongrightarrow> \<langle>P\<rangle> \<star> UNIV\<close>
    using assms aentails_true by (rule apure_precise_entailsR)
  then show ?thesis
    by (simp add: apure_crush_obligation_def asepconj_comm)
qed

text \<open>This automation variant keeps the Boolean obligation spatial, as an entailment to a
dedicated opaque assertion. Spatial destruction and cancellation rules can therefore establish the
fact before proof search crosses into HOL.\<close>
lemma apure_precise_entailsR_spatial:
  assumes pure: \<open>\<phi> \<longlongrightarrow> apure_crush_obligation P\<close>
      and ent: \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<psi>\<close>
proof (rule apure_precise_entailsR[OF _ ent])
  assume \<open>is_sat \<phi>\<close>
  then obtain s where sat: \<open>s \<Turnstile> \<phi>\<close>
    by (auto simp add: is_sat_def)
  from pure sat have \<open>s \<Turnstile> UNIV \<star> \<langle>P\<rangle>\<close>
    by (auto simp add: aentails_def apure_crush_obligation_def)
  then show \<open>P\<close>
    by (auto elim!: asepconjE)
qed

text \<open>Given an arbitrary entailment goal, this rule lets you perform forward reasoning from an
already-established fact, in a way that interacts well with the usual proof automation tactics.
Generally, one will use this lemma via \<^verbatim>\<open>rule aentails_forward[OF fact]\<close> or similar.\<close>
lemma aentails_forward:
  assumes \<open>pre \<longlongrightarrow> post\<close>
      and \<open>\<phi> \<longlongrightarrow> pre \<star> (post \<Zsurj> \<psi>)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
proof (intro aentailsI)
  fix x
  assume \<open>x \<Turnstile> \<phi>\<close>
  then have \<open>x \<Turnstile> pre \<star> (post \<Zsurj> \<psi>)\<close>
    using assms unfolding aentails_def by auto
  then have \<open>x \<Turnstile> post \<star> (post \<Zsurj> \<psi>)\<close>
    using assms by (meson aentailsE asepconj_mono2)
  then show \<open>x \<Turnstile> \<psi>\<close>
    unfolding aentails_def using asepconjE awandE asepconj_comm
    by metis
qed

lemma aentails_fold_def:
  shows \<open>x \<equiv> y \<Longrightarrow> \<phi> \<longlongrightarrow> y \<star> (x \<Zsurj> \<psi>) \<Longrightarrow>  \<phi> \<longlongrightarrow> \<psi>\<close>
by (rule aentails_forward, auto intro: aentails_intro)

section \<open>Iterated separating conjunctions\<close>

text \<open>Since the separating conjunction \<^term>\<open>(\<star>)\<close> is commutative, its folded application descends
to a map from \<^emph>\<open>multisets\<close> of assertions to assertions. In fact, this is a very general observation,
which, unsurprisingly, has already been formalized in the standard library in great generality.

Note that multisets are the natural domain here as the quotient of lists by the permutation
equivalence relation. We could in principle also work with sets of assertions, but we would bump
into tedious equality constraints which would be technical complications without apparent benefit.\<close>
interpretation ASepConjComm: comp_fun_commute asepconj
  using comp_fun_commute_def asepconj_assoc asepconj_comm by fastforce

definition asepconj_multi' :: \<open>'a assert multiset \<Rightarrow> 'a assert \<Rightarrow> 'a assert\<close> (infix "\<star>\<star>\<star>" 51) where
  \<open>asepconj_multi' \<Phi> \<tau> \<equiv> fold_mset asepconj \<tau> \<Phi>\<close>

definition asepconj_multi :: \<open>'a assert multiset \<Rightarrow> 'a assert\<close> ("\<star>\<star>")  where
  \<open>asepconj_multi \<Phi> \<equiv> asepconj_multi' \<Phi> emp\<close>

text \<open>The \<^term>\<open>emp\<close> fold unit makes an iterated conjunction own exactly its factors; the empty
iteration owns zero.\<close>

text \<open>Iterated separating conjunction preserves upwards-closure:\<close>
lemma asepconj_multi'_ucincl [ucincl_intros]:
  assumes 1: \<open>\<And>\<phi>. \<phi> \<in># \<Phi> \<Longrightarrow> ucincl \<phi>\<close>
      and 2: \<open>ucincl \<tau>\<close>
    shows \<open>ucincl (\<Phi> \<star>\<star>\<star> \<tau>)\<close>
  using 1 by (induction \<Phi>) (auto simp: 2 asepconj_multi'_def local.ucincl_asepconjL)

text \<open>A non-empty iteration of upwards-closed factors is upwards closed. Both premises are
determined by the conclusion, so the rule participates in closure search.\<close>
corollary asepconj_multi_ucincl [ucincl_intros]:
    fixes \<Phi> :: \<open>'a assert multiset\<close>
  assumes \<open>\<Phi> \<noteq> {#}\<close>
      and \<open>\<And>\<phi>. \<phi> \<in># \<Phi> \<Longrightarrow> ucincl \<phi>\<close>
    shows \<open>ucincl (\<star>\<star>\<Phi>)\<close>
proof -
  from assms(1) obtain \<phi> \<Psi> where \<open>\<Phi> = add_mset \<phi> \<Psi>\<close>
    by (metis multiset_cases)
  with assms(2) show ?thesis
    by (simp add: asepconj_multi_def asepconj_multi'_def local.ucincl_asepconjL)
qed

text \<open>One upwards-closed member suffices, but its witness is not determined by the conclusion, so
this sharper rule stays outside \<^verbatim>\<open>ucincl_intros\<close>.\<close>
corollary asepconj_multi_ucincl_member:
    fixes \<Phi> :: \<open>'a assert multiset\<close>
  assumes \<open>\<phi> \<in># \<Phi>\<close>
      and \<open>ucincl \<phi>\<close>
    shows \<open>ucincl (\<star>\<star>\<Phi>)\<close>
proof -
  from assms(1) obtain \<Psi> where \<open>\<Phi> = add_mset \<phi> \<Psi>\<close>
    by (metis multi_member_split)
  with assms(2) show ?thesis
    by (simp add: asepconj_multi_def asepconj_multi'_def local.ucincl_asepconjL)
qed

text \<open>The following are generalisations of identity, symmetric, and associativity results for the
standard separating conjunction to the iterated separating conjunction:\<close>

lemma asepconj_multi'_empty [asepconj_simp]:
  shows \<open>{#} \<star>\<star>\<star> \<tau> = \<tau>\<close>
by (auto simp add: asepconj_multi_def asepconj_multi'_def)

lemma asepconj_multi'_add_mset [asepconj_simp]:
  shows \<open>(add_mset \<phi> \<Phi>) \<star>\<star>\<star> \<tau> = \<phi> \<star> (\<Phi> \<star>\<star>\<star> \<tau>)\<close>
by (simp add: asepconj_multi'_def ASepConjComm.fold_mset_add_mset)

lemma asepconj_multi_empty [asepconj_simp]:
  shows \<open>\<star>\<star>{#} = emp\<close>
by (auto simp add: asepconj_multi_def asepconj_multi'_def)

lemma asepconj_multi_split:
  shows \<open>(\<Phi> + \<Psi>) \<star>\<star>\<star> \<tau> = \<Phi> \<star>\<star>\<star> (\<Psi> \<star>\<star>\<star> \<tau>)\<close>
  by (metis ASepConjComm.fold_mset_union asepconj_multi'_def union_commute)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma asepconj_multi_comm:
  shows \<open>\<Phi> \<star>\<star>\<star> (\<Psi> \<star>\<star>\<star> \<tau>) = \<Psi> \<star>\<star>\<star> (\<Phi> \<star>\<star>\<star> \<tau>)\<close>
using asepconj_multi_split union_commute by (metis (mono_tags))

lemma asepconj_multi_single [asepconj_simp]:
  shows \<open>{# \<phi> #} \<star>\<star>\<star> \<psi> = \<phi> \<star> \<psi>\<close>
by (clarsimp simp add: asepconj_multi_def asepconj_multi'_def; auto)

text \<open>A singleton iteration is exactly its factor.\<close>
lemma asepconj_multi_single' [asepconj_simp]:
  shows \<open>\<star>\<star>{# \<phi> #} = \<phi>\<close>
by (simp add: asepconj_simp asepconj_multi_def)

lemma asepconj_multi_assoc0:
  shows \<open>(\<Phi> \<star>\<star>\<star> \<tau>) \<star> \<rho> = \<Phi> \<star>\<star>\<star> (\<tau> \<star> \<rho>)\<close>
  by (force simp add: ASepConjComm.fold_mset_fun_left_comm asepconj_comm asepconj_multi'_def)

text \<open>An explicit starting value is a trailing conjunct of the exact fold.\<close>
lemma asepconj_multi_multi':
  shows \<open>(\<star>\<star> \<Phi>) \<star> \<tau> = \<Phi> \<star>\<star>\<star> \<tau>\<close>
  by (simp add: asepconj_multi_assoc0 asepconj_multi_def local.asepconj_emp_unit(2))

lemma asepconj_multi_split' [asepconj_simp]:
  shows \<open>\<star>\<star> (\<Phi> + \<Psi>) = \<star>\<star> \<Phi> \<star> \<star>\<star> \<Psi>\<close>
by (metis asepconj_multi_def asepconj_multi_multi' asepconj_multi_split)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma asepconj_multi_split'':
  assumes \<open>\<Phi> \<subseteq># \<Psi>\<close>
    shows \<open>\<star>\<star> \<Psi> = \<star>\<star> \<Phi> \<star> \<star>\<star> (\<Psi> - \<Phi>)\<close>
by (metis asepconj_multi_split' assms subset_mset.add_diff_inverse)

text \<open>An iterated conjunction is discardable when every factor is discardable.\<close>
lemma discardable_in_multi [discardable_in_intros]:
  assumes \<open>\<And>\<phi>. \<phi> \<in># \<Phi> \<Longrightarrow> discardable_in \<phi> \<rho>\<close>
    shows \<open>discardable_in (\<star>\<star>\<Phi>) \<rho>\<close>
using assms proof (induction \<Phi>)
  case empty
  then show ?case
    by (simp add: asepconj_simp discardable_in_empI)
next
  case (add \<phi> \<Phi>)
  from add have 1: \<open>discardable_in \<phi> \<rho>\<close> and 2: \<open>discardable_in (\<star>\<star>\<Phi>) \<rho>\<close>
    by auto
  have \<open>\<star>\<star>(add_mset \<phi> \<Phi>) = \<phi> \<star> \<star>\<star>\<Phi>\<close>
    by (simp add: asepconj_multi_def asepconj_multi'_add_mset)
  with 1 2 show ?case
    by (simp add: discardable_in_conj)
qed

lemma is_sat_multiE[is_sat_elim]:
  assumes \<open>is_sat (\<star>\<star>{# \<xi> . ms #})\<close>
      and \<open>(\<And>x. x \<in># ms \<Longrightarrow> is_sat (\<xi> x)) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (metis (no_types, lifting) asepconj_multi_def asepconj_multi_single asepconj_multi_split'
    image_mset_single image_mset_union insert_DiffM2 is_sat_splitE)

(*<*)
end

context sepalg begin
(*>*)

corollary asepconj_multi_mapped_ucincl [ucincl_intros]:
  assumes \<open>m \<noteq> {#}\<close>
      and \<open>\<And>r. ucincl (e r)\<close>
    shows \<open>ucincl (\<star>\<star> {# e . m #})\<close>
using assms by (intro asepconj_multi_ucincl) auto

\<comment>\<open>This sharper form stays outside \<^verbatim>\<open>ucincl_intros\<close> because its witness is not
determined by the conclusion.\<close>
corollary asepconj_multi_mapped_ucincl_member:
  assumes \<open>r \<in># m\<close>
      and \<open>ucincl (e r)\<close>
    shows \<open>ucincl (\<star>\<star> {# e . m #})\<close>
using assms by (intro asepconj_multi_ucincl_member[where \<phi>=\<open>e r\<close>]) auto

text \<open>The following technical result is at the heart of the cancellation tactic for iterated
separating conjunctions.  Before it is applied, it should be ensured that all separating
conjunction components of the form \<^term>\<open>\<star>\<star>{# e . ms #}\<close> have been gathered together.\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aentails_multi_subset:
  assumes \<open>ms' \<subseteq># ms\<close>
     and \<open>\<And>r. ucincl (e r)\<close>
     and \<open>ms' \<noteq> {#}\<close>
   shows \<open>\<star>\<star> {# e . ms #} \<longlongrightarrow> \<star>\<star> {# e . ms' #}\<close>
using assms by (metis aentails_cancel_r asepconj_multi_mapped_ucincl asepconj_multi_split'
      image_mset_is_empty_iff image_mset_union subset_mset.le_iff_add)

text \<open>The following results are useful when trying to show entailments between iterated separating
conjunctions:\<close>
lemma aentails_cancel_multi_0R':
  assumes \<open>ms' \<subseteq># ms\<close>
      and \<open>\<phi> \<longlongrightarrow> \<star>\<star>{# e . (ms - ms') #}\<close>
    shows \<open>\<star>\<star>{# e . ms' #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . ms #}\<close>
using assms by (metis asepconj_mono asepconj_multi_split' image_mset_union
      subset_mset.add_diff_inverse)

lemma aentails_cancel_multi':
  assumes \<open>\<star>\<star>{# e . ms' #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . ms #} \<star> \<phi>'\<close>
    shows \<open>\<star>\<star>{# e . ms' + ms'' #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . ms + ms'' #} \<star> \<phi>'\<close>
using assms asepconj_comm asepconj_mono2 asepconj_multi_split' by (fastforce simp add: asepconj_simp)

lemma aentails_cancel_multi:
  assumes \<open>\<star>\<star>{# e . ms' - ms #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . (ms - ms') #} \<star> \<phi>'\<close>
    shows \<open>\<star>\<star>{# e . ms' #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . ms #} \<star> \<phi>'\<close>
proof -
  have \<open>ms' = (ms' - ms) + (ms' \<inter># ms)\<close>
    using diff_intersect_left_idem subset_mset.inf.cobounded1 subset_mset.le_imp_diff_is_add by blast
  moreover have \<open>ms = (ms - ms') + (ms' \<inter># ms)\<close>
    using diff_intersect_right_idem subset_mset.inf.cobounded2 subset_mset.le_imp_diff_is_add by blast
  moreover from assms have \<open>\<star>\<star>{# e . (ms' - ms) + ms' \<inter># ms #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . (ms - ms') + ms' \<inter># ms #} \<star> \<phi>'\<close>
    by (blast intro: aentails_cancel_multi')
  ultimately show ?thesis
    by presburger
qed

lemma aentails_cancel_multi_0L:
  assumes \<open>\<star>\<star>{# e . ms' - ms #} \<longlongrightarrow> \<star>\<star>{# e . (ms - ms') #} \<star> \<phi>'\<close>
    shows \<open>\<star>\<star>{# e . ms' #} \<longlongrightarrow> \<star>\<star>{# e . ms #} \<star> \<phi>'\<close>
using aentails_cancel_multi by (metis assms local.asepconj_emp_unit(1))

lemma aentails_cancel_multi_0R:
  assumes \<open>\<star>\<star>{# e . ms' - ms #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . (ms - ms') #}\<close>
    shows \<open>\<star>\<star>{# e . ms' #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# e . ms #}\<close>
using aentails_cancel_multi by (metis assms local.asepconj_emp_unit(1))

lemma asepconj_add_mset [simp]:
  shows \<open>\<star>\<star>(add_mset x xs) = x \<star> \<star>\<star>xs\<close>
by (metis add_mset_add_single asepconj_multi_def asepconj_multi_single asepconj_multi_split
  union_commute)

lemma asepconj_multi_cons [simp]:
  shows \<open>\<star>\<star>{# f \<Colon> (x#xs) #} = f x \<star> \<star>\<star>{# f \<Colon> xs #}\<close>
by auto

lemma asepconj_multi_mapped_pick:
  assumes \<open>i < length lst\<close>
    shows \<open>\<star>\<star>{# \<xi> \<Colon> lst #} = \<xi> (lst ! i) \<star>  \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #}\<close>
using assms by (metis asepconj_multi_cons list_update_id mset.simps(2) mset_drop_nth' mset_update)

text \<open>Precise-pure assertions collapse uniformly because \<^term>\<open>\<langle>True\<rangle> = emp\<close>.\<close>
lemma asepconj_multi_pure_precise:
  shows \<open>\<star>\<star>{# \<langle>P x\<rangle> . x\<leftarrow>ms #} = \<langle>\<forall>x \<in># ms. P x\<rangle>\<close>
by (induction ms; simp add: asepconj_simp)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma aentails_multi_list_pure_precise:
  shows \<open>\<star>\<star>{# \<langle>f x\<rangle> \<Colon> x \<leftarrow> xs #} = \<langle>\<forall>x \<in> set xs. f x\<rangle>\<close>
by (simp add: asepconj_multi_pure_precise)

lemma aentails_multi_list_pointwise:
    notes asepconj_simp [simp] aentails_intro [intro]
  assumes \<open>length xs = length ys\<close>
      and \<open>\<And>i. i < length xs \<Longrightarrow> f (xs!i) \<longlongrightarrow> g (ys!i)\<close>
    shows \<open>\<star>\<star>{# f \<Colon> xs #} \<longlongrightarrow> \<star>\<star>{# g \<Colon> ys #}\<close>
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs ys)
  then obtain z zs where \<open>ys = z#zs\<close> and len: \<open>length xs = length zs\<close>
    by (metis length_Suc_conv)
  with Cons have \<open>\<star>\<star> {# f \<Colon> xs #} \<longlongrightarrow> \<star>\<star> {# g \<Colon> zs #}\<close>
    by (metis Suc_less_eq length_Cons nth_Cons_Suc)
  moreover have \<open>f x \<longlongrightarrow> g z\<close>
    using \<open>ys = z#zs\<close> Cons.prems(2) by fastforce
  ultimately show ?case
    by (simp add: \<open>\<star>\<star> {# f \<Colon> xs #} \<longlongrightarrow> \<star>\<star> {# g \<Colon> zs #}\<close> \<open>ys = z # zs\<close> local.asepconj_mono4)
qed

lemma aentails_multi_list_pointwise_fixed_indexing:
    notes asepconj_simp [simp]
  assumes \<open>\<And>x. x\<in># xs \<Longrightarrow> f x \<longlongrightarrow> g x\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<star>\<star>{# f . xs #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# g . xs #} \<star> \<psi>\<close>
using assms proof (induction xs)
  case empty then show ?case
  using assms asepconj_multi_empty
    by (simp add: asepconj_mono)
next
  case (add x xs) then show ?case
  using assms asepconj_mono4 by auto
qed

lemma aentails_multi_list_pointwise_fixed_indexing2:
    notes asepconj_simp [simp]
  assumes \<open>\<And>x. x\<in># xs \<Longrightarrow> f x \<longlongrightarrow> g x\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<star> \<star>\<star>{# f . xs #} \<longlongrightarrow> \<psi> \<star> \<star>\<star>{# g . xs #}\<close>
proof -
  have \<open>\<phi> \<star> \<star>\<star>{# f . xs #} = \<star>\<star>{# f . xs #} \<star> \<phi>\<close>
    by (simp add: asepconj_AC(1))
  moreover have \<open>\<psi> \<star> \<star>\<star>{# g . xs #} = \<star>\<star>{# g . xs #} \<star> \<psi>\<close>
    by (simp add: asepconj_AC(1))
  moreover from assms have \<open>\<star>\<star>{# f . xs #} \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# g . xs #} \<star> \<psi>\<close>
    by (auto intro: aentails_multi_list_pointwise_fixed_indexing)
  ultimately show ?thesis
    by auto
qed

theorem asepconj_frame_rev_multi_single:
  assumes \<open>\<xi> (lst ! i) \<star> \<phi> \<longlongrightarrow> \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<psi>\<close>
      and \<open>\<And>r. ucincl (\<xi> r)\<close>
      and \<open>i < length lst\<close>
    shows \<open>\<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
proof -
  from assms have \<open>\<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<star> \<xi> (lst ! i) \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
     by (simp add: aentails_simp local.asepconj_comm)
  moreover have \<open>\<xi> (lst ! i) = \<star>\<star>{# \<xi> \<Colon> [lst ! i] #}\<close>
    using assms asepconj_multi_single' by force
  ultimately show ?thesis
    using assms by (metis asepconj_multi_mapped_pick asepconj_assoc asepconj_comm)
qed

lemma aentails_multi_list_pointwise_fixed_indexing':
  assumes \<open>\<And>x. x \<in># xs \<Longrightarrow> f x \<longlongrightarrow> g x\<close>
  shows \<open>\<star>\<star>{# f . xs #} \<longlongrightarrow> \<star>\<star>{# g . xs #}\<close>
  using assms by (induction xs) (auto intro: asepconj_mono4 aentails_intro)

text \<open>Dropping factors requires the retained iteration to be non-empty and upwards closed.\<close>
lemma aentails_multi_list_pointwise_fixed_indexing'':
  assumes \<open>ys \<subseteq># xs\<close>
      and \<open>\<And>x. x \<in># xs \<Longrightarrow> f x \<longlongrightarrow> g x\<close>
      and \<open>ys \<noteq> {#}\<close>
      and \<open>\<And>y. ucincl (g y)\<close>
    shows \<open>\<star>\<star>{# f . xs #} \<longlongrightarrow> \<star>\<star>{# g . ys #}\<close>
using assms proof -
  have \<open>\<star>\<star>{# f . xs #} \<longlongrightarrow> \<star>\<star>{# g . xs #}\<close>
    using assms by (simp add: aentails_multi_list_pointwise_fixed_indexing')
  also have \<open>\<dots> \<longlongrightarrow> \<star>\<star>{# g . ys #}\<close>
    using assms by (intro aentails_multi_subset)
  finally show ?thesis
    by blast
qed

lemma aentails_multi_list_pointwise_fixed_indexing''':
  assumes \<open>\<And>x. x\<in># xs \<Longrightarrow> f x \<longlongrightarrow> g x\<close>
      and \<open>emp \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<star>\<star>{# f . xs #} \<longlongrightarrow> \<star>\<star>{# g . xs #} \<star> \<psi>\<close>
using assms by (meson aentails_multi_list_pointwise_fixed_indexing' aentails_trans'
    local.asepconj_mono5)

lemma aentails_multi_mapped_pick:
  assumes \<open>i < length lst\<close>
      and \<open>\<xi> (lst ! i) \<star> \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<phi> \<longlongrightarrow> \<psi>\<close>
using asepconj_multi_mapped_pick assms asepconj_assoc by metis

lemma aentails_multi_mapped_pick_0L:
  assumes \<open>i < length lst\<close>
      and \<open>\<xi> (lst ! i) \<star> \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<star>\<star>{# \<xi> \<Colon> lst #} \<longlongrightarrow> \<psi>\<close>
using asepconj_multi_mapped_pick assms asepconj_assoc by metis

lemma asepconj_multi_split_body:
  shows \<open>\<star>\<star>{# \<lambda>s. (\<xi> s \<star> \<tau> s) . ms #} = \<star>\<star>{# \<xi> s . s \<leftarrow> ms #} \<star> \<star>\<star>{# \<tau> s . s \<leftarrow> ms #}\<close>
proof (induction ms)
  case empty
  then show ?case
    by (simp add: local.asepconj_emp_unit(1) asepconj_multi_empty)
next
  case (add x ms)
  then show ?case
    by (simp add: asepconj_assoc asepconj_swap_top)
qed

text \<open>A precise pure factor can be copied into every member of a non-empty iteration because it
is idempotent under \<^term>\<open>(\<star>)\<close>.\<close>
lemma asepconj_multi_hoist_pure_precise:
  assumes \<open>ms \<noteq> {#}\<close>
    shows \<open>\<langle>P\<rangle> \<star> \<star>\<star>{# \<xi> x . x \<leftarrow> ms #} =
      \<star>\<star>{# (\<xi> x \<star> \<langle>P\<rangle>) . x \<leftarrow> ms #}\<close>
proof -
  have nonempty: \<open>\<exists>x. x \<in># ms\<close>
    using assms by auto
  have \<open>\<star>\<star>{# (\<xi> x \<star> \<langle>P\<rangle>) . x \<leftarrow> ms #} =
      \<star>\<star>{# \<xi> x . x \<leftarrow> ms #} \<star> \<star>\<star>{# \<langle>P\<rangle> . x \<leftarrow> ms #}\<close>
    by (rule asepconj_multi_split_body)
  also from nonempty have \<open>\<star>\<star>{# \<langle>P\<rangle> . x \<leftarrow> ms #} = \<langle>P\<rangle>\<close>
    by (simp add: asepconj_multi_pure_precise assms)
  finally show ?thesis
    by (simp add: local.asepconj_comm)
qed

lemma asepconj_union_singleton:
  shows \<open>(\<Union>x. (\<langle>x = y\<rangle> \<star> \<xi> x)) = \<xi> y\<close>
by (auto simp add: apure_precise_def asepconj_def asat_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma asepconj_union_singleton':
  shows \<open>(\<Union>a b. (\<langle>a=t\<rangle> \<star> \<xi> a b)) = (\<Union>b. \<xi> t b)\<close>
by (auto simp add: apure_precise_def asepconj_def asat_def)

lemma asepconj_Union_pure:
  shows \<open>(\<Squnion>x. \<langle>P x\<rangle>) = \<langle>\<exists>x. P x\<rangle>\<close>
by (auto simp add: apure_precise_def)

lemma aentails_multi_map_core:
  assumes \<open>\<And>x.  x \<in># ms \<Longrightarrow> \<xi>' (f x) = \<xi> x\<close>
    shows \<open>\<star>\<star>{# \<xi> . ms #} = \<star>\<star>{# \<xi>' . image_mset f ms #}\<close>
using assms by (induction ms; auto)

lemma asepconj_multi_eq_pointwise_fixed_indexing:
  assumes \<open>\<And>x. x \<in># ms \<Longrightarrow> \<xi> x = \<xi>' x\<close>
    shows \<open>\<star>\<star>{# \<xi> . ms #} = \<star>\<star>{# \<xi>' . ms #}\<close>
by (metis assms mapped_multiset_eq)

lemma sepconj_multi_set_access_element :
  assumes \<open>m \<in># M\<close>
    shows \<open>\<star>\<star>{# \<Phi> . M #} = \<Phi> m \<star> \<star>\<star>{# \<Phi> . M - (mset_set {m}) #}\<close>
  using assms
proof (induction M)
  case empty
  then show ?case
    by auto
next
  case (add x M)
  then consider \<open>m = x\<close> | \<open>m \<in># M\<close>
    by fastforce
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      by (metis add.prems asepconj_add_mset emptyE finite.emptyI insert_DiffM msed_map_invL mset_set.empty mset_set.insert)
  qed
qed

lemma aentails_multi_map_core':
  shows \<open>\<star>\<star>{# \<xi>' . f `# ms #} = \<star>\<star>{# \<xi>' (f x) . x \<leftarrow> ms #}\<close>
using aentails_multi_map_core by metis

corollary asepconj_mset_map_sum_lift_single:
  shows \<open>\<langle>add_mset x ms0 = (f `# ms')\<rangle> =
    (\<Squnion>x' ms0'. \<langle>ms' = add_mset x' ms0'\<rangle> \<star> \<langle>x = f x'\<rangle> \<star>
      \<langle>ms0 = (f `# ms0')\<rangle>)\<close>
by (clarsimp simp add: asepconj_simp asepconj_Union_pure mset_map_sum_lift_single)

text \<open>Distributing existential choices records one witness per index. The index constraint is
precise-pure so both sides own the same resource.\<close>
lemma asepconj_multi_Union:
  shows \<open>\<star>\<star>{# (\<Union>x. \<xi> s x) . s \<leftarrow> idxs #} =
       (\<Union>idxs'. \<langle>idxs = (fst `# idxs')\<rangle> \<star> \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> idxs' #})\<close>
proof (induction idxs)
  case empty
  show ?case
  proof (intro aentails_eq)
    show \<open>\<star>\<star>{# (\<Union>x. \<xi> s x) . s \<leftarrow> {#} #} \<longlongrightarrow>
        (\<Union>idxs'. \<langle>{#} = (fst `# idxs')\<rangle> \<star> \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> idxs' #})\<close>
      by (rule aexists_entailsR[of _ _ \<open>{#}\<close>]) (simp add: asepconj_simp aentails_refl)
  next
    show \<open>(\<Union>idxs'. \<langle>{#} = (fst `# idxs')\<rangle> \<star> \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> idxs' #}) \<longlongrightarrow>
        \<star>\<star>{# (\<Union>x. \<xi> s x) . s \<leftarrow> {#} #}\<close>
    proof (intro aexists_entailsL)
      fix idxs' show \<open>\<langle>{#} = (fst `# idxs')\<rangle> \<star> \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> idxs' #} \<longlongrightarrow>
          \<star>\<star>{# (\<Union>x. \<xi> s x) . s \<leftarrow> {#} #}\<close>
        by (cases \<open>idxs' = {#}\<close>)
           (auto simp add: asepconj_simp aentails_refl bot_aentails_all)
    qed
  qed
next
  case IH: (add s idxs)
  show ?case (is \<open>?lhs = ?rhs\<close>)
  proof (intro aentails_eq, goal_cases)
    case 1
    have step1: \<open>?lhs \<longlongrightarrow> (\<Union>x. \<xi> s x) \<star>
        (\<Union>r. \<langle>idxs = (fst `# r)\<rangle> \<star> \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> r #})\<close>
      by (simp add: IH aentails_refl asepconj_add_mset)
    have step2: \<open>\<xi> s x \<star> \<langle>idxs = (fst `# r)\<rangle> \<star>
        \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> r #} \<longlongrightarrow> ?rhs\<close> for x r
      using asepconj_assoc asepconj_comm
      by (rule_tac aexists_entailsR[of _ _ \<open>add_mset (s, x) r\<close>]) (simp add: aentails_refl)
    show ?case
      by (rule aentails_trans[OF step1])
         (auto intro!: aexists_entailsL aentails_trans[OF step2] aentails_refl
          simp add: asepconj_Inf_distrib_right asepconj_Inf_distrib)
  next
    case 2
    have step: \<open>\<langle>add_mset s idxs = (fst `# idxs')\<rangle> \<star>
        \<star>\<star>{# \<xi> (fst t) (snd t) . t \<leftarrow> idxs' #} \<longlongrightarrow> ?lhs\<close> for idxs'
    proof (cases \<open>(fst `# idxs') = add_mset s idxs\<close>)
      case True
      then obtain w r where \<open>idxs' = add_mset (s, w) r\<close> and \<open>(fst `# r) = idxs\<close>
        using msed_map_invR by fastforce
      then show ?thesis
        by (auto simp add: asepconj_simp IH asepconj_Inf_distrib asepconj_Inf_distrib_right
                    aentails_refl
                 intro!: aexists_entailsR[of _ _ r] aexists_entailsR[of _ _ w])
    qed (simp add: asepconj_simp bot_aentails_all)
    show ?case
      by (auto intro!: aexists_entailsL step simp only:)
  qed
qed

lemma aentails_multi_map:
  assumes \<open>\<And>x.  x \<in># ms \<Longrightarrow> \<xi>' (f x) = \<xi> x\<close>
      and \<open>ms' = (f `# ms)\<close>
    shows \<open>\<star>\<star>{# \<xi> . ms #} = \<star>\<star>{# \<xi>' . ms' #}\<close>
using assms aentails_multi_map_core by blast

text\<open>The following says that a multiset of pairs whose first components exhaust a \<^emph>\<open>set\<close> is in fact
``functional'': it is the graph of a function on that set.\<close>
lemma multi_set_set_functionality:
    fixes M ME
  assumes \<open>mset_set M = (fst `# ME)\<close>
    shows \<open>\<exists>f. ME = {# (m, f m) . m \<leftarrow> mset_set M #}\<close>
using assms proof (induction ME arbitrary: M)
  case empty
  then show ?case
    by simp
next
  case (add x ME)
  note IH = this
  have \<open>finite M \<or> infinite M\<close>
    by simp
  then have \<open>finite M\<close>
    using IH(2) by force
  then have dist: \<open>mset_set M = add_mset (fst x) (mset_set (M - {fst x}))\<close>
    using IH(2) elem_mset_set Multiset.mset_set.remove by fastforce
  then have IHprem: \<open>mset_set (M - {fst x}) = (fst `# ME)\<close>
    by (simp add: IH(2))
  with \<open>finite M\<close> have \<open>fst ` set_mset ME = M - {fst x}\<close>
    by (metis finite_Diff finite_set_mset_mset_set multiset.set_map)
  then have fst_ineq: \<open>\<And>y. y \<in> fst ` set_mset ME \<Longrightarrow> y \<noteq> fst x\<close>
    by blast
  obtain f where \<open>ME = {# (m, f m) . m \<leftarrow> mset_set (M - {fst x}) #}\<close>
    using IH IHprem by force
  moreover let ?f' = \<open>\<lambda>y. if y \<noteq> fst x then f y else snd x\<close>
  from calculation have \<open>add_mset x ME = {# (m, ?f' m) . m \<leftarrow> mset_set M #}\<close>
    by (simp add: dist) (force intro!: image_mset_cong simp add: IHprem fst_ineq)
  ultimately show ?case
    by force
qed

text\<open>The set-indexed choice law follows by representing the witness multiset as a function
graph.\<close>
lemma asepconj_multi_Union_set:
  shows \<open>\<star>\<star>{# (\<Union>x. \<xi> s x) . s \<leftarrow> mset_set idxs #} =
      (\<Union>f. \<star>\<star>{# \<xi> s (f s) . s \<leftarrow> mset_set idxs #})\<close>
proof (simp add: asepconj_multi_Union, intro aentails_eq aexists_entailsL, goal_cases)
  case (1 x)
  show ?case
  proof (cases \<open>(fst `# x) = mset_set idxs\<close>)
    case True
    obtain f where \<open>x = {# (m, f m) . m \<leftarrow> mset_set idxs #}\<close>
      using multi_set_set_functionality[OF True[symmetric]] by blast
    then show ?thesis
      apply (simp only: True[symmetric] HOL.refl apure_precise_True asepconj_emp_unit)
      apply (rule aexists_entailsR[of _ _ f])
      by (metis (mono_tags, lifting) aentails_multi_map aentails_refl_eq split_pairs)
  qed (simp add: asepconj_simp bot_aentails_all)
next
  case (2 f)
  have \<open>mset_set idxs = (fst `# {# (s, f s) . s \<leftarrow> mset_set idxs #})\<close>
    by (simp add: multiset_map_comp')
  then show ?case
    apply (rule_tac aexists_entailsR[of _ _ \<open>{# (s, f s). s \<leftarrow> mset_set idxs #}\<close>])
    apply (simp add: apure_precise_True asepconj_emp_unit)
    by (metis (mono_tags, lifting) aentails_multi_map_core aentails_refl fst_conv snd_conv)
qed

lemma asepconj_multi_flatten:
  shows \<open>\<star>\<star>{# \<star>\<star>{# \<xi> y x . x \<leftarrow> msA y #} . y \<leftarrow> msB #} =
         \<star>\<star>{# \<xi> y x . (y, x) \<leftarrow> \<Sum>\<^sub># ((\<lambda>y. (Pair y) `# (msA y)) `# msB) #}\<close>
proof (induction msB)
  case empty
  then show ?case by clarsimp
next
  case (add x msB)
  then show ?case
  proof (induction \<open>msA x\<close>)
    case empty
    then show ?case
      using local.asepconj_multi_split' by force
  next
    case (add x xa)
    have \<open>\<And>t. \<star>\<star> {#  (case a of (a, b) \<Rightarrow> \<xi> a b) . a \<leftarrow> {# Pair t . msA t #} #}
             = \<star>\<star> {# \<xi> t . msA t #}\<close>
      by (metis (mono_tags) aentails_multi_map case_prod_conv)
    then show ?case
      using local.asepconj_multi_split' add.prems by force
  qed
qed

lemma asepconj_multi_flatten_set:
  assumes \<open>finite B\<close>
      and \<open>\<And>y. y \<in> B \<Longrightarrow> finite (A y)\<close>
    shows \<open>\<star>\<star>{# \<star>\<star>{# \<xi> y x . x \<leftarrow> mset_set (A y) #} . y \<leftarrow> mset_set B #} =
           \<star>\<star>{# \<xi> y x . (y, x) \<leftarrow> mset_set { (y,x). y \<in> B \<and> x \<in> A y} #}\<close>
  using assms
proof (induction rule: Finite_Set.finite_induct)
  case empty
  then show ?case
    by auto
next
  case (insert x F)
  then have [simp]: \<open>{a. case a of (y,t) \<Rightarrow> (y = x \<or> y \<in> F) \<and> t \<in> A y} = {(y,t). y \<in> F \<and> t \<in> A y} \<union> Pair x ` A x\<close>
                    \<open>Pair x ` A x \<inter> {(y,t). y \<in> F \<and> t \<in> A y} = {}\<close>
    by auto
  have [simp]: \<open>finite {(y,t). y \<in> F \<and> t \<in> A y}\<close>
    using insert by (simp add: set_dependent_union_finite)
  have \<open>mset_set (Pair x ` A x) = (Pair x `# mset_set (A x))\<close>
    by (simp add: image_mset_mset_set inj_on_def)
  moreover
  have \<open>\<star>\<star> {# \<xi> x . mset_set (A x) #} \<star> \<star>\<star> {# \<xi> x y . (x, y) \<leftarrow> mset_set {(y, x). y \<in> F \<and> x \<in> A y} #} =
        \<star>\<star> {# \<xi> x y . (x, y) \<leftarrow> mset_set {(y,t). y \<in> F \<and> t \<in> A y} + mset_set (Pair x ` A x) #}\<close>
    by (simp add: aentails_multi_map_core' calculation local.asepconj_multi_split' union_commute)
  ultimately show ?case
    using insert by (simp add: Int_commute mset_set_Union)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma asepconj_multi_flatten_constant_indexing_set:
  assumes \<open>finite A\<close>
      and \<open>finite B\<close>
    shows \<open>\<star>\<star>{# \<star>\<star>{# \<xi> y x . x \<leftarrow> mset_set A #} . y \<leftarrow> mset_set B #} =
              \<star>\<star>{# \<xi> y x . (y, x) \<leftarrow> mset_set (B \<times> A) #}\<close>
using assms by (clarsimp simp add: asepconj_multi_flatten set_product_sum)

lemma asepconj_multi_true_collapse [simp]:
  "\<star>\<star> {# UNIV . x \<leftarrow> M #} = (if M = {#} then emp else UNIV)"
by (induction M; simp add: asepconj_simp)

(*<*)
end
(*>*)

(*<*)
end
(*>*)
