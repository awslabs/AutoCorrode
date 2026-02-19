(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Eval
  imports Core_Expression_Lemmas "HOL-Library.Datatype_Records"
    Numeric_Types_Lemmas
begin

text\<open>The following definitions are central: They provide a declarative view of the
execution of \<^verbatim>\<open>\<mu>Rust\<close> programs. Currently, they are derived from the deterministic evaluation
function associated with \<^verbatim>\<open>\<mu>Rust\<close> expressions, but if and when non-deterministic elements get
introduced into \<^verbatim>\<open>\<mu>Rust\<close>, this may change.\<close>

named_theorems urust_eval_predicate_defs
named_theorems urust_eval_action_via_predicate
named_theorems urust_eval_predicate_via_action

definition evaluates_to_return :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow>
      bool\<close> where
  [urust_eval_predicate_defs]: \<open>evaluates_to_return \<Gamma> e \<sigma> r \<sigma>' \<equiv>
    Return r \<sigma>' \<in> deep_evaluates_nondet_basic \<Gamma> e \<sigma> \<close>

definition eval_return :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> ('r \<times> 's) \<Rightarrow> bool\<close> where
  \<open>eval_return \<Gamma> e \<equiv> \<lambda>\<sigma> (r, \<sigma>'). evaluates_to_return \<Gamma> e \<sigma> r \<sigma>'\<close>

definition evaluates_to_value :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow>
      bool\<close> where
  [urust_eval_predicate_defs]: \<open>evaluates_to_value \<Gamma> e \<sigma> v \<sigma>' \<equiv>
    Success v \<sigma>'\<in> deep_evaluates_nondet_basic \<Gamma> e \<sigma> \<close>

definition eval_value :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> ('v \<times> 's) \<Rightarrow> bool\<close> where
  \<open>eval_value \<Gamma> e \<equiv> \<lambda>\<sigma> (v, \<sigma>'). evaluates_to_value \<Gamma> e \<sigma> v \<sigma>'\<close>

definition evaluates_to_abort :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> 'abort abort \<Rightarrow> 's \<Rightarrow>
      bool\<close> where
  [urust_eval_predicate_defs]: \<open>evaluates_to_abort \<Gamma> e \<sigma> a \<sigma>' \<equiv>
    Abort a \<sigma>' \<in> deep_evaluates_nondet_basic \<Gamma> e \<sigma>\<close>

definition eval_abort :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> ('abort abort \<times> 's) \<Rightarrow> bool\<close> where
  \<open>eval_abort \<Gamma> e \<equiv> \<lambda>\<sigma> (a, \<sigma>'). evaluates_to_abort \<Gamma> e \<sigma> a \<sigma>'\<close>

(*<*)
syntax
 "_evaluates_to_return" ::
    \<open>'s \<Rightarrow> ('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<leadsto>\<^sub>r \<langle>_,_\<rangle> '(_,_')" [30,0,0,51]64)
 "_evaluates_to_value" ::
    \<open>'s \<Rightarrow> ('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<leadsto>\<^sub>v \<langle>_,_\<rangle> '(_,_')" [30,0,0,51]64)
 "_evaluates_to_abort" ::
    \<open>'s \<Rightarrow> ('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 'abort abort \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<leadsto>\<^sub>a \<langle>_,_\<rangle> '(_,_')" [30,0,0,51]64)

translations
  "_evaluates_to_return \<sigma> \<Gamma> e r \<sigma>'" \<rightleftharpoons> "(CONST evaluates_to_return) \<Gamma> e \<sigma> r \<sigma>'"
  "_evaluates_to_value \<sigma> \<Gamma> e v \<sigma>'"  \<rightleftharpoons> "(CONST evaluates_to_value) \<Gamma> e \<sigma> v \<sigma>'"
  "_evaluates_to_abort \<sigma> \<Gamma> e a \<sigma>'"  \<rightleftharpoons> "(CONST evaluates_to_abort) \<Gamma> e \<sigma> a \<sigma>'"
(*>*)

text\<open>Some alternative (equivalent) views of the evaluation predicates.\<close>

definition return_evaluations :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow>
      ('r \<times> 's) set\<close> ("'(_,_') \<diamondop>\<^sub>r _" [30,0,51]64) where
  [urust_eval_action_via_predicate]: \<open>(\<Gamma>,e) \<diamondop>\<^sub>r \<sigma> \<equiv> { (r, \<sigma>') . \<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (r,\<sigma>') }\<close>

definition value_evaluations :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow>
      ('v \<times> 's) set\<close> ("'(_,_') \<diamondop>\<^sub>v _" [30,0,51]64) where
  [urust_eval_action_via_predicate]: \<open>(\<Gamma>,e) \<diamondop>\<^sub>v \<sigma> \<equiv> { (v, \<sigma>') . \<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>') }\<close>

definition abort_evaluations :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow>
      ('abort abort \<times> 's) set\<close> ("'(_,_') \<diamondop>\<^sub>a _" [30,0,51]64) where
  [urust_eval_action_via_predicate]: \<open>(\<Gamma>, e) \<diamondop>\<^sub>a \<sigma> \<equiv> { (a, \<sigma>') . (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,e\<rangle> (a, \<sigma>')) }\<close>

lemma evaluates_to_return_eq:
  shows [urust_eval_predicate_via_action]: \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (v,\<sigma>') \<longleftrightarrow> (v,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>r \<sigma>\<close>
by (simp add: return_evaluations_def)

lemma evaluates_to_value_eq:
  shows [urust_eval_predicate_via_action]: \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>') \<longleftrightarrow> (v,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>\<close>
by (simp add: value_evaluations_def)

lemma evaluates_to_abort_eq:
  shows [urust_eval_predicate_via_action]: \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,e\<rangle> (a, \<sigma>') \<longleftrightarrow> (a, \<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>a \<sigma>\<close>
by (simp add: abort_evaluations_def)

subsubsection\<open>Evaluation of various program constructs\<close>

named_theorems urust_eval_predicate_simps
named_theorems urust_eval_action_simps

text\<open>The following lemmas capture the relation between evaluation and binding.\<close>

lemma urust_eval_predicate_bind_success:
  shows \<open>((\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,Core_Expression.bind e f\<rangle> (v'',\<sigma>'')) \<longleftrightarrow>
     (\<exists>v' \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v',\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v\<langle>\<Gamma>,f v'\<rangle> (v'',\<sigma>''))))\<close>
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>''' e')
    then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
      using expression_wf_base_def by fastforce
    from less[OF \<omega>] Yield show ?thesis
      unfolding evaluates_to_value_def
      apply safe
      apply (erule deep_evaluate_basicE; fastforce simp: bind_evaluate intro: deep_evaluate_basic_YieldContinueI)+
      done
  qed (auto simp add: Core_Expression.bind.simps deep_evaluates_nondet_basic.simps evaluate_def evaluates_to_value_def)
qed

lemma urust_eval_predicate_bind_return:
  shows \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,Core_Expression.bind e f\<rangle> (r,\<sigma>'')) \<longleftrightarrow>
     (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (r,\<sigma>'')) \<or> (\<exists>v \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r\<langle>\<Gamma>,f v\<rangle> (r,\<sigma>'')))\<close>
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>''' e')
    then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
      using expression_wf_base_def by fastforce
    from less[OF \<omega>] Yield show ?thesis
      unfolding evaluates_to_value_def evaluates_to_return_def
      apply safe
      apply (erule deep_evaluate_basicE; fastforce simp: bind_evaluate intro: deep_evaluate_basic_YieldContinueI)+
      done
  qed (auto simp add: Core_Expression.bind.simps deep_evaluates_nondet_basic.simps evaluate_def evaluates_to_return_def evaluates_to_value_def)
qed

lemma urust_eval_predicate_bind_abort:
  shows \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,Core_Expression.bind e f\<rangle> (a, \<sigma>'')) \<longleftrightarrow>
     (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,e\<rangle> (a, \<sigma>'')) \<or> (\<exists>v \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a\<langle>\<Gamma>,f v\<rangle> (a, \<sigma>'')))\<close>
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>''' e')
    then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
      using expression_wf_base_def by fastforce
    from less[OF \<omega>] Yield show ?thesis
      unfolding evaluates_to_value_def evaluates_to_abort_def
      apply safe
      apply (erule deep_evaluate_basicE; fastforce simp: bind_evaluate intro: deep_evaluate_basic_YieldContinueI deep_evaluate_basic_YieldAbortI)+
      done
  qed (auto simp add: Core_Expression.bind.simps deep_evaluates_nondet_basic.simps evaluate_def evaluates_to_abort_def evaluates_to_value_def)
qed


text\<open>We note that the right hand sides of the previous lemmas are generic relation-composition
expressions. The lemmas can therefore be interpreted as saying that evaluation is compatible with
monadic composition.\<close>

definition rel_compose :: \<open>('a \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow>
      ('a \<Rightarrow> 'v \<Rightarrow> bool)\<close> (infix "\<lozenge>" 60) where
  \<open>(R \<lozenge> S) \<sigma> r \<equiv> \<exists>v' \<sigma>'. R \<sigma> (v', \<sigma>') \<and> S v' \<sigma>' r\<close>

corollary urust_eval_predicate_bind_value_rel [urust_eval_predicate_simps]:
  shows \<open>eval_value \<Gamma> (Core_Expression.bind e f) = (eval_value \<Gamma> e) \<lozenge> (eval_value \<Gamma> \<circ> f)\<close>
using urust_eval_predicate_bind_success by (fastforce simp add: eval_value_def rel_compose_def)

lemma urust_eval_predicate_bind_return_rel[urust_eval_predicate_simps]:
  shows \<open>eval_return \<Gamma> (Core_Expression.bind e f) = (\<lambda>\<sigma> res.
           eval_return \<Gamma> e \<sigma> res \<or> ((eval_value \<Gamma> e) \<lozenge> (eval_return \<Gamma> \<circ> f)) \<sigma> res)\<close>
using urust_eval_predicate_bind_return by (fastforce simp add: eval_return_def eval_value_def
  rel_compose_def)

lemma urust_eval_predicate_bind_abort_rel[urust_eval_predicate_simps]:
  shows \<open>eval_abort \<Gamma> (Core_Expression.bind e f) = (\<lambda>\<sigma> a.
           eval_abort \<Gamma> e \<sigma> a \<or> ((eval_value \<Gamma> e) \<lozenge> (eval_abort \<Gamma> \<circ> f)) \<sigma> a)\<close>
using urust_eval_predicate_bind_abort by (fastforce simp add: eval_abort_def eval_value_def
  rel_compose_def)

corollary urust_eval_predicate_bind [urust_eval_predicate_simps]:
  shows \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,Core_Expression.bind e f\<rangle> (v'',\<sigma>'')) \<longleftrightarrow>
     (\<exists>v' \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v',\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v\<langle>\<Gamma>,f v'\<rangle> (v'',\<sigma>'')))\<close>
    and \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,Core_Expression.bind e f\<rangle> (r,\<sigma>'')) \<longleftrightarrow>
     (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (r,\<sigma>'')) \<or> (\<exists>v \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r\<langle>\<Gamma>,f v\<rangle> (r,\<sigma>'')))\<close>
    and \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,Core_Expression.bind e f\<rangle> (a, \<sigma>'')) \<longleftrightarrow>
     (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,e\<rangle> (a, \<sigma>'')) \<or> (\<exists>v \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a\<langle>\<Gamma>,f v\<rangle> (a, \<sigma>'')))\<close>
by (auto simp add: urust_eval_predicate_bind_success urust_eval_predicate_bind_return
  urust_eval_predicate_bind_abort)

lemma urust_eval_action_bind [urust_eval_action_simps]:
  shows \<open>(\<Gamma>,Core_Expression.bind e f) \<diamondop>\<^sub>v \<sigma> = (\<Union>(v,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. (\<Gamma>,f v) \<diamondop>\<^sub>v \<sigma>')\<close>
    and \<open>(\<Gamma>,Core_Expression.bind e f) \<diamondop>\<^sub>r \<sigma> = ((\<Gamma>,e) \<diamondop>\<^sub>r \<sigma>) \<union> (\<Union>(v,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. (\<Gamma>,f v) \<diamondop>\<^sub>r \<sigma>')\<close>
    and \<open>(\<Gamma>,Core_Expression.bind e f) \<diamondop>\<^sub>a \<sigma> = ((\<Gamma>,e) \<diamondop>\<^sub>a \<sigma>) \<union> (\<Union>(v,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. (\<Gamma>,f v) \<diamondop>\<^sub>a \<sigma>')\<close>
by (auto simp add: value_evaluations_def abort_evaluations_def return_evaluations_def
  urust_eval_predicate_bind)

lemma urust_eval_action_sequence [urust_eval_action_simps]:
  shows \<open>(\<Gamma>,Core_Expression.sequence e f) \<diamondop>\<^sub>v \<sigma> = (\<Union>(v,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. (\<Gamma>,f) \<diamondop>\<^sub>v \<sigma>')\<close>
    and \<open>(\<Gamma>,Core_Expression.sequence e f) \<diamondop>\<^sub>r \<sigma> = ((\<Gamma>,e) \<diamondop>\<^sub>r \<sigma>) \<union> (\<Union>(_,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. (\<Gamma>,f) \<diamondop>\<^sub>r \<sigma>')\<close>
    and \<open>(\<Gamma>,Core_Expression.sequence e f) \<diamondop>\<^sub>a \<sigma> = ((\<Gamma>,e) \<diamondop>\<^sub>a \<sigma>) \<union> (\<Union>(_,\<sigma>') \<in> (\<Gamma>,e) \<diamondop>\<^sub>v \<sigma>. (\<Gamma>,f) \<diamondop>\<^sub>a \<sigma>')\<close>
by (auto simp add: sequence_def urust_eval_action_simps)

corollary urust_eval_predicate_sequence [urust_eval_predicate_simps]:
  shows \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,Core_Expression.sequence e f\<rangle> (v'',\<sigma>'')) \<longleftrightarrow>
     (\<exists>v' \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v',\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v\<langle>\<Gamma>,f\<rangle> (v'',\<sigma>'')))\<close>
    and \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,Core_Expression.sequence e f\<rangle> (r,\<sigma>'')) \<longleftrightarrow>
     (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (r,\<sigma>'')) \<or> (\<exists>v \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r\<langle>\<Gamma>,f\<rangle> (r,\<sigma>'')))\<close>
    and \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,Core_Expression.sequence e f\<rangle> (a, \<sigma>'')) \<longleftrightarrow>
     (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,e\<rangle> (a, \<sigma>'')) \<or> (\<exists>v \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a\<langle>\<Gamma>,f\<rangle> (a, \<sigma>'')))\<close>
by (auto simp add: sequence_def urust_eval_predicate_simps)

lemma urust_eval_action_refine:
  assumes \<open>yield_handler_nondet_basic_refines \<Theta> \<Gamma>\<close>
      and \<open>(\<Gamma>, e) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    shows \<open>(\<Theta>, e) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Theta>, e) \<diamondop>\<^sub>v \<sigma> = (\<Gamma>, e) \<diamondop>\<^sub>v \<sigma>\<close>
      and \<open>(\<Theta>, e) \<diamondop>\<^sub>r \<sigma> = (\<Gamma>, e) \<diamondop>\<^sub>r \<sigma>\<close>
  using assms
  by (auto simp add: urust_eval_action_via_predicate urust_eval_predicate_defs
    deep_evaluate_basic_nondet_refine)

lemma urust_eval_predicate_refine:
  assumes \<open>yield_handler_nondet_basic_refines \<Theta> \<Gamma>\<close>
      and \<open>(\<Gamma>, e) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Theta>, e\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Theta>, e\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>, e\<rangle> (v, \<sigma>')\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Theta>, e\<rangle> (r, \<sigma>') \<longleftrightarrow> \<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>, e\<rangle> (r, \<sigma>')\<close>
  using assms
  by (auto simp add: urust_eval_predicate_via_action urust_eval_action_refine)

text\<open>The skip/literal operator\<close>

lemma urust_eval_action_literal [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, literal v) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    and \<open>(\<Gamma>, literal v) \<diamondop>\<^sub>v \<sigma> = {(v, \<sigma>)}\<close>
    and \<open>(\<Gamma>, literal v) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: evaluate_def literal_def urust_eval_action_via_predicate
  urust_eval_predicate_defs deep_evaluates_nondet_basic.simps)

corollary urust_eval_predicate_literal [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,literal v\<rangle> (v',\<sigma>') \<longleftrightarrow> v = v' \<and> \<sigma> = \<sigma>'\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,literal v\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,literal v\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_action_literal urust_eval_predicate_via_action)

corollary urust_eval_action_skip [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, skip) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    and \<open>(\<Gamma>, skip) \<diamondop>\<^sub>v \<sigma> = {((), \<sigma>)}\<close>
    and \<open>(\<Gamma>, skip) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: urust_eval_action_literal)

corollary urust_eval_predicate_skip [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,skip\<rangle> (v,\<sigma>') \<longleftrightarrow> v = () \<and> \<sigma> = \<sigma>'\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,skip\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,skip\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_literal)

text\<open>The return operator\<close>

lemma urust_eval_action_return [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, return_val r) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    and \<open>(\<Gamma>, return_val r) \<diamondop>\<^sub>v \<sigma> = {}\<close>
    and \<open>(\<Gamma>, return_val r) \<diamondop>\<^sub>r \<sigma> = {(r, \<sigma>)}\<close>
by (auto simp add: evaluate_def return_val_def urust_eval_action_via_predicate
  urust_eval_predicate_defs deep_evaluates_nondet_basic.simps)

corollary urust_eval_predicate_return [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,return_val r\<rangle> (v,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,return_val r\<rangle> (r',\<sigma>') \<longleftrightarrow> r = r' \<and> \<sigma> = \<sigma>'\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,return_val r\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_action_return urust_eval_predicate_via_action)

text\<open>The abort operator\<close>

lemma urust_eval_action_abort [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, abort a) \<diamondop>\<^sub>a \<sigma> = {(a, \<sigma>)}\<close>
    and \<open>(\<Gamma>, abort a) \<diamondop>\<^sub>v \<sigma> = {}\<close>
    and \<open>(\<Gamma>, abort a) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: evaluate_def abort_def urust_eval_action_via_predicate
  urust_eval_predicate_defs deep_evaluates_nondet_basic.simps)

corollary urust_eval_predicate_abort [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,abort a\<rangle> (v,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,abort a\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,abort a\<rangle> (a', \<sigma>') \<longleftrightarrow> a = a' \<and> \<sigma>=\<sigma>'\<close>
by (auto simp add: urust_eval_action_abort urust_eval_predicate_via_action)

text\<open>The assert operator\<close>

lemma urust_eval_action_assert [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, assert_val r) \<diamondop>\<^sub>a \<sigma> = (if r then {} else {(AssertionFailed, \<sigma>)})\<close>
    and \<open>(\<Gamma>, assert_val r) \<diamondop>\<^sub>v \<sigma> = (if r then {((),\<sigma>)} else {})\<close>
    and \<open>(\<Gamma>, assert_val r) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: assert_val_def urust_eval_action_simps)

corollary urust_eval_predicate_assert [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,assert_val r\<rangle> (v,\<sigma>') \<longleftrightarrow> r \<and> \<sigma>' = \<sigma> \<and> v = ()\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,assert_val r\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,assert_val r\<rangle> (a, \<sigma>') \<longleftrightarrow> \<not>r \<and> a = AssertionFailed \<and> \<sigma>=\<sigma>'\<close>
by (auto simp add: urust_eval_action_assert urust_eval_predicate_via_action)

text\<open>The pause operator\<close>

lemma urust_eval_action_pause [urust_eval_action_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>(\<Gamma>, pause) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Gamma>, pause) \<diamondop>\<^sub>v \<sigma> = {((), \<sigma>)}\<close>
      and \<open>(\<Gamma>, pause) \<diamondop>\<^sub>r \<sigma> = {}\<close>
using assms by (auto simp add: pause_def urust_eval_action_via_predicate urust_eval_predicate_defs
  is_log_transparent_yield_handler_def deep_evaluates_nondet_basic.simps evaluate_def literal_def)

lemma urust_eval_predicate_pause [urust_eval_predicate_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, pause\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, pause\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma>' = \<sigma>\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, pause\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
using assms by (simp add: urust_eval_predicate_via_action urust_eval_action_simps)+

text\<open>The log operator\<close>

lemma urust_eval_action_log [urust_eval_action_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>(\<Gamma>, log p l) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Gamma>, log p l) \<diamondop>\<^sub>v \<sigma> = {((), \<sigma>)}\<close>
      and \<open>(\<Gamma>, log p l) \<diamondop>\<^sub>r \<sigma> = {}\<close>
using assms by (auto simp add: log_def urust_eval_action_via_predicate urust_eval_predicate_defs
  is_log_transparent_yield_handler_def deep_evaluates_nondet_basic.simps evaluate_def literal_def)

lemma urust_eval_predicate_log [urust_eval_predicate_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, log p l\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, log p l\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma>' = \<sigma>\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, log p l\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
using assms by (simp add: urust_eval_predicate_via_action urust_eval_action_simps)+

text\<open>The fatal operator\<close>

lemma urust_eval_action_fatal [urust_eval_action_simps]:
  assumes \<open>is_aborting_yield_handler \<Gamma>\<close>
    shows \<open>(\<Gamma>, fatal msg) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Gamma>, fatal msg) \<diamondop>\<^sub>v \<sigma> = {}\<close>
      and \<open>(\<Gamma>, fatal msg) \<diamondop>\<^sub>r \<sigma> = {}\<close>
using assms by (auto simp add: pause_def urust_eval_action_via_predicate urust_eval_predicate_defs
  deep_evaluates_nondet_basic.simps evaluate_def literal_def is_aborting_yield_handler_def fatal_def)

lemma urust_eval_predicate_fatal [urust_eval_predicate_simps]:
  assumes \<open>is_aborting_yield_handler \<Gamma>\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, fatal msg\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, fatal msg\<rangle> (v, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, fatal msg\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
  using assms by (simp add: urust_eval_predicate_via_action urust_eval_action_simps)+

text\<open>The generic yield\<close>

lemma urust_eval_predicate_yield [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, yield \<omega>\<rangle> (v, \<sigma>') \<longleftrightarrow> YieldContinue (v, \<sigma>') \<in> \<Gamma> \<omega> \<sigma>\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, yield \<omega>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, yield \<omega>\<rangle> (a, \<sigma>') \<longleftrightarrow> YieldAbort a \<sigma>' \<in> \<Gamma> \<omega> \<sigma>\<close>
  apply (auto simp add: evaluates_to_value_def evaluates_to_return_def
    evaluates_to_abort_def deep_evaluates_nondet_basic.simps evaluate_def literal_def yield_def
    split!: yield_handler_nondet_basic_result.splits)
  apply (metis surj_pair yield_handler_nondet_basic_result.exhaust)
  apply blast
  apply (metis surj_pair yield_handler_nondet_basic_result.exhaust)
  done

lemma urust_eval_action_yield [urust_eval_predicate_simps]:
  shows \<open>(\<Gamma>, yield \<pi>) \<diamondop>\<^sub>v \<sigma> = { (\<omega>, \<sigma>') . YieldContinue (\<omega>, \<sigma>') \<in> \<Gamma> \<pi> \<sigma> }\<close>
    and \<open>(\<Gamma>, yield \<pi>) \<diamondop>\<^sub>a \<sigma> = { (a, \<sigma>') . YieldAbort a \<sigma>' \<in> \<Gamma> \<pi> \<sigma> }\<close>
    and \<open>(\<Gamma>, yield \<pi>) \<diamondop>\<^sub>r \<sigma> = {}\<close>
  by (auto simp add: urust_eval_predicate_simps simp flip: urust_eval_predicate_via_action)

text\<open>The call operator\<close>

text\<open>Even though the following are trivial consequences of
\<^verbatim>\<open>Core_Expression_Lemmas.evaluate_call_function_bodyE\<close>, spelling them out seem to be necessary for
the proofs below.\<close>
lemma evaluate_call_function_body_yield:
  assumes \<open>evaluate (call_function_body e) \<sigma> = continuation.Yield \<pi> \<sigma>' e'\<close>
  obtains e'' where \<open>evaluate e \<sigma> = Yield \<pi> \<sigma>' e''\<close> and \<open>e' = (\<lambda>\<omega>. call_function_body (e'' \<omega>))\<close>
using assms by (auto elim!: evaluate_call_function_bodyE)

lemma evaluate_call_function_body_value:
  assumes \<open>evaluate (call_function_body e) \<sigma> = Success v \<sigma>'\<close>
    shows \<open>evaluate e \<sigma> = Success v \<sigma>' \<or> evaluate e \<sigma> = Return v \<sigma>'\<close>
using assms by (auto elim!: evaluate_call_function_bodyE)

lemma urust_eval_predicate_call_function_body_value:
  fixes e :: \<open>('s, 'v, 'v, 'abort, 'i, 'o) expression\<close>
  shows \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,call_function_body e :: ('s, 'v, 'r, 'abort, 'i, 'o) expression\<rangle> (v,\<sigma>') \<longleftrightarrow>
           ((\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<or> (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (v,\<sigma>'))))\<close> 
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>''' e')
    then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
      using expression_wf_base_def by fastforce
    from less[OF \<omega>] Yield show ?thesis
      unfolding evaluates_to_return_def evaluates_to_value_def
      apply safe
      apply (erule deep_evaluate_basicE; force simp: call_function_body.simps evaluate_def deep_evaluate_basic_YieldContinueI deep_evaluate_basic_YieldAbortI elim: evaluate_call_function_body_yield)+
      done
  qed (auto simp add: call_function_body.simps deep_evaluates_nondet_basic.simps evaluate_def evaluates_to_return_def evaluates_to_value_def)
qed

lemma urust_eval_predicate_call_function_body_return:
  fixes e :: \<open>('s, 'v, 'v, 'abort, 'i, 'o) expression\<close>
  shows \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,call_function_body e :: ('s, 'v, 'r, 'abort, 'i, 'o) expression\<rangle> (r,\<sigma>'))
           \<longleftrightarrow> False\<close> 
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>'' e')
    then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
      using expression_wf_base_def by fastforce
    from less[OF \<omega>] Yield show ?thesis
      by (force simp: evaluates_to_return_def call_function_body.simps evaluate_def elim: deep_evaluate_basicE)
  qed (auto simp: evaluates_to_return_def call_function_body.simps deep_evaluates_nondet_basic.simps evaluate_def)
qed

lemma urust_eval_predicate_call_function_body_abort:
  fixes e :: \<open>('s, 'v, 'v, 'abort, 'i, 'o) expression\<close>
  shows \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,call_function_body e :: ('s, 'v, 'r, 'abort, 'i, 'o) expression\<rangle> (a, \<sigma>''))
           \<longleftrightarrow> (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>, e\<rangle> (a, \<sigma>''))\<close> 
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>''' e')
    then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
      using expression_wf_base_def by fastforce
    from less[OF \<omega>] Yield show ?thesis
      unfolding evaluates_to_abort_def
      by (force simp: call_function_body.simps evaluate_def deep_evaluate_basic_YieldContinueI deep_evaluate_basic_YieldAbortI elim: evaluate_call_function_body_yield deep_evaluate_basicE)
  qed (auto simp add: evaluates_to_abort_def call_function_body.simps deep_evaluates_nondet_basic.simps evaluate_def)
qed


lemmas urust_eval_predicate_call_function_body [urust_eval_predicate_simps] = 
  urust_eval_predicate_call_function_body_value
  urust_eval_predicate_call_function_body_return
  urust_eval_predicate_call_function_body_abort


lemma urust_eval_action_call_function_body [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, call_function_body e) \<diamondop>\<^sub>a \<sigma> = (\<Gamma>, e) \<diamondop>\<^sub>a \<sigma>\<close>
    and \<open>(\<Gamma>, call_function_body e) \<diamondop>\<^sub>v \<sigma> = ((\<Gamma>, e) \<diamondop>\<^sub>v \<sigma>)
                          \<union> ((\<Gamma>, e) \<diamondop>\<^sub>r \<sigma>)\<close>
    and \<open>(\<Gamma>, call_function_body e) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: urust_eval_action_via_predicate urust_eval_predicate_call_function_body)

lemma urust_eval_predicate_call_value:
  fixes e :: \<open>('s, 'v, 'v, 'abort, 'i, 'o) expression\<close>
  shows \<open>\<And>v \<sigma> \<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,call (FunctionBody e) :: ('s, 'v, 'r, 'abort, 'i, 'o) expression\<rangle> (v,\<sigma>') \<longleftrightarrow>
           ((\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<or> (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (v,\<sigma>'))))\<close> 
by (simp add: call_def urust_eval_predicate_call_function_body_value)

lemma urust_eval_predicate_call_return:
  fixes e :: \<open>('s, 'v, 'v, 'abort, 'i, 'o) expression\<close>
  shows \<open>\<And>r \<sigma> \<sigma>'. (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,call (FunctionBody e) :: ('s, 'v, 'r, 'abort, 'i, 'o) expression\<rangle> (r,\<sigma>'))
           \<longleftrightarrow> False\<close> 
by (simp add: call_def urust_eval_predicate_call_function_body_return)

lemma urust_eval_predicate_call_abort:
  fixes e :: \<open>('s, 'v, 'v, 'abort, 'i, 'o) expression\<close>
  shows \<open>\<And>a \<sigma> \<sigma>'. (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,call (FunctionBody e) :: ('s, 'v, 'r, 'abort, 'i, 'o) expression\<rangle> (a, \<sigma>'))
           \<longleftrightarrow> (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>, e\<rangle> (a, \<sigma>'))\<close>
by (simp add: call_def urust_eval_predicate_call_function_body_abort)

lemma urust_eval_predicate_call [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,call f\<rangle> (v,\<sigma>') \<longleftrightarrow> (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,function_body f\<rangle> (v,\<sigma>'))
                                \<or>  (\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,function_body f\<rangle> (v,\<sigma>'))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,call f\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,call f\<rangle> (a, \<sigma>') \<longleftrightarrow> (\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,(function_body f)\<rangle> (a, \<sigma>'))\<close>
  apply (metis function_body.collapse urust_eval_predicate_call_value)
  apply (metis function_body.exhaust_sel urust_eval_predicate_call_return)
  apply (metis function_body.exhaust_sel urust_eval_predicate_call_abort)
  done

lemma urust_eval_predicate_call_rel [urust_eval_predicate_simps]:
  shows \<open>eval_value \<Gamma> (call f) = (\<lambda>a b. eval_value \<Gamma> (function_body f) a b
                                      \<or> eval_return \<Gamma> (function_body f) a b)\<close>
    and \<open>eval_return \<Gamma> (call f) = (\<lambda>_ _. False)\<close>
    and \<open>eval_abort \<Gamma> (call f) = eval_abort \<Gamma> (function_body f)\<close>
by (auto simp add: eval_value_def eval_abort_def eval_return_def urust_eval_predicate_simps)

lemma urust_eval_action_call [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, call f) \<diamondop>\<^sub>a \<sigma> = (\<Gamma>, (function_body f)) \<diamondop>\<^sub>a \<sigma>\<close>
    and \<open>(\<Gamma>, call f) \<diamondop>\<^sub>v \<sigma> = ((\<Gamma>, (function_body f)) \<diamondop>\<^sub>v \<sigma>)
                          \<union> ((\<Gamma>, (function_body f)) \<diamondop>\<^sub>r \<sigma>)\<close>
    and \<open>(\<Gamma>, call f) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: urust_eval_action_via_predicate urust_eval_predicate_call)

text\<open>Conditionals\<close>

corollary urust_eval_action_two_armed_conditional [urust_eval_action_simps]:
  shows \<open>(\<Gamma>,two_armed_conditional cond then_branch else_branch) \<diamondop>\<^sub>v \<sigma> =
            (\<Union>(v, \<sigma>') \<in> (\<Gamma>,cond) \<diamondop>\<^sub>v \<sigma>. if v then (\<Gamma>,then_branch) \<diamondop>\<^sub>v \<sigma>'
                                     else (\<Gamma>, else_branch) \<diamondop>\<^sub>v \<sigma>')\<close> (is ?g1)
    and \<open>(\<Gamma>,two_armed_conditional cond then_branch else_branch) \<diamondop>\<^sub>r \<sigma> =
            ((\<Gamma>,cond) \<diamondop>\<^sub>r \<sigma>) \<union>
            (\<Union>(v, \<sigma>') \<in> (\<Gamma>,cond) \<diamondop>\<^sub>v \<sigma>. if v then (\<Gamma>,then_branch) \<diamondop>\<^sub>r \<sigma>'
                                     else (\<Gamma>, else_branch) \<diamondop>\<^sub>r \<sigma>')\<close> (is ?g2)
    and \<open>(\<Gamma>,two_armed_conditional cond then_branch else_branch) \<diamondop>\<^sub>a \<sigma> =
            ((\<Gamma>,cond) \<diamondop>\<^sub>a \<sigma>) \<union>
            (\<Union>(v, \<sigma>') \<in> (\<Gamma>,cond) \<diamondop>\<^sub>v \<sigma>. if v then (\<Gamma>,then_branch) \<diamondop>\<^sub>a \<sigma>'
                                     else (\<Gamma>, else_branch) \<diamondop>\<^sub>a \<sigma>')\<close> (is ?g3)
proof -
  have A: \<open>\<And>x a b. (case x of (v, t) \<Rightarrow> if v then a t else b t)
              = (case x of (True, t) \<Rightarrow> a t | (False, t) \<Rightarrow> b t)\<close>
    by auto
  have E1: \<open>\<And>\<Gamma> \<sigma> v a b. ((\<Gamma>,(if v then a else b)) \<diamondop>\<^sub>v \<sigma>) =
            (if v then ((\<Gamma>,a) \<diamondop>\<^sub>v \<sigma>) else ((\<Gamma>,b) \<diamondop>\<^sub>v \<sigma>))\<close> by auto
  have E2: \<open>\<And>\<Gamma> \<sigma> v a b. ((\<Gamma>,(if v then a else b)) \<diamondop>\<^sub>r \<sigma>) =
            (if v then ((\<Gamma>,a) \<diamondop>\<^sub>r \<sigma>) else ((\<Gamma>,b) \<diamondop>\<^sub>r \<sigma>))\<close> by auto
  have E3: \<open>\<And>\<Gamma> \<sigma> v a b. ((\<Gamma>,(if v then a else b)) \<diamondop>\<^sub>a \<sigma>) =
            (if v then ((\<Gamma>,a) \<diamondop>\<^sub>a \<sigma>) else ((\<Gamma>,b) \<diamondop>\<^sub>a \<sigma>))\<close> by auto
  show ?g1 ?g2 ?g3 by (auto simp add: two_armed_conditional_def
    urust_eval_action_bind E1 E2 E3)
qed

corollary urust_eval_predicate_two_armed_conditional [urust_eval_predicate_simps]:
  shows \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,two_armed_conditional cond then_branch else_branch\<rangle> (v,\<sigma>'')) =
          ((\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (True,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v \<langle>\<Gamma>,then_branch\<rangle> (v,\<sigma>''))) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (False,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v \<langle>\<Gamma>,else_branch\<rangle> (v,\<sigma>''))))\<close> (is ?g1)
    and \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,two_armed_conditional cond then_branch else_branch\<rangle> (r,\<sigma>'')) =
            ((\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,cond\<rangle> (r, \<sigma>'')) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (True,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r \<langle>\<Gamma>,then_branch\<rangle> (r,\<sigma>''))) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (False,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r \<langle>\<Gamma>,else_branch\<rangle> (r,\<sigma>''))))\<close> (is ?g2)
    and \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,two_armed_conditional cond then_branch else_branch\<rangle> (a, \<sigma>'')) =
          ((\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,cond\<rangle> (a, \<sigma>'')) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (True,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a \<langle>\<Gamma>,then_branch\<rangle> (a, \<sigma>''))) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (False,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a \<langle>\<Gamma>,else_branch\<rangle> (a, \<sigma>''))))\<close> (is ?g3)
proof -
  show ?g1
    by (auto simp add: urust_eval_action_two_armed_conditional urust_eval_predicate_via_action,
      metis (full_types), force, force)
  show ?g2
    by (auto simp add: urust_eval_action_two_armed_conditional  urust_eval_predicate_via_action,
      metis (full_types), force, force)
  show ?g3
    by (auto simp add: urust_eval_action_two_armed_conditional urust_eval_predicate_via_action,
      metis (full_types), force, force)
qed

text\<open>Get and put operators\<close>

lemma urust_eval_action_get [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, get f) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    and \<open>(\<Gamma>, get f) \<diamondop>\<^sub>v \<sigma> = {(f \<sigma>, \<sigma>)}\<close>
    and \<open>(\<Gamma>, get f) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: evaluate_def get_def urust_eval_action_via_predicate urust_eval_predicate_defs
  deep_evaluates_nondet_basic.simps)

corollary urust_eval_predicate_get [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,get f\<rangle> (v,\<sigma>') \<longleftrightarrow> (v = f \<sigma> \<and> \<sigma>' = \<sigma>)\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,get f\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,get f\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_action_get urust_eval_predicate_via_action)

lemma urust_eval_action_put [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, put \<tau>) \<diamondop>\<^sub>a \<sigma> = {}\<close>
    and \<open>(\<Gamma>, put \<tau>) \<diamondop>\<^sub>v \<sigma> = {((), \<tau> \<sigma>)}\<close>
    and \<open>(\<Gamma>, put \<tau>) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: evaluate_def put_def urust_eval_action_via_predicate urust_eval_predicate_defs
  deep_evaluates_nondet_basic.simps)

corollary urust_eval_predicate_put [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,put \<tau>\<rangle> (v,\<sigma>') \<longleftrightarrow> \<sigma>' = \<tau> \<sigma>\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,put \<tau>\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,put \<tau>\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_action_put urust_eval_predicate_via_action)

lemma urust_eval_action_put_assert [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, put_assert \<tau> a) \<diamondop>\<^sub>a \<sigma> = (case \<tau> \<sigma> of None \<Rightarrow> {(a, \<sigma>)} | Some _ \<Rightarrow> {})\<close>
    and \<open>(\<Gamma>, put_assert \<tau> a) \<diamondop>\<^sub>v \<sigma> = (case \<tau> \<sigma> of None \<Rightarrow> {} | Some \<sigma>' \<Rightarrow> {((), \<sigma>')})\<close>
    and \<open>(\<Gamma>, put_assert \<tau> a) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: evaluate_def put_assert_def urust_eval_action_via_predicate
urust_eval_predicate_defs deep_evaluates_nondet_basic.simps split: option.splits)

corollary urust_eval_predicate_put_assert [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,put_assert \<tau> a\<rangle> (v,\<sigma>') \<longleftrightarrow> \<tau> \<sigma> = Some \<sigma>'\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,put_assert \<tau> a\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,put_assert \<tau> a\<rangle> (a', \<sigma>') \<longleftrightarrow> a' = a \<and> \<sigma> = \<sigma>' \<and> \<tau> \<sigma> = None\<close>
by (auto simp add: urust_eval_action_put_assert urust_eval_predicate_via_action split: option.splits)

text\<open>Numeric operators\<close>

lemma urust_eval_action_add_no_wrap [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if (unat x + unat y < 2 ^ LENGTH('l)) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    and \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if (unat x + unat y < 2 ^ LENGTH('l)) then {(x + y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
proof -
  show \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
      (if (unat x + unat y < 2 ^ LENGTH('l)) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    by (simp add: word_add_no_wrap_def urust_eval_action_bind micro_rust_simps
      urust_eval_action_literal urust_eval_action_abort word_add_no_wrap_core_def Let_def
      word_add_no_wrap_as_urust_def urust_eval_action_call word_add_no_wrap_pure_def
      word_op_no_wrap_pure_def option_unwrap_expr_def split: option.splits if_splits)
  show \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
      (if (unat x + unat y < 2 ^ LENGTH('l)) then {(x + y, \<sigma>)} else {})\<close>
    by (simp add: word_add_no_wrap_def urust_eval_action_bind micro_rust_simps
      urust_eval_action_literal urust_eval_action_abort word_add_no_wrap_core_def Let_def
      word_add_no_wrap_as_urust_def urust_eval_action_call word_add_no_wrap_pure_def
      word_op_no_wrap_pure_def option_unwrap_expr_def split: option.splits if_splits)
  show \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
    by (simp add: word_add_no_wrap_def urust_eval_action_bind micro_rust_simps
      urust_eval_action_literal urust_eval_action_abort word_add_no_wrap_core_def Let_def
      word_add_no_wrap_as_urust_def urust_eval_action_call word_add_no_wrap_pure_def
      word_op_no_wrap_pure_def option_unwrap_expr_def split: option.splits if_splits)
qed

corollary urust_eval_predicate_add_no_wrap [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat x + unat y < 2^LENGTH('l)) \<and> \<sigma> = \<sigma>' \<and> v = x + y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat x + unat y \<ge> 2^LENGTH('l)) \<and> a = Panic overflow_err_msg \<and> \<sigma> = \<sigma>'\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_add_no_wrap)

lemma urust_eval_action_mul_no_wrap [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if (unat x * unat y < 2 ^ LENGTH('l)) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    and \<open>((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if (unat x * unat y < 2 ^ LENGTH('l)) then {(x * y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
proof -
  show \<open>((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
      (if (unat x * unat y < 2 ^ LENGTH('l)) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    by (simp add: word_mul_no_wrap_def urust_eval_action_bind micro_rust_simps
      urust_eval_action_literal urust_eval_action_abort word_mul_no_wrap_core_def Let_def
      word_mul_no_wrap_as_urust_def urust_eval_action_call word_mul_no_wrap_pure_def
      word_op_no_wrap_pure_def option_unwrap_expr_def split: option.splits if_splits)
  show \<open>((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
      (if (unat x * unat y < 2 ^ LENGTH('l)) then {(x * y, \<sigma>)} else {})\<close>
    by (simp add: word_mul_no_wrap_def urust_eval_action_bind micro_rust_simps
      urust_eval_action_literal urust_eval_action_abort word_mul_no_wrap_core_def Let_def
      word_mul_no_wrap_as_urust_def urust_eval_action_call word_mul_no_wrap_pure_def
      word_op_no_wrap_pure_def option_unwrap_expr_def split: option.splits if_splits)
  show \<open>((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
    by (simp add: word_mul_no_wrap_def urust_eval_action_bind micro_rust_simps
      urust_eval_action_literal urust_eval_action_abort word_mul_no_wrap_core_def Let_def
      word_mul_no_wrap_as_urust_def urust_eval_action_call word_mul_no_wrap_pure_def
      word_op_no_wrap_pure_def option_unwrap_expr_def split: option.splits if_splits)
qed

corollary urust_eval_predicate_mul_no_wrap [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x * y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat x * unat y < 2^LENGTH('l)) \<and> \<sigma> = \<sigma>' \<and> v = x * y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x * y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x * y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat x * unat y \<ge> 2^LENGTH('l)) \<and> \<sigma> = \<sigma>' \<and> a = Panic overflow_err_msg\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_mul_no_wrap)

lemma urust_eval_action_sub_no_wrap [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if ( unat y \<le> unat x) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    and \<open>((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if ( unat y \<le> unat x) then {(x - y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp flip: word_le_nat_alt simp add: word_minus_no_wrap_def urust_eval_action_bind
  micro_rust_simps urust_eval_action_literal urust_eval_action_abort word_minus_no_wrap_core_def
  word_minus_no_wrap_as_urust_def urust_eval_action_call word_op_no_wrap_pure_def
  word_minus_no_wrap_pure_def option_unwrap_expr_def Let_def)

corollary urust_eval_predicate_sub_no_wrap [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x - y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat y \<le> unat x) \<and> \<sigma> = \<sigma>' \<and> v = x - y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x - y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x - y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y > unat x) \<and> a = Panic overflow_err_msg \<and> \<sigma> = \<sigma>'\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_sub_no_wrap)

lemma urust_eval_action_div [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if ( unat y \<noteq> 0) then {} else { (Panic (String.implode ''division by zero''), \<sigma>) })\<close>
    and \<open>((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if ( unat y \<noteq> 0) then {(x div y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp add: unat_gt_0 word_div_def urust_eval_action_bind micro_rust_simps
  urust_eval_action_literal urust_eval_action_abort word_udiv_core_def word_udiv_def
  urust_eval_action_call)

corollary urust_eval_predicate_div [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat y \<noteq> 0) \<and> \<sigma> = \<sigma>' \<and> v = x div y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y = 0) \<and> \<sigma> = \<sigma>' \<and> a = Panic (String.implode ''division by zero'')\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_div)

lemma urust_eval_action_mod [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if ( unat y \<noteq> 0) then {} else { (Panic (String.implode ''division by zero''), \<sigma>) })\<close>
    and \<open>((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if ( unat y \<noteq> 0) then {(x mod y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp add: unat_gt_0 word_mod_def urust_eval_action_bind micro_rust_simps
  urust_eval_action_literal urust_eval_action_abort word_umod_core_def word_umod_def
  urust_eval_action_call)

corollary urust_eval_predicate_mod [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x % y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat y \<noteq> 0) \<and> \<sigma> = \<sigma>' \<and> v = x mod y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x % y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x % y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y = 0) \<and> a = Panic (String.implode ''division by zero'') \<and> \<sigma> = \<sigma>'\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_mod)

lemma urust_eval_action_shift_left [urust_eval_action_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x << y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if unat y < LENGTH('l0) then {} else {(Panic overflow_err_msg, \<sigma>)})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x << y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if unat y < LENGTH('l0) then {(push_bit (unat y) x, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x << y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp flip: word_le_nat_alt simp add: word_shift_left_pure_def urust_eval_action_bind
  micro_rust_simps urust_eval_action_literal urust_eval_action_abort word_shift_left_core_def
  word_shift_left_as_urust_def urust_eval_action_call word_shift_left_def
  word_shift_left_shift64_def option_unwrap_expr_def Let_def)

corollary urust_eval_predicate_shift_left [urust_eval_predicate_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x << y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow>
            unat y < LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> v = push_bit (unat y) x\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x << y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x << y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y \<ge> LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> a = Panic overflow_err_msg)\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_shift_left)

lemma urust_eval_action_shift_right [urust_eval_action_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) =
            (if unat y < LENGTH('l0) then {} else {(Panic overflow_err_msg, \<sigma>)})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) =
            (if unat y < LENGTH('l0) then {(drop_bit (unat y) x, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp flip: word_le_nat_alt simp add: word_shift_right_pure_def urust_eval_action_bind
  micro_rust_simps urust_eval_action_literal urust_eval_action_abort word_shift_right_core_def
  word_shift_right_as_urust_def urust_eval_action_call word_shift_right_def
  word_shift_right_shift64_def option_unwrap_expr_def Let_def)

corollary urust_eval_predicate_shift_right [urust_eval_predicate_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x >> y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow>
            unat y < LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> v = drop_bit (unat y) x\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x >> y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x >> y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y \<ge> LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> a = Panic overflow_err_msg)\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_shift_right)

lemma urust_eval_action_xor [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x ^ y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x ^ y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(x XOR y, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x ^ y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_xor [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x ^ y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = x XOR y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x ^ y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x ^ y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_xor)

lemma urust_eval_action_or [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x | y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x | y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(x OR y, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x | y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_or [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x | y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = x OR y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x | y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x | y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_or)

lemma urust_eval_action_and [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x & y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x & y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(x AND y, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x & y \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_and [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x & y \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = x AND y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> x & y \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x & y \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_and)

lemma urust_eval_action_not [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, \<lbrakk> !x \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, \<lbrakk> !x \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(NOT x, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> !x \<rbrakk>) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_not [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> !x \<rbrakk>\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = NOT x\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, \<lbrakk> !x \<rbrakk>\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> !x \<rbrakk>\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_not)

end
