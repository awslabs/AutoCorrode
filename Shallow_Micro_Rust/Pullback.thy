(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Pullback
  imports Core_Expression_Lemmas Eval
begin

section\<open>Pulling back Micro Rust expressions along lenses\<close>

text\<open>Suppose  \<^verbatim>\<open>'r \<Rightarrow> 'v\<close> is a lens from record-like type \<^verbatim>\<open>'r\<close> to a 'field' type
\<^verbatim>\<open>'v\<close>. Then, by definition of lenses, any endomorphism \<^verbatim>\<open>f :: 'v \<Rightarrow> 'v\<close> yields a
(chosen) \<^emph>\<open>lift\<close> \<^verbatim>\<open>\<nabla>f :: 'r \<Rightarrow> 'r\<close>.

On the other hand, micro rust expressions on \<open>'v\<close> (or, more precisely, their denotations under
the shallow embedding into HOL) are \<^emph>\<open>essentially\<close> endomorphisms on \<^verbatim>\<open>'r\<close>, with the tweak
that they may abort and produce return or literal values.

Intuitively, one would therefore expect that it should be possible to 'pull back' micro rust
expressions on \<^verbatim>\<open>'v\<close> to micro rust expressions on \<^verbatim>\<open>'a\<close>. The goal of this section is to
make this precise.\<close>

consts pull_back_const :: \<open>'a \<Rightarrow> 'b\<close> ("_\<inverse>" [1000] 1000)

function expression_pull_back :: \<open>('r, 'v) lens \<Rightarrow> ('v, 'a, 'b, 'abort, 'i, 'o) expression \<Rightarrow>
  ('r, 'a, 'b, 'abort, 'i, 'o) expression\<close> where
  \<open>expression_pull_back l e = Expression (\<lambda>\<sigma>.
     let \<tau> = lens_view l \<sigma> in
       case evaluate e \<tau> of
         Success v \<tau>' \<Rightarrow> Success v (lens_update l \<tau>' \<sigma>)
       | Return r \<tau>'  \<Rightarrow> Return r (lens_update l \<tau>' \<sigma>)
       | Abort a \<tau>'   \<Rightarrow> Abort a (lens_update l \<tau>' \<sigma>)
       | Yield p \<tau>' c \<Rightarrow> Yield p (lens_update l \<tau>' \<sigma>) (\<lambda>\<omega>. expression_pull_back l (c \<omega>)))\<close>
by pat_completeness auto

termination
  expression_pull_back
proof (relation \<open>inv_image expression_wf snd\<close>)
  show \<open>wf (inv_image expression_wf snd)\<close>
    by force
next
  fix l :: \<open>('a, 'b) lens\<close> and e :: \<open>('b, 'c, 'd, 'e, 'f, 'g) expression\<close> and x xa x41 x42 x43 xb
  assume \<open>xa = lens_view l x\<close>
     and \<open>evaluate e xa = Yield x41 x42 x43\<close>
  from this show \<open>((l, x43 xb), l, e) \<in> inv_image expression_wf snd\<close>
    by (force simp add: expression_wf_def expression_wf_base_def)
qed

declare expression_pull_back.simps[simp del]

adhoc_overloading pull_back_const \<rightleftharpoons> expression_pull_back

definition function_pull_back :: \<open>('r, 'v) lens \<Rightarrow> ('v, 'a, 'abort, 'i, 'o) function_body \<Rightarrow> ('r, 'a, 'abort, 'i, 'o) function_body\<close>
  where \<open>function_pull_back l f \<equiv> FunctionBody (expression_pull_back l (function_body f))\<close>
adhoc_overloading pull_back_const \<rightleftharpoons> function_pull_back

lemma expression_pull_back_evaluate:
  shows \<open>evaluate (expression_pull_back l e) \<sigma> =
     (let \<tau> = lens_view l \<sigma> in
      case evaluate e \<tau> of
         Success v \<tau>' \<Rightarrow> Success v (lens_update l \<tau>' \<sigma>)
       | Return r \<tau>' \<Rightarrow> Return r (lens_update l \<tau>' \<sigma>)
       | Abort a \<tau>' \<Rightarrow> Abort a (lens_update l \<tau>' \<sigma>)
       | Yield p \<tau>' c \<Rightarrow> Yield p (lens_update l \<tau>' \<sigma>)
                            (\<lambda>\<omega>. expression_pull_back l (c \<omega>)))\<close>
  by (simp add: evaluate_def expression_pull_back.simps)

text\<open>Pull-back is a morphism of monads in the following sense:\<close>

lemma expression_pull_back_bind:
  shows \<open>is_valid_lens l \<Longrightarrow> l\<inverse> (bind e f) = bind (l\<inverse> e) (l\<inverse> \<circ> f)\<close>
proof (induct e rule: wf_induct_rule[OF expression_wf_base_is_wf])
  fix e assume IH: \<open>\<And>e'. (e',e)\<in>expression_wf_base
                      \<Longrightarrow> is_valid_lens l \<Longrightarrow> l\<inverse> (bind e' f) = bind (l\<inverse> e') (l\<inverse> \<circ> f)\<close>
  from IH have \<open>\<And>\<sigma>. is_valid_lens l \<Longrightarrow> (evaluate (l\<inverse> (bind e f)) \<sigma> =
                        evaluate (bind (l\<inverse> e) (l\<inverse> \<circ> f)) \<sigma>)\<close>
    by (clarsimp simp add: expression_pull_back_evaluate bind_evaluate
      expression_wf_base_def lens_laws split!: continuation.splits) blast
  from this show \<open>is_valid_lens l \<Longrightarrow> l\<inverse> (bind e f) = bind (l\<inverse> e) (l\<inverse> \<circ> f)\<close>
    by (simp add: expression_eqI2)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma expression_pull_back_sequence:
  shows \<open>is_valid_lens l \<Longrightarrow> l\<inverse> (e ; f) = (l\<inverse> e ; l\<inverse> f)\<close>
  by (simp add: expression_pull_back_bind sequence_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma expression_pull_back_literal:
  shows \<open>is_valid_lens l \<Longrightarrow> l\<inverse> (literal v) = literal v\<close>
  by (clarsimp simp add: expression_pull_back_evaluate evaluate_literal
    is_valid_lens_def lens_update_def intro!: expression_eqI2)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma expression_pull_back_return:
  shows \<open>is_valid_lens l \<Longrightarrow> l\<inverse> (return_val r) = return_val r\<close>
  by (clarsimp simp add: expression_pull_back_evaluate evaluate_return_val
    is_valid_lens_def lens_update_def intro!: expression_eqI2)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma expression_pull_back_abort:
  shows \<open>is_valid_lens l \<Longrightarrow> l\<inverse> (abort a) = abort a\<close>
  by (clarsimp simp add: expression_pull_back_evaluate evaluate_abort
    is_valid_lens_def lens_update_def intro!: expression_eqI2)

subsection\<open>Pull back of yield handlers\<close>

context
    fixes l :: \<open>('a, 'b) lens\<close>
  assumes LV: \<open>is_valid_lens l\<close>
begin

text\<open>If a lens \<^verbatim>\<open>l :: ('a, 'b) lens\<close> and a yield handler \<^verbatim>\<open>y\<close> on \<^verbatim>\<open>'b\<close> are given, \<^emph>\<open>a\<close> (!)
pull back of \<^verbatim>\<open>y\<close> is any yield handler on \<^verbatim>\<open>'a\<close> which makes the same choices as \<^verbatim>\<open>y\<close> under
the view of \<^verbatim>\<open>l\<close>.\<close>

definition lift_yield_result ::
  \<open>'a \<Rightarrow> ('b, 'abort, 'o) yield_handler_nondet_basic_result \<Rightarrow> ('a, 'abort, 'o) yield_handler_nondet_basic_result\<close> where
  \<open>lift_yield_result \<sigma> res \<equiv> case res of
      YieldAbort a \<tau> \<Rightarrow> YieldAbort a (lens_update l \<tau> \<sigma>)
    | YieldContinue (\<omega>, \<tau>) \<Rightarrow> YieldContinue (\<omega>, lens_update l \<tau> \<sigma>)\<close>

definition lower_yield_result ::
  \<open>('a, 'abort, 'o) yield_handler_nondet_basic_result \<Rightarrow> ('b, 'abort, 'o) yield_handler_nondet_basic_result\<close> where
  \<open>lower_yield_result res_hi \<equiv> case res_hi of
      YieldAbort a \<sigma>' \<Rightarrow> YieldAbort a (lens_view l \<sigma>')
    | YieldContinue (\<omega>, \<sigma>') \<Rightarrow> YieldContinue (\<omega>, lens_view l \<sigma>')\<close>

definition is_lifted_yield_handler ::
   \<open>('b, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('a, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> bool\<close> where
  \<open>is_lifted_yield_handler yh_lo yh_hi \<equiv>
      \<forall>\<pi> \<sigma>. yh_lo \<pi> (lens_view l \<sigma>) = lower_yield_result ` (yh_hi \<pi> \<sigma>)\<close>

text\<open>Note that we do \<^emph>\<open>not\<close> require that a lifted yield handler only modifies state components in
\<^verbatim>\<open>'b\<close>. This \<^emph>\<open>is\<close> a canonical choice of lifted yield handler, but there may be others.\<close>

definition canonical_pull_back_yield_handler ::
  \<open>('b, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('a, 'abort, 'i, 'o) yield_handler_nondet_basic\<close> where
  \<open>canonical_pull_back_yield_handler y \<pi> \<sigma> \<equiv> lift_yield_result \<sigma> ` y \<pi> (lens_view l \<sigma>)\<close>

lemma canonical_pull_back_yield_handler_no_yield[simp]:
  shows \<open>canonical_pull_back_yield_handler yield_handler_no_yield =
            yield_handler_no_yield\<close>
  unfolding fun_eq_iff 
  by (simp add: canonical_pull_back_yield_handler_def yield_handler_no_yield_def
                lift_yield_result_def LV lens_laws_update(2))

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma canonical_pull_back_yield_handler_is_lift:
  \<open>is_lifted_yield_handler y (canonical_pull_back_yield_handler y)\<close>
  by (force simp add: canonical_pull_back_yield_handler_def is_lifted_yield_handler_def
    lift_yield_result_def lower_yield_result_def lens_laws[OF LV]
    image_comp case_prod_unfold split!: prod.splits yield_handler_nondet_basic_result.splits)

lemma canonical_pull_back_yield_handler_log_preserving:
  assumes \<open>is_log_transparent_yield_handler y\<close>
  shows \<open>is_log_transparent_yield_handler (canonical_pull_back_yield_handler y)\<close>
  using assms by (clarsimp simp add: is_log_transparent_yield_handler_def
    canonical_pull_back_yield_handler_def lift_yield_result_def)
    (metis LV is_valid_lens_def lens_update_def)

lemma canonical_pull_back_yield_handler_nondet_order_preserving:
  assumes \<open>is_nondet_order_yield_handler y\<close>
  shows \<open>is_nondet_order_yield_handler (canonical_pull_back_yield_handler y)\<close>
  using assms
  by (clarsimp simp add: is_nondet_order_yield_handler_def
    canonical_pull_back_yield_handler_def lift_yield_result_def)
    (metis LV is_valid_lens_def lens_update_def)

text\<open>At the level of the evaluation relation, pullback of expressions is pullback of relations:\<close>

definition continuation_map :: \<open>('a, 'v, 'r, 'abort, 'i, 'o) continuation \<Rightarrow> ('b, 'v, 'r, 'abort, 'i, 'o) continuation\<close>
  where \<open>continuation_map c \<equiv>
     (case c of
        Success v \<sigma> \<Rightarrow> Success v (lens_view l \<sigma>)
      | Return r \<sigma> \<Rightarrow> Return r (lens_view l \<sigma>)
      | Abort a \<sigma> \<Rightarrow> Abort a (lens_view l \<sigma>)
      | Yield _ _ _ \<Rightarrow> undefined)\<close>

lemma expression_pull_back_deep_evaluates:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>continuation_map ` (deep_evaluates_nondet_basic x (l\<inverse> e) \<sigma>)
           = deep_evaluates_nondet_basic y e (lens_view l \<sigma>)\<close>
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  note simps = deep_evaluates_nondet_basic.simps expression_pull_back_evaluate 
               continuation_map_def is_valid_lens_def
  show ?case
  proof (cases \<open>evaluate e (lens_view l \<sigma>)\<close>)
    case (Yield \<pi> \<sigma>' e')
    show ?thesis
    proof -
      have \<open>local.continuation_map c \<in> deep_evaluates_nondet_basic y e (lens_view l \<sigma>)\<close>
        if \<open>c \<in> deep_evaluates_nondet_basic x (l\<inverse> e) \<sigma>\<close>
        for c :: \<open>('a, 'f, 'g, 'd, 'c, 'e) continuation\<close>
      proof (rule deep_evaluate_basicE [OF that])
        fix e'' :: \<open>'e \<Rightarrow> ('a, 'f, 'g, 'd, 'c, 'e) expression\<close> and \<pi>' \<omega> \<sigma>'' \<sigma>'''
        assume e: \<open>evaluate (l\<inverse> e) \<sigma> = Yield \<pi>' \<sigma>'' e''\<close>
          and \<omega>: \<open>YieldContinue (\<omega>, \<sigma>''') \<in> x \<pi>' \<sigma>''\<close> 
          and c: \<open>c \<in> deep_evaluates_nondet_basic x (e'' \<omega>) \<sigma>'''\<close>
        have \<dagger>: \<open>((e' \<omega>), e) \<in> expression_wf_base\<close>
          using expression_wf_base_def Yield by fastforce
        have \<open>y \<pi>' (lens_view l \<sigma>'') = local.lower_yield_result ` x \<pi>' \<sigma>''\<close>
          by (meson assms is_lifted_yield_handler_def)
        with e \<omega> LV Yield have \<open>YieldContinue (\<omega>, lens_view l \<sigma>''') \<in> y \<pi>' \<sigma>'\<close>
          by (fastforce elim!: is_valid_lensE simp add: image_iff expression_pull_back_evaluate lower_yield_result_def)
        with e c Yield less [OF \<dagger>]
        show \<open>local.continuation_map c \<in> deep_evaluates_nondet_basic y e (lens_view l \<sigma>)\<close>
          by (fastforce simp: simps split!: yield_handler_nondet_basic_result.splits)
      next
        fix e' :: \<open>'e \<Rightarrow> ('a, 'f, 'g, 'd, 'c, 'e) expression\<close> and \<pi>' a \<sigma>'' \<sigma>'''
        assume e: \<open>evaluate (l\<inverse> e) \<sigma> = Yield \<pi>' \<sigma>'' e'\<close>
           and a: \<open>YieldAbort a \<sigma>''' \<in> x \<pi>' \<sigma>''\<close> 
           and c: \<open>c = Abort a \<sigma>'''\<close>
        have \<open>y \<pi>' (lens_view l \<sigma>'') = local.lower_yield_result ` x \<pi>' \<sigma>''\<close>
          by (meson assms is_lifted_yield_handler_def)
        with Yield LV e a lens_laws_update(1) have \<open>YieldAbort a (lens_view l \<sigma>''') \<in> y \<pi> \<sigma>'\<close>
          by (fastforce simp: lower_yield_result_def image_iff expression_pull_back_evaluate)
        with Yield c show \<open>local.continuation_map c \<in> deep_evaluates_nondet_basic y e (lens_view l \<sigma>)\<close>
          by (simp add: continuation_map_def deep_evaluate_basic_YieldAbortI)
      qed (use Yield in \<open>auto simp: expression_pull_back_evaluate\<close>)
      moreover 
      have \<open>\<exists>x\<in>deep_evaluates_nondet_basic x (l\<inverse> e) \<sigma>. c = local.continuation_map x\<close>
        if \<open>c \<in> deep_evaluates_nondet_basic y e (lens_view l \<sigma>)\<close>
        for c :: \<open>('b, 'f, 'g, 'd, 'c, 'e) continuation\<close>
      proof (rule deep_evaluate_basicE [OF that])
        fix e'' :: \<open>'e \<Rightarrow> ('b, 'f, 'g, 'd, 'c, 'e) expression\<close> and \<pi>' \<omega> \<sigma>'' \<sigma>'''
        assume e: \<open>evaluate e (lens_view l \<sigma>) = Yield \<pi>' \<sigma>'' e''\<close>
          and \<omega>: \<open>YieldContinue (\<omega>, \<sigma>''') \<in> y \<pi>' \<sigma>''\<close>
          and c: \<open>c \<in> deep_evaluates_nondet_basic y (e'' \<omega>) \<sigma>'''\<close>
        have \<dagger>: \<open>((e'' \<omega>), e) \<in> expression_wf_base\<close>
          using e expression_wf_base_def by fastforce
        have \<open>YieldContinue (\<omega>, \<sigma>''') \<in> lower_yield_result ` x \<pi>' (lens_update l \<sigma>' \<sigma>)\<close>
          by (metis LV Yield \<omega> assms continuation.inject(4) e is_lifted_yield_handler_def is_valid_lensE)
        with Yield less[OF \<dagger>] e \<omega> c
        show \<open>\<exists>x\<in>deep_evaluates_nondet_basic x (l\<inverse> e) \<sigma>. c = local.continuation_map x\<close>
          by (fastforce simp: simps lower_yield_result_def split!: yield_handler_nondet_basic_result.splits)
      next
        fix e'' :: \<open>'e \<Rightarrow> ('b, 'f, 'g, 'd, 'c, 'e) expression\<close> and \<pi>' a \<sigma>'' \<sigma>'''
        assume e: \<open>evaluate e (lens_view l \<sigma>) = Yield \<pi>' \<sigma>'' e''\<close>
          and a: \<open>YieldAbort a \<sigma>''' \<in> y \<pi>' \<sigma>''\<close>
          and c: \<open>c = Abort a \<sigma>'''\<close>
        then have \<open>YieldAbort a \<sigma>''' \<in> lower_yield_result ` x \<pi>' (lens_update l \<sigma>' \<sigma>)\<close>
          by (metis LV Yield assms continuation.inject(4) is_lifted_yield_handler_def is_valid_lensE)
        with Yield e c
        show \<open>\<exists>x\<in>deep_evaluates_nondet_basic x (l\<inverse> e) \<sigma>. c = local.continuation_map x\<close>
          by (force simp: simps lower_yield_result_def split!: yield_handler_nondet_basic_result.splits)
      qed (use Yield in auto)
      ultimately show ?thesis
        by (auto simp: image_iff)
    qed
  qed (use LV in \<open>(auto simp: simps)\<close>)
qed

lemma expression_pull_back_eval_action_abort:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>(apsnd (lens_view l)) ` ((x, l\<inverse> e) \<diamondop>\<^sub>a \<sigma>) = (y, e) \<diamondop>\<^sub>a (lens_view l \<sigma>)\<close>
  using assms by (auto simp add: abort_evaluations_def urust_eval_predicate_defs
     continuation_map_def deep_evaluate_basic_no_yield' split!: continuation.splits
     simp flip: expression_pull_back_deep_evaluates) force+

corollary expression_pull_back_eval_abort:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>a\<langle>y, e\<rangle> (a, \<tau>') \<longleftrightarrow> (\<exists>\<sigma>'. \<sigma> \<leadsto>\<^sub>a\<langle>x, l\<inverse> e\<rangle> (a, \<sigma>') \<and> lens_view l \<sigma>' = \<tau>')\<close>
  using assms by (auto simp flip: expression_pull_back_eval_action_abort
    simp add: apsnd_def map_prod_def urust_eval_predicate_via_action)

lemma expression_pull_back_eval_action_value:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>(apsnd (lens_view l)) ` ((x, l\<inverse> e) \<diamondop>\<^sub>v \<sigma>) = (y, e) \<diamondop>\<^sub>v (lens_view l \<sigma>)\<close>
  using assms by (auto simp add: value_evaluations_def urust_eval_predicate_defs
     continuation_map_def deep_evaluate_basic_no_yield' split!: continuation.splits
     simp flip: expression_pull_back_deep_evaluates) force+

corollary expression_pull_back_eval_value:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>v\<langle>y, e\<rangle> (v, \<tau>') \<longleftrightarrow> (\<exists>\<sigma>'. \<sigma> \<leadsto>\<^sub>v\<langle>x, l\<inverse> e\<rangle> (v, \<sigma>') \<and> lens_view l \<sigma>' = \<tau>')\<close>
  using assms by (auto simp flip: expression_pull_back_eval_action_value
    simp add: apsnd_def map_prod_def urust_eval_predicate_via_action)

corollary expression_pull_back_eval_value':
  assumes \<open>is_lifted_yield_handler y x\<close>
     and \<open> \<sigma> \<leadsto>\<^sub>v\<langle>x, l\<inverse> e\<rangle> (v, \<sigma>')\<close>
   shows \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>v\<langle>y, e\<rangle> (v, lens_view l \<sigma>')\<close>
  using assms by (force simp add: expression_pull_back_eval_value)

lemma expression_pull_back_eval_action_return:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>(apsnd (lens_view l)) ` ((x, l\<inverse> e) \<diamondop>\<^sub>r \<sigma>) = (y, e) \<diamondop>\<^sub>r (lens_view l \<sigma>)\<close>
  using assms by (auto simp add: return_evaluations_def urust_eval_predicate_defs
     continuation_map_def deep_evaluate_basic_no_yield' split!: continuation.splits
     simp flip: expression_pull_back_deep_evaluates) force+

corollary expression_pull_back_eval_valueE:
  assumes \<open>\<sigma> \<leadsto>\<^sub>v\<langle>x, l\<inverse> e\<rangle> (v, \<sigma>')\<close>
      and \<open>is_lifted_yield_handler y x\<close>
     and \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>v\<langle>y, e\<rangle> (v, lens_view l \<sigma>') \<Longrightarrow> R\<close>
   shows R
  using assms by (force simp add: expression_pull_back_eval_value)

corollary expression_pull_back_eval_return:
  assumes \<open>is_lifted_yield_handler y x\<close>
  shows \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>r\<langle>y, e\<rangle> (r, \<tau>') \<longleftrightarrow> (\<exists>\<sigma>'. \<sigma> \<leadsto>\<^sub>r\<langle>x, l\<inverse> e\<rangle> (r, \<sigma>') \<and> lens_view l \<sigma>' = \<tau>')\<close>
  using assms by (auto simp flip: expression_pull_back_eval_action_return
    simp add: apsnd_def map_prod_def urust_eval_predicate_via_action)

corollary expression_pull_back_eval_return':
  assumes \<open>is_lifted_yield_handler y x\<close>
     and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>x, l\<inverse> e\<rangle> (r, \<sigma>')\<close>
   shows \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>r\<langle>y, e\<rangle> (r, lens_view l \<sigma>')\<close>
  using assms by (force simp add: expression_pull_back_eval_return)

corollary expression_pull_back_eval_returnE:
  assumes \<open>\<sigma> \<leadsto>\<^sub>r\<langle>x, l\<inverse> e\<rangle> (r, \<sigma>')\<close>
      and \<open>is_lifted_yield_handler y x\<close>
     and \<open>(lens_view l \<sigma>) \<leadsto>\<^sub>r\<langle>y, e\<rangle> (r, lens_view l \<sigma>') \<Longrightarrow> R\<close>
   shows R
  using assms by (force simp add: expression_pull_back_eval_return)

text\<open>For the canonical lifted yield handler, we can make stronger statements
about the possible evaluations of pulled back expressions:\<close>

definition continuation_lift ::
  \<open>'a \<Rightarrow> ('b, 'v, 'r, 'abort, 'i, 'o) continuation \<Rightarrow> ('a, 'v, 'r, 'abort, 'i, 'o) continuation\<close>
  where \<open>continuation_lift \<sigma> c \<equiv>
     (case c of
        Success v \<tau>' \<Rightarrow> Success v (lens_update l \<tau>' \<sigma>)
      | Return r \<tau>' \<Rightarrow> Return r (lens_update l \<tau>' \<sigma>)
      | Abort a \<tau>' \<Rightarrow> Abort a (lens_update l \<tau>' \<sigma>)
      | Yield _ _ _ \<Rightarrow> undefined)\<close>

lemma continuation_lift_update_overwrite_core:
  assumes \<open>\<And>p \<sigma> t. c \<noteq> Yield p \<sigma> t\<close>
  shows \<open>continuation_lift (lens_update l \<tau> \<sigma>) c = continuation_lift \<sigma> c\<close>
  using assms by (clarsimp simp add: continuation_lift_def lens_laws[OF LV]
    split!: continuation.splits)

lemma continuation_lift_update_overwrite:
  assumes \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma>'\<close>
  shows \<open>continuation_lift (lens_update l \<tau> \<sigma>) c = continuation_lift \<sigma> c\<close>
  by (metis assms continuation_lift_update_overwrite_core deep_evaluate_basic_no_yield')

lemma expression_pull_back_deep_evaluates_canonical:
  shows \<open>deep_evaluates_nondet_basic (canonical_pull_back_yield_handler y) (l\<inverse> e) \<sigma>
     = (continuation_lift \<sigma>) ` (deep_evaluates_nondet_basic y e (lens_view l \<sigma>))\<close>
  using expression_wf_base_is_wf
proof (induct e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  note simps = LV continuation_lift_def deep_evaluates_nondet_basic.simps expression_pull_back_evaluate
  show ?case
  proof (cases \<open>evaluate e (lens_view l \<sigma>)\<close>)
    case (Yield \<pi> \<sigma>' e')
    then have \<dagger>: \<open>\<And>\<omega>. (e' \<omega>, e) \<in> expression_wf_base\<close>
      using expression_wf_base_def by fastforce
    have \<open>(case lift_yield_result (lens_update l \<sigma>' \<sigma>) x of 
               YieldContinue (\<omega>, \<tau>) \<Rightarrow> deep_evaluates_nondet_basic (\<lambda>a \<sigma>. lift_yield_result \<sigma> ` y a (lens_view l \<sigma>)) (l\<inverse> (e' \<omega>)) \<tau>
             | YieldAbort a \<sigma>' \<Rightarrow> {Abort a \<sigma>'})
          = continuation_lift \<sigma> ` 
               (case x of YieldContinue (\<omega>, \<tau>) \<Rightarrow> deep_evaluates_nondet_basic y (e' \<omega>) \<tau> | YieldAbort a \<sigma>' \<Rightarrow> {Abort a \<sigma>'})\<close>
      for x
      using LV less [OF \<dagger>]
      apply (simp add: lift_yield_result_def canonical_pull_back_yield_handler_def continuation_lift_update_overwrite is_valid_lens_def 
                  split: yield_handler_nondet_basic_result.splits)
      apply (simp add: continuation_lift_def lens_laws_update)
      done
    with LV Yield show ?thesis
      by (auto simp add: lens_laws_update simps canonical_pull_back_yield_handler_def)
  qed (auto simp: simps)
qed

lemma expression_pull_back_eval_action_abort_canonical:
  shows \<open>(canonical_pull_back_yield_handler y, l\<inverse> e) \<diamondop>\<^sub>a \<sigma> =
           (apsnd (\<lambda>\<tau>'. lens_update l \<tau>' \<sigma>)) `  ((y, e) \<diamondop>\<^sub>a (lens_view l \<sigma>))\<close>
  by (auto simp add: abort_evaluations_def urust_eval_predicate_defs
     continuation_lift_def deep_evaluate_basic_no_yield' split!: continuation.splits
     simp add: expression_pull_back_deep_evaluates_canonical) force+

corollary expression_pull_back_eval_abort_canonical:
  shows \<open>\<sigma> \<leadsto>\<^sub>a\<langle>canonical_pull_back_yield_handler y, l\<inverse> e\<rangle> (a, \<sigma>') \<longleftrightarrow>
           (\<exists>\<tau>'. (lens_view l \<sigma>) \<leadsto>\<^sub>a\<langle>y, e\<rangle> (a, \<tau>') \<and> lens_update l \<tau>' \<sigma> = \<sigma>')\<close>
  by (auto simp add: expression_pull_back_eval_action_abort_canonical
    simp add: apsnd_def map_prod_def urust_eval_predicate_via_action)

lemma expression_pull_back_eval_action_value_canonical:
  shows \<open>(canonical_pull_back_yield_handler y, l\<inverse> e) \<diamondop>\<^sub>v \<sigma>
            = (apsnd (\<lambda>\<tau>'. lens_update l \<tau>' \<sigma>)) ` ((y, e) \<diamondop>\<^sub>v (lens_view l \<sigma>))\<close>
  by (auto simp add: value_evaluations_def urust_eval_predicate_defs
     continuation_lift_def deep_evaluate_basic_no_yield' split!: continuation.splits
     simp add: expression_pull_back_deep_evaluates_canonical) force+

corollary expression_pull_back_eval_value_canonical:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>canonical_pull_back_yield_handler y, l\<inverse> e\<rangle> (v, \<sigma>') \<longleftrightarrow>
     (\<exists>\<tau>'. (lens_view l \<sigma>) \<leadsto>\<^sub>v\<langle>y, e\<rangle> (v, \<tau>') \<and> lens_update l \<tau>' \<sigma> = \<sigma>')\<close>
  by (auto simp add: expression_pull_back_eval_action_value_canonical
    simp add: apsnd_def map_prod_def urust_eval_predicate_via_action)

lemma expression_pull_back_eval_action_return_canonical:
  shows \<open>(canonical_pull_back_yield_handler y, l\<inverse> e) \<diamondop>\<^sub>r \<sigma>
            = (apsnd (\<lambda>\<tau>'. lens_update l \<tau>' \<sigma>)) ` ((y, e) \<diamondop>\<^sub>r (lens_view l \<sigma>))\<close>
  by (auto simp add: return_evaluations_def urust_eval_predicate_defs
     continuation_lift_def deep_evaluate_basic_no_yield' split!: continuation.splits
     simp add: expression_pull_back_deep_evaluates_canonical) force+

corollary expression_pull_back_eval_return_canonical:
  shows \<open>\<sigma> \<leadsto>\<^sub>r\<langle>canonical_pull_back_yield_handler y, l\<inverse> e\<rangle> (v, \<sigma>') \<longleftrightarrow>
     (\<exists>\<tau>'. (lens_view l \<sigma>) \<leadsto>\<^sub>r\<langle>y, e\<rangle> (v, \<tau>') \<and> lens_update l \<tau>' \<sigma> = \<sigma>')\<close>
  by (auto simp add: expression_pull_back_eval_action_return_canonical
    simp add: apsnd_def map_prod_def urust_eval_predicate_via_action)

end

adhoc_overloading pull_back_const \<rightleftharpoons> canonical_pull_back_yield_handler

end
