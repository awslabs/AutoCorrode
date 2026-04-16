(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Core_Expression_Lemmas
  imports
    Core_Expression
    Core_Syntax
    "Micro_Rust_Shallow_Embedding"
begin
(*>*)

section\<open>Basic lemmas about the \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> monad\<close>

named_theorems micro_rust_intros
named_theorems micro_rust_elims
named_theorems micro_rust_ssa

subsection\<open>Equality and semantic equivalence\<close>

text\<open>Note that, as expressions are modelled in HOL as functions, we can produce a dedicated
\<^emph>\<open>introduction rule\<close> for establishing the semantic equivalence of two expressions, and which will
simplify some proofs.  In essence: if two expressions behave exactly the same on all possible
starting machine states then they are semantically equal, and can be considered interchangeable.
This is captured as follows:\<close>

lemma expression_eqI:
    fixes e f :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  assumes \<open>\<And>k \<sigma>. evaluate e \<sigma> = k \<Longrightarrow> evaluate f \<sigma> = k\<close>
      and \<open>\<And>k \<sigma>. evaluate f \<sigma> = k \<Longrightarrow> evaluate e \<sigma> = k\<close>
    shows \<open>e = f\<close>
using assms by (cases \<open>e\<close>; cases \<open>f\<close>; force simp: evaluate_def)

lemma expression_eqI2:
    fixes e f :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  assumes \<open>\<And>\<sigma>. evaluate e \<sigma> = evaluate f \<sigma>\<close>
    shows \<open>e = f\<close>
using assms by (cases \<open>e\<close>; cases \<open>f\<close>; force simp: evaluate_def)

text\<open>The following is a ``congruence rule'' which tells Isabelle how to go about proving the
equivalence of a pair of \<^term>\<open>Core_Expression.bind\<close> expressions.\<close>
lemma bind_cong [cong]:
  fixes e\<^sub>1 e\<^sub>2 :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  assumes \<open>e\<^sub>1 = e\<^sub>2\<close>
      and \<open>\<And>x. f\<^sub>1 x = f\<^sub>2 x\<close>
    shows \<open>(bind e\<^sub>1 f\<^sub>1) = (bind e\<^sub>2 f\<^sub>2)\<close>
using assms by presburger \<comment> \<open>A presburger suddenly appears\<close>

subsection\<open>Connecting various versions of deep evaluation\<close>

text\<open>After deep evaluation, no yields remain:\<close>

lemma deep_evaluate_basic_no_yield:
  shows \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma> \<Longrightarrow>
     (\<exists>v \<sigma>'. c = Success v \<sigma>') \<or> (\<exists>r \<sigma>'. c = Return r \<sigma>') \<or> (\<exists>a \<sigma>'. c = Abort a \<sigma>')\<close>
  using expression_wf_base_is_wf
proof (induction e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  note deep_evaluates_nondet_basic.simps [simp]
  have ?case if \<section>: \<open>(\<forall>a \<sigma>'. c \<noteq> Abort a \<sigma>')\<close>
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>' e')
    then obtain  \<omega> \<sigma>'' where \<open>c \<in> deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>''\<close>
      using less.prems \<section>
      apply(simp split!: yield_handler_nondet_basic_result.splits)
      by (metis surj_pair yield_handler_nondet_basic_result.exhaust)
    moreover have *: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close>
      using Yield expression_wf_base_def by fastforce
    ultimately show ?thesis
      using less.IH [OF *]
      by blast
  qed (use less.prems in auto)
  then show ?case
    by blast
qed

lemma deep_evaluate_basic_no_yield':
  shows \<open>Yield \<pi> \<sigma>' e' \<in> deep_evaluates_nondet_basic y e \<sigma> \<longleftrightarrow> False\<close>
using deep_evaluate_basic_no_yield by force

lemma deep_evaluate_basicE:
  assumes \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
      and \<open>evaluate e \<sigma> = c \<Longrightarrow> (\<forall>\<pi> \<sigma>' e'. c \<noteq> Yield \<pi> \<sigma>' e') \<Longrightarrow> R\<close>
      and \<open>\<And>\<pi> e' \<omega> \<sigma>'' \<sigma>'''. evaluate e \<sigma> = Yield \<pi> \<sigma>'' e' \<Longrightarrow> YieldContinue (\<omega>,\<sigma>''') \<in> y \<pi> \<sigma>''
               \<Longrightarrow> c \<in> deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>''' \<Longrightarrow> R\<close>
      and \<open>\<And>\<pi> e' \<sigma>'' a \<sigma>'''. evaluate e \<sigma> = Yield \<pi> \<sigma>'' e' \<Longrightarrow> YieldAbort a \<sigma>''' \<in> y \<pi> \<sigma>''
               \<Longrightarrow> c = Abort a \<sigma>''' \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms
  apply (cases c; subst (asm) deep_evaluates_nondet_basic.simps; clarsimp simp: assms evaluate_def
    split!: continuation.splits expression.splits yield_handler_nondet_basic_result.splits)
  apply (metis assms(3) evaluate_def expression.case fst_eqD prod.expand snd_conv
    yield_handler_nondet_basic_result.exhaust)
  apply (metis assms(3) evaluate_def expression.case fst_eqD prod.expand snd_conv
    yield_handler_nondet_basic_result.exhaust)
  apply (metis assms(3) assms(4) evaluate_def expression.case surjective_pairing
    yield_handler_nondet_basic_result.exhaust)
  apply (meson deep_evaluate_basic_no_yield')
  done

lemma deep_evaluate_basicI:
  assumes \<open>(\<exists>v \<sigma>'. c = Success v \<sigma>' \<and> evaluate e \<sigma> = c) \<or>
           (\<exists>r \<sigma>'. c = Return r \<sigma>' \<and> evaluate e \<sigma> = c) \<or>
           (\<exists>a \<sigma>'. c = Abort a \<sigma>' \<and> evaluate e \<sigma> = c) \<or>
           (\<exists>\<pi> e' \<omega> \<sigma>'' \<sigma>'''. evaluate e \<sigma> = Yield \<pi> \<sigma>'' e' \<and> YieldContinue (\<omega>,\<sigma>''') \<in> y \<pi> \<sigma>''
               \<and> c \<in> deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>''') \<or>
           (\<exists>\<pi> e' \<omega> \<sigma>'' a \<sigma>'''. evaluate e \<sigma> = Yield \<pi> \<sigma>'' e' \<and> YieldAbort a \<sigma>''' \<in> y \<pi> \<sigma>''
               \<and> c = Abort a \<sigma>''')\<close>
    shows \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  using assms by (elim disjE; subst deep_evaluates_nondet_basic.simps; clarsimp
    split!: continuation.splits expression.splits yield_handler_nondet_basic_result.splits; blast)

lemma deep_evaluate_basic_SuccessI:
  assumes \<open>evaluate e \<sigma> = Success v \<sigma>'\<close>
    shows \<open>Success v \<sigma>' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  by (simp add: assms deep_evaluates_nondet_basic.simps)

lemma deep_evaluate_basic_ReturnI:
  assumes \<open>evaluate e \<sigma> = Return r \<sigma>'\<close>
    shows \<open>Return r \<sigma>' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  by (simp add: assms deep_evaluates_nondet_basic.simps)

lemma deep_evaluate_basic_AbortI:
  assumes \<open>evaluate e \<sigma> = Abort a \<sigma>'\<close>
    shows \<open>Abort a \<sigma>' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  by (simp add: assms deep_evaluates_nondet_basic.simps)

lemma deep_evaluate_basic_YieldContinueI:
  assumes \<open>evaluate e \<sigma> = Yield \<pi> \<sigma>'' e'\<close> \<open>YieldContinue (\<omega>,\<sigma>''') \<in> y \<pi> \<sigma>''\<close> 
          \<open>c \<in> deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>'''\<close>
    shows \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  using assms deep_evaluates_nondet_basic.simps by fastforce

lemma deep_evaluate_basic_YieldAbortI:
  assumes \<open>evaluate e \<sigma> = Yield \<pi> \<sigma>'' e'\<close> \<open>YieldAbort a \<sigma>''' \<in> y \<pi> \<sigma>''\<close>
    shows \<open>Abort a \<sigma>''' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  using assms deep_evaluates_nondet_basic.simps by fastforce

lemma deep_evaluates_nondet_basic_nonempty:
  assumes \<open>is_nonempty_yield_handler y\<close>
  shows \<open>deep_evaluates_nondet_basic y e \<sigma> \<noteq> {}\<close>
  using expression_wf_base_is_wf
proof (induction e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case 
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>' e')
    with less have \<open>\<And>\<omega> \<sigma>''. deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>'' \<noteq> {}\<close>
      using expression_wf_base_def by fastforce
    with Yield yield_handler_nondet_basic_result.exhaust assms show ?thesis
      unfolding is_nonempty_yield_handler_def
      by (metis all_not_in_conv deep_evaluate_basic_YieldAbortI deep_evaluate_basic_YieldContinueI surj_pair)
  qed (auto simp: deep_evaluates_nondet_basic.simps)
qed

lemma deep_evaluates_nondet_basic:
  shows \<open>deep_evaluates_nondet (yield_handler_nondet_basic_to_nondet y) e \<sigma> =
         deep_evaluates_nondet_basic y e \<sigma>\<close>
  using expression_wf_base_is_wf
proof (induction e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case 
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>' e')
    with less have \<open>deep_evaluates_nondet (yield_handler_nondet_basic_to_nondet y) (e' \<omega>) =
                    deep_evaluates_nondet_basic y (e' \<omega>)\<close> for \<omega>
      using expression_wf_base_def by fastforce
    with Yield  show ?thesis
      apply (clarsimp split: continuation.splits simp: deep_evaluates_nondet_basic.simps)
      apply (auto simp: yield_handler_nondet_basic_to_nondet_def)
      done
  qed (auto simp: deep_evaluates_nondet_basic.simps)
qed

lemma no_abort_deep_evaluates:
  assumes \<open>evaluate e \<sigma> = Yield \<pi> \<sigma>' e'\<close> and \<open>yield_handler_no_abort_at x \<pi> \<sigma>'\<close> 
  shows \<open>deep_evaluates_nondet_basic x e \<sigma> =
        (\<Union> ((\<lambda>(\<omega>, \<sigma>''). deep_evaluates_nondet_basic x (e' \<omega>) \<sigma>'') ` { (\<omega>, \<sigma>'') . YieldContinue (\<omega>, \<sigma>'') \<in> x \<pi> \<sigma>' }))\<close>
proof -
  have "\<exists>\<omega> \<sigma>''. YieldContinue (\<omega>, \<sigma>'') \<in> x \<pi> \<sigma>' \<and> c \<in> deep_evaluates_nondet_basic x (e' \<omega>) \<sigma>''"
    if "c \<in> deep_evaluates_nondet_basic x e \<sigma>" for c 
    using that assms by (bestsimp simp: yield_handler_no_abort_at_def elim: deep_evaluate_basicE)
  with assms show ?thesis
    by (auto simp: deep_evaluate_basic_YieldContinueI)
qed

lemma deep_evaluate_basic_nondet_refine:
  assumes \<open>yield_handler_nondet_basic_refines y x\<close>
   shows \<open>(\<And>a \<sigma>'. Abort a \<sigma>' \<notin> deep_evaluates_nondet_basic x e \<sigma>) \<Longrightarrow>
             deep_evaluates_nondet_basic y e \<sigma> = deep_evaluates_nondet_basic x e \<sigma>\<close>
  using expression_wf_base_is_wf
proof (induction e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e) 
  show ?case 
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>' e')
    have \<open>YieldAbort a \<sigma>'' \<notin> x \<pi> \<sigma>'\<close> for a \<sigma>''
      by (meson Yield deep_evaluate_basic_YieldAbortI less.prems)
    then have x_no_abort: \<open>yield_handler_no_abort_at x \<pi> \<sigma>'\<close>
      unfolding yield_handler_no_abort_at_def by auto
    then have \<open>y \<pi> \<sigma>' = x \<pi> \<sigma>'\<close>
      using assms unfolding yield_handler_nondet_basic_refines_def by auto
    with x_no_abort have y_no_abort: \<open>yield_handler_no_abort_at y \<pi> \<sigma>'\<close>
      unfolding yield_handler_no_abort_at_def by auto
    have \<open>deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>'' = deep_evaluates_nondet_basic x (e' \<omega>) \<sigma>''\<close>
      if \<open>YieldContinue (\<omega>, \<sigma>'') \<in> x \<pi> \<sigma>'\<close> for \<omega> \<sigma>''
      using Yield less that
      by (simp add: expression_wf_base_def) (metis deep_evaluate_basic_YieldContinueI)
    with x_no_abort y_no_abort \<open>y \<pi> \<sigma>' = x \<pi> \<sigma>'\<close> Yield show ?thesis by (auto simp: no_abort_deep_evaluates)
  qed (auto simp: deep_evaluates_nondet_basic.simps)
qed


lemma deep_evaluate_det:
  shows \<open>deep_evaluates_nondet (yield_handler_det_to_nondet y) e \<sigma> = { deep_evaluate_det y e \<sigma> }\<close>
  using expression_wf_base_is_wf
proof (induction e arbitrary: \<sigma> rule: wf_induct_rule)
  case (less e)
  show ?case 
  proof (cases \<open>evaluate e \<sigma>\<close>)
    case (Yield \<pi> \<sigma>' e')
    with less have \<open>deep_evaluates_nondet (yield_handler_det_to_nondet y) (e' \<omega>) \<sigma>'' = 
           { deep_evaluate_det y (e' \<omega>) \<sigma>'' }\<close> for \<omega> \<sigma>''
      using expression_wf_base_def by fastforce
    with Yield show ?thesis
      apply (clarsimp simp: evaluate_def deep_evaluate_det.simps
          split: expression.splits continuation.splits)
      apply (clarsimp simp: yield_handler_det_to_nondet_def;
          auto simp: deep_evaluate_det.simps evaluate_def)
      apply (metis deep_evaluate_det.simps evaluate_def expression.case expression_eqI2)
      done
  qed (auto simp: deep_evaluate_det.simps)
qed

subsection\<open>General facts about monadic composition\<close>

lemma evaluate_bindI [micro_rust_intros]:
  notes Core_Expression.bind.simps[simp]
  assumes \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>'\<close>
      and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>'\<close>
      and \<open>\<And>v \<sigma>'. evaluate e \<sigma> = Success v \<sigma>' \<Longrightarrow> evaluate (f v) \<sigma>' = k\<close>
      and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. bind (e' \<omega>) f)\<close>
  shows \<open>evaluate (bind e f) \<sigma> = k\<close>
  using assms by (auto simp: evaluate_def split: continuation.splits)

lemma evaluate_bindE [micro_rust_elims]:
  notes Core_Expression.bind.simps[simp]
  assumes \<open>evaluate (bind e g) \<sigma> = k\<close>
    and \<open>\<And>v \<sigma>'. evaluate e \<sigma> = Success v \<sigma>' \<Longrightarrow> evaluate (g v) \<sigma>' = k\<Longrightarrow> R\<close>
    and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. bind (e' \<omega>) g) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms
  by (cases \<open>evaluate e \<sigma>\<close>; cases \<open>k\<close>; simp add: evaluate_def)

text\<open>Moreover, the monad \<^term>\<open>Core_Expression.bind\<close> operation is also \<^emph>\<open>associative\<close>
in the following sense, allowing us to reorder sequences of expressions:\<close>

lemma bind_assoc[micro_rust_simps]:
  notes Core_Expression.bind.simps[simp]
  fixes e :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  shows \<open>bind (bind e f) g = bind e (\<lambda>x. bind (f x) g)\<close>
  using expression_wf_base_is_wf
proof (induction e rule: wf_induct_rule)
  case (less e)
  then have \<open>evaluate (bind (bind e f) g) \<sigma> =
                        evaluate (bind e (\<lambda>x. bind (f x) g)) \<sigma>\<close> for \<sigma>
    by (simp add:evaluate_def expression_wf_base_def split:continuation.splits; blast)
  then show ?case
    using expression_eqI2 by blast
qed

lemma evaluate_sequenceI [micro_rust_intros]:
  assumes \<open>(\<exists>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<and> k = Abort a \<sigma>') \<or>
    (\<exists>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<and> k = Return r \<sigma>') \<or>
    (\<exists>v \<sigma>'. evaluate e \<sigma> = Success v \<sigma>' \<and> k = evaluate f \<sigma>') \<or>
    (\<exists>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<and> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. sequence (e' \<omega>) f))\<close>
  shows \<open>evaluate (e; f) \<sigma> = k\<close>
  using assms by (simp only: sequence_def; intro evaluate_bindI; auto)

lemma evaluate_sequenceE [micro_rust_elims]:
  assumes \<open>evaluate (e; f) \<sigma> = k\<close>
    and \<open>\<And>v \<sigma>'. evaluate e \<sigma> = Success v \<sigma>' \<Longrightarrow> evaluate f \<sigma>' = k \<Longrightarrow> R\<close>
    and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. (e' \<omega>); f) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (simp add: sequence_def; elim evaluate_bindE)

text\<open>The fact that \<^term>\<open>Core_Expression.sequence\<close> is a degenerate instance of the monadic bind operation
immediately gives us a few properties.  Sequencing is immediately associative for example, which is
an immediate corollary of the fact that the monadic bind operation is also associative, too:\<close>
lemma sequence_assoc [micro_rust_simps]:
  shows \<open> \<lbrakk> { \<epsilon>\<open>e\<close>; \<epsilon>\<open>f\<close> }; \<epsilon>\<open>g\<close> \<rbrakk> = \<lbrakk> \<epsilon>\<open>e\<close>; \<epsilon>\<open>f\<close>; \<epsilon>\<open>g\<close> \<rbrakk>\<close>
  by (simp add: sequence_def Core_Expression_Lemmas.bind_assoc)

subsection\<open>Literals\<close>

lemma evaluate_literalE [micro_rust_elims]:
  assumes \<open>evaluate (literal v) \<sigma> = k\<close>
    and \<open>k = Success v \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: literal_def evaluate_def)

lemma evaluate_literal [micro_rust_simps]:
  shows \<open>evaluate (\<up>v) \<sigma> = Success v \<sigma>\<close>
  by (auto simp: evaluate_def literal_def)

text\<open>Note that \<^term>\<open>literal\<close> is the \<^emph>\<open>unit\<close> of the expression monad, in the sense that it behaves a
little bit like an identity element with respect to the monadic bind operation.  This is why the
\<^term>\<open>literal\<close> definition was introduced first, at the top of this section, before everything else.
We can make this idea more precise by \<^emph>\<open>proving\<close> the following lemma:\<close>

lemma bind_literal_unit [micro_rust_simps]:
  notes Core_Expression.bind.simps[simp]
  shows \<open>bind (\<up>v) f = f v\<close>
  by (cases \<open>f v\<close>) (clarsimp simp: evaluate_def literal_def)

lemma bind_literal_unit2 [micro_rust_simps]:
  notes Core_Expression.bind.simps[simp]
  fixes e :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  shows \<open>bind e literal = e\<close>
  using expression_wf_base_is_wf
proof (induction e rule: wf_induct_rule)
  case (less e)
  then have \<open>\<And>\<sigma>. (evaluate (bind e literal) \<sigma> = evaluate e \<sigma>)\<close>
    by (force simp: evaluate_def literal_def expression_wf_base_def split:continuation.splits)
  then show ?case
    using expression_eqI2 by blast
qed

subsection\<open>State extraction and modification\<close>

lemma evaluate_getE [micro_rust_elims]:
  assumes \<open>evaluate (get f) \<sigma> = k\<close>
    and \<open>k = Success (f \<sigma>) \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: evaluate_def get_def)

lemma evaluate_get [micro_rust_simps]:
  shows \<open>evaluate (get f) \<sigma> = Success (f \<sigma>) \<sigma>\<close>
  by (auto simp: evaluate_def get_def)

text\<open>Note that if we read twice from the underlying machine state, without writing to any component
in between the reads, then we can reorder these reads (this is akin to a compiler being allowed to
reorder reads):\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma get_reorder:
  shows \<open>\<lbrace> let f = get f; let g = get g; e f g \<rbrace> = \<lbrace> let g = get g; let f = get f; e f g \<rbrace>\<close>
  by (auto simp: evaluate_def Core_Expression.bind.simps get_def split: expression.splits
    continuation.splits)

text\<open>Alternatively, we can merge the two get operations into a single one:\<close>
lemma get_merge[micro_rust_simps]:
  shows \<open> \<lbrakk> let vf = \<epsilon>\<open>get f\<close>;
            let vg = \<epsilon>\<open>get g\<close>;
            \<epsilon>\<open>e vf vg\<close> \<rbrakk> =
          \<lbrakk> let (vf, vg) = \<epsilon>\<open>get (\<lambda>\<sigma>. ((f \<sigma>), (g \<sigma>), nil))\<close>;
            \<epsilon>\<open>e vf vg\<close> \<rbrakk> \<close>
  by (auto simp: Core_Expression.bind.simps evaluate_def get_def split: expression.splits
    continuation.splits)

lemma evaluate_putE [micro_rust_elims]:
  assumes \<open>evaluate (put f) \<sigma> = k\<close>
    and \<open>k = Success () (f \<sigma>) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: evaluate_def put_def)

lemma evaluate_put [micro_rust_simps]:
  shows \<open>evaluate (put f) \<sigma> = Success () (f \<sigma>)\<close>
  by (auto simp: evaluate_def put_def)

text\<open>Like \<^term>\<open>get\<close>, this can also be reordered arbitrarily, as long as we can provably establish
that the ordering of the writes does not matter (for example, the writes modify distinct elements of
the underlying machine state, like distinct registers):\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma put_reorder:
  assumes commut: \<open>f \<circ> g = g \<circ> f\<close>
  shows \<open> \<lbrace> put f; put g \<rbrace> = \<lbrace> put g; put f \<rbrace>\<close>
  using commut by (clarsimp simp: Core_Expression.bind.simps sequence_def evaluate_def put_def)
    (metis comp_apply)

lemma put_merge[micro_rust_simps]:
  shows \<open> \<lbrakk> \<epsilon>\<open>put f\<close>; \<epsilon>\<open>put g\<close> \<rbrakk> = \<lbrakk> \<epsilon>\<open>put (g \<circ> f)\<close> \<rbrakk>\<close>
  by (clarsimp simp: micro_rust_simps put_def Core_Expression.bind.simps evaluate_def
    sequence_def)

subsection\<open>Calls and repeated bindings\<close>

text\<open>Lifting the \<^emph>\<open>identity function\<close> into an expression just gives you back that same expression,
i.e., the result of the expression is unmodified:\<close>

lemma bindlift1_ident [micro_rust_simps]:
  shows \<open>bindlift1 id = id\<close>
  by (auto simp: micro_rust_simps)

text\<open>Moreover, lifting two functions, one after the other, is equivalent to lifting a single
composed function:\<close>
lemma bindlift1_comp [micro_rust_simps]:
  shows \<open>bindlift1 f (bindlift1 g e) = bindlift1 (f \<circ> g) e\<close>
  by (auto simp: micro_rust_simps)

text\<open>The following is an \<^emph>\<open>elimination rule\<close> which allows us to perform a case analysis on the
different reasons why the evaluation of a \<^term>\<open>bindlift1\<close> expression either succeeds or fails:\<close>
lemma evaluate_bindlift1E [micro_rust_elims]:
  notes micro_rust_simps[simp]
  assumes \<open>evaluate (bindlift1 f e) \<sigma> = k\<close>
    and \<open>\<And>r \<sigma>'. k = Success (f r) \<sigma>' \<Longrightarrow> evaluate e \<sigma> = Success r \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>r \<sigma>'. k = Return r \<sigma>' \<Longrightarrow> evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. bindlift1 f (e' \<omega>)) \<Longrightarrow> evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> R\<close>
    and \<open>\<And>a \<sigma>'. k = Abort a \<sigma>' \<Longrightarrow> evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (simp; elim evaluate_bindE evaluate_literalE; auto)

lemma evaluate_bindlift1I [micro_rust_intros]:
  notes micro_rust_simps[simp]
  assumes \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Success r \<sigma>' \<Longrightarrow> k = Success (f r) \<sigma>'\<close>
    and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>'\<close>
    and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>'\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. bindlift1 f (e' \<omega>))\<close>
  shows \<open>evaluate (bindlift1 f e) \<sigma> = k\<close>
  using assms
  apply simp
  apply (intro evaluate_bindI; cases \<open>evaluate e \<sigma>\<close>)
  apply (auto simp: evaluate_def literal_def)
  done

subsection\<open>Return\<close>

lemma evaluate_return_val[micro_rust_simps]:
  shows \<open>evaluate (return_val r) \<sigma> = Return r \<sigma>\<close>
  by (simp add: evaluate_def return_val_def)

lemma evaluate_return_valE [micro_rust_elims]:
  assumes \<open>evaluate (return_val r) \<sigma> = k\<close>
    and \<open>k = Return r \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: return_val_def evaluate_def)

lemma evaluate_return_valE' [micro_rust_elims]:
  assumes \<open>k = evaluate (return_val r) \<sigma>\<close>
    and \<open>k = Return r \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: return_val_def evaluate_def)

lemma evaluate_returnE [micro_rust_elims]:
  assumes \<open>evaluate (return_func r) \<sigma> = k\<close>
    and \<open>\<And>v \<sigma>'. k = Return v \<sigma>' \<Longrightarrow> evaluate r \<sigma> = Success v \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>a \<sigma>'. k = Abort a \<sigma>' \<Longrightarrow> evaluate r \<sigma> = Abort a \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>v \<sigma>'. k = Return v \<sigma>' \<Longrightarrow> evaluate r \<sigma> = Return v \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. return_func (e' \<omega>)) \<Longrightarrow> evaluate r \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms unfolding return_func_def
  by (elim evaluate_bindE evaluate_return_valE; auto)

lemma evaluate_returnI [micro_rust_intros]:
  assumes \<open>\<And>v \<sigma>'. evaluate r \<sigma> = Success v \<sigma>' \<Longrightarrow> k = Return v \<sigma>'\<close>
    and \<open>\<And>a \<sigma>'. evaluate r \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>'\<close>
    and \<open>\<And>v \<sigma>'. evaluate r \<sigma> = Return v \<sigma>' \<Longrightarrow> k = Return v \<sigma>'\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. evaluate r \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. return_func (e' \<omega>))\<close>
  shows \<open>evaluate (return_func r) \<sigma> = k\<close>
  using assms
  unfolding return_func_def
  apply (intro evaluate_bindI; cases \<open>evaluate r \<sigma>\<close>)
  apply (auto simp: evaluate_def return_val_def)
  done

lemma evaluate_return_literal [micro_rust_simps]:
  notes micro_rust_simps[simp]
  shows \<open>evaluate (return (\<up>v)) \<sigma> = Return v \<sigma>\<close>
  by (simp add: evaluate_def return_func_def return_val_def)

lemma evaluate_call_function_bodyE [micro_rust_elims]:
  assumes \<open>evaluate (call_function_body e) \<sigma> = k\<close>
      and \<open>\<And>v \<sigma>'. evaluate e \<sigma> = Success v \<sigma>' \<Longrightarrow> k = Success v \<sigma>' \<Longrightarrow> R\<close>
      and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Success r \<sigma>' \<Longrightarrow> R\<close>
      and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. call_function_body (e' \<omega>))\<Longrightarrow> R\<close>
      and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>' \<Longrightarrow> R\<close>
    shows \<open>R\<close>
  using assms by (cases \<open>evaluate e \<sigma>\<close>; simp add: evaluate_def Core_Expression.call_function_body.simps)

lemma evaluate_call_function_bodyI [micro_rust_intros]:
  assumes \<open>\<And>v \<sigma>'. evaluate e \<sigma> = Success v \<sigma>' \<Longrightarrow> k = Success v \<sigma>'\<close>
      and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Success r \<sigma>'\<close>
      and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. call_function_body (e' \<omega>))\<close>
      and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>'\<close>
    shows \<open>evaluate (call_function_body e) \<sigma> = k\<close>
  using assms by (cases \<open>evaluate e \<sigma>\<close>; simp add: evaluate_def Core_Expression.call_function_body.simps)

lemma call_return [micro_rust_simps]:
  shows \<open>(call (FunctionBody (\<lbrakk> return v; \<rbrakk>))) = (literal v)\<close>
  by (simp add: call_def call_function_body.simps Core_Expression.bind.simps evaluate_def literal_def
      return_func_def return_val_def)

lemma call_literal [micro_rust_simps]:
  shows \<open>(call (FunctionBody (\<lbrakk>v\<rbrakk>))) = (literal v)\<close>
  by (simp add: call_def call_function_body.simps evaluate_def literal_def)

lemma call_literal2 [micro_rust_simps]:
  shows \<open>(call (fun_literal v)) = (literal v)\<close>
  by (simp add: micro_rust_simps fun_literal_def)

text\<open>Note that \<^term>\<open>return_func\<close> is not the \<^emph>\<open>unit\<close> of the expression monad, as one may expect from the
name if you are coming from Haskell!  That is \<^term>\<open>literal\<close>.\<close>

subsection\<open>Inlining function calls\<close>

text\<open>For expressions which do not \<^verbatim>\<open>return\<close>, it does not matter whether they are wrapped
in function calls or not. More precisely:\<close>

function no_return :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> bool\<close> where
  \<open>no_return e = (\<forall>\<sigma>. 
          (case evaluate e \<sigma> of
             Success x \<sigma>' \<Rightarrow> True
           | Return x \<sigma>'  \<Rightarrow> False
           | Yield \<pi> \<sigma>' e' \<Rightarrow> (\<forall>\<omega>. no_return (e' \<omega>))
           | Abort abt \<sigma>'  \<Rightarrow> True
          ))\<close>
by pat_completeness auto
termination
  no_return
proof(relation \<open>expression_wf\<close>, goal_cases)
  case 1
  then show \<open>wf expression_wf\<close>
    by force
next
  case (2 e x x41 x42 x43 xa)
  then show \<open>(x43 xa, e) \<in> expression_wf\<close> 
   by (force simp add: expression_wf_def expression_wf_base_def)
qed
declare no_return.simps[simp del]

lemma expression_no_return:
  assumes \<open>no_return e\<close>
  shows \<open>evaluate e \<sigma> \<noteq> Return x \<sigma>'\<close>
    and \<open>evaluate e \<sigma> = Yield \<pi> \<sigma>'' e' \<Longrightarrow> no_return (e' \<omega>)\<close>
proof -
  show \<open>evaluate e \<sigma> \<noteq> Return x \<sigma>'\<close>
    using assms by (auto simp add: no_return.simps split!: continuation.splits)
  show \<open>evaluate e \<sigma> = Yield \<pi> \<sigma>'' e' \<Longrightarrow> no_return (e' \<omega>)\<close>
    using assms by (metis continuation.simps(20) no_return.elims(2))
qed

\<comment>\<open>Expressions which never return can be turned into function calls without change of semantics.
   (Of course, this is false for expressions which \<^emph>\<open>do\<close> return, as the scope of the \<^verbatim>\<open>return\<close>
   is bounded by the \<^term>\<open>call\<close>.\<close>
lemma no_return_call_inline:
  shows \<open>no_return e \<Longrightarrow> e = call (FunctionBody e)\<close>
  using expression_wf_base_is_wf
proof (induct e rule: wf_induct_rule) 
  case (less e)
  { fix \<sigma>
    have \<open>evaluate e \<sigma> = evaluate (call (FunctionBody e)) \<sigma>\<close>
    proof (cases \<open>evaluate e \<sigma>\<close>)
      case (Success x11 x12)
      then show ?thesis by (simp add: call_def evaluate_call_function_body)
    next
      case (Return x21 x22) 
      from this and less(2) have False 
        by (simp add: expression_no_return) 
      then show ?thesis by simp
    next
      case (Abort x31 x32)
      then show ?thesis by (simp add: call_def evaluate_call_function_body)
    next
      case (Yield \<pi> \<sigma>''' e')
      then have \<omega>: \<open>(e' \<omega>, e) \<in> expression_wf_base\<close> for \<omega>
        using expression_wf_base_def by fastforce 
      moreover have nr: \<open>\<And>\<omega>. no_return (e' \<omega>)\<close>
        by (meson Yield expression_no_return(2) less.prems)
      have \<open>\<And>\<omega>. call_function_body (e' \<omega>) = e' \<omega>\<close> thm less(1)[OF \<omega>]
        using less(1)[OF \<omega> nr] by (simp add: call_def)
      then show ?thesis
        by (simp add: Yield call_def evaluate_call_function_body)
    qed 
  }
  then show ?case
    by - (rule expression_eqI; simp)
qed

lemma no_return_call_inline':
  shows \<open>no_return (function_body e) \<Longrightarrow> call e = function_body e\<close>
  using no_return_call_inline[of \<open>function_body e\<close>] by simp

named_theorems no_return_intros

lemma call_no_return[no_return_intros]:
    shows \<open>no_return (call f)\<close>
proof -
  have aux: "no_return (call_function_body e)" for e
  proof (induct e rule: call_function_body.induct)
    case (1 e)
    show ?case
      by (subst no_return.simps)
         (auto simp: evaluate_call_function_body split: continuation.splits intro: 1)
  qed
  then show ?thesis
    by (cases f) (simp add: call_def)
qed

lemma no_return_basic[no_return_intros]:
  shows \<open>no_return (literal v)\<close>
    and \<open>no_return (abort a)\<close>
    and \<open>no_return (get f)\<close>
    and \<open>no_return (put g)\<close>
    and \<open>no_return (put_assert h a)\<close>
    and \<open>no_return skip\<close>
  by (subst no_return.simps; simp add: evaluate_def literal_def abort_def get_def put_def put_assert_def split: option.splits)+

lemma bind_no_return[no_return_intros]:
  assumes \<open>no_return e\<close>
      and \<open>\<And>v. no_return (f v)\<close>
    shows \<open>no_return (bind e f)\<close>
  using assms(1)
proof (induction e rule: no_return.induct)
  case (1 e)
  show ?case
  proof (subst no_return.simps, simp only: bind_evaluate, intro allI)
    fix \<sigma>
    show \<open>case (case evaluate e \<sigma> of Success v \<sigma>' \<Rightarrow> evaluate (f v) \<sigma>' | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
                | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>' | Yield \<pi> \<sigma>' e' \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<rho>. bind (e' \<rho>) f))
          of Return x \<sigma>' \<Rightarrow> False | Yield \<pi> \<sigma>' e' \<Rightarrow> \<forall>\<omega>. no_return (e' \<omega>) | _ \<Rightarrow> True\<close>
    proof (cases \<open>evaluate e \<sigma>\<close>)
      case (Success x11 x12)
      from assms(2) show ?thesis
        unfolding Success by (subst (asm) no_return.simps) (auto split: continuation.splits)
    next
      case (Return x21 x22)
      then have False using expression_no_return(1)[OF "1.prems"] by auto
      then show ?thesis by simp
    next
      case (Abort x31 x32)
      then show ?thesis by simp
    next
      case (Yield x41 x42 x43)
      from expression_no_return(2)[OF "1.prems" Yield]
      have nr_sub: \<open>no_return (x43 \<omega>)\<close> for \<omega> by simp
      from "1.IH"[OF Yield nr_sub] show ?thesis
        unfolding Yield by simp
    qed
  qed
qed

lemma sequence_no_return[no_return_intros]:
  assumes nr_e: \<open>no_return e\<close>
      and nr_f: \<open>no_return f\<close>
    shows \<open>no_return (sequence e f)\<close>
  unfolding sequence_def using nr_e
proof (induction e rule: no_return.induct)
  case (1 e)
  show ?case
  proof (subst no_return.simps, simp only: bind_evaluate, intro allI)
    fix \<sigma>
    show \<open>case (case evaluate e \<sigma> of Success v \<sigma>' \<Rightarrow> evaluate f \<sigma>' | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
                | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>' | Yield \<pi> \<sigma>' e' \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<rho>. bind (e' \<rho>) (\<lambda>_. f)))
          of Return x \<sigma>' \<Rightarrow> False | Yield \<pi> \<sigma>' e' \<Rightarrow> \<forall>\<omega>. no_return (e' \<omega>) | _ \<Rightarrow> True\<close>
    proof (cases \<open>evaluate e \<sigma>\<close>)
      case (Success x11 x12)
      from nr_f show ?thesis
        unfolding Success by (subst (asm) no_return.simps) (auto split: continuation.splits)
    next
      case (Return x21 x22)
      then have False using expression_no_return(1)[OF "1.prems"] by auto
      then show ?thesis by simp
    next
      case (Abort x31 x32)
      then show ?thesis by simp
    next
      case (Yield x41 x42 x43)
      from expression_no_return(2)[OF "1.prems" Yield]
      have nr_sub: \<open>no_return (x43 \<omega>)\<close> for \<omega> by simp
      from "1.IH"[OF Yield nr_sub] show ?thesis
        unfolding Yield by simp
    qed
  qed
qed

subsection\<open>Aborts\<close>

lemma evaluate_abortE [micro_rust_elims]:
  assumes \<open>evaluate (abort a) \<sigma> = k\<close>
    and \<open>k = Abort a \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: evaluate_def abort_def)

lemma evaluate_abort [micro_rust_simps]:
  shows \<open>evaluate (abort a) \<sigma> = Abort a \<sigma>\<close>
  by (auto simp: abort_def evaluate_def)

lemma evaluate_panicE [micro_rust_elims]:
  assumes \<open>evaluate (panic m) \<sigma> = k\<close>
    and \<open>k = Abort (Panic m) \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: evaluate_def abort_def)

lemma evaluate_panic [micro_rust_simps]:
  shows \<open>evaluate (panic msg) \<sigma> = Abort (Panic msg) \<sigma>\<close>
  by (simp add: evaluate_abort)

text\<open>Moreover \<^term>\<open>skip\<close>, which as we saw above is merely a \<^term>\<open>literal\<close> in disguise, and which is
known to be the unit value of the monad, is the unit value for sequencing:\<close>
lemma skip_sequence_ident [micro_rust_simps]:
  shows \<open>\<lbrace> skip; f \<rbrace> = f\<close>
    and \<open>\<lbrace> e; skip \<rbrace> = e\<close>
  by (auto simp: micro_rust_simps sequence_def)

text\<open>As a result, we can always "rewrite away" instances of \<^term>\<open>skip\<close> whenever and wherever they
appear in a chain of sequenced expressions, as one would expect.  Similarly, the expression
 \<^term>\<open>panic\<close>, and more generally any \<^term>\<open>abort\<close>, acts as a form of "zero" value for the sequencing
operation, in the following sense:\<close>

lemma abort_sequence_zero [micro_rust_simps]:
  shows \<open>\<lbrakk> \<epsilon>\<open>abort a\<close>; \<epsilon>\<open>e\<close> \<rbrakk> = \<lbrakk> \<epsilon>\<open>abort a\<close> \<rbrakk>\<close>
  by (simp add: evaluate_abort evaluate_sequenceI expression_eqI2)

lemma panic_sequence_zero [micro_rust_simps]:
  fixes msg :: \<open>String.literal\<close>
  shows \<open>\<lbrakk> panic!(msg); \<epsilon>\<open>e\<close> \<rbrakk> = \<lbrakk> panic!(msg) \<rbrakk>\<close>
  by (simp only: abort_sequence_zero)

  text\<open>This, too, also allows us to rewrite a chain of sequenced expressions should they contain an
instance of \<^term>\<open>panic\<close>.\<close>

text\<open>The SSA transformation often produces nested let bindings which can be flattened out.\<close>

lemma let_nested [micro_rust_simps]:
  shows \<open>\<lbrakk> let v0 = {
              let v1 = \<epsilon>\<open>v1_expr\<close>;
              \<epsilon>\<open>cont1 v1\<close>
           };
           \<epsilon>\<open>cont0 v0\<close>
         \<rbrakk> = \<lbrakk>
           let v1 = \<epsilon>\<open>v1_expr\<close>;
           let v0 = \<epsilon>\<open>cont1 v1\<close>;
           \<epsilon>\<open>cont0 v0\<close>
         \<rbrakk>\<close>
  by (simp add: micro_rust_simps)

(*<*)
end
(*>*)