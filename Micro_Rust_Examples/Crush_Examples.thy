(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Crush_Examples
  imports Micro_Rust_Std_Lib.StdLib_All
begin

section\<open>\<^verbatim>\<open>crush\<close> guide\<close>

text\<open>This file is a brief guide to usage and configuration of the \<^verbatim>\<open>crush\<close> family of tactics.\<close>

subsection\<open>Overview\<close>

text\<open>\<^verbatim>\<open>crush\<close> is a high-level tactic for dealing with goals in classical and
separation logic. \<^verbatim>\<open>crush\<close> is never trying to be 'clever'. Its goal, instead,
is to do the (seemingly) obvious thing reliably, and to discharge hundreds or thousands
of elementary reasoning steps without human intervention. The proof author is then left with
the tasks of calling \<^verbatim>\<open>crush\<close> suitably -- which is what the bulk of this guide is about -- and
filling in the steps that \<^verbatim>\<open>crush\<close> cannot solve (such as providing loop invariants, for example).

The birds'-eye view of \<^verbatim>\<open>crush\<close> is that of a long disjunction of different branches.
That is, try branch A; if it fails, try branch B; if it fails, try branch C, and so on.
Care has to be taken in choosing the order of branches correctly, both for correctness and
for performance: Regarding correctness, for example, introducing schematic variables must
be handled with a lower priority than operations introducing free variables -- otherwise, the
schematic variables may not instantiate correctly. Regarding performance, powerful tactics
such as a plain \<^verbatim>\<open>simp\<close> or \<^verbatim>\<open>clarsimp\<close> have to be called with low priority, or otherwise \<^verbatim>\<open>crush\<close>
will be too slow for the highly complex goals that we use it for. Even more powerful tactics
such as \<^verbatim>\<open>force\<close>, \<^verbatim>\<open>blast\<close> or \<^verbatim>\<open>auto\<close> are not considered at all. Instead, branches aim to implement
their solution strategy through a mixture of standard tactics \<^verbatim>\<open>simp only\<close>, \<^verbatim>\<open>elim\<close>, and \<^verbatim>\<open>intro\<close>,
or custom ML.

\<^verbatim>\<open>crush\<close> is highly configurable and shares part of its configuration mechanism with the classical
reasonders such as \<^verbatim>\<open>clarsimp\<close>, \<^verbatim>\<open>force\<close> or \<^verbatim>\<open>auto\<close>: That is, simplification rules can be added/removed
via \<^verbatim>\<open>simp add/del: ...\<close>, introduction, split and elimination rules can be added via \<^verbatim>\<open>intro: ...\<close>,
\<^verbatim>\<open>elim: ...\<close> or \<^verbatim>\<open>split: ...\<close>. However, there are various other configuration options that the user
needs to be aware of, some specific to separation logic, some refining the classical reasoning.
Those configuration options will be described and exemplified below. It is essential that the users
familiarizes themselves with the configurations, as a bare \<^verbatim>\<open>apply crush\<close> is rarely getting far.

\<^verbatim>\<open>crush\<close> comes in three variants:

- \<^verbatim>\<open>crush_base_step\<close>: A single iteration of the \<^verbatim>\<open>crush\<close> loop
- \<^verbatim>\<open>fastcrush_base\<close>: Run the `crush` loop on the current goal and all emerging goals, until no
   progress can be made anymore.
- \<^verbatim>\<open>crush_base\<close>: Run the \<^verbatim>\<open>crush\<close> loop on all goals and all emerging goals, until no progress
   can be made anymore.

Since, like \<^verbatim>\<open>auto\<close> for example, \<^verbatim>\<open>crush_base\<close> can affect the entire goal set, using it in the middle
of proofs can make them harder to maintain. Relying on \<^verbatim>\<open>fastcrush_base\<close> usually leads to more robust
proofs. Finally, \<^verbatim>\<open>crush_base_step\<close> is mostly useful for debugging purposes; complex proofs require
hundreds of iterations of the \<^verbatim>\<open>crush\<close> loop, so manual invocation of \<^verbatim>\<open>crush_base_step\<close> is typically
not useful.
\<close>

subsection\<open>\<^verbatim>\<open>crush\<close> arguments and configurations\<close>

text\<open>In this section, we go through various arguments and configuration options of \<^verbatim>\<open>crush\<close>
and explain and exemplify their use.

All options apply to all of \<^verbatim>\<open>crush\<close>, \<^verbatim>\<open>fastcrush\<close> and \<^verbatim>\<open>crush_step\<close>, but we illustrate them for
\<^verbatim>\<open>crush\<close> only.\<close>

subsubsection\<open>Classical reasoning options\<close>

text\<open>\<^verbatim>\<open>crush\<close> supports all arguments that classical reasoning tactics like \<^verbatim>\<open>clarsimp\<close>,
\<^verbatim>\<open>auto\<close>, \<^verbatim>\<open>fastforce\<close> or \<^verbatim>\<open>force\<close> do. Some examples:\<close>

paragraph\<open>Simplification rules\<close>

notepad
begin
  fix a b :: bool
  assume h: \<open>a \<equiv> b\<close>
     and b: \<open>b\<close>
  have \<open>a\<close>
  apply (clarsimp simp add: h)
  apply (rule b)
  done
next
  fix a b :: bool
  assume h: \<open>a \<equiv> b\<close>
     and b: \<open>b\<close>
  have \<open>a\<close>
  \<comment>\<open>Same behavior for \<^verbatim>\<open>crush\<close>\<close>
  apply (crush_base simp add: h)
  apply (rule b)
  done
end

paragraph\<open>Elimination rules\<close>

notepad
begin
  fix a b c :: bool
  assume h: \<open>\<And>R. a \<Longrightarrow> (b \<Longrightarrow> R) \<Longrightarrow> R\<close>
     and j: \<open>b \<Longrightarrow> c\<close>
  have \<open>a \<Longrightarrow> c\<close>
  apply (clarsimp elim!: h) \<comment>\<open>Eliminates \<^verbatim>\<open>a\<close> using \<^verbatim>\<open>h\<close>\<close>
  apply (rule j, force)
  done
next
  fix a b c :: bool
  assume h: \<open>\<And>R. a \<Longrightarrow> (b \<Longrightarrow> R) \<Longrightarrow> R\<close>
     and j: \<open>b \<Longrightarrow> c\<close>
  have \<open>a \<Longrightarrow> c\<close>
  \<comment>\<open>Same behavior for \<^verbatim>\<open>crush\<close>\<close>
  apply (crush_base elim!: h) \<comment>\<open>Eliminates \<^verbatim>\<open>a\<close> using \<^verbatim>\<open>h\<close>\<close>
  apply (rule j, force)
  done
end

paragraph\<open>Split rules\<close>

notepad
begin
     fix a b c :: bool
  assume 1: \<open>a \<Longrightarrow> b\<close>
     and 2: \<open>\<not> a \<Longrightarrow> c\<close>
  have \<open>if a then b else c\<close>
  apply (clarsimp split!: if_splits) \<comment>\<open>Case split along \<^verbatim>\<open>a\<close>\<close>
  using 1 2 apply auto
  done
next
     fix a b c :: bool
  assume 1: \<open>a \<Longrightarrow> b\<close>
     and 2: \<open>\<not> a \<Longrightarrow> c\<close>
  have \<open>if a then b else c\<close>
  \<comment>\<open>Same behavior for \<^verbatim>\<open>crush\<close>\<close>
  apply (crush_base split!: if_splits)
  using 1 2 apply auto
  done
end

text\<open>Note, however, that \<^verbatim>\<open>clarsimp\<close> is attempted by \<^verbatim>\<open>crush\<close> with very low priority. This can not
only be an issue for performance, but also for correctness, as the following example shows. It is
a bit artifical, but instances of this pattern do emerge in practice:\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
  assumes PQ: \<open>\<And>x. P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    apply (crush_base simp add: Some_Ex_def)
    \<comment>\<open>Leaving us with \<^verbatim>\<open> \<And>x. P x \<longlongrightarrow> Q ?x\<close> which we cannot solve because \<^verbatim>\<open>?x\<close> was introduced
    too early and cannot depend on \<^verbatim>\<open>x\<close>.\<close>
    oops

  text\<open>We can confirm that the simplification happened too late by single-stepping through the proof:\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    apply (crush_base_step simp add: Some_Ex_def) \<comment>\<open>Introducing existential for \<^verbatim>\<open>Q ?x\<close>\<close>
    apply (crush_base_step simp add: Some_Ex_def)
    apply (crush_base_step simp add: Some_Ex_def) \<comment>\<open>Unfolding \<^verbatim>\<open>Some_Ex\<close> -- too late!\<close>
    oops
end

text\<open>The next section shows how to fix the situation through 'eager' simplification.\<close>

subsubsection\<open>Premise/Conclusion simplifications\<close>

text\<open>The previous section explained that simplifications registered via \<^verbatim>\<open>... simp add: ...\<close>
are unfolded with very low priority, which can lead to \<^verbatim>\<open>crush\<close> introducing unsolvable schematics
too early. To remedy, \<^emph>\<open>premises\<close> can be unfolded with higher priority by using the
\<^verbatim>\<open>simp prems add: ...\<close> parameter. It appplies to both pure and spatial premises.\<close>

text\<open>Let's see how the previous example can be fixed using \<^verbatim>\<open>simp prems add: ...\<close>:\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
  assumes PQ: \<open>\<And>x. P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    apply (crush_base simp prems add: Some_Ex_def)
    \<comment>\<open>Now the goal is \<^verbatim>\<open>\<And>x. P x \<longlongrightarrow> Q (?x1 x)\<close>, which can actually be solved by setting
    \<^verbatim>\<open>?x1 x \<equiv> x\<close>\<close>
    apply (rule PQ)
    done

  text\<open>We can confirm that the simplification happened earlier than in the previous example
  by single-stepping through the proof:\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    apply (crush_base_step simp prems add: Some_Ex_def)
    apply (crush_base_step simp prems add: Some_Ex_def)  \<comment>\<open>Premise unfold!\<close>
    apply (crush_base_step simp prems add: Some_Ex_def)  \<comment>\<open>Introducing existential for Q ?x\<close>
    apply (rule PQ)
    done

  text\<open>\<^verbatim>\<open>simp prems/concls\<close> should automatically eta expand definitions:\<close>
  definition not_eta_expanded where \<open>not_eta_expanded \<equiv> \<lambda>x f. f x\<close>  
  lemma \<open>\<And>foo. not_eta_expanded f t \<longlongrightarrow> foo\<close>
    apply (crush_base simp prems add: not_eta_expanded_def) 
    oops

end

text\<open>There is also \<^verbatim>\<open>simp concls add: ...\<close> for unfolding pure or spatial \<^emph>\<open>conclusions\<close>. In contrast
to \<^verbatim>\<open>simp prems add: ...\<close>, this is less about correctness than about performance: Unfolding conclusions
late should not lead to bad schematics, but it can lead to performance issues because \<^verbatim>\<open>simp add: ...\<close>
is costly and (therefore) only attempted late withihn \<^verbatim>\<open>crush\<close>.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
  assumes PQ: \<open>\<And>x. P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex T \<equiv> \<Squnion>x. T x\<close>

  lemma \<open>Some_Ex P \<longlongrightarrow> Some_Ex Q\<close>
    apply (crush_base simp prems add: Some_Ex_def simp concls add: Some_Ex_def)
    \<comment>\<open>Now the goal is \<^verbatim>\<open>\<And>x. P x \<longlongrightarrow> Q (?x1 x)\<close>, which can actually be solved by setting
    \<^verbatim>\<open>?x1 x \<equiv> x\<close>\<close>
    apply (rule PQ)
    done

  text\<open>We can confirm that \<^verbatim>\<open>simp prems add: ...\<close> takes precedence over \<^verbatim>\<open>simp concls add: ...\<close>,
  that is, premises are unfolded with higher priority than conclusions:\<close>

  lemma \<open>Some_Ex P \<longlongrightarrow> Some_Ex Q\<close>
    apply (crush_base_step simp prems add: Some_Ex_def simp concls add: Some_Ex_def)
    apply (crush_base_step simp prems add: Some_Ex_def simp concls add: Some_Ex_def)
    apply (crush_base_step simp prems add: Some_Ex_def simp concls add: Some_Ex_def)
    apply (crush_base_step simp prems add: Some_Ex_def simp concls add: Some_Ex_def)
    apply (rule PQ)
    done
end

text\<open>You can also combine \<^verbatim>\<open>simp prems\<close> and \<^verbatim>\<open>simp concls\<close> by providing a list of
simpsets which should be modified. The 'normal' simpset used for the \<^verbatim>\<open>[clar]simp\<close>
branch in \<^verbatim>\<open>crush\<close> is identified by \<^verbatim>\<open>generic\<close>:\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
  assumes PQ: \<open>\<And>x. P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    apply (crush_base simp [prems, concls, generic] add: Some_Ex_def)
    \<comment>\<open>Now the goal is \<^verbatim>\<open>\<And>x. P x \<longlongrightarrow> Q (?x1 x)\<close>, which can actually be solved by setting
    \<^verbatim>\<open>?x1 x \<equiv> x\<close>\<close>
    apply (rule PQ)
    done

end

text\<open>If you write \<^verbatim>\<open>simp add: ...\<close>, the default set of simpsets is determined by the
configuration of \<^verbatim>\<open>Crush_Config.crush_simp_general_implies_prems\<close> and
\<^verbatim>\<open>Crush_Config.crush_simp_general_implies_concls\<close>. Depending on whether they are set/unset,
\<^verbatim>\<open>simp add: ...\<close> will by default include \<^verbatim>\<open>prems/concls\<close>; it will always include \<^verbatim>\<open>generic\<close>.
Currently, \<^verbatim>\<open>Crush_Config.crush_simp_general_implies_prems\<close> and
\<^verbatim>\<open>Crush_Config.crush_simp_general_implies_concls\<close> are both globally \<^verbatim>\<open>false\<close> by default.\<close>

text\<open>Finally, there is also \<^verbatim>\<open>simp early add/del: ...\<close> which are simplifications which are attempted
at highest priority in the first branch of \<^verbatim>\<open>crush\<close>. The underlying named theorem list is \<^verbatim>\<open>crush_early_simps\<close>.

WARNING: Be careful with adding to \<^verbatim>\<open>crush_early_simps\<close> globally -- it may not only break existing proofs
but also cause a significant slowdown since early simplification is attempted at high priority.\<close>

subsubsection\<open>High-priority introduction rules\<close>

text\<open>In the previous sections, we discussed how \<^verbatim>\<open>crush\<close> includes a low priority branch for  \<^verbatim>\<open>clarsimp\<close>
and its configuration via \<^verbatim>\<open>simp add/del: ...\<close>, but that for performance and correctness dedicated
parameters \<^verbatim>\<open>simp prems/concls/early add/del: ...\<close> should be used.

The situation for introduction rules is similar: They can be registered via \<^verbatim>\<open>intro[!]: ...\<close>, in which
case they will be attempted as part of \<^verbatim>\<open>clarsimp\<close>, but only with very low priority.

To apply safe introduction rules at high priority, you can instead use \<^verbatim>\<open>intro add: ...\<close>, which will
make \<^verbatim>\<open>crush\<close> attempt the respective rules in a high priority branch. The underlying named theorem list
is \<^verbatim>\<open>crush_intros\<close>, which can also be populated locally/globally via \<^verbatim>\<open>declare/notes\<close> as usual.

Beware of the minor syntactic difference between \<^verbatim>\<open>crush intro: foo\<close>, which affects only the low-priority
\<^verbatim>\<open>clarsimp\<close> branch, and \<^verbatim>\<open>crush intro add: foo\<close>, which adds to high-priority introduction rules.

Note that \<^verbatim>\<open>intro add: ...\<close> registers classical introduction rules. Introduction rules for
separation logic are discussed next.\<close>

subsubsection\<open>Separation logic introduction and destruction rules\<close>

text\<open>Separation logic introduction rules can be registered with \<^verbatim>\<open>seplog rule add: ...\<close>. Under the
hood, this applies the \<^verbatim>\<open>aentails_rule\<close> tactic that we already discussed in \<^file>\<open>../Crush/Examples.thy\<close>.\<close>

text\<open>Using \<^verbatim>\<open>seplog drule add: ...\<close>, the previous example can be subsumed into a single \<^verbatim>\<open>crush\<close>
call.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
  assumes PQ: \<open>\<And>x. P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)

text\<open>Similarly, spatial assertions can be destructed using \<^verbatim>\<open>seplog drule add: ...\<close>, which wraps
\<^verbatim>\<open>aentails_drule\<close>.\<close>
  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog drule add: PQ)
end

text\<open>Separation logic introduction and destruction rules can have pure premises as well, in which
case those premises will be introduced as new subgoals:\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>R \<Longrightarrow> Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)

  lemma \<open>R \<Longrightarrow> Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog drule add: PQ)
end

subsubsection\<open>Generic simplifications\<close>

text\<open>We have already seen that \<^verbatim>\<open>crush\<close> applies simplification rules for separation logic
automatically. For example, the previous example requires \<^verbatim>\<open>crush\<close> to use

 \<^verbatim>\<open>
lemma aexists_entailsL':
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> \<phi> x \<longlongrightarrow> \<psi>\<close>
    shows \<open>(\<Squnion>x \<in> S. \<phi> x) \<longlongrightarrow> \<psi>\<close>

lemma aexists_entailsR:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> x\<close>
    shows \<open>\<phi> \<longlongrightarrow> (\<Squnion>x. \<psi> x)\<close>
\<close>

from \<^file>\<open>../Shallow_Separation_Logic/Assertion_Language.thy\<close>, to destruct the existential premise
and to introduce a schematic for the existentially quantified variable in the goal.\<close>

text\<open>There are many more separation logic simplification and introduction steps that are routinely
applied by \<^verbatim>\<open>crush\<close>, such as associativity normalization for \<^verbatim>\<open>\<star>\<close>, distributivity of \<^verbatim>\<open>\<star>\<close> and \<^verbatim>\<open>\<Squnion>\<close>,
cancellation, or hoisting out of pure premises. Here is another example:\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)

  text\<open>This example would already be rather tedious to prove by hand. Indeed, already the number of
  \<^verbatim>\<open>crush\<close> steps has increased notably:\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    done
end

text\<open>Usually, \<^verbatim>\<open>crush\<close>'s simplifications are robust and do not need tweaking, and in the rare case
where simplifications need to be watched closely, one can either call individual \<^verbatim>\<open>crush\<close> steps
or fall back to lower level tactics and rules.

One notable exception is the omission of rules introducting schematics, which may sometimes need to
be withheld to avoid unsolvable schematics (even though \<^verbatim>\<open>simp prems add: ...\<close> and guards -- described below --
already help to avoid those situations).
If you want to prevent \<^verbatim>\<open>crush\<close> from introducing schematics for existentially quantified goals,
use \<^verbatim>\<open>no_schematics\<close>.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>
  \<comment>\<open>Helper command for automatically proving \<^verbatim>\<open>ucincl\<close> assertions and registering them
  with \<^verbatim>\<open>crush\<close>.\<close>
  ucincl_auto Some_Ex

  lemma \<open>Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> \<gamma>\<close>
    \<comment>\<open>This would not have worked without \<^verbatim>\<open>no_schematics\<close> because \<^verbatim>\<open>Some_Ex\<close> needs early unfolding.
    Alternatively to \<^verbatim>\<open>simp prems add: ..\<close>, we can also avoid introducing schematics for now, and this
    way ensure that \<^verbatim>\<open>Some_Ex\<close> gets unfolded before schematics are introduced:\<close>
    apply (crush_base simp add: Some_Ex_def no_schematics)
    apply (crush_base seplog rule add: PQ)
    done
end

subsection\<open>Disabling case splits\<close>

text\<open>By default \<^verbatim>\<open>crush\<close> uses \<^verbatim>\<open>safe\<close> to split disjunctive premises, and to split conjunctive
subgoals. While safe, this can sometimes lead to an explosion in the number of subgoals, which
is problematic from a performance perspective, esp. if the various cases still have reasoning in
common. \<^verbatim>\<open>crush\<close> itself applies \<^verbatim>\<open>safe\<close> with a low priority to do as much common reasoning on the
cases as possible, but if such common reasoning happens outside of \<^verbatim>\<open>crush\<close>, \<^verbatim>\<open>crush\<close> must be forced
not to use \<^verbatim>\<open>safe\<close> at all. This is done by passing the \<^verbatim>\<open>no_safe\<close> argument.\<close>

experiment
  fixes A B C D :: bool
begin
  lemma \<open>A \<or> B \<Longrightarrow> C \<and> D\<close>
    apply crush_base \<comment>\<open>Now we have 4 subgoals\<close>
    oops

  text\<open>Trying again without \<^verbatim>\<open>safe\<close>:\<close>

  lemma \<open>A \<or> B \<Longrightarrow> C \<and> D\<close>
    apply ((crush_base no_safe)?) \<comment>\<open>No progress!\<close>
    oops
end

text\<open>WARNING: As it stands, \<^verbatim>\<open>crush\<close> will unconditionally split \<^verbatim>\<open>spatial\<close> goals, and \<^emph>\<open>never\<close>
split spatial disjunctions:\<close>

experiment
  fixes P Q R S :: \<open>'s::sepalg assert\<close>
    and A B C D :: bool
begin
  lemma \<open>A \<or> B \<Longrightarrow> (P \<squnion> Q \<longlongrightarrow> R \<sqinter> S)\<close>
    \<comment>\<open>TODO: I was expecting \<^verbatim>\<open>P \<squnion> Q\<close> would be split by default, but that's not the case...\<close>
    apply crush_base \<comment>\<open>Now we have 4 subgoals\<close>
    oops

  text\<open>Trying again without \<^verbatim>\<open>safe\<close>:\<close>

  lemma \<open>A \<or> B \<Longrightarrow> (P \<squnion> Q \<longlongrightarrow> R \<sqinter> S)\<close>
    apply (crush_base no_safe) \<comment>\<open>Spatial conjunction still split...\<close>
    oops
end

subsubsection\<open>Adding branches\<close>

text\<open>As mentioned, \<^verbatim>\<open>crush\<close> never tries to be 'clever' and deliberately relies on foundational tactics
only. If you find that within the realm of some proof(s) you repeatedly need to switch between \<^verbatim>\<open>crush\<close>
and another context-specific proof step, you can locally register this step as another branch of \<^verbatim>\<open>crush\<close>
using \<^verbatim>\<open>branch add: ...\<close>, which takes a \<^emph>\<open>method\<close> as an argument.\<close>

experiment
  fixes A B C D :: bool
  assumes AB_CD: \<open>A \<Longrightarrow> C\<close> \<open>A \<Longrightarrow> D\<close> \<open>B \<Longrightarrow> C\<close> \<open>B \<Longrightarrow> D\<close>
begin
  lemma \<open>A \<or> B \<Longrightarrow> C \<and> D\<close>
    by (crush_base branch add: \<open>intro AB_CD; assumption\<close>)
end

subsubsection\<open>Debugging \<^verbatim>\<open>crush\<close>\<close>

text\<open>If \<^verbatim>\<open>crush\<close> behaves surprisingly and you find yourself in need of inspecting what is happening,
there are multiple options.

A useful first step is typically to reproduce the issue with \<^verbatim>\<open>fastcrush\<close> rather than \<^verbatim>\<open>crush\<close>.
The former should be easier to debug since it applies only to the current goal, while \<^verbatim>\<open>crush\<close> applies
to \<^emph>\<open>all\<close> goals. Also, you should try to minimize the number of arguments passed to \<^verbatim>\<open>crush\<close>:
Can you ascribe the unexpected behavior to the addition/deletion of a certain argument?

When that's done, consider one of the following steps:\<close>

paragraph\<open>Single-stepping\<close>

text\<open>You can replace \<^verbatim>\<open>crush/fastcrush\<close> by \<^verbatim>\<open>crush_[base_]step\<close> to trace what \<^verbatim>\<open>crush\<close> is doing.
Note, however, that for complex \<^verbatim>\<open>crush\<close> calls this may require you to copy-paste the respective
\<^verbatim>\<open>crush\<close> call dozens or hundreds of times, which is not terribly user friendly.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)

  text\<open>This example would already be rather tedious to prove by hand. Indeed, already the number of
  \<^verbatim>\<open>crush\<close> steps has increased notably:\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    apply (crush_base_step simp prems add: Some_Ex_def seplog rule add: PQ)
    done
end

paragraph\<open>Use gas\<close>

text\<open>You can limit the maximum number of \<^verbatim>\<open>crush\<close> iterations by providing the numeric \<^verbatim>\<open>gas\<close> argument
in conjunction with \<^verbatim>\<open>bigstep: false\<close>. This allows you to conduct a binary search to look out for
where \<^verbatim>\<open>crush\<close>'s behavior starts to diverge from your expectation.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)

  \<comment>\<open>How many steps did we actually need?\<close>
  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ bigstep: false gas: 10)
    done \<comment>\<open>10 was enough!\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ bigstep: false gas: 5)
    oops \<comment>\<open>5 not enough\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ bigstep: false gas: 9)
    done \<comment>\<open>9 was enough!\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ bigstep: false gas: 8)
    oops \<comment>\<open>8 not enough\<close>

  \<comment>\<open>So we need exactly 8 steps. In this example, we could of course have found out more quickly
  by the 'copy-paste-method', but it does not scale as well.\<close>

end

paragraph\<open>Use single-stepping\<close>

text\<open>You can also run \<^verbatim>\<open>crush\<close> in single-stepping mode by passing \<^verbatim>\<open>stepwise\<close>.
Then, the \<^verbatim>\<open>step\<close> command can be used to run the \<^verbatim>\<open>crush\<close> once a time. Multiple steps can be taken
using \<^verbatim>\<open>step n\<close>, and the entire tactic can be run via \<^verbatim>\<open>step *\<close>. You can also run until one of the
goals matches a certain pattern using \<^verbatim>\<open>step to goal pattern "PATTERN"\<close>, or until one of the premises
of one of the goals satisfies a certain pattern, using \<^verbatim>\<open>step to premise pattern "PATTERN"\<close>. In both
cases, the pattern is expected to be of type \<^verbatim>\<open>bool\<close> (not \<^verbatim>\<open>prop\<close>). To stop at the occurrence of a
specific schematic, use \<^verbatim>\<open>step to schematic "name" index\<close>, where \<^verbatim>\<open>?name'idx\<close> is the target schematic.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    using [[crush_log_toplevel]]
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ stepwise)
    step to goal pattern "_ \<longlongrightarrow> (\<Squnion>_. _)"
    step
    step 2
    step *
    done

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    using [[crush_log_toplevel]]
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ stepwise)
    step to premise pattern "R"
    step *
    done

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    using [[crush_log_toplevel]]
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ stepwise)
    step to schematic "x" 7
    step *
    done
end

paragraph\<open>Use backtracking\<close>

text\<open>You can also use backtracking to retroactively inspect the path \<^verbatim>\<open>crush\<close> has taken. For this,
you set the  \<^verbatim>\<open>history\<close> argument and use Isabelle's normal backtracking command
\<^verbatim>\<open>back\<close> after the tactic invocation.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    \<comment>\<open>TODO: This should be configurable through the \<^verbatim>\<open>crush\<close> command line\<close>
    apply (crush_base simp prems add: Some_Ex_def seplog rule add: PQ history)
    back back back back
    back back back
    \<comment>\<open>Back at the original goal!\<close>
    oops
end

text\<open>Using backtracking is often more effective than \<^verbatim>\<open>gas\<close> as one can easily paste a very large
number of \<^verbatim>\<open>back back back ...\<close> blocks and do a binary search by moving the cursor through them,
which will show the intermediate states of \<^verbatim>\<open>crush\<close> in the output panel.\<close>

text\<open>WARNING: You should \<^emph>\<open>not\<close> use backtracking to manually revert \<^verbatim>\<open>crush\<close> to the last good intermediate
goal and continue manually from there: Instead, it should only be used temporarily to identify what
went wrong where, and fix the proof. Manual backtracking would lead to proofs that are very hard to
maintain in the face of changes to \<^verbatim>\<open>crush\<close>. For the same reason, \<^verbatim>\<open>gas\<close> should only be used as a
debugging mechanism, not as a way to control \<^verbatim>\<open>crush\<close>.\<close>

paragraph\<open>Aborting \<^verbatim>\<open>crush\<close>\<close>

text\<open>Another mechanism by which \<^verbatim>\<open>crush\<close> can be debugged is by stopping it once the goal matches
a given criterion. The motivation, here, is to facilitate identifying the \<^verbatim>\<open>crush\<close> step at which
a certain goal has emerged.

There are two variants: First, you can specify a pattern against which the meta-conclusion of the
intermediate goals should be matched, stopping \<^verbatim>\<open>crush\<close> if so. More generally, via \<^verbatim>\<open>abort at filter: ...\<close>
you can specify an arbitrary abort filter of type \<^verbatim>\<open>Proof.context -> term -> bool\<close> which goal
meta-conclusions will be fed through.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>
  ucincl_auto Some_Ex

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    \<comment>\<open>Stopping once the existential quantification on the right has reached the top-level\<close>
    apply (crush_base bigstep:false abort at pattern: "_ \<longlongrightarrow> (\<Squnion>_. _)")
    oops

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    \<comment>\<open>Stopping on the first non-separation logic goal\<close>
    apply (crush_base bigstep:false simp prems add: Some_Ex_def seplog rule add: PQ abort at filter: \<open>
      fn (ctxt : Proof.context) => fn (goal : term) =>
        (* Double-check that the filter is run on all intermediate goals *)
        let val _ = Pretty.block [Pretty.str "Current goal: ",
                                  goal |> Syntax.pretty_term ctxt] |> Pretty.writeln
        in not (Separation_Logic_Tactics.is_entailment goal) end\<close>)
    oops
end

paragraph\<open>Case splitting\<close>

experiment
begin
lemma \<open>(case y of Some t \<Rightarrow> True | None \<Rightarrow> True) \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> match x { Some(y) \<Rightarrow> f(), None \<Rightarrow> g() } \<rbrakk> \<beta> \<gamma> \<delta>\<close>
  \<comment>\<open>You could use the following, but that would aggressively split \<^verbatim>\<open>option\<close> everywhere.\<close>
  apply (crush_base split!: option.splits)
  \<comment>\<open>\<^verbatim>\<open> 1. \<And>x2 x2a. x = Some x2 \<Longrightarrow> y = Some x2a \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<beta> \<gamma> \<delta>
        2. \<And>x2. x = Some x2 \<Longrightarrow> y = None \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<beta> \<gamma> \<delta>
        3. \<And>x2. x = None \<Longrightarrow> y = Some x2 \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> (call g) \<beta> \<gamma> \<delta>
        4. x = None \<Longrightarrow> y = None \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> (call g) \<beta> \<gamma> \<delta>\<close>\<close>
  oops

lemma \<open>(case y of Some t \<Rightarrow> True | None \<Rightarrow> True) \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> match x { None \<Rightarrow> f(), Some(y) \<Rightarrow> g() } \<rbrakk> \<beta> \<gamma> \<delta>\<close>
  \<comment>\<open>If you instead want to split only micro rust expressions, use \<^verbatim>\<open>wp split: ...\<close>\<close> 
  apply (crush_base wp split: option.splits)
  \<comment>\<open>\<^verbatim>\<open> 1. \<And>x2. case y of None \<Rightarrow> True | _ \<Rightarrow> True \<Longrightarrow> x = Some x2 \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> (call g) \<beta> \<gamma> \<delta>
        2. case y of None \<Rightarrow> True | _ \<Rightarrow> True \<Longrightarrow> x = None \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<beta> \<gamma> \<delta>\<close>\<close>
  oops
end

paragraph\<open>Logging \<^verbatim>\<open>crush\<close>\<close>

text\<open>You can get a trace of the steps that \<^verbatim>\<open>crush\<close> has run by adding \<^verbatim>\<open>crush_log_toplevel\<close>.
If you want to see all intermediate goals, add \<^verbatim>\<open>crush_log_goal\<close>:\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    using [[crush_log_toplevel]]
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)
    (* crush_branch_aentails_cancel_tac success (0.000091s)
       crush_branch_unfold_prems_tac success (0.000019s)
       crush_branch_aentails_core_tac success (0.000321s)
       crush_branch_schematics_tac success (0.000021s)
       crush_branch_aentails_cancel_tac success (0.000063s)
       crush_branch_aentails_rule_tac success (0.000080s)
       crush_branch_base_simps_tac success (0.000015s)
       crush_branch_aentails_cancel_tac success (0.000049s) *)

  \<comment>\<open>The same, but now also showing all intermediate goals:\<close>
  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    using [[crush_log_toplevel, crush_log_goal]]
    by (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)
end

text\<open>There are various other logging options which can be used to trace individual branches.
See \<^file>\<open>../Crush/config.ML\<close> for a complete list.\<close>

paragraph\<open>Comparing two \<^verbatim>\<open>crush\<close> calls\<close>

text\<open>It sometimes happens that one notices one \<^verbatim>\<open>crush\<close> call succeeding and another failing, but it
not being clear where the divergence is emerging. In this case, you can use the \<^verbatim>\<open>divergence\<close>
tactical, which takes two methods as arguments and repeats them in lock-step to find the point
of divergence. It then stops and uses backtracking to allow the user to inspect the diverging states.

Note that the tactics passed to \<^verbatim>\<open>divergence\<close> have to be repeatable, to for use with \<^verbatim>\<open>crush\<close>
one needs to pass \<^verbatim>\<open>crush_base_step\<close>.

Here is a simple example demonstrating the higher priority of \<^verbatim>\<open>simp prems ...\<close> vs. \<^verbatim>\<open>simp\<close>:\<close>


experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
  assumes PQ: \<open>\<And>x. P x \<longlongrightarrow> Q x\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>Some_Ex \<longlongrightarrow> (\<Squnion>x. Q x)\<close>
    apply (divergence
       \<open>crush_base_step simp prems add: Some_Ex_def\<close>
       \<open>crush_base_step simp add: Some_Ex_def\<close>
    )
    \<comment>\<open>Use backtracking to inspect diverging states\<close>
    back \<comment>\<open>State when applying LHS \<^verbatim>\<open>crush_base_step simp prems add: Some_Ex_def\<close>\<close>
    back \<comment>\<open>State when applying RHS \<^verbatim>\<open>crush_base_step simp add: Some_Ex_def\<close>\<close>
    oops
end

subsubsection\<open>Profiling \<^verbatim>\<open>crush\<close>\<close>

text\<open>Despite all efforts to keep \<^verbatim>\<open>crush\<close> fast, some \<^verbatim>\<open>crush\<close> invocations can take a long time.
In this case, the general profiling variant \<^verbatim>\<open>apply\<tau>\<close> can be used in conjunction with some or all
of the configuration options \<^verbatim>\<open>crush_time_...\<close> to get a timing profile for \<^verbatim>\<open>crush\<close>.

NB: Unfortunately, timing profiles are proof local, so you cannot currently aggregate performance
statistics along multiple proofs.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    \<comment>\<open>By default, the timing mechanism ignores runtimes < 2ms, which is too high to observe
    the runtime of the tactics in this trivial example. We reduce the threshold to 5ns.\<close>
    using [[crush_time_toplevel, crush_timing_threshold=5]]
    apply\<tau> (crush_base simp prems add: Some_Ex_def seplog rule add: PQ)
    show_timelogs
(* Top ten time sinks
- crush_branch_aentails_core_tac: 0.000374s (0.000073s failing, 0.000301s succeeding)
- crush_branch_aentails_cancel_tac: 0.000301s (0.000118s failing, 0.000183s succeeding)
- crush_branch_base_simps_tac: 0.000261s (0.000250s failing, 0.000011s succeeding)
- crush_branch_aentails_rule_tac: 0.000079s (0.000000s failing, 0.000079s succeeding)
- crush_branch_unfold_prems_tac: 0.000041s (0.000028s failing, 0.000013s succeeding)
- crush_branch_focus_tac: 0.000026s (0.000026s failing, 0.000000s succeeding)
- crush_branch_schematics_tac: 0.000022s (0.000000s failing, 0.000022s succeeding)
- crush_branch_unfold_concls_tac: 0.000017s (0.000017s failing, 0.000000s succeeding)
Timing statistics for: crush_branch_aentails_core_tac
- Total time: 0.000374s
- SUCCESSES
  * Number of time reports: 1
  * total 0.000301s, average 0.000301s, median 0.000301s
  * Percentiles:  0.000301s 0.000301s 0.000301s 0.000301s 0.000301s 0.000301s ...
- FAILURES
  * Number of time reports: 2
  * total 0.000073s, average 0.000036s, median 0.000039s
  * Percentiles:  0.000034s 0.000034s 0.000034s 0.000034s 0.000034s 0.000039s ...
Timing statistics for: crush_branch_aentails_cancel_tac
- Total time: 0.000301s
- SUCCESSES
  * Number of time reports: 3
  * total 0.000183s, average 0.000061s, median 0.000064s
  * Percentiles:  0.000044s 0.000044s 0.000044s 0.000044s 0.000064s 0.000064s ...
- FAILURES
  * Number of time reports: 4
  * total 0.000118s, average 0.000029s, median 0.000047s
  * Percentiles:  0.000006s 0.000006s 0.000006s 0.000007s 0.000007s 0.000047s ...
Timing statistics for: crush_branch_base_simps_tac
- Total time: 0.000261s
- SUCCESSES
  * Number of time reports: 1
  * total 0.000011s, average 0.000011s, median 0.000011s
  * Percentiles:  0.000011s 0.000011s 0.000011s 0.000011s 0.000011s 0.000011s ...
- FAILURES
  * Number of time reports: 7
  * total 0.000250s, average 0.000035s, median 0.000038s
  * Percentiles:  0.000026s 0.000026s 0.000027s 0.000031s 0.000031s 0.000038s ...
Timing statistics for: crush_branch_aentails_rule_tac
- Total time: 0.000079s
- SUCCESSES
  * Number of time reports: 1
  * total 0.000079s, average 0.000079s, median 0.000079s
  * Percentiles:  0.000079s 0.000079s 0.000079s 0.000079s 0.000079s 0.000079s ...
- FAILURES
  * Number of time reports: 0
  * total 0.000000s, average 0.000000s, median 0.000000s
  * Percentiles:
Timing statistics for: crush_branch_unfold_prems_tac
- Total time: 0.000041s
- SUCCESSES
  * Number of time reports: 1
  * total 0.000013s, average 0.000013s, median 0.000013s
  * Percentiles:  0.000013s 0.000013s 0.000013s 0.000013s 0.000013s 0.000013s ...
- FAILURES
  * Number of time reports: 3
  * total 0.000028s, average 0.000009s, median 0.000010s
  * Percentiles:  0.000006s 0.000006s 0.000006s 0.000006s 0.000010s 0.000010s ...
Timing statistics for: crush_branch_focus_tac
- Total time: 0.000026s
- SUCCESSES
  * Number of time reports: 0
  * total 0.000000s, average 0.000000s, median 0.000000s
  * Percentiles:
- FAILURES
  * Number of time reports: 1
  * total 0.000026s, average 0.000026s, median 0.000026s
  * Percentiles:  0.000026s 0.000026s 0.000026s 0.000026s 0.000026s 0.000026s ...
Timing statistics for: crush_branch_schematics_tac
- Total time: 0.000022s
- SUCCESSES
  * Number of time reports: 1
  * total 0.000022s, average 0.000022s, median 0.000022s
  * Percentiles:  0.000022s 0.000022s 0.000022s 0.000022s 0.000022s 0.000022s ...
- FAILURES
  * Number of time reports: 0
  * total 0.000000s, average 0.000000s, median 0.000000s
  * Percentiles:
Timing statistics for: crush_branch_unfold_concls_tac
- Total time: 0.000017s
- SUCCESSES
  * Number of time reports: 0
  * total 0.000000s, average 0.000000s, median 0.000000s
  * Percentiles:
- FAILURES
  * Number of time reports: 1
  * total 0.000017s, average 0.000017s, median 0.000017s
  * Percentiles:  0.000017s 0.000017s 0.000017s 0.000017s 0.000017s 0.000017s ...
Top ten time sinks *)
  done
end

text\<open>If you suspect that poor performance of \<^verbatim>\<open>crush\<close> is due to a particular branch running slowly,
you can instruct \<^verbatim>\<open>crush\<close> to stop when the duration of single step surpasses a configurable threshold.
For example, \<^verbatim>\<open>[clar]simp\<close> invocations on highly complex goals can sometimes take seconds, and in this
case the abort mechanism is a good way to identify and debug them.\<close>

experiment
  fixes P Q :: \<open>'a \<Rightarrow> 's::sepalg assert\<close>
    and \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s assert\<close>
    and R :: bool
  assumes PQ: \<open>\<And>x. R \<Longrightarrow> P x \<star> \<beta> \<longlongrightarrow> Q x \<star> \<gamma>\<close>
     and P_ucincl[ucincl_intros]: \<open>\<And>x. ucincl (P x)\<close>
begin
  definition \<open>Some_Ex \<equiv> \<Squnion>x. P x\<close>

  lemma \<open>\<delta> \<star> Some_Ex \<star> (\<alpha> \<star> \<beta>) \<star> \<langle>R\<rangle> \<longlongrightarrow> \<alpha> \<star> (\<Squnion>x. Q x) \<star> (\<gamma> \<star> \<delta>)\<close>
    \<comment>\<open>Stop if \<^verbatim>\<open>crush\<close> hits a branch that takes more than 1s\<close>
    using [[crush_time_steps, crush_time_step_bound_ms=1000]]
    apply (crush_base simp prems add: Some_Ex_def bigstep: false branch add: \<open>sleep 2\<close>)
    (* step time bound exceeded: 2.001638s
       inner tactic raised stop exception at step 5 *)
    oops
end

subsubsection\<open>Reasoning in the weakest precondition calculus\<close>

text\<open>In addition to classical and generic separation logic reasoning, \<^verbatim>\<open>crush\<close> supports reasoning
in the weakest precondition (WP) calculus for \<mu>Rust. \<^verbatim>\<open>crush\<close> is aware of WP-rules for various \<mu>Rust
program constructs and discharges them automatically, thereby effectively stepping through programs.\<close>

text\<open>We consider a simple example of a \<mu>Rust expression swapping the values of two references:\<close>

context reference
begin
adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

definition swap_ref :: \<open>('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> ('s, unit, unit, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>swap_ref rA rB \<equiv> \<lbrakk>
     let oldA = *rA;
     let oldB = *rB;
     rA = oldB;
     rB = oldA;
  \<rbrakk>\<close>

text\<open>Let's prove that this indeed swaps the contents of the references \<^verbatim>\<open>rA\<close> and \<^verbatim>\<open>rB\<close>:\<close>

lemma swap_ref_correct:
  fixes \<Gamma> :: \<open>('s, 'abort, 'i, 'o) striple_context\<close>
    and gA gB :: 'b
    and vA vB :: 'v
    and rA rB :: \<open>('a, 'b, 'v) ref\<close>
  shows \<open>\<Gamma> ;   \<comment>\<open>Initial reference contents\<close>
              rA \<mapsto> \<langle>\<top>\<rangle> gA\<down>vA \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB\<down>vB
            \<turnstile> swap_ref rA rB
              \<comment>\<open>Updated reference contents\<close>
            \<stileturn> (\<lambda>_.  (\<Squnion>gA' gB'. rA \<mapsto> \<langle>\<top>\<rangle> gA'\<down>vB \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB'\<down>vA))
                \<bowtie> \<bottom> \<comment>\<open>No \<^verbatim>\<open>return\<close>\<close> \<bowtie> \<bottom> \<comment>\<open>No abort\<close>
  \<close>
  \<comment>\<open>Move to WP calculus -- this is not usually done manually but part of the automation for
  function specifications, which is discussed further below.\<close>
  apply (simp add: wp_sstriple_iff)
  using [[crush_log_toplevel]]
  apply (crush_base simp add: swap_ref_def)
  done

text\<open>NB: It is instructive to see how many low-level proof steps are already necessary for code
as simple as this:\<close>

lemma
  fixes \<Gamma> :: \<open>('s, 'abort, 'i, 'o) striple_context\<close>
    and gA gB :: 'b
    and vA vB :: 'v
    and rA rB :: \<open>('a, 'b, 'v) ref\<close>
  shows \<open>\<Gamma> ;   \<comment>\<open>Initial reference contents\<close>
              rA \<mapsto> \<langle>\<top>\<rangle> gA\<down>vA \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB\<down>vB
            \<turnstile> swap_ref rA rB
              \<comment>\<open>Updated reference contents\<close>
            \<stileturn> (\<lambda>_.  (\<Squnion>gA' gB'. rA \<mapsto> \<langle>\<top>\<rangle> gA'\<down>vB \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB'\<down>vA))
                \<bowtie> \<bottom> \<comment>\<open>No \<^verbatim>\<open>return\<close>\<close> \<bowtie> \<bottom> \<comment>\<open>No abort\<close>
  \<close>
  \<comment>\<open>Move to WP calculus -- this is not usually done manually but part of the automation for
  function specifications, which is discussed further below.\<close>
  apply (simp add: wp_sstriple_iff)
  using [[crush_log_toplevel]]
  apply (crush_base simp add: swap_ref_def stepwise)
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  done

subsubsection\<open>Function contracts and specifications\<close>

text\<open>Normally, we would not reason about individual \<mu>Rust expressions, but functions, and use
specifications and contracts to do so. We illustrate this in the example of the above
reference-swapping code wrapped into a function:\<close>

definition swap_ref_fun :: \<open>('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>swap_ref_fun rA rB \<equiv> FunctionBody \<lbrakk>
     let oldA = *rA;
     let oldB = *rB;
     rA = oldB;
     rB = oldA;
  \<rbrakk>\<close>

text\<open>The contract for a uRust function is usually captured in a separate definition of type
\<^verbatim>\<open>function_contract\<close>. In this case:\<close>

definition swap_ref_fun_contract ::
   \<open>('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close>
  where \<open>swap_ref_fun_contract rA rB gA vA gB vB \<equiv>
     let pre = rA \<mapsto> \<langle>\<top>\<rangle> gA\<down>vA \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB\<down>vB in
     let post = \<lambda>_. (\<Squnion>gA' gB'. rA \<mapsto> \<langle>\<top>\<rangle> gA'\<down>vB \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB'\<down>vA) in
      make_function_contract pre post\<close>

text\<open>Note how we are force to make all contextual parameters of the function specification arguments
to the function contract definition.\<close>

text\<open>As with all assertions, we need to prove that pre and post conditions are upwards closed.
Luckily, there is custom automation to do this:\<close>
ucincl_auto swap_ref_fun_contract

text\<open>If the proof isn't trivial, you can use \<^verbatim>\<open>ucincl_proof\<close> instead to open up a proof context
for the required \<^verbatim>\<open>ucincl\<close> assertions.\<close>

text\<open>Next, we state and prove the function specification:\<close>

lemma swap_ref_fun_spec:
  shows \<open>\<Gamma>; swap_ref_fun rA rB \<Turnstile>\<^sub>F swap_ref_fun_contract rA rB gA vA gB vB\<close>
  \<comment>\<open>There is a separate 'boot' tactic for specification proofs\<close>
  apply (crush_boot f: swap_ref_fun_def contract: swap_ref_fun_contract_def)
  apply crush_base
  done

text\<open>Next, imagine we write a higher-level function which relies on \<^verbatim>\<open>swap_ref_fun\<close>.\<close>

definition rotate_ref3 :: \<open>('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rotate_ref3 rA rB rC \<equiv> FunctionBody \<lbrakk>
     swap_ref_fun (rA, rB);
     swap_ref_fun (rB, rC);
  \<rbrakk>\<close>

text\<open>Next, we write the contract for \<^verbatim>\<open>rotate_ref3\<close>:\<close>

definition rotate_ref3_contract ::
   \<open>('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close>
  where \<open>rotate_ref3_contract rA rB rC gA vA gB vB gC vC \<equiv>
     let pre = rA \<mapsto> \<langle>\<top>\<rangle> gA\<down>vA \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB\<down>vB \<star> rC \<mapsto>\<langle>\<top>\<rangle> gC\<down>vC in
     let post = \<lambda>_. (\<Squnion>gA' gB' gC'. rA \<mapsto> \<langle>\<top>\<rangle> gA'\<down>vB \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB'\<down>vC \<star> rC \<mapsto>\<langle>\<top>\<rangle> gC'\<down>vA) in
      make_function_contract pre post\<close>
ucincl_auto rotate_ref3_contract

text\<open>To prove the specification for \<^verbatim>\<open>rotate_ref3\<close>, we could just unfold/inline the definition of
\<^verbatim>\<open>swap_ref_fun\<close>:\<close>

lemma rotate_ref3_spec:
  shows \<open>\<Gamma>; rotate_ref3 rA rB rC \<Turnstile>\<^sub>F rotate_ref3_contract rA rB rC gA vA gB vB gC vC\<close>
  \<comment>\<open>There is a separate 'boot' tactic for specification proofs\<close>
  apply (crush_boot f: rotate_ref3_def contract: rotate_ref3_contract_def)
  apply (crush_base simp add: swap_ref_fun_def)
  done

text\<open>This \<^emph>\<open>can\<close> work, but may lead to issues with SSA normalization. The more robust way to inline
a function is to explicitly mark it via the \<^verbatim>\<open>inline: ...\<close> configuration option:\<close>

lemma rotate_ref3_spec':
  shows \<open>\<Gamma>; rotate_ref3 rA rB rC \<Turnstile>\<^sub>F rotate_ref3_contract rA rB rC gA vA gB vB gC vC\<close>
  \<comment>\<open>There is a separate 'boot' tactic for specification proofs\<close>
  apply (crush_boot f: rotate_ref3_def contract: rotate_ref3_contract_def)
  apply (crush_base inline: swap_ref_fun_def)
  done

text\<open>This looks like a fine proof -- certainly without much work -- but we effectively need to reprove
the spec for \<^verbatim>\<open>swap_ref_fun\<close> with every invocation, which is neither scalable nor modular.

Instead, the proof should refer to the already-proven specification of \<^verbatim>\<open>swap_ref_fun\<close>. This is done
by registering spec and proof via \<^verbatim>\<open>contracts add: ...\<close> and \<^verbatim>\<open>spec add: ...\<close>, respectively:\<close>

lemma
  \<comment>\<open>TODO: There is some issue with simplification of `f ` N` expressions which causes
  bad schematics unless we remove \<^verbatim>\<open>image_cong\<close> as a congruence rule. To be investigated.\<close>
  notes image_cong[cong del]
  shows \<open>\<Gamma>; rotate_ref3 rA rB rC \<Turnstile>\<^sub>F rotate_ref3_contract rA rB rC gA vA gB vB gC vC\<close>
  \<comment>\<open>There is a separate 'boot' tactic for specification proofs\<close>
  apply (crush_boot f: rotate_ref3_def contract: rotate_ref3_contract_def)
  using [[crush_log_toplevel]]
  apply (crush_base specs add: swap_ref_fun_spec contracts add: swap_ref_fun_contract_def)
  done

text\<open>To avoid explicitly listing all specifications and contracts needed by a proof, one can
alternatively globally or locally populate the underlying named theorem lists \<^verbatim>\<open>crush_specs\<close>
and \<^verbatim>\<open>crush_contracts\<close>. This is the prevalent style used in the code base, where we mark
contracts/specs as \<^verbatim>\<open>crush_contracts/crush_specs\<close> at time of definition/proofs.\<close>

declare swap_ref_fun_spec[crush_specs, crush_specs_eager]
declare swap_ref_fun_contract_def[crush_contracts]

lemma
  shows \<open>\<Gamma>; rotate_ref3 rA rB rC \<Turnstile>\<^sub>F rotate_ref3_contract rA rB rC gA vA gB vB gC vC\<close>
  \<comment>\<open>There is a separate 'boot' tactic for specification proofs\<close>
  apply (crush_boot f: rotate_ref3_def contract: rotate_ref3_contract_def)
  by crush_base

no_adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

end

subsubsection\<open>Reasoning about references and structures\<close>

text\<open>The next examples demonstrate how \<^verbatim>\<open>crush\<close> can reason about structure and array manipulation.
They are also useful as vehicles to understand and improve the underlying focus and lens mechanics.\<close>

text\<open>The examples will operate on the following structures:\<close>

datatype_record test_record =
  foo :: int
  bar :: int
micro_rust_record test_record

datatype_record test_record2 =
  f0 :: int
  f1 :: int
  f2 :: int
  f3 :: int
  f4 :: int
  f5 :: int
  f6 :: int
  f7 :: int
  f8 :: int
  f9 :: int
  f10 :: int
  f11 :: int
  f12 :: int
  f13 :: int
  f14 :: int
  f15 :: int
  f16 :: int
  f17 :: int
  f18 :: int
  f19 :: int
  f20 :: int
micro_rust_record test_record2

datatype_record test_record3 =
  data :: \<open>(int, 20) array\<close>
  rest :: int
micro_rust_record test_record3

context reference
begin
adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

text\<open>Overwrite one structure field, return the other:\<close>

definition write_foo_read_bar :: \<open>('a, 'b, test_record) ref \<Rightarrow> ('s, int, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>write_foo_read_bar ptr \<equiv> FunctionBody \<lbrakk>
     ptr.foo = 42;
     *(ptr.bar)
  \<rbrakk>\<close>

definition write_foo_read_bar_contract ::
   \<open>('a, 'b, test_record) ref \<Rightarrow> 'b \<Rightarrow> test_record \<Rightarrow> ('s, int, 'abort) function_contract\<close>
  where \<open>write_foo_read_bar_contract r g v \<equiv>
     let pre = r \<mapsto> \<langle>\<top>\<rangle> g\<down>v in
     let post = \<lambda>t. \<langle>t = test_record.bar v\<rangle> \<star> (\<Squnion>g'. r \<mapsto> \<langle>\<top>\<rangle> g'\<down>(test_record.update_foo (\<lambda>_. 42) v)) in
      make_function_contract pre post\<close>
ucincl_auto write_foo_read_bar_contract

lemma write_foo_read_bar_spec:
  shows \<open>\<Gamma>; write_foo_read_bar ptr \<Turnstile>\<^sub>F write_foo_read_bar_contract ptr g v\<close>
  apply (crush_boot f: write_foo_read_bar_def contract: write_foo_read_bar_contract_def)
  apply crush_base
  done

text\<open>Let's prove the same in single-stepping mode:\<close>

lemma write_foo_read_bar_spec':
  shows \<open>\<Gamma>; write_foo_read_bar ptr \<Turnstile>\<^sub>F write_foo_read_bar_contract ptr g v\<close>
  apply (crush_boot f: write_foo_read_bar_def contract: write_foo_read_bar_contract_def)
  using [[crush_log_toplevel]]
  apply (crush_base stepwise)
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  step
  done

text\<open>Clear many structure fields, return another:\<close>

definition test_record2_zeroize :: \<open>('a, 'b, test_record2) ref \<Rightarrow> ('s, int, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>test_record2_zeroize ptr \<equiv> FunctionBody \<lbrakk>(
     ptr.f0 = 3;
     ptr.f1 = 3;
     ptr.f2 = 3;
     ptr.f3 = 3;
     ptr.f4 = 3;
     ptr.f5 = 3;
     ptr.f6 = 3;
     ptr.f7 = 3;
     ptr.f8 = 3;
     ptr.f9 = 3;
     ptr.f10 = 3;
     ptr.f11 = 3;
     ptr.f12 = 3;
     ptr.f13 = 3;
     ptr.f14 = 3;
     ptr.f15 = 3;
     ptr.f16 = 3;
     ptr.f17 = 3;
     ptr.f18 = 3;
     ptr.f19 = 3;
     ptr.f0 = 2;
     ptr.f1 = 2;
     ptr.f2 = 2;
     ptr.f3 = 2;
     ptr.f4 = 2;
     ptr.f5 = 2;
     ptr.f6 = 2;
     ptr.f7 = 2;
     ptr.f8 = 2;
     ptr.f9 = 2;
     ptr.f10 = 2;
     ptr.f11 = 2;
     ptr.f12 = 2;
     ptr.f13 = 2;
     ptr.f14 = 2;
     ptr.f15 = 2;
     ptr.f16 = 2;
     ptr.f17 = 2;
     ptr.f18 = 2;
     ptr.f19 = 2;
     ptr.f0 = 1;
     ptr.f1 = 1;
     ptr.f2 = 1;
     ptr.f3 = 1;
     ptr.f4 = 1;
     ptr.f5 = 1;
     ptr.f6 = 1;
     ptr.f7 = 1;
     ptr.f8 = 1;
     ptr.f9 = 1;
     ptr.f10 = 1;
     ptr.f11 = 1;
     ptr.f12 = 1;
     ptr.f13 = 1;
     ptr.f14 = 1;
     ptr.f15 = 1;
     ptr.f16 = 1;
     ptr.f17 = 1;
     ptr.f18 = 1;
     ptr.f19 = 1;
     ptr.f0 = 0;
     ptr.f1 = 0;
     ptr.f2 = 0;
     ptr.f3 = 0;
     ptr.f4 = 0;
     ptr.f5 = 0;
     ptr.f6 = 0;
     ptr.f7 = 0;
     ptr.f8 = 0;
     ptr.f9 = 0;
     ptr.f10 = 0;
     ptr.f11 = 0;
     ptr.f12 = 0;
     ptr.f13 = 0;
     ptr.f14 = 0;
     ptr.f15 = 0;
     ptr.f16 = 0;
     ptr.f17 = 0;
     ptr.f18 = 0;
     ptr.f19 = 0;
     *(ptr.f20)
  )\<rbrakk>\<close>

definition test_record2_zeroize_contract ::
   \<open>('a, 'b, test_record2) ref \<Rightarrow> 'b \<Rightarrow> test_record2 \<Rightarrow> ('s, int, 'abort) function_contract\<close>
  where \<open>test_record2_zeroize_contract r g v \<equiv>
     let pre = r \<mapsto> \<langle>\<top>\<rangle> g\<down>v in
     let post = \<lambda>t. \<langle>t = test_record2.f20 v\<rangle> \<star> (\<Squnion>g'. r \<mapsto> \<langle>\<top>\<rangle> g'\<down>(
          test_record2.update_f0 (\<lambda>_. 0) (
          test_record2.update_f1 (\<lambda>_. 0) (
          test_record2.update_f2 (\<lambda>_. 0) (
          test_record2.update_f3 (\<lambda>_. 0) (
          test_record2.update_f4 (\<lambda>_. 0) (
          test_record2.update_f5 (\<lambda>_. 0) (
          test_record2.update_f6 (\<lambda>_. 0) (
          test_record2.update_f7 (\<lambda>_. 0) (
          test_record2.update_f8 (\<lambda>_. 0) (
          test_record2.update_f9 (\<lambda>_. 0) (
          test_record2.update_f10 (\<lambda>_. 0) (
          test_record2.update_f11 (\<lambda>_. 0) (
          test_record2.update_f12 (\<lambda>_. 0) (
          test_record2.update_f13 (\<lambda>_. 0) (
          test_record2.update_f14 (\<lambda>_. 0) (
          test_record2.update_f15 (\<lambda>_. 0) (
          test_record2.update_f16 (\<lambda>_. 0) (
          test_record2.update_f17 (\<lambda>_. 0) (
          test_record2.update_f18 (\<lambda>_. 0) (
          test_record2.update_f19 (\<lambda>_. 0) (
            v
          )))))))))))))))))))))) in
      make_function_contract pre post\<close>
ucincl_auto test_record2_zeroize_contract

lemma test_record2_zeroize_contract_spec:
  shows \<open>\<Gamma>; test_record2_zeroize ptr \<Turnstile>\<^sub>F test_record2_zeroize_contract ptr g v\<close>
  apply (crush_boot f: test_record2_zeroize_def contract: test_record2_zeroize_contract_def)
  using [[crush_time_steps, crush_time_base_simps]]
  apply\<tau> (crush_base stepwise)
  step *
  show_timelogs
  done

text\<open>Another similar stress test, but this time using array accesses behind a function wrapper.\<close>

definition test_record3_zero_field :: \<open>('a, 'b, test_record3) ref \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>test_record3_zero_field r i \<equiv> FunctionBody \<lbrakk>
     r.data[i] = 0
  \<rbrakk>\<close>

definition test_record3_zero_field_contract ::
   \<open>('a, 'b, test_record3) ref \<Rightarrow> 64 word \<Rightarrow> 'b \<Rightarrow> test_record3 \<Rightarrow> ('s, unit, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>test_record3_zero_field_contract r i g v \<equiv>
     let pre = r \<mapsto> \<langle>\<top>\<rangle> g\<down>v \<star> \<langle>i < 20\<rangle> in
     let zero_ith_pure :: test_record3 \<Rightarrow> test_record3 = (\<lambda>t. t \<lparr> data := array_update (data t) (unat i) 0 \<rparr> ) in
     let post = \<lambda>_. r \<mapsto> \<langle>\<top>\<rangle> zero_ith_pure\<sqdot>(g\<down>v) in
      make_function_contract pre post\<close>
ucincl_auto test_record3_zero_field_contract

text\<open>For many non-trivial examples it is useful to conduct some Isar-style reasoning prior to
starting the \<^verbatim>\<open>apply\<close>-style \<^verbatim>\<open>crush\<close> proof. The following proof demonstrates this pattern:\<close>

lemma test_record3_zero_field_spec[crush_specs]:
  shows \<open>\<Gamma>; test_record3_zero_field ptr i \<Turnstile>\<^sub>F test_record3_zero_field_contract ptr i g v\<close>
proof (crush_boot f: test_record3_zero_field_def contract: test_record3_zero_field_contract_def; goal_cases)
  case 1 note assms = this
  from assms have \<open>unat i < 20\<close>
    by (simp add: unat_less_helper)
  then show ?case
    by crush_base
qed

definition test_record3_zeroize :: \<open>('a, 'b, test_record3) ref \<Rightarrow> ('s, int, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>test_record3_zeroize ptr \<equiv> FunctionBody \<lbrakk>(
     ptr.test_record3_zero_field(0);
     ptr.test_record3_zero_field(1);
     ptr.test_record3_zero_field(2);
     ptr.test_record3_zero_field(3);
     ptr.test_record3_zero_field(4);
     ptr.test_record3_zero_field(5);
     ptr.test_record3_zero_field(6);
     ptr.test_record3_zero_field(7);
     ptr.test_record3_zero_field(8);
     ptr.test_record3_zero_field(9);
     ptr.test_record3_zero_field(10);
     ptr.test_record3_zero_field(11);
     ptr.test_record3_zero_field(12);
     ptr.test_record3_zero_field(13);
     ptr.test_record3_zero_field(14);
     ptr.test_record3_zero_field(15);
     ptr.test_record3_zero_field(16);
     ptr.test_record3_zero_field(17);
     ptr.test_record3_zero_field(18);
     ptr.test_record3_zero_field(19);
     ptr.test_record3_zero_field(0);
     ptr.test_record3_zero_field(1);
     ptr.test_record3_zero_field(2);
     ptr.test_record3_zero_field(3);
     ptr.test_record3_zero_field(4);
     ptr.test_record3_zero_field(5);
     ptr.test_record3_zero_field(6);
     ptr.test_record3_zero_field(7);
     ptr.test_record3_zero_field(8);
     ptr.test_record3_zero_field(9);
     ptr.test_record3_zero_field(10);
     ptr.test_record3_zero_field(11);
     ptr.test_record3_zero_field(12);
     ptr.test_record3_zero_field(13);
     ptr.test_record3_zero_field(14);
     ptr.test_record3_zero_field(15);
     ptr.test_record3_zero_field(16);
     ptr.test_record3_zero_field(17);
     ptr.test_record3_zero_field(18);
     ptr.test_record3_zero_field(19);
     ptr.test_record3_zero_field(0);
     ptr.test_record3_zero_field(1);
     ptr.test_record3_zero_field(2);
     ptr.test_record3_zero_field(3);
     ptr.test_record3_zero_field(4);
     ptr.test_record3_zero_field(5);
     ptr.test_record3_zero_field(6);
     ptr.test_record3_zero_field(7);
     ptr.test_record3_zero_field(8);
     ptr.test_record3_zero_field(9);
     ptr.test_record3_zero_field(10);
     ptr.test_record3_zero_field(11);
     ptr.test_record3_zero_field(12);
     ptr.test_record3_zero_field(13);
     ptr.test_record3_zero_field(14);
     ptr.test_record3_zero_field(15);
     ptr.test_record3_zero_field(16);
     ptr.test_record3_zero_field(17);
     ptr.test_record3_zero_field(18);
     ptr.test_record3_zero_field(19);
     *(ptr.rest)
  )\<rbrakk>\<close>

definition test_record3_zeroize_contract ::
   \<open>('a, 'b, test_record3) ref \<Rightarrow> 'b \<Rightarrow> test_record3 \<Rightarrow> ('s, int, 'abort) function_contract\<close>
  where \<open>test_record3_zeroize_contract r g v \<equiv>
     let pre = r \<mapsto> \<langle>\<top>\<rangle> g\<down>v in
     let zero_data_pure :: test_record3 \<Rightarrow> test_record3 = (\<lambda>t. t \<lparr> data := array_constant 0 \<rparr> ) in
     let post = \<lambda>ret. \<langle>ret = rest v\<rangle> \<star> (\<Squnion>g'. r \<mapsto> \<langle>\<top>\<rangle> g'\<down>(zero_data_pure v)) in
      make_function_contract pre post\<close>
ucincl_auto test_record3_zeroize_contract

lemma test_record3_zeroize_spec:
  \<comment>\<open>TODO: This can go away once specs are eager by default\<close>
  notes test_record3_zero_field_spec[crush_specs_eager]
  shows \<open>\<Gamma>; test_record3_zeroize ptr \<Turnstile>\<^sub>F test_record3_zeroize_contract ptr g v\<close>
\<comment>\<open>Again, we hoist out some pure lemma into an initial Isar-style proof block. We could
inline the argument into the \<^verbatim>\<open>crush\<close> call, but that would slow it down significantly because
of a large number of irrelevant assumptions.\<close>
proof (crush_boot f: test_record3_zeroize_def contract: test_record3_zeroize_contract_def, goal_cases)
  case 1
  { fix x :: \<open>(int, 20) array\<close>
    let ?x = x
    let ?x0 = \<open>array_update ?x  0 0\<close>
    let ?x1 = \<open>array_update ?x0 1 0\<close>
    let ?x2 = \<open>array_update ?x1 2 0\<close>
    let ?x3 = \<open>array_update ?x2 3 0\<close>
    let ?x4 = \<open>array_update ?x3 4 0\<close>
    let ?x5 = \<open>array_update ?x4 5 0\<close>
    let ?x6 = \<open>array_update ?x5 6 0\<close>
    let ?x7 = \<open>array_update ?x6 7 0\<close>
    let ?x8 = \<open>array_update ?x7 8 0\<close>
    let ?x9 = \<open>array_update ?x8 9 0\<close>
    let ?x10 = \<open>array_update ?x9 10 0\<close>
    let ?x11 = \<open>array_update ?x10 11 0\<close>
    let ?x12 = \<open>array_update ?x11 12 0\<close>
    let ?x13 = \<open>array_update ?x12 13 0\<close>
    let ?x14 = \<open>array_update ?x13 14 0\<close>
    let ?x15 = \<open>array_update ?x14 15 0\<close>
    let ?x16 = \<open>array_update ?x15 16 0\<close>
    let ?x17 = \<open>array_update ?x16 17 0\<close>
    let ?x18 = \<open>array_update ?x17 18 0\<close>
    let ?x19 = \<open>array_update ?x18 19 0\<close>
    have \<open>?x19 = array_constant 0\<close>
      by (auto intro!: array_extI simp add: less_Suc_eq numeral_Bit0 numeral_Bit1)
  }
  note eq = this[simplified]
  show ?case
  \<comment>\<open>TODO: This proof gets slower over time. Investigate\<close>
  apply\<tau> (crush_base stepwise)
  step 100
  step 100
  step 100
  step 100
  step 100
  step 100
  step 100
  step 100
  step *
  show_timelogs
  apply (simp add: eq)
  done
qed

end

end