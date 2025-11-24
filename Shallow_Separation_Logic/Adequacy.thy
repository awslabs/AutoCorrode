(*<*)
theory Adequacy
  imports
    Weakest_Precondition
    Function_Contract
begin
(*>*)

section\<open>Adequacy\<close>
text\<open>This session shows that we can derive properties on programs from proofs in our program logic.
In other words: 
\begin{itemize*}
\item
from a Hoare triple/weakest precondition entailment/function contract on a program \<^term>\<open>e\<close>
\item
we can derive that the evaluating \<^term>\<open>e\<close> on appropriate machines does not go wrong.
\end{itemize*}
This is usually called 'adequacy' in the literature. We first build up the required adequacy results
for low-level connectives, before proving them for the top-level connectives:
\begin{itemize*}
\item
Hoare triples \<^term>\<open>sstriple\<close>
\item
Weakest precondition entailments of the form \<^term>\<open>\<xi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<phi> \<rho> \<theta>\<close>
\item
Function contracts \<^term>\<open>satisfies_function_contract\<close>
\end{itemize*}\<close>

subsection\<open>Low-level adequacy results\<close>
text\<open>Note that the final \<^verbatim>\<open>shows\<close> clauses of all these theorems is of shape \<^term>\<open>\<phi> \<star> \<top>\<close>: the
upward closedness requirements (\<^term>\<open>ucincl\<close>) is part of the definition of these triples.\<close>
lemma atriple_rel_eval_value_adequacy:
  assumes \<open>\<xi> \<turnstile> eval_value Y e \<stileturn>\<^sub>R \<phi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>continuation.Success v \<sigma>' \<in> deep_evaluates_nondet_basic Y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<phi> v \<star> \<top>\<close>
  using assms by (auto simp add: atriple_rel_def eval_value_def urust_eval_predicate_defs)

lemma atriple_rel_eval_return_adequacy:
  assumes \<open>\<xi> \<turnstile> eval_return Y e \<stileturn>\<^sub>R \<phi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>continuation.Return v \<sigma>' \<in> deep_evaluates_nondet_basic Y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<phi> v \<star> \<top>\<close>
  using assms by (auto simp add: atriple_rel_def eval_return_def urust_eval_predicate_defs)

lemma atriple_rel_eval_abort_adequacy:
  assumes \<open>\<xi> \<turnstile> eval_abort Y e \<stileturn>\<^sub>R \<phi>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>continuation.Abort a \<sigma>' \<in> deep_evaluates_nondet_basic Y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> \<phi> a \<star> \<top>\<close>
  using assms by (auto simp add: atriple_rel_def eval_abort_def urust_eval_predicate_defs)

subsection\<open>Main adequacy results\<close>
lemma sstriple_adequacy:
  assumes \<open>\<Gamma> ; \<xi> \<turnstile> e \<stileturn> \<phi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>c \<in> deep_evaluates_nondet_basic (yield_handler \<Gamma>) e \<sigma>\<close>
    shows \<open>case c of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<phi> v \<star> \<top>
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<rho> v \<star> \<top>
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<theta> a \<star> \<top>
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
  \<comment> \<open>Evaluating with \<^term>\<open>deep_evaluates_nondet_basic\<close> will never terminate in \<^term>\<open>Yield\<close>\<close>
  using assms
  by (auto simp add: sstriple_def deep_evaluate_basic_no_yield'
      atriple_rel_eval_value_adequacy atriple_rel_eval_return_adequacy
      atriple_rel_eval_abort_adequacy split: continuation.splits)

corollary wp_adequacy:
  assumes \<open>\<xi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<phi> \<rho> \<theta>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>c \<in> deep_evaluates_nondet_basic (yield_handler \<Gamma>) e \<sigma>\<close>
    shows \<open>case c of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<phi> v \<star> \<top>
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<rho> v \<star> \<top>
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<theta> a \<star> \<top>
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
  using assms by (auto simp add: sstriple_adequacy dest!: wp_to_sstriple)

text\<open>Function contracts (\<^term>\<open>satisfies_function_contract\<close>) additionaly require \<^term>\<open>ucincl\<close> on
the pre-, post- and abort conditions. This means we can get rid of program logic connectives
altogether, replacing \<^term>\<open>\<sigma> \<Turnstile> \<phi> \<star> \<top>\<close> with \<^term>\<open>\<sigma> \<in> \<phi>\<close>\<close>
corollary contract_adequacy:
  assumes \<open>\<Gamma>; body \<Turnstile>\<^sub>F contract\<close>
      and \<open>\<sigma> \<in> function_contract_pre contract\<close>
      and \<open>c \<in> deep_evaluates_nondet_basic (yh \<Gamma>) (function_body body) \<sigma>\<close>
    shows \<open>case c of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<in> function_contract_post contract v
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<in> function_contract_post contract v
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<in> function_contract_abort contract a
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
  using assms
  by (auto simp add: asat_def asepconj_ident2 satisfies_function_contract_def
              split: continuation.splits dest!: sstriple_adequacy)

definition is_yield :: \<open>('a, 'b, 'c, 'd, 'e, 'f) continuation \<Rightarrow> bool\<close> where
  \<open>is_yield c \<equiv> \<exists> i m h. c = Yield i m h\<close>

text\<open>In case your expression does not interact with the yield handler, one gets the following
simpler adequacy, using \<^term>\<open>evaluate\<close> instead of \<^term>\<open>deep_evaluates_nondet_basic\<close>.\<close>
corollary wp_adequacy_deterministic:
  assumes \<open>\<xi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<phi> \<rho> \<theta>\<close>
      and \<open>\<sigma> \<Turnstile> \<xi>\<close>
      and \<open>\<not> is_yield (evaluate e \<sigma>)\<close>
    shows \<open>case evaluate e \<sigma> of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<phi> v \<star> \<top>
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<rho> v \<star> \<top>
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<theta> a \<star> \<top>
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
  using assms(3) wp_adequacy[OF assms(1) assms(2), where c=\<open>evaluate e \<sigma>\<close>]
  by (auto simp add: deep_evaluate_basic_SuccessI deep_evaluate_basic_ReturnI
                     deep_evaluate_basic_AbortI is_yield_def
              split: continuation.splits)


section\<open>From raw evaluation back to the program logic\<close>
text\<open>Interestingly, one can also go the other way: one can derive statements in the program logic
from proofs about the evaluation of a program.
These results are mostly of theoretical interest -
especially state manipulating programs are much easier to prove correct via the program logic. This
might one day be useful for purely functional \<mu>Rust programs, where this approach allows you to
derive the contract from the program.
Finally, these results show that results in our program logic are not vacuously true.\<close>

subsection\<open>Program logic connectives from evaluation\<close>
text\<open>Note that all these results require \<^term>\<open>urust_is_local\<close>, which essentially states that
program evaluation on (part of) a machine cannot change that machine outside of its footprint,
nor can elements outside of the footprint influence the behavior of the program. We include ways
to derive this property for simple programs later.\<close>
text\<open>These results could in principle be extended to use \<^term>\<open>deep_evaluates_nondet_basic\<close> instead
of \<^term>\<open>evaluate\<close>.\<close>
lemma sstriple_from_evaluation:
  assumes \<open>\<And> \<sigma>. \<sigma> \<Turnstile> \<xi> \<Longrightarrow> case evaluate e \<sigma> of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<phi> v \<star> \<top>
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<rho> v \<star> \<top>
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<theta> a \<star> \<top>
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
      and \<open>urust_is_local (yh \<Gamma>) e \<xi>\<close>
    shows \<open>\<Gamma> ; \<xi> \<turnstile> e \<stileturn> \<phi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (force simp add: deep_evaluates_nondet_basic.simps urust_eval_predicate_defs
                      eval_value_def eval_return_def eval_abort_def sstriple_def atriple_rel_def
               split: continuation.splits)

lemma wp_from_evaluation:
  assumes \<open>\<And> \<sigma>. \<sigma> \<Turnstile> \<xi> \<Longrightarrow> case evaluate e \<sigma> of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<phi> v \<star> \<top>
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<rho> v \<star> \<top>
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> \<theta> a \<star> \<top>
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
      and \<open>urust_is_local (yh \<Gamma>) e \<xi>\<close>
    shows \<open>\<xi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<phi> \<rho> \<theta>\<close>
  using assms by (auto intro: wp_is_weakest_precondition sstriple_from_evaluation)

lemma contract_from_evaluation:
  assumes \<open>\<And> \<sigma>. \<sigma> \<Turnstile> function_contract_pre contract \<Longrightarrow> case evaluate (function_body func) \<sigma> of
            continuation.Success v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> function_contract_post contract v
          | continuation.Return v \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> function_contract_post contract v
          | continuation.Abort a \<sigma>' \<Rightarrow> \<sigma>' \<Turnstile> function_contract_abort contract a
          | continuation.Yield _ _ _ \<Rightarrow> False\<close>
      and \<open>urust_is_local (yh \<Gamma>) (function_body func) (function_contract_pre contract)\<close>
      and \<open>ucincl (function_contract_pre contract)\<close>
      and \<open>\<forall> v. ucincl (function_contract_post contract v)\<close>
      and \<open>\<forall> v. ucincl (function_contract_abort contract v)\<close>
    shows \<open>\<Gamma>; func \<Turnstile>\<^sub>F contract\<close>
  using assms(2-)
  by (auto intro!: sstriple_from_evaluation simp add: satisfies_function_contract_def asepconj_ident2
      dest!: assms(1) split: continuation.splits)

subsection\<open>Evaluating pure functions\<close>
text\<open>To start off, some technical results showing that \<^term>\<open>urust_is_local\<close> holds if evaluating
an expression always results in Success/Return with the same machine, independent of the machine.\<close>
lemma success_independent_of_machine_then_local:
  assumes \<open>\<And> m. evaluate e m = continuation.Success v m\<close>
    shows \<open>urust_is_local \<Gamma> e \<phi>\<close>
  using assms
  by (simp add: is_local_def urust_eval_predicate_defs deep_evaluates_nondet_basic.simps)

lemma return_independent_of_machine_then_local:
  assumes \<open>\<And> m. evaluate e m = continuation.Return v m\<close>
    shows \<open>urust_is_local \<Gamma> e \<phi>\<close>
  using assms
  by (simp add: is_local_def urust_eval_predicate_defs deep_evaluates_nondet_basic.simps)

text\<open>Now, we can derive quite simple lemmas to derive \<^term>\<open>\<W>\<P>\<close> of pure expressions, or function
contracts for such expressions\<close>
corollary pure_function_derive_wp:
  assumes \<open>\<And> m. evaluate e m = continuation.Success v m\<close>
    shows \<open>\<top> \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda> r. \<langle>r = v\<rangle>) \<bottom> \<bottom>\<close>
  using assms
  by (auto intro!: wp_from_evaluation success_independent_of_machine_then_local
         simp add: asepconj_False_True asepconj_UNIV_idempotent)

corollary pure_function_derive_contract:
  assumes \<open>\<And> m. evaluate (function_body func) m = continuation.Success v m\<close>
    shows \<open>\<Gamma>; func \<Turnstile>\<^sub>F make_function_contract \<top> (\<lambda> r. \<langle>r = v\<rangle>)\<close>
  using assms
  by (auto intro!: contract_from_evaluation success_independent_of_machine_then_local ucincl_apure)

text\<open>With these results, one can first prove that there exists some \<^term>\<open>v\<close> such that your
expression evaluates to that value \<^term>\<open>v\<close>, and then define the 'pure' counterpart of your expression
using \<^term>\<open>The\<close>. However, there is a technical wrinkle here related to higher-order quantification.

Note that the full condition of e.g. @{thm pure_function_derive_contract} is:
\<^term>\<open>\<And> m :: 'machine. evaluate (function_body func) m = continuation.Success v m\<close>
with \<^term>\<open>evaluate\<close> also having more generic arguments for the abort condition, and types of
yield input and output.

The definition of \<^term>\<open>v\<close> should then be: it is \<^term>\<open>The\<close> value that \<^term>\<open>e\<close> evaluates to, whatever
the machine, and \<^emph>\<open>whatever the machine type\<close>. But that is not expressible in Isabelle/HOL. It is
possible to define this pure counterpart \<^term>\<open>v\<close> for a particular machine, abort type and yield
input and output, and then use @{thm pure_function_derive_contract} for those instantiations. But
it is somewhat fiddly.\<close>

(*<*)
end
(*>*)