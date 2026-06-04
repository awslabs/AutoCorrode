theory Tutorial_HoareSetup
  imports Main "HOL-Library.Monad_Syntax" Slides
begin

(*<*)
\<comment> \<open>A dedicated entailment constant for state-set assertions.
  Wrapping \<open>\<subseteq>\<close> in a fresh definition means the parser/printer never
  confuses entailment with boolean implication or subset.\<close>

definition entails :: \<open>'s set \<Rightarrow> 's set \<Rightarrow> bool\<close>
  where \<open>entails P Q \<equiv> P \<subseteq> Q\<close>

lemma entailsI: \<open>P \<subseteq> Q \<Longrightarrow> entails P Q\<close>
  by (simp add: entails_def)

lemma entailsD: \<open>entails P Q \<Longrightarrow> P \<subseteq> Q\<close>
  by (simp add: entails_def)

bundle hoare_set_syntax
begin
  \<comment> \<open>Lattice-style notation for sets: \<open>\<sqinter>\<close> for intersection (the
    \<open>HOL.lattice_syntax\<close> glyph, bound directly to \<open>inter\<close> so it
    both parses \<^emph>\<open>and\<close> prints), and \<open>\<longlongrightarrow>\<close> for the dedicated
    entailment constant \<open>entails\<close>.\<close>
  no_notation inter (infixl \<open>\<inter>\<close> 70)
  notation    inter (infixl \<open>\<sqinter>\<close> 70)
  notation    entails (infix  \<open>\<longlongrightarrow>\<close> 50)
end

(*>*)


slide \<open>A toy non-deterministic state monad\<close>

text \<open>To make the next few slides concrete, we set up a small
  state-monad playground. We pick the \<^bold>\<open>non-deterministic\<close>
  variant: from one state, a program can produce \<^emph>\<open>several\<close>
  possible \<open>(result, end-state)\<close> outcomes. This matches the shape
  uRust uses upstream.\<close>

datatype ('s, 'a) m = M (run: \<open>'s \<Rightarrow> ('a \<times> 's) set\<close>)

definition return :: \<open>'a \<Rightarrow> ('s, 'a) m\<close> where
  \<open>return x = M (\<lambda>s. {(x, s)})\<close>

definition mbind :: \<open>('s, 'a) m \<Rightarrow> ('a \<Rightarrow> ('s, 'b) m) \<Rightarrow> ('s, 'b) m\<close> where
  \<open>mbind c k = M (\<lambda>s. \<Union>(x, s')\<in>run c s. run (k x) s')\<close>

text \<open>Hook into \<open>HOL-Library.Monad_Syntax\<close> for \<open>do\<close>-notation:\<close>

adhoc_overloading bind \<rightleftharpoons> mbind

end_slide


slide \<open>The evaluation relation \<open>\<leadsto>\<close>: in our toy example\<close>

text \<open>One primitive: ``from \<open>s\<close>, program \<open>e\<close> can produce result \<open>x\<close>
  and end in state \<open>s'\<close>''.\<close>

definition evals :: \<open>'s \<Rightarrow> ('s, 'a) m \<Rightarrow> ('a \<times> 's) \<Rightarrow> bool\<close>
    (\<open>_ \<leadsto>\<langle>_\<rangle> _\<close> [60, 0, 60] 60)
      \<comment> \<open>the numbers fix operator precedence (binding strength)\<close>
  where \<open>s \<leadsto>\<langle>e\<rangle> xs' \<equiv> xs' \<in> run e s\<close>

text \<open>(This is the same shape uRust uses -- see later.)\<close>

text \<open>Characterisations of \<open>\<leadsto>\<close> on \<open>return\<close>, \<open>do\<close>-bind, and plain
  sequencing that we'll need below:\<close>

lemma evals_simps:
  shows evals_return: \<open>s \<leadsto>\<langle>return x\<rangle> (y, s') \<longleftrightarrow> y = x \<and> s' = s\<close>
    and evals_bind: \<open>s \<leadsto>\<langle>do { x \<leftarrow> e; k x }\<rangle> (y, s'')
                 \<longleftrightarrow> (\<exists>x s'. s \<leadsto>\<langle>e\<rangle> (x, s') \<and> s' \<leadsto>\<langle>k x\<rangle> (y, s''))\<close>
    and evals_seq: \<open>s \<leadsto>\<langle>do { e\<^sub>1; e\<^sub>2 }\<rangle> (y, s'')
       \<longleftrightarrow> (\<exists>x s'. s \<leadsto>\<langle>e\<^sub>1\<rangle> (x, s') \<and> s' \<leadsto>\<langle>e\<^sub>2\<rangle> (y, s''))\<close>

  by %visible (auto simp: evals_def return_def mbind_def)+

end_slide


interlude \<open>A peek ahead: real uRust evaluation rules\<close>

text_raw \<open>%
\begingroup
\renewenvironment{isabellebody}{}{}%
\renewcommand{\setisabellecontext}[1]{}%
\input{Tutorial_UrustPeek_Eval.tex}%
\endgroup
\<close>

end_interlude

end
