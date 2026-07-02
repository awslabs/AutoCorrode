theory Tutorial_HoareWorked
  imports Tutorial_HoareSetup
begin

(*<*)
unbundle hoare_set_syntax
(*>*)

slide \<open>Hoare triples\<close>

text \<open>For a program \<open>e\<close> in our monad, a contract is a pair of:

  \<^item> a \<^bold>\<open>precondition\<close> \<open>P\<close>: a predicate on the state \<^emph>\<open>before\<close> running \<open>e\<close>.

  \<^item> a \<^bold>\<open>postcondition\<close> \<open>Q\<close>: a predicate on the result \<^emph>\<open>and\<close> the state \<^emph>\<open>after\<close> \<open>e\<close>.\<close>

text \<open>We write \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close> for the claim ``if \<open>P\<close> holds before \<open>e\<close>,
  then \<open>Q\<close> holds after'' -- a \<^bold>\<open>Hoare triple\<close>. The exact meaning
  is given case-by-case per monad. \<^bold>\<open>Important:\<close> this is the notion
  we ultimately use to state correctness of programs.\<close>

text \<open>Whatever the meaning, any sensible triple notion should be
  \<^emph>\<open>compositional\<close> -- bind two triples sharing an intermediate
  predicate \<open>R\<close>, get a triple for the composition:\<close>

text_raw \<open>
\begin{center}
\AxiomC{$\{P\}\;c_1\;\{R\}$}
\AxiomC{$\{R\}\;c_2\;\{Q\}$}
\RightLabel{(\textsc{Seq})}
\BinaryInfC{$\{P\}\;c_1;\;c_2\;\{Q\}$}
\DisplayProof
\end{center}
\<close>

end_slide


slide \<open>Triple and \<open>(SEQ)\<close> for the toy monad\<close>

text \<open>For our toy monad, the triple says ``every reachable
  outcome satisfies \<open>Q\<close>'' -- expressed via \<open>\<leadsto>\<close>:\<close>

definition triple :: \<open>'s set \<Rightarrow> ('s, 'a) m \<Rightarrow> ('a \<Rightarrow> 's set) \<Rightarrow> bool\<close>
    (\<open>\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<close>) where
  \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace> \<equiv> \<forall>s x s'. s \<in> P \<and> s \<leadsto>\<langle>e\<rangle> (x, s') \<longrightarrow> s' \<in> Q x\<close>

text \<open>and \<open>(SEQ)\<close> is then a \<^bold>\<open>theorem\<close>:\<close>

lemma triple_seq:
  assumes \<open>\<lbrace>P\<rbrace> e\<^sub>1 \<lbrace>\<lambda>x. R x\<rbrace>\<close>
      and \<open>\<And>x. \<lbrace>R x\<rbrace> e\<^sub>2 x \<lbrace>Q\<rbrace>\<close>
    shows \<open>\<lbrace>P\<rbrace> do { x \<leftarrow> e\<^sub>1; e\<^sub>2 x } \<lbrace>Q\<rbrace>\<close>
  using assms by (fastforce simp: triple_def evals_bind)

end_slide


slide \<open>The practical question\<close>

text \<open>Recall \<open>(SEQ)\<close>: to chain \<open>c\<^sub>1; c\<^sub>2\<close> we must produce an
  intermediate \<open>R\<close>.\<close>

text_raw \<open>
\begin{center}
\AxiomC{$\{P\}\;c_1\;\{R\}$}
\AxiomC{$\{R\}\;c_2\;\{Q\}$}
\RightLabel{(\textsc{Seq})}
\BinaryInfC{$\{P\}\;c_1;\;c_2\;\{Q\}$}
\DisplayProof
\end{center}
\medskip
\<close>

text \<open>\<^bold>\<open>Question:\<close> how do we know what to pick as \<open>R\<close>?
  In a program with many sequenced steps, every \<open>;\<close> introduces
  one -- and a fresh proof obligation. We need a systematic way
  to compute it.\<close>

end_slide


slide \<open>Weakest preconditions\<close>

text \<open>\<^bold>\<open>Idea:\<close> for each program \<open>e\<close> and postcondition \<open>Q\<close>, define
  the \<^bold>\<open>weakest precondition\<close> \<open>\<W>\<P> e Q\<close> -- the largest predicate
  on the start state for which \<open>e\<close> establishes \<open>Q\<close>:\<close>

definition wp :: \<open>('s, 'a) m \<Rightarrow> ('a \<Rightarrow> 's set) \<Rightarrow> 's set\<close> (\<open>\<W>\<P>\<close>) where
  \<open>\<W>\<P> e Q \<equiv> { s. \<forall>x s'. s \<leadsto>\<langle>e\<rangle> (x, s') \<longrightarrow> s' \<in> Q x }\<close>
    \<comment> \<open>the set of states from which \<^emph>\<open>every\<close> outcome lands in \<open>Q\<close>\<close>

text_raw \<open>\medskip\<close>

text \<open>\<^bold>\<open>Universal property\<close> -- the triple holds iff its
  precondition entails \<open>\<W>\<P> e Q\<close>:\<close>

lemma wp_triple_iff: \<open>(\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>) \<longleftrightarrow> (P \<longlongrightarrow> \<W>\<P> e Q)\<close>
  by %visible (auto simp: triple_def wp_def entails_def)

text \<open>The RHS uses the \<^emph>\<open>entailment\<close> arrow \<^term>\<open>(\<longlongrightarrow>)\<close>, which is just syntax for
set-inclusion \<^term>\<open>(\<subseteq>)\<close> in this case.\<close>

text \<open>This is \<^emph>\<open>functor-representability\<close> of the triple by \<open>\<W>\<P>\<close>.
  It reduces every triple proof to a single \<^emph>\<open>entailment\<close>, and turns
  the intermediate \<open>R\<close>'s of \<open>(SEQ)\<close> into \<^emph>\<open>computations\<close> over
  \<open>\<W>\<P>\<close>.\<close>

end_slide


slide \<open>Weakest precondition calculus\<close>

text \<open>Every statement about triples has a corresponding statement
  about \<open>\<W>\<P>\<close>. For example, bind:\<close>

lemma %visible wp_bind: 
  shows \<open>\<W>\<P> (do { x \<leftarrow> e; k x }) Q = \<W>\<P> e (\<lambda>x. \<W>\<P> (k x) Q)\<close>
  by (auto simp: wp_def evals_bind)

text \<open>With @{thm [source] wp_bind}, the \<^term>\<open>\<W>\<P>\<close> can be broken into individual statements and 
language's constructs.\<close>

lemma wp_prog:
  \<open>\<W>\<P> (do { x \<leftarrow> foo; y \<leftarrow> bar x; beef x y; return 42 }) Q
     = \<W>\<P> foo (\<lambda>x. 
         \<W>\<P> (bar x) (\<lambda>y. 
           \<W>\<P> (beef x y) (\<lambda>_. 
             \<W>\<P> (return 42) Q)))\<close>
  by %visible (simp add: wp_bind)

text\<open>We then apply dedicated rules per construct. \<^bold>\<open>Weakest Precondition Calculus\<close>.\<close>

end_slide

slide \<open>WP rules: Equation vs. Consequence form\<close>

text\<open>There's a WP rule for every language construct. For example:\<close>

lemma wp_return: \<open>\<W>\<P> (return x) Q = Q x\<close>
  by (auto simp: wp_def evals_return)

text\<open>For a proof calculus, WP rules are best stated in \<^bold>\<open>consequence form:\<close>\<close>

lemma wp_from_eq: 
 assumes \<open>\<W>\<P> e Q = \<psi>\<close> \<comment>\<open>Equational form\<close>
   shows \<open>(\<phi> \<longlongrightarrow> \<psi>) \<Longrightarrow> (\<phi> \<longlongrightarrow> \<W>\<P> e Q)\<close> \<comment>\<open>Rule form\<close>
  using assms by simp

text\<open>With this, we can easily map one or more equational rules into consequence form:\<close>

lemmas wp_returnI = wp_return[THEN wp_from_eq] \<comment>\<open>@{thm [show_question_marks=false, display] wp_returnI}\<close>
lemmas wp_bindI = wp_bind[THEN wp_from_eq] \<comment>\<open>@{thm [show_question_marks=false, display] wp_bindI}\<close>

end_slide

slide \<open>WP rules, bundled together for automation\<close>

text \<open>We accumulate WP rules in two named bundles -- \<open>wp_simps\<close> and \<open>wp_intros\<close>:\<close>

named_theorems wp_simps  \<comment> \<open>equational WP rewrites for \<open>simp\<close>\<close>
named_theorems wp_intros \<comment> \<open>consequence-form rules for \<open>intro\<close>/\<open>rule\<close>\<close>

text \<open>Register previously proved lemmas as WP simp/intro rules:\<close>

declare wp_bind[wp_simps] and wp_return[wp_simps]
declare wp_returnI[wp_intros] and wp_bindI[wp_intros]

text\<open>Note that @{method intro} @{thm [source] wp_intros} will only peel off one statement
at a time:\<close>

lemma %visible \<open>\<phi> \<longlongrightarrow> \<W>\<P> (do { x \<leftarrow> foo; y \<leftarrow> bar; beef; return (42::int) }) Q\<close>
 apply (intro wp_intros)
  \<comment>\<open>@{term \<open>\<phi> \<longlongrightarrow> \<W>\<P> foo (\<lambda>x. \<W>\<P> (bar \<bind> (\<lambda>y. beef \<bind> (\<lambda>_. return 42))) Q)\<close>}\<close>
  oops \<comment>\<open>Abandon this proof\<close>

text\<open>This is a \<^emph>\<open>feature\<close>, not a bug, because programs can be huge and we don't want to spend time
on parts of the code we are not yet ready to reason about.\<close>

(*<*)
lemma %invisible wp_mono:
  assumes \<open>\<And>x. R x \<longlongrightarrow> Q x\<close>
    shows \<open>\<W>\<P> e R \<longlongrightarrow> \<W>\<P> e Q\<close>
  using assms by (auto simp: wp_def entails_def)

\<comment> \<open>Lift an entailment \<open>\<psi> \<longlongrightarrow> \<W>\<P> e Q\<close> into rule form.\<close>
lemma wp_from_entails:
  assumes \<open>\<psi> \<longlongrightarrow> \<W>\<P> e Q\<close> 
      and \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> e Q\<close>
  using assms by (auto simp: entails_def)
(*>*)

end_slide



interlude \<open>A peek ahead: real uRust WP rules\<close>

text_raw \<open>%
\begingroup
\renewenvironment{isabellebody}{}{}%
\renewcommand{\setisabellecontext}[1]{}%
\input{Tutorial_UrustPeek_WP.tex}%
\endgroup
\<close>

end_interlude


slide \<open>WP calculus: Call-by-contract\<close>

text\<open>If we invoke a (sub)program we have a triple for, we can derive a WP rule
for "call-by-contact":\<close>

lemma wp_call_by_contractI:
  assumes \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close> \<comment>\<open>Already proved contract\<close>
      and \<open>\<phi> \<longlongrightarrow> P\<close> \<comment>\<open>Precondition entailment\<close>
      and \<open>\<And>x. Q x \<longlongrightarrow> R x\<close> \<comment>\<open>Postcondition entailment\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> e R\<close>
  using assms by (force simp: wp_triple_iff wp_def triple_def entails_def)

text\<open>This is crucial for enabling modular verification at the level of functions or even
sub-programs.\<close>

text \<open>We also register the following basic rules:\<close>

lemma %visible
  shows entails_refl[wp_intros]: \<open>\<phi> \<longlongrightarrow> \<phi>\<close>
    and entails_univ[wp_intros]: \<open>\<phi> \<longlongrightarrow> UNIV\<close>
  by (simp_all add: entails_def)

end_slide

slide \<open>Working example: Setup\<close>

text \<open>To illustrate, we now work through a concrete worked example: a function \<open>foo\<close>
  that increments the \<open>x\<close>-field of a two-field record, and a
  caller \<open>bar\<close> that reuses it.\<close>

text \<open>First, our state record:\<close>

record twoint =
  fx :: int
  fy :: int

text \<open>Next, get/set primitives for reading/updating the whole state:\<close>

definition get :: \<open>('s, 's) m\<close> 
  where \<open>get = M (\<lambda>s. {(s, s)})\<close> \<comment>\<open>Return whole state, leave it unchanged\<close>

definition put :: \<open>'s \<Rightarrow> ('s, unit) m\<close> 
  where \<open>put s' = M (\<lambda>_. {((), s')})\<close> \<comment>\<open>Update whole state, return @{term \<open>()\<close>}\<close>

end_slide

slide \<open>Working example: Per-field reads and writes\<close>

text \<open>Field operations can now be written as monadic programs over \<open>get\<close>/\<open>put\<close>:\<close>

definition get_x :: \<open>(twoint, int) m\<close> where
  \<open>get_x = do { s \<leftarrow> get; return (fx s) }\<close>

definition get_y :: \<open>(twoint, int) m\<close> where
  \<open>get_y = do { s \<leftarrow> get; return (fy s) }\<close>

definition put_x :: \<open>int \<Rightarrow> (twoint, unit) m\<close> where
  \<open>put_x v = do { s \<leftarrow> get; put (s\<lparr>fx := v\<rparr>) }\<close>

definition put_y :: \<open>int \<Rightarrow> (twoint, unit) m\<close> where
  \<open>put_y v = do { s \<leftarrow> get; put (s\<lparr>fy := v\<rparr>) }\<close>

end_slide

slide \<open>Working example: Two pieces of state-set notation\<close>

text \<open>\<^bold>\<open>Field equality\<close>: Foreshadowing the point-to- notation common from separation logic, we 
temporarily use \<open>f \<mapsto> v\<close> to denote the set of states whose field \<open>f\<close> equals \<open>v\<close>:\<close>

abbreviation \<open>field_eq f v \<equiv> {s. f s = v}\<close>

bundle field_eq_syntax \<comment>\<open>Define configurable syntax\<close>
begin
  notation field_eq (\<open>_ \<mapsto> _\<close> [76, 60] 75)
end
unbundle field_eq_syntax \<comment>\<open>Enable the syntax\<close>

text \<open>\<^bold>\<open>Pure assertion\<close> -- \<open>\<langle>\<phi>\<rangle>\<close> lifts state-independent fact \<open>\<phi>\<close> to full or empty set:\<close>

definition pure_assn :: \<open>bool \<Rightarrow> 's set\<close> (\<open>\<langle>_\<rangle>\<close>)
  where \<open>\<langle>\<phi>\<rangle> \<equiv> if \<phi> then UNIV else {}\<close>

(*<*)
lemma entails_hoist_pure[wp_intros]: 
  assumes \<open>P \<Longrightarrow> (\<phi> \<longlongrightarrow> \<psi>)\<close>
  shows \<open>(\<phi> \<sqinter> \<langle>P\<rangle>) \<longlongrightarrow> \<psi>\<close>
  using assms by (simp add: entails_def pure_assn_def)
(*>*)

end_slide

slide \<open>Working example: WP rules for read and write\<close>

text \<open>Let's make an attempt at specifying the get/put operators through contracts:\<close>

(*<*)
lemma wp_get_put [wp_simps]: shows
  wp_get:   \<open>\<W>\<P> get        Q = {s. s \<in> Q s}\<close>         and
  wp_get_x: \<open>\<W>\<P> get_x      P = {s. s \<in> P (fx s)}\<close>    and
  wp_get_y: \<open>\<W>\<P> get_y      S = {s. s \<in> S (fy s)}\<close>    and
  wp_put:   \<open>\<W>\<P> (put s')   R = \<langle>s' \<in> R ()\<rangle>\<close>           and
  wp_put_x: \<open>\<W>\<P> (put_x v) T = {s. s\<lparr>fx := v\<rparr> \<in> T ()}\<close> and
  wp_put_y: \<open>\<W>\<P> (put_y v) U = {s. s\<lparr>fy := v\<rparr> \<in> U ()}\<close>
by (auto simp: wp_def evals_def get_def put_def get_x_def pure_assn_def
      get_y_def put_x_def put_y_def mbind_def return_def)
(*>*)

lemma %visible put_get_triples_0:
  shows triple_get_x: "\<lbrace> fx \<mapsto> v \<rbrace> get_x \<lbrace> \<lambda>r. \<langle>r = v\<rangle> \<rbrace>"
    and triple_get_y: "\<lbrace> fy \<mapsto> v \<rbrace> get_y \<lbrace> \<lambda>r. \<langle>r = v\<rangle> \<rbrace>"
    and triple_put_x: "\<lbrace> UNIV \<rbrace> put_x v \<lbrace> \<lambda>_. fx \<mapsto> v \<rbrace>"
    and triple_put_y: "\<lbrace> UNIV \<rbrace> put_y v \<lbrace> \<lambda>_. fy \<mapsto> v \<rbrace>"
  unfolding wp_triple_iff wp_simps by (simp_all add: entails_def pure_assn_def)

text\<open>Register the derived WP rules in @{thm [source] wp_intros}:\<close>

lemmas put_get_contracts_0 = put_get_triples_0[THEN wp_call_by_contractI]

declare put_get_contracts_0[wp_intros]

end_slide

slide \<open>Working example: Proving increment\<close>

text \<open>A simple program \<open>foo\<close> incrementing @{term \<open>fx\<close>}:\<close>

definition foo :: \<open>(twoint, unit) m\<close> where
  \<open>foo = do { v \<leftarrow> get_x; put_x (v + 1) }\<close>

text \<open>Let's prove the contract \<open>\<lbrace> fx \<mapsto> v \<rbrace> foo \<lbrace> \<lambda>_. fx \<mapsto> v + 1 \<rbrace>\<close> using our WP calculus:\<close>

lemma %visible shows \<open>\<lbrace> fx \<mapsto> v \<rbrace> foo \<lbrace> \<lambda>_. fx \<mapsto> v + 1 \<rbrace>\<close>
  unfolding wp_triple_iff foo_def
  \<comment>\<open>Repeatedly apply WP rules\<close>
  apply (rule wp_intros)+
  \<comment>\<open>Goal residue: \<open>\<And>x xa. fx \<mapsto> x + 1 \<longlongrightarrow> fx \<mapsto> v + 1\<close>\<close>
  oops

 text\<open>\<^bold>\<open>Stuck.\<close> Contract says \<open>\<lbrace>fx \<mapsto> v\<rbrace> get_x \<lbrace>\<lambda>r. \<langle>r = v\<rangle>\<rbrace>\<close> --
   we learn \<open>r = v\<close> but \<^bold>\<open>loose\<close> the assertion \<open>fx \<mapsto> v\<close>. So we cannot say where \<open>put_x (v + 1)\<close> lands.\<close>

end_slide

slide \<open>Working example: Proving increment -- attempt 2\<close>

text \<open>\<^bold>\<open>Fix:\<close> have \<open>get_x\<close> \<^bold>\<open>re-assert\<close> \<open>fx \<mapsto> v\<close> in its post-condition; same for \<open>get_y\<close>:\<close>

declare put_get_contracts_0 [wp_intros del] \<comment>\<open>Remove previous contracts\<close>

lemma %visible put_get_triples_1:
  shows triple_get_x_1: \<open>\<lbrace> fx \<mapsto> v \<rbrace> get_x \<lbrace> \<lambda>r. fx \<mapsto> v \<sqinter> \<langle>r = v\<rangle> \<rbrace>\<close>
    and triple_get_y_1: \<open>\<lbrace> fy \<mapsto> v \<rbrace> get_y \<lbrace> \<lambda>r. fy \<mapsto> v \<sqinter> \<langle>r = v\<rangle> \<rbrace>\<close>
    and triple_put_x_1: \<open>\<lbrace> UNIV \<rbrace> put_x v \<lbrace> \<lambda>_. fx \<mapsto> v \<rbrace>\<close>
    and triple_put_y_1: \<open>\<lbrace> UNIV \<rbrace> put_y v \<lbrace> \<lambda>_. fy \<mapsto> v \<rbrace>\<close>
  unfolding wp_triple_iff wp_simps by (auto simp: entails_def pure_assn_def)

text\<open>Add new contracts:\<close>

lemmas put_get_contracts_1 = put_get_triples_1[THEN wp_call_by_contractI]
declare put_get_contracts_1 [wp_intros]

text \<open>Now \<open>foo\<close>'s contract goes through, by pure \<open>wp_intros\<close> chaining and simplification:\<close>

lemma %visible foo_spec: shows \<open>\<lbrace> fx \<mapsto> v \<rbrace> foo \<lbrace> \<lambda>_. fx \<mapsto> v + 1 \<rbrace>\<close>
  unfolding wp_triple_iff foo_def by (rule wp_intros | simp)+

(*<*)
text\<open>Register the contract:\<close>
lemmas wp_foo = foo_spec[THEN wp_call_by_contractI]
declare wp_foo [wp_intros]
(*>*)

end_slide

slide \<open>Working example: Increment, \<^emph>\<open>and more\<close>\<close>

text \<open>Boosted in confidence, consider a caller that runs \<open>foo\<close> and then reads \<open>fy\<close>:\<close>

definition bar :: \<open>(twoint, int) m\<close> where
  \<open>bar = do { foo; get_y }\<close>

text \<open>Let's try to specify and prove what @{term bar} does:\<close>

(*<*)                     
lemma entails_project[wp_intros]: \<open>\<alpha> \<sqinter> \<beta> \<longlongrightarrow> \<alpha>\<close> unfolding entails_def by simp
(*>*)

lemma %visible \<comment>\<open>Pre value \<open>(x,y)\<close>, post value \<open>(x+1,y)\<close>\<close>
  shows \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> bar \<lbrace> \<lambda>r. fx \<mapsto> x + 1 \<sqinter> fy \<mapsto> y \<sqinter> \<langle>r = y\<rangle> \<rbrace>\<close>
  unfolding wp_triple_iff bar_def     
  apply (rule wp_intros)+        
  \<comment>\<open>Goal residue: \<open>\<And>xa. fx \<mapsto> x + 1 \<longlongrightarrow> fy \<mapsto> ?v xa\<close> -- \<open>fy\<close> post is unconstrained.\<close>
  oops
                                                      
\<comment>\<open>\<^bold>\<open>Stuck again.\<close> We did not specify that @{term foo} does not change @{term fy}!\<close>

end_slide

slide \<open>Working example: Increment, \<^emph>\<open>and more\<close> -- attempt 2\<close>

text \<open>\<^bold>\<open>Fix:\<close> every contract mentions \<^bold>\<open>every\<close> field -- what it
  preserves and what it changes.\<close>

declare put_get_contracts_1 [wp_intros del] \<comment>\<open>Remove previous contracts\<close>
declare wp_foo              [wp_intros del]

lemma %visible put_get_triples_2:
  shows \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> get_x \<lbrace> \<lambda>r. fx \<mapsto> x \<sqinter> fy \<mapsto> y \<sqinter> \<langle>r = x\<rangle> \<rbrace>\<close>
    and \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> get_y \<lbrace> \<lambda>r. fx \<mapsto> x \<sqinter> fy \<mapsto> y \<sqinter> \<langle>r = y\<rangle> \<rbrace>\<close>
    and \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> put_x v \<lbrace> \<lambda>_. fx \<mapsto> v \<sqinter> fy \<mapsto> y \<rbrace>\<close>
    and \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> put_y v \<lbrace> \<lambda>_. fx \<mapsto> x \<sqinter> fy \<mapsto> v \<rbrace>\<close>
  unfolding wp_triple_iff wp_simps by (auto simp: entails_def pure_assn_def)

text\<open>Add new contracts:\<close>

lemmas put_get_contracts_2 = put_get_triples_2[THEN wp_call_by_contractI]
declare put_get_contracts_2 [wp_intros]

end_slide

slide \<open>Working example: Increment, \<^emph>\<open>and more\<close> -- attempt 2 (continued)\<close>

text \<open>Re-prove \<open>foo\<close>'s contract under the new bundle, with \<open>fy\<close> in
  pre and post, then lift it for callers:\<close>

lemma %visible foo_spec_framed:
  shows \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> foo \<lbrace> \<lambda>_. fx \<mapsto> x + 1 \<sqinter> fy \<mapsto> y \<rbrace>\<close>
  unfolding wp_triple_iff foo_def by (rule wp_intros | simp)+

(*<*)
text\<open>Add new contracts:\<close>
lemmas wp_foo_framed = foo_spec_framed[THEN wp_call_by_contractI]
declare wp_foo_framed [wp_intros]
(*>*)

text \<open>Now \<open>bar\<close> goes through:\<close>

lemma %visible bar_spec:
  shows \<open>\<lbrace> fx \<mapsto> x \<sqinter> fy \<mapsto> y \<rbrace> bar \<lbrace> \<lambda>r. fx \<mapsto> x + 1 \<sqinter> fy \<mapsto> y \<sqinter> \<langle>r = y\<rangle> \<rbrace>\<close>
  unfolding wp_triple_iff bar_def
  apply (rule wp_intros)
  apply (rule wp_intros)
  apply (rule wp_intros)
  apply (rule wp_intros)
  apply (rule wp_intros)
  apply (rule wp_intros)
  done

end_slide


slide \<open>Reflection\<close>

text \<open>\<^bold>\<open>What worked.\<close> We pushed through the proof by repeatedly applying
  generic WP rules. It's clear that this is, in principle, amenable to a high
  degree of automation -- crucial for large-scale program verification. This is
exactly what AutoCorrode's \<open>crush\<close> does.\<close>

text \<open>\<^bold>\<open>What didn't work (well):\<close> To re-use \<open>foo\<close> inside \<open>bar\<close> we re-stated
  \<open>foo\<close>'s contract with \<open>fy \<mapsto> y\<close> in pre and post -- even though
  \<open>foo\<close> does not look at \<open>fy\<close>. That clause is pure \<^bold>\<open>framing
  noise\<close>: information about state \<open>foo\<close> did not touch, added by
  hand to make composition go through.\<close>

text \<open>With \<open>n\<close> fields and one untouched, every contract grows by \<open>n - 1\<close>
  such clauses, every caller adding another. \<^bold>\<open>This is the frame
  problem.\<close>\<close>

end_slide


slide \<open>The frame problem: approaches\<close>

text \<open>Three approaches in active use:\<close>

text \<open>\<^bold>\<open>1. Explicit modifies-clauses (s2n-bignum).\<close>  Each spec
  carries a \<open>MAYCHANGE\<close> clause listing the memory, registers, or flags
  it may alter. Composition discharges a syntactic ``mine-fits-yours''
  side condition. Used in AWS's HOL-Light bignum verification.\<close>

text \<open>\<^bold>\<open>2. AutoCorrode's \<open>AutoLocality\<close> autogen.\<close>  Driven by
  \<^emph>\<open>record footprints\<close>: declare which fields each operation touches,
  and \<open>locality_autoderive\<close> produces all pairwise commutativity lemmas
  automatically. Plain HOL; no SL connectives.\<close>

text \<open>\<^bold>\<open>3. Separation logic.\<close> \<^emph>\<open>What AutoCorrode picks -- see next section...\<close>\<close>

end_slide

(*<*)

slide \<open>WP for any monad: the CPS view\<close>

text \<open>Our toy \<open>wp\<close> took a program and a postcondition. Generally,
  \<^bold>\<open>WP is a function\<close> \<open>('a \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> 'state \<Rightarrow> bool\<close>. That
  is the \<^bold>\<open>continuation monad\<close> with answer type \<open>'state \<Rightarrow> bool\<close>:\<close>

type_synonym ('s, 'a) cwp = \<open>('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool\<close>
  \<comment> \<open>continuations into state-predicates\<close>

definition %internal cps_wp ::
    \<open>('s, 'a) cwp \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>cps_wp m Q \<equiv> m Q\<close>

definition %internal cps_triple ::
    \<open>('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a) cwp \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>cps_triple P m Q \<equiv> \<forall>s. P s \<longrightarrow> cps_wp m Q s\<close>

lemma %internal cps_wp_universal:
  shows \<open>cps_triple P m Q \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> cps_wp m Q s)\<close>
  by (simp add: cps_triple_def)

text \<open>Punchline: \<open>('s, 'a) cwp\<close> \<^bold>\<open>is\<close> the type of WP transformers
  for \<open>'a\<close>-valued state computations. CPS \<open>bind\<close> = WP for sequencing;
  CPS \<open>return\<close> = WP for pure values.\<close>

text \<open>The actual programs sit inside this type as the \<^bold>\<open>healthy\<close>
  fragment (monotone in \<open>Q\<close>, conjunctive -- Dijkstra's healthiness);
  the wider type also accommodates refinement-calculus features like
  demonic and angelic choice.\<close>

end_slide
(*>*)

text %internal \<open>Release the toy \<open>\<lbrace>...\<rbrace>\<close> notation so the SepLogic
  slides can use the real \<open>Shallow_Separation_Logic.Triple\<close> mixfix
  with the same brackets without ambiguity.\<close>

no_notation %internal triple (\<open>\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<close>)

unbundle %internal no hoare_set_syntax

end
