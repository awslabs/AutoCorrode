(* Toy separation logic, built on the first half's monad and reusing
   AutoCorrode's separation-algebra + assertion-language infrastructure
   (Apartness, Separation_Algebra, Assertion_Language). The toy state
   `twoint_sl = field \<rightharpoonup> int` is automatically a sepalg via
   `'b option :: apart` and `('a \<Rightarrow> 'b) :: apart` instances. *)

theory Tutorial_SLWorked
  imports
    Tutorial_HoareSetup
    Shallow_Separation_Logic.Assertion_Language
begin

slide \<open>The frame problem, recap\<close>

text \<open>To make \<open>bar\<close> go through in the first half, we strengthened
  \<open>foo\<close>'s contract by hand to mention \<open>fy\<close>:\<close>

text \<open>\quad \<open>\<lbrace> \<lambda>s. fx s = v \<and> fy s = w \<rbrace>
            foo
         \<lbrace> \<lambda>_ s. fx s = v + 1 \<and> fy s = w \<rbrace>\<close>\<close>

text \<open>The \<open>fy s = w\<close> conjunct is \<^bold>\<open>framing noise\<close> -- it adds nothing
  local to \<open>foo\<close>; it just witnesses ``\<open>fy\<close> is unchanged''. With \<open>n\<close>
  fields, every contract grows by \<open>n-1\<close> such clauses.\<close>

text \<open>\<^bold>\<open>What we want:\<close> a logic where a contract mentions only the
  cells a function touches, and any "disjoint" fragment is preserved
  by a \<^emph>\<open>structural rule\<close>.\<close>

text\<open>\<^bold>\<open>Question:\<close> What does "disjoint" mean?\<close>

end_slide

slide \<open>Separation algebras\<close>

text \<open>The notion of ``state with disjointness'' is captured by a
  \<^bold>\<open>separation algebra\<close>: a structure with an \<^bold>\<open>empty state\<close> \<open>0\<close>,
  a \<^bold>\<open>disjointness predicate\<close> \<open>\<sharp>\<close>, and the ability to \<^bold>\<open>join disjoint
  pieces\<close> \<open>+\<close>. AutoCorrode encodes this as a typeclass and provides
  several models. Verbatim, from
  \<open>Shallow_Separation_Logic.Separation_Algebra\<close>:\<close>

text_raw \<open>%
\begingroup
\renewenvironment{isabellebody}{}{}%
\renewcommand{\setisabellecontext}[1]{}%
\input{Tutorial_SepalgIntro.tex}%
\endgroup
\<close>

text \<open>\<^bold>\<open>Reusable\<close>: every SL connective below will be defined once,
  generically, for any type in this class.\<close>

end_slide


slide \<open>Examples of separation algebras\<close>

text \<open>AutoCorrode ships sepalg instances for a stack of constructions.
  Each row gives the disjointness and join, both antiquoted from
  \<open>Separation_Algebra.thy\<close>:\<close>

text_raw \<open>%
\begin{center}\small
\begin{tabular}{lll}
\textbf{Type} & \textbf{Disjointness ($\sharp$)} & \textbf{Join (+)} \\\hline
\isa{{\isacharprime}{\kern0pt}a\ option}
   & at most one \isa{Some}
   & take the \isa{Some}, else \isa{None} \\
\isa{{\isacharprime}{\kern0pt}a\ set}
   & disjoint sets ($A \cap B = \emptyset$)
   & union ($A \cup B$) \\
\isa{{\isacharprime}{\kern0pt}a\ {\isasymRightarrow}\ {\isacharprime}{\kern0pt}b}
   & pointwise on \isa{{\isacharprime}{\kern0pt}b}
   & pointwise on \isa{{\isacharprime}{\kern0pt}b} \\
\isa{{\isacharprime}{\kern0pt}a\ {\isasymtimes}\ {\isacharprime}{\kern0pt}b}
   & componentwise
   & componentwise \\
records
   & componentwise (lift over fields)
   & componentwise \\
\end{tabular}\end{center}\<close>

text \<open>\<^bold>\<open>Read down the table\<close>: each line uses the previous one. A heap
  \<open>field \<rightharpoonup> int\<close> is the partial-function instance composed with the
  option instance; a set \<open>'a set\<close> is the function-of-option instance
  at \<open>'b = unit option\<close> (membership = \<open>Some ()\<close>); a multi-component
  machine state is the product instance composed over its record fields.\<close>

end_slide


slide \<open>Our toy state, as a separation algebra\<close>

text \<open>Earlier, our state was \<open>record twoint = fx :: int, fy :: int\<close>
  -- both fields \<^emph>\<open>always\<close> present. To get a separation algebra, we
  loosen this so each field is independently \<^bold>\<open>present or absent\<close>:\<close>

datatype field = FX | FY

type_synonym twoint_sl = \<open>field \<rightharpoonup> int\<close>

text \<open>Equivalently, we could consider a record of \<open>fx :: int option, fy :: int option\<close>.
  By the table on the previous slide \<open>twoint_sl\<close> \<^bold>\<open>automatically inherits\<close>
  a separation algebra structure. Isabelle's sort-checker confirms it:\<close>

lemma \<open>OFCLASS(twoint_sl, sepalg_class)\<close>
  by intro_classes

text_raw\<open>\vspace*{-4mm}\<close>
text \<open>The atomic assertion \<open>f \<mapsto> v\<close> says the heap contains the cell \<open>f\<close>
  holding \<open>v\<close>, leaving the rest of the heap unconstrained -- i.e. it is
  \<^emph>\<open>upwards closed\<close>:\<close>

definition pto :: \<open>field \<Rightarrow> int \<Rightarrow> twoint_sl assert\<close>  (infix \<open>\<mapsto>\<close> 70) where
  \<open>(f \<mapsto> v) \<equiv> { m. m f = Some v }\<close>

end_slide


slide \<open>Lifting disjointness to assertions: introducing \<open>\<star>\<close>\<close>

text \<open>\<^bold>\<open>Goal:\<close> Bake stability under disjoint extension into the triple.\<close>

text \<open>\<^bold>\<open>Need:\<close> Notion of disjoint composition for \<^emph>\<open>assertions\<close> (sets of states), not
individual states.\<close>

text \<open>@{thm [display, show_question_marks=false] asepconj_def}\<close>

text \<open>So @{term \<open>s \<Turnstile> \<phi> \<star> \<psi>\<close>} if it can
    be \<^emph>\<open>split\<close> into two \<^bold>\<open>disjoint\<close> pieces
    @{term \<open>t \<sharp> u\<close>}, where @{term \<open>t \<Turnstile> \<phi>\<close>} and @{term \<open>u \<Turnstile> \<psi>\<close>}.\<close>

text \<open>\<^bold>\<open>Some algebraic laws\<close>:\<close>

text \<open>
\<^item> @{thm [show_question_marks=false] asepconj_comm} \<comment>\<open>Commutativity\<close>
\<^item> @{thm [show_question_marks=false] asepconj_assoc} \<comment>\<open>Associativity\<close>
\<^item> @{thm [show_question_marks=false] asepconj_pure} \<comment>\<open>Ordinary conjunction on pure assertions\<close>\<close>

end_slide

slide \<open>Upwards closure: \<open>\<star> UNIV\<close> and \<open>ucincl\<close>\<close>

text \<open>\<open>P \<star> UNIV\<close> holds on a heap that has \<^emph>\<open>at least\<close> the resources
  required by \<open>P\<close> -- it is the \<^bold>\<open>upwards closure\<close> of \<open>P\<close> under disjoint
  extension. An assertion that absorbs further resources, \<open>P \<star> UNIV = P\<close>,
  is called \<^bold>\<open>upwards closed\<close>:\<close>

text \<open>@{thm [display, show_question_marks=false] ucincl_alt}\<close>

text \<open>The main practical relevance of \<open>ucincl\<close> is that we can \<^bold>\<open>hoist
  pure assertions\<close> out of an entailment, on either side:\<close>

text \<open>
\<^item> @{thm [show_question_marks=false] apure_entails_iff}
\<^item> @{thm [show_question_marks=false] apure_entailsR}\<close>

text \<open>AutoCorrode tracks \<open>ucincl\<close> via a named-theorems bundle
  \<open>ucincl_intros\<close>; the \<open>ucincl_solve\<close> tactic discharges such side-conditions
  automatically.\<close>

end_slide


slide \<open>Common operations on entailments\<close>

text \<open>Working with \<open>\<longlongrightarrow>\<close> and \<open>\<star>\<close> feels similar to working in Pure logic, except that assertions
are \<^bold>\<open>resourceful\<close> and cannot be duplicated (but they can be dropped under \<^term>\<open>ucincl\<close>!).\<close>

text \<open>\<^bold>\<open>Cancellation\<close> (drop a shared conjunct on LHS and RHS):\<close>
text \<open>
\<^item> @{thm [show_question_marks=false] asepconj_mono2}
\<^item> @{thm [show_question_marks=false] asepconj_mono}\<close>

text \<open>\<^bold>\<open>Spatial \<open>drule\<close>\<close> -- replace a conjunct on the LHS by something
  it entails:\<close>

text \<open>
\<^item> @{lemma [show_question_marks=false]
    \<open>\<lbrakk> \<phi> \<longlongrightarrow> \<xi>; \<xi> \<star> \<psi> \<longlongrightarrow> \<theta> \<rbrakk> \<Longrightarrow> \<phi> \<star> \<psi> \<longlongrightarrow> \<theta>\<close>
    by (meson aentails_trans asepconj_mono2)}\<close>
(*<*)
text\<open>\<^item> @{lemma [show_question_marks=false]
    \<open>\<lbrakk> \<psi> \<longlongrightarrow> \<xi>; \<phi> \<star> \<xi> \<longlongrightarrow> \<theta> \<rbrakk> \<Longrightarrow> \<phi> \<star> \<psi> \<longlongrightarrow> \<theta>\<close>
    by (meson aentails_trans asepconj_mono)}\<close>
(*>*)

text \<open>\<^bold>\<open>Spatial \<open>rule\<close>\<close> -- back-chain an entailment on the RHS:\<close>

text \<open>
\<^item> @{lemma [show_question_marks=false]
    \<open>\<lbrakk> \<phi> \<longlongrightarrow> \<xi> \<star> \<psi>; \<xi> \<longlongrightarrow> \<xi>' \<rbrakk> \<Longrightarrow> \<phi> \<longlongrightarrow> \<xi>' \<star> \<psi>\<close>
    by (meson aentails_trans asepconj_mono2)}\<close>
(*<*)
text\<open>\<^item> @{lemma [show_question_marks=false]
    \<open>\<lbrakk> \<phi> \<longlongrightarrow> \<xi> \<star> \<psi>; \<psi> \<longlongrightarrow> \<psi>' \<rbrakk> \<Longrightarrow> \<phi> \<longlongrightarrow> \<xi> \<star> \<psi>'\<close>
    by (meson aentails_trans asepconj_mono)}\<close>
(*>*)

text \<open>\<^bold>\<open>Spatial \<open>congruence rules\<close>\<close> also exist, but not discussed here.\<close>

end_slide

slide \<open>Hoare triples --- in separation logic\<close>

text\<open>Intuitively, we want any component disjoint from pre/post-condition left unchanged. 
Concretely, we say that any \<^emph>\<open>assertion\<close> disjoint from pre/post-condition is preserved:\<close>

definition sltriple (\<open>\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>\<close>) where 
   \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace> \<equiv> 
      \<forall>h x h'. \<comment>\<open>For all states @{term h}, @{term h'} and return values @{term x} ...\<close>
      h \<leadsto>\<langle>e\<rangle> (x, h') \<comment>\<open>... if @{term e} can tranform @{term h} into @{term h'}, producing @{term x} ...\<close>
      \<longrightarrow> (\<forall>\<pi>. ucincl \<pi> \<longrightarrow> \<comment>\<open>then for any predicate @{term \<pi>} (disjoint from P)\<close> 
          \<comment>\<open>if @{term h} satisfies the precondition and, disjointly, @{term \<pi>}\<close>
          h \<Turnstile> P \<star> \<pi> \<longrightarrow> 
          \<comment>\<open>then @{term h'} satisfies the postcondition and, disjointly, still @{term \<pi>}\<close>
          h' \<Turnstile> Q x \<star> \<pi>)\<close>

text\<open>By definition, we obtain the \<^bold>\<open>frame rule\<close>, which we saw failing in the previous session:\<close>

lemma frame_rule:
  assumes \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close>
    shows \<open>\<lbrace>P \<star> S\<rbrace> e \<lbrace>\<lambda>x. Q x \<star> S\<rbrace>\<close>
  unfolding sltriple_def
proof (intro allI impI)
  fix h x h' \<pi>
  assume step: \<open>h \<leadsto>\<langle>e\<rangle> (x, h')\<close> and uc: \<open>ucincl \<pi>\<close>
                                and pre: \<open>h \<Turnstile> (P \<star> S) \<star> \<pi>\<close>
  have \<open>h \<Turnstile> P \<star> (S \<star> \<pi>)\<close> using pre by (simp add: asepconj_assoc)
  moreover have \<open>ucincl (S \<star> \<pi>)\<close> using uc by (rule ucincl_asepconjR)
  ultimately have \<open>h' \<Turnstile> Q x \<star> (S \<star> \<pi>)\<close>
    using assms step by (force simp: sltriple_def)
  thus \<open>h' \<Turnstile> (\<lambda>x. Q x \<star> S) x \<star> \<pi>\<close>
    by (simp add: asepconj_assoc)
qed

end_slide

interlude \<open>A peek ahead: real uRust (weak) triple\<close>

text_raw \<open>%
\begingroup
\renewenvironment{isabellebody}{}{}%
\renewcommand{\setisabellecontext}[1]{}%
\input{Tutorial_UrustPeek_Triple.tex}%
\endgroup
\<close>

end_interlude

slide \<open>WP, and triple-WP equivalence\<close>

text \<open>As in the first half, defining \<open>wp_sl e Q\<close> is the \<^bold>\<open>largest precondition\<close>
  making the triple hold:\<close>

definition wp_sl (\<open>\<W>\<P>\<close>) where \<open>\<W>\<P> e Q \<equiv> \<Union> {P. \<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>}\<close>

text \<open>By construction the triple is then \<^bold>\<open>represented\<close> by \<open>wp_sl\<close>:\<close>

lemma sltriple_wp_iff: 
  shows \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace> \<longleftrightarrow> P \<longlongrightarrow> \<W>\<P> e Q\<close>
proof
  assume \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close> thus \<open>P \<longlongrightarrow> \<W>\<P> e Q\<close>
    by (auto simp: wp_sl_def aentails_def asat_def)
next
  assume H: \<open>P \<longlongrightarrow> \<W>\<P> e Q\<close>
  show \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close> unfolding sltriple_def
  proof (intro allI impI)
    fix h x h' \<pi>
    assume st: \<open>h \<leadsto>\<langle>e\<rangle> (x, h')\<close> and uc: \<open>ucincl \<pi>\<close>
                                  and pre: \<open>h \<Turnstile> P \<star> \<pi>\<close>
    from pre obtain t u where \<open>h = t + u\<close> \<open>t \<sharp> u\<close> \<open>t \<Turnstile> P\<close> \<open>u \<Turnstile> \<pi>\<close>
      by (auto simp: asepconj_def asat_def)
    moreover from \<open>t \<Turnstile> P\<close> H obtain P' where \<open>\<lbrace>P'\<rbrace> e \<lbrace>Q\<rbrace>\<close> \<open>t \<Turnstile> P'\<close>
      by (auto simp: aentails_def wp_sl_def asat_def)
    ultimately have \<open>h \<Turnstile> P' \<star> \<pi>\<close>
      by (auto simp: asepconj_def asat_def)
    with \<open>\<lbrace>P'\<rbrace> e \<lbrace>Q\<rbrace>\<close> st uc show \<open>h' \<Turnstile> Q x \<star> \<pi>\<close>
      by (force simp: sltriple_def)
  qed
qed

text \<open>As before, weakest precondition rules for \<open>return\<close> and \<open>bind\<close>:\<close>

(*<*)
lemma wp_sl_return: \<open>Q x \<longlongrightarrow> \<W>\<P> (return x) Q\<close>
  unfolding sltriple_wp_iff[symmetric] sltriple_def
  by (auto simp: evals_def return_def)

lemma wp_sl_bind: \<open>\<W>\<P> e (\<lambda>x. \<W>\<P> (k x) Q) \<longlongrightarrow> \<W>\<P> (do { x \<leftarrow> e; k x }) Q\<close>
proof -
  have wp_self_e: \<open>\<lbrace>\<W>\<P> e (\<lambda>x. \<W>\<P> (k x) Q)\<rbrace> e \<lbrace>\<lambda>x. \<W>\<P> (k x) Q\<rbrace>\<close>
    using sltriple_wp_iff aentails_refl by metis
  have wp_self_k: \<open>\<And>x. \<lbrace>\<W>\<P> (k x) Q\<rbrace> k x \<lbrace>Q\<rbrace>\<close>
    using sltriple_wp_iff aentails_refl by metis
  have \<open>\<lbrace>\<W>\<P> e (\<lambda>x. \<W>\<P> (k x) Q)\<rbrace> do { x \<leftarrow> e; k x } \<lbrace>Q\<rbrace>\<close>
    using wp_self_e wp_self_k by (auto simp: sltriple_def evals_bind)
  thus ?thesis using sltriple_wp_iff by blast
qed

text \<open>\<^bold>\<open>Consequence form\<close> (rule shape, useful for back-chaining):\<close>
(*>*)

lemma wp_sl_returnI:
  assumes \<open>\<phi> \<longlongrightarrow> Q x\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> (return x) Q\<close>
  using assms by (rule aentails_trans[OF _ wp_sl_return])

text\<open>\<close>

lemma wp_sl_bindI:
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> e (\<lambda>x. \<W>\<P> (k x) Q)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> (do { x \<leftarrow> e; k x }) Q\<close>
  using assms by (rule aentails_trans[OF _ wp_sl_bind])

end_slide

slide \<open>The magic wand: spatial subtraction\<close>

text \<open>We need one more SL connective: the \<^bold>\<open>magic wand\<close> \<open>\<phi> \<Zsurj> \<psi>\<close>,
  intuitively ``the resources you'd need to add to \<open>\<phi>\<close>
  in order to obtain \<open>\<psi>\<close>'' -- \<^bold>\<open>spatial subtraction\<close>
  \<open>\<psi> - \<phi>\<close>.\<close>

text \<open>It's determined by its \<^bold>\<open>universal property\<close>: \<open>\<Zsurj>\<close> is
  right-adjoint to \<open>\<star>\<close>.\<close>

text \<open>@{thm [display, show_question_marks=false] awand_adjoint}\<close>

text \<open>Read left-to-right: to entail \<open>\<psi> \<Zsurj> \<xi>\<close>, it suffices to entail \<open>\<xi>\<close>
  after gluing on a \<open>\<psi>\<close>. Read right-to-left: anything entailed by
  \<open>\<phi> \<star> \<psi>\<close> can be ``factored'' as \<open>\<phi>\<close> entailing \<open>\<psi> \<Zsurj> ...\<close>. We use this
  in call-by-contract on the next slide.\<close>

end_slide

slide \<open>Call-by-contract, in SL\<close>

text \<open>As in the first half, a contract \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close> yields a WP rule:
  if the precondition entails \<open>P\<close> and the post can be \<^bold>\<open>swapped\<close> for
  \<open>R\<close> via the magic wand, the WP follows.\<close>

lemma sl_call_by_contractI:
  assumes \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close>
      and \<open>\<phi> \<longlongrightarrow> P \<star> (\<Sqinter>x. Q x \<Zsurj> R x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> wp_sl e R\<close>
proof -
  let ?W = \<open>\<Sqinter>x. Q x \<Zsurj> R x\<close>
  have step1: \<open>\<lbrace>P \<star> ?W\<rbrace> e \<lbrace>\<lambda>x. Q x \<star> ?W\<rbrace>\<close>
    using \<open>\<lbrace>P\<rbrace> e \<lbrace>Q\<rbrace>\<close> frame_rule by blast
  have step2: \<open>\<And>x. Q x \<star> ?W \<longlongrightarrow> R x\<close>
    by (meson aentails_forallL aentails_trans' asepconj_mono awand_counit)
  have step4: \<open>\<lbrace>P \<star> ?W\<rbrace> e \<lbrace>R\<rbrace>\<close>
    by (smt (verit, ccfv_threshold) aentails_def asat_def asepconj_def
        mem_Collect_eq sltriple_def step1 step2)
  from step4 \<open>\<phi> \<longlongrightarrow> P \<star> (\<Sqinter>x. Q x \<Zsurj> R x)\<close> show \<open>\<phi> \<longlongrightarrow> wp_sl e R\<close>
    using sltriple_wp_iff aentails_trans by metis
qed

text \<open>\<^bold>\<open>Intuition:\<close> Practically, the rule is applied as follows:
 \<^item> Find the pre-condition \<open>P\<close> in the LHS \<open>\<phi>\<close>
 \<^item> Cancel it, leaving \<open>\<Sqinter>x. Q x \<Zsurj> R x\<close> on the RHS.
 \<^item> Move the post-condition \<open>Q x\<close> over to the LHS by adjunction.
 \<^item> Continue, with \<open>P\<close> now being a new assumption.

In effect, one has simply "swapped" the precondition \<open>P\<close> for the post-condition \<open>Q\<close>.
This usage pattern for the magic wand is extremely common.\<close>

end_slide

interlude \<open>A peek ahead: real uRust call-by-contract\<close>

text_raw \<open>%
\begingroup
\renewenvironment{isabellebody}{}{}%
\renewcommand{\setisabellecontext}[1]{}%
\input{Tutorial_UrustPeek_Call.tex}%
\endgroup
\<close>

end_interlude

slide \<open>Working example: Setup\<close>

text \<open>We rerun the increment example, this time with SL contracts. The
  state monad over \<open>twoint_sl\<close> is exactly the toy monad from the first
  half; the only new ingredient is the SL triple.\<close>

text \<open>Generic \<open>get\<close>/\<open>put\<close> on the heap:\<close>

definition get :: \<open>(twoint_sl, twoint_sl) m\<close> where
  \<open>get = M (\<lambda>h. {(h, h)})\<close>

definition put :: \<open>twoint_sl \<Rightarrow> (twoint_sl, unit) m\<close> where
  \<open>put h' = M (\<lambda>_. {((), h')})\<close>

end_slide

slide \<open>Working example: Per-field reads and writes\<close>

text \<open>Per-field operations follow the same shape as in the Hoare chapter:\<close>

definition get_x :: \<open>(twoint_sl, int) m\<close> where
  \<open>get_x = M (\<lambda>h. {(the (h FX), h)})\<close>

definition put_x :: \<open>int \<Rightarrow> (twoint_sl, unit) m\<close> where
  \<open>put_x v = M (\<lambda>h. {((), h(FX \<mapsto> v))})\<close>

definition get_y :: \<open>(twoint_sl, int) m\<close> where
  \<open>get_y = M (\<lambda>h. {(the (h FY), h)})\<close>

definition put_y :: \<open>int \<Rightarrow> (twoint_sl, unit) m\<close> where
  \<open>put_y v = M (\<lambda>h. {((), h(FY \<mapsto> v))})\<close>

end_slide

slide \<open>Working example: Local SL contracts for get/put\<close>

text \<open>Each operation gets a contract that mentions \<^emph>\<open>only\<close> the cell it
  touches -- no \<open>fy\<close>-conjunct on a \<open>get_x\<close> spec, no framing noise. The
  frame rule will absorb whatever else is in the heap.\<close>

(*<*)
lemma ucincl_pto[ucincl_intros]: \<open>ucincl (f \<mapsto> v)\<close>
  unfolding pto_def ucincl_def ucpred_def derived_order_def
  by (clarsimp simp: plus_fun_def plus_option_def disjoint_fun_def disjoint_option_def
                split: option.splits)

lemma get_x_triple: \<open>\<lbrace>FX \<mapsto> v\<rbrace> get_x \<lbrace>\<lambda>r. \<langle>r = v\<rangle> \<star> FX \<mapsto> v\<rbrace>\<close>
  unfolding sltriple_def
proof (intro allI impI)
  fix h x h' \<pi>
  assume step: \<open>h \<leadsto>\<langle>get_x\<rangle> (x, h')\<close> and uc: \<open>ucincl \<pi>\<close>
                                       and pre: \<open>h \<Turnstile> FX \<mapsto> v \<star> \<pi>\<close>
  from step have h_eq: \<open>h' = h\<close> and x_eq: \<open>x = the (h FX)\<close>
    by (auto simp: evals_def get_x_def)
  from pre obtain t u where \<open>h = t + u\<close> \<open>t \<sharp> u\<close> \<open>t FX = Some v\<close> \<open>u \<Turnstile> \<pi>\<close>
    by (auto simp: asepconj_def asat_def pto_def)
  hence \<open>h FX = Some v\<close>
    by (auto simp: plus_fun_def plus_option_def
                   disjoint_fun_def disjoint_option_def split: option.splits)
  hence pure_eq: \<open>\<langle>x = v\<rangle> = (UNIV :: twoint_sl assert)\<close>
    using x_eq by (simp add: apure_def)
  have \<open>ucincl ((FX \<mapsto> v) :: twoint_sl assert)\<close> by (rule ucincl_pto)
  thus \<open>h' \<Turnstile> (\<langle>x = v\<rangle> \<star> FX \<mapsto> v) \<star> \<pi>\<close>
    using pre h_eq pure_eq by (simp add: asepconj_simp asepconj_assoc)
qed

lemma put_x_triple: \<open>\<lbrace>FX \<mapsto> u\<rbrace> put_x v \<lbrace>\<lambda>_. FX \<mapsto> v\<rbrace>\<close>
  unfolding sltriple_def
proof (intro allI impI)
  fix h x h' \<pi>
  assume step: \<open>h \<leadsto>\<langle>put_x v\<rangle> (x, h')\<close> and uc: \<open>ucincl \<pi>\<close>
                                         and pre: \<open>h \<Turnstile> FX \<mapsto> u \<star> \<pi>\<close>
  from step have h'_eq: \<open>h' = h(FX \<mapsto> v)\<close>
    by (auto simp: evals_def put_x_def)
  from pre obtain t r where split: \<open>h = t + r\<close> and disj: \<open>t \<sharp> r\<close>
                          and tFX: \<open>t FX = Some u\<close> and rR: \<open>r \<Turnstile> \<pi>\<close>
    by (auto simp: asepconj_def asat_def pto_def)
  from disj tFX have rFX: \<open>r FX = None\<close>
    by (force simp: disjoint_fun_def disjoint_option_def split: option.splits)
  define t' where t'_def: \<open>t' = t(FX \<mapsto> v)\<close>
  have t'FX: \<open>t' FX = Some v\<close> by (simp add: t'_def)
  have disj': \<open>t' \<sharp> r\<close>
    using disj rFX unfolding t'_def disjoint_fun_def disjoint_option_def
    by (clarsimp split: option.splits)
  have h'_split: \<open>h' = t' + r\<close>
    using h'_eq split rFX
    unfolding t'_def plus_fun_def fun_eq_iff
    by (auto simp: plus_option_def split: option.splits)
  show \<open>h' \<Turnstile> (\<lambda>_. FX \<mapsto> v) x \<star> \<pi>\<close>
    using disj' h'_split t'FX rR
    unfolding asepconj_def asat_def pto_def by blast
qed

lemma get_y_triple: \<open>\<lbrace>FY \<mapsto> v\<rbrace> get_y \<lbrace>\<lambda>r. \<langle>r = v\<rangle> \<star> FY \<mapsto> v\<rbrace>\<close>
  unfolding sltriple_def
proof (intro allI impI)
  fix h x h' \<pi>
  assume step: \<open>h \<leadsto>\<langle>get_y\<rangle> (x, h')\<close> and uc: \<open>ucincl \<pi>\<close>
                                       and pre: \<open>h \<Turnstile> FY \<mapsto> v \<star> \<pi>\<close>
  from step have h_eq: \<open>h' = h\<close> and x_eq: \<open>x = the (h FY)\<close>
    by (auto simp: evals_def get_y_def)
  from pre obtain t u where \<open>h = t + u\<close> \<open>t \<sharp> u\<close> \<open>t FY = Some v\<close> \<open>u \<Turnstile> \<pi>\<close>
    by (auto simp: asepconj_def asat_def pto_def)
  hence \<open>h FY = Some v\<close>
    by (auto simp: plus_fun_def plus_option_def
                   disjoint_fun_def disjoint_option_def split: option.splits)
  hence pure_eq: \<open>\<langle>x = v\<rangle> = (UNIV :: twoint_sl assert)\<close>
    using x_eq by (simp add: apure_def)
  have \<open>ucincl ((FY \<mapsto> v) :: twoint_sl assert)\<close> by (rule ucincl_pto)
  thus \<open>h' \<Turnstile> (\<langle>x = v\<rangle> \<star> FY \<mapsto> v) \<star> \<pi>\<close>
    using pre h_eq pure_eq by (simp add: asepconj_simp asepconj_assoc)
qed

lemma put_y_triple: \<open>\<lbrace>FY \<mapsto> u\<rbrace> put_y v \<lbrace>\<lambda>_. FY \<mapsto> v\<rbrace>\<close>
  unfolding sltriple_def
proof (intro allI impI)
  fix h x h' \<pi>
  assume step: \<open>h \<leadsto>\<langle>put_y v\<rangle> (x, h')\<close> and uc: \<open>ucincl \<pi>\<close>
                                         and pre: \<open>h \<Turnstile> FY \<mapsto> u \<star> \<pi>\<close>
  from step have h'_eq: \<open>h' = h(FY \<mapsto> v)\<close>
    by (auto simp: evals_def put_y_def)
  from pre obtain t r where split: \<open>h = t + r\<close> and disj: \<open>t \<sharp> r\<close>
                          and tFY: \<open>t FY = Some u\<close> and rR: \<open>r \<Turnstile> \<pi>\<close>
    by (auto simp: asepconj_def asat_def pto_def)
  from disj tFY have rFY: \<open>r FY = None\<close>
    by (force simp: disjoint_fun_def disjoint_option_def split: option.splits)
  define t' where t'_def: \<open>t' = t(FY \<mapsto> v)\<close>
  have t'FY: \<open>t' FY = Some v\<close> by (simp add: t'_def)
  have disj': \<open>t' \<sharp> r\<close>
    using disj rFY unfolding t'_def disjoint_fun_def disjoint_option_def
    by (clarsimp split: option.splits)
  have h'_split: \<open>h' = t' + r\<close>
    using h'_eq split rFY
    unfolding t'_def plus_fun_def fun_eq_iff
    by (auto simp: plus_option_def split: option.splits)
  show \<open>h' \<Turnstile> (\<lambda>_. FY \<mapsto> v) x \<star> \<pi>\<close>
    using disj' h'_split t'FY rR
    unfolding asepconj_def asat_def pto_def by blast
qed
(*>*)

text \<open>
\<^item> @{thm [show_question_marks=false] get_x_triple}
\<^item> @{thm [show_question_marks=false] put_x_triple}
\<^item> @{thm [show_question_marks=false] get_y_triple}
\<^item> @{thm [show_question_marks=false] put_y_triple}
\<close>

text \<open>From each contract, \<open>sl_call_by_contractI\<close> gives a back-chainable
  WP rule:\<close>

lemma get_x_wp: \<open>\<phi> \<longlongrightarrow> FX \<mapsto> v \<star> (\<Sqinter>r. (\<langle>r = v\<rangle> \<star> FX \<mapsto> v) \<Zsurj> R r) \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> get_x R\<close>
  using get_x_triple sl_call_by_contractI by blast
text\<open>\<close>
lemma put_x_wp: \<open>\<phi> \<longlongrightarrow> FX \<mapsto> u \<star> (\<Sqinter>r. FX \<mapsto> v \<Zsurj> R r) \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> (put_x v) R\<close>
  using put_x_triple sl_call_by_contractI by blast

(*<*)
lemma get_y_wp: \<open>\<phi> \<longlongrightarrow> FY \<mapsto> v \<star> (\<Sqinter>r. (\<langle>r = v\<rangle> \<star> FY \<mapsto> v) \<Zsurj> R r) \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> get_y R\<close>
  using get_y_triple sl_call_by_contractI by blast

lemma put_y_wp: \<open>\<phi> \<longlongrightarrow> FY \<mapsto> u \<star> (\<Sqinter>r. FY \<mapsto> v \<Zsurj> R r) \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> (put_y v) R\<close>
  using put_y_triple sl_call_by_contractI by blast
(*>*)

end_slide

slide \<open>Working example: Proving \<open>foo\<close>\<close>

definition foo :: \<open>(twoint_sl, unit) m\<close> where
  \<open>foo = do { v \<leftarrow> get_x; put_x (v + 1) }\<close>

lemma %visible foo_spec: \<open>\<lbrace>FX \<mapsto> v\<rbrace> foo \<lbrace>\<lambda>_. FX \<mapsto> (v + 1)\<rbrace>\<close>
  unfolding sltriple_wp_iff foo_def
  apply (rule wp_sl_bindI)
  apply (rule get_x_wp[where v=v])
  apply (rule asepconj_mono5)
  apply (rule ucincl_pto)
  apply (rule aentails_intro(10))
  apply (subst awand_adjoint)
  apply (subst asepconj_swap_top)
  apply (rule apure_entailsL)
  \<comment>\<open>...\<close>
  (*<*)
  subgoal by (auto intro: ucincl_intros)
  apply simp
  apply (subst asepconj_comm)
  apply (subst asepconj_ident2)
  apply (rule ucincl_pto)
  apply (rule put_x_wp[where u=v])
  apply (rule asepconj_mono5)
  apply (rule ucincl_pto)
  apply (rule aentails_intro(10))
  apply (subst awand_adjoint)
  apply (rule aentails_cancel_l)
  apply (rule ucincl_pto)
  done
  (*>*)

(*<*)
lemma foo_wp: \<open>\<phi> \<longlongrightarrow> FX \<mapsto> v \<star> (\<Sqinter>r. FX \<mapsto> (v + 1) \<Zsurj> R r) \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> foo R\<close>
  using foo_spec sl_call_by_contractI by blast
(*>*)

end_slide

slide \<open>Working example: Proving \<open>bar\<close> -- by contract\<close>

definition bar :: \<open>(twoint_sl, int) m\<close> where
  \<open>bar = do { put_y 42; foo; get_y }\<close>

lemma %visible bar_spec: \<open>\<lbrace>FX \<mapsto> x \<star> FY \<mapsto> y\<rbrace> bar \<lbrace>\<lambda>r. \<langle>r = 42\<rangle> \<star> FX \<mapsto> (x + 1) \<star> FY \<mapsto> 42\<rbrace>\<close>
  unfolding sltriple_wp_iff bar_def
  apply (rule wp_sl_bindI)
  apply (rule put_y_wp[where u=y])
  apply (subst (1) asepconj_comm)
  apply (rule asepconj_mono)
  apply (rule aentails_intro(10))
  apply (subst awand_adjoint)
  apply (rule wp_sl_bindI)
  apply (rule foo_wp[where v=x])
  apply (rule asepconj_mono)
  \<comment>\<open>...\<close>
  (*<*)
  apply (rule aentails_intro(10))
  apply (subst awand_adjoint)
  apply (rule get_y_wp[where v=42])
  apply (rule asepconj_mono)
  apply (rule aentails_intro(10))
  apply (subst awand_adjoint)
  apply (simp add: asepconj_AC)
  apply (rule aentails_refl)
  done
  (*>*)

end_slide

slide \<open>To be continued ...\<close>

text_raw \<open>\vfill\begin{center}\Huge To be continued ...\end{center}\vfill\<close>

end_slide

end
