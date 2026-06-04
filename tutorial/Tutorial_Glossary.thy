theory Tutorial_Glossary
  imports Main Slides
begin

slide \<open>HOL-Light \<open>\<rightarrow>\<close> Isabelle: the logical core\<close>

text \<open>HOL-Light and Isabelle/HOL share the \<^bold>\<open>same logical core\<close>:
  classical, polymorphic higher-order logic. Both build the
  propositional connectives and quantifiers from equality and \<open>\<lambda>\<close>.
  The literal kernel definitions, side by side (HOL-Light
  \<^verbatim>\<open>bool.ml\<close> vs.\ Isabelle \<^verbatim>\<open>HOL.thy\<close>):\<close>

text_raw \<open>
\begin{center}\scriptsize
\begin{tabular}{c l l}
       & \textbf{HOL-Light} & \textbf{Isabelle/HOL} \\
\hline
$\top$ & \texttt{T = ($\lambda$p. p) = ($\lambda$p. p)} & \texttt{True $\equiv$ ($\lambda$x. x) = ($\lambda$x. x)} \\
$\land$ & \texttt{$\land$ = $\lambda$p q. ($\lambda$f. f p q) = ($\lambda$f. f T T)} & \texttt{P $\land$ Q $\equiv$ $\forall$R. (P $\to$ Q $\to$ R) $\to$ R} \\
$\to$ & \texttt{$\to$ = $\lambda$p q. p $\land$ q $\Leftrightarrow$ p} & \emph{axiomatised (\texttt{impI}, \texttt{mp})} \\
$\forall$ & \texttt{$\forall$ = $\lambda$P. P = $\lambda$x. T} & \texttt{All P $\equiv$ (P = ($\lambda$x. True))} \\
$\exists$ & \texttt{$\exists$ = $\lambda$P. $\forall$q. ($\forall$x. P x $\to$ q) $\to$ q} & \texttt{Ex P $\equiv$ $\forall$Q. ($\forall$x. P x $\to$ Q) $\to$ Q} \\
$\bot$ & \texttt{F = $\forall$p. p} & \texttt{False $\equiv$ ($\forall$P. P)} \\
$\lnot$ & \texttt{$\lnot$ = $\lambda$p. p $\to$ F} & \texttt{$\lnot$ P $\equiv$ P $\to$ False} \\
$\lor$ & \texttt{$\lor$ = $\lambda$p q. $\forall$r. (p $\to$ r) $\to$ (q $\to$ r) $\to$ r} & \texttt{P $\lor$ Q $\equiv$ $\forall$R. (P $\to$ R) $\to$ (Q $\to$ R) $\to$ R} \\
\end{tabular}
\end{center}
\<close>

text \<open>\<^bold>\<open>Differences.\<close> Only \<open>\<and>\<close> and \<open>\<longrightarrow>\<close> diverge.
  HOL-Light uses Andrews' \<^emph>\<open>pairing trick\<close> for \<open>\<and>\<close>; Isabelle uses
  the impredicative \<open>\<forall>R. \<dots>\<close> encoding (cleaner to reason with).
  HOL-Light defines \<open>\<longrightarrow>\<close> from \<open>\<and>\<close>; Isabelle introduces it as an
  uninterpreted \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> constant via \<^verbatim>\<open>axiomatization\<close>
  in \<open>HOL.thy\<close>, governed by the rules \<^verbatim>\<open>impI\<close> and \<^verbatim>\<open>mp\<close>.\<close>

end_slide


slide \<open>What Isabelle adds on top\<close>

text \<open>Same logical kernel, \<^emph>\<open>but\<close> Isabelle layers more conveniences
  on top:

  \<^item> \<^bold>\<open>Isar\<close>: a structured proof language;

  \<^item> \<^bold>\<open>locales\<close> -- parametrised theory sections;

  \<^item> \<^bold>\<open>code generation\<close> to OCaml / Haskell / Scala / SML;

  \<^item> \<^bold>\<open>interactive editing\<close> (PIDE) with continuous proof checking;

  \<^item> a \<^bold>\<open>document preparation\<close> system (these slides are an example).\<close>

text \<open>None of these enlarge the trust base -- they all reduce to the same
underlying axioms -- but they change the day-to-day experience of
writing proofs.\<close>

end_slide


slide \<open>HOL-Light \<open>\<rightarrow>\<close> Isabelle: types and terms\<close>

text \<open>\<^bold>\<open>Type variables.\<close>
  HOL-Light: \<^verbatim>\<open>`!x:A. P x ==> P x`\<close>.
  Isabelle: \<open>\<forall>x::'a. P x \<longrightarrow> P x\<close>.

  \<^bold>\<open>Function type.\<close>
  HOL-Light: \<^verbatim>\<open>`:A->B`\<close>.
  Isabelle: @{typ \<open>'a \<Rightarrow> 'b\<close>}.

  \<^bold>\<open>Polymorphism.\<close>
  As in HOL-Light, type parameters are written \<^emph>\<open>on the left\<close>:
  @{typ \<open>'a list\<close>} is the type of lists over \<open>'a\<close>.

  \<^bold>\<open>Equality, iff.\<close>
  HOL-Light: \<^verbatim>\<open>`x = y`\<close>, \<^verbatim>\<open>`P <=> Q`\<close>.
  Isabelle: \<open>x = y\<close>, \<open>P \<longleftrightarrow> Q\<close>. The two are equal on \<open>bool\<close>;
  the \<open>\<longleftrightarrow>\<close> form just marks intent.

  \<^bold>\<open>Schematic variables.\<close>
  HOL-Light: shown as plain free variables in goals.
  Isabelle: shown with a question mark in stored facts; e.g.\
  the elimination rule
  @{thm [show_question_marks] conjE}.\<close>

end_slide


slide \<open>HOL-Light \<open>\<rightarrow>\<close> Isabelle: definitions\<close>

text \<open>\<^bold>\<open>Plain definition.\<close> HOL-Light:

  \<^verbatim>\<open>let double = new_definition `double x = x + x`;;\<close>

  Isabelle:\<close>

definition double :: \<open>nat \<Rightarrow> nat\<close>
    \<comment> \<open>type may be omitted; the most general type is inferred\<close>
  where \<open>double x = x + x\<close>

text \<open>\<^bold>\<open>Recursive function.\<close> HOL-Light:

  \<^verbatim>\<open>let LEN = define `LEN [] = 0 /\ LEN (CONS x xs) = SUC (LEN xs)`;;\<close>

  Isabelle:\<close>

fun len :: \<open>'a list \<Rightarrow> nat\<close> where
  \<open>len [] = 0\<close>
| \<open>len (x # xs) = Suc (len xs)\<close>

text %internal \<open>Inductive definition (kept in the .thy as an example
  but hidden from the slide -- already crowded).\<close>

inductive %internal even' :: \<open>nat \<Rightarrow> bool\<close> where
  even_zero: \<open>even' 0\<close>
| even_step: \<open>even' n \<Longrightarrow> even' (Suc (Suc n))\<close>

end_slide


slide \<open>HOL-Light \<open>\<rightarrow>\<close> Isabelle: data\<close>

text \<open>\<^bold>\<open>Algebraic datatypes.\<close> HOL-Light:

  \<^verbatim>\<open>let option_INDUCT,option_RECURSION =
    define_type "option = NONE | SOME A";;\<close>

  Isabelle:\<close>

datatype 'a opt = NONE | SOME 'a

text \<open>\<^bold>\<open>Records.\<close> Recent HOL-Light has them too (J.\ Harrison,
  2023); Isabelle's are older and slightly fancier (anonymous
  functional update built in). Field accessors and a functional
  update operator come from one declaration:\<close>

record point =
  px :: int
  py :: int

text \<open>The functional update \<open>p\<lparr>px := 7\<rparr>\<close> reads ``\<open>p\<close> with \<open>px\<close>
  set to \<open>7\<close>''. We use this throughout the Hoare-logic worked example.\<close>

end_slide


slide \<open>HOL-Light \<open>\<rightarrow>\<close> Isabelle: tactic proofs\<close>

text \<open>\<^bold>\<open>Tactic-only\<close>: same content, different syntax. HOL-Light:

  \<^verbatim>\<open>let DOUBLE_THM = prove(`double x = 2 * x`,
    REWRITE_TAC[double] THEN ARITH_TAC);;\<close>

  Isabelle equivalent:\<close>

text_raw \<open>\isakeeptag{proof}\<close>

lemma double_thm: \<open>double x = 2 * x\<close>
    \<comment> \<open>\<open>simp\<close>: Isabelle's simplifier\<close>
    \<comment> \<open>\<open>add: double_def\<close>: register the defining equation as a rewrite rule\<close>
  by (simp add: double_def)

text_raw \<open>\isadroptag{proof}\<close>

text \<open>\<^bold>\<open>Case expressions.\<close> HOL-Light: \<^verbatim>\<open>match x with NONE -> 0 | SOME y -> y\<close>.
  Isabelle:\<close>

definition unopt :: \<open>nat option \<Rightarrow> nat\<close> where
  \<open>unopt x = (case x of None \<Rightarrow> 0 | Some y \<Rightarrow> y)\<close>

end_slide


slide \<open>HOL-Light \<open>\<rightarrow>\<close> Isabelle: structured proofs\<close>

text \<open>Apply-style and HOL-Light tactics are \<^bold>\<open>backward\<close> reasoning:
  start from the goal, peel rules off until the trivial.

  \<^bold>\<open>Structured (Isar)\<close>, by contrast, is \<^bold>\<open>forward\<close> reasoning -- the
  way humans write proofs on paper.\<close>

text \<open>\<^bold>\<open>Example:\<close>\<close>

text_raw \<open>\isakeeptag{proof}\<close>

lemma len_append: \<open>len (xs @ ys) = len xs + len ys\<close>
proof (induction xs)
  case Nil
  show \<open>len ([] @ ys) = len [] + len ys\<close> by simp
next
  case (Cons x xs)
  have \<open>len ((x # xs) @ ys) = Suc (len (xs @ ys))\<close> by simp
  also have \<open>\<dots> = Suc (len xs + len ys)\<close> using Cons.IH by simp
  also have \<open>\<dots> = len (x # xs) + len ys\<close> by simp
  finally show ?case .
qed

text_raw \<open>\isadroptag{proof}\<close>

end_slide

(*<*)
slide \<open>HOL-Light analogue: \<^verbatim>\<open>LIST_INDUCT_TAC\<close>\<close>

text \<open>HOL-Light has no \<open>induction\<close> keyword, but the same proof goes
  through with the corresponding induction tactic:\<close>

text \<open>\<^verbatim>\<open>let LEN_APPEND = prove
 (`!xs ys. LEN (APPEND xs ys) = LEN xs + LEN ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LEN; APPEND; ADD; ADD_SUC]);;\<close>\<close>

text \<open>\<^verbatim>\<open>LIST_INDUCT_TAC\<close> splits the goal into a \<open>Nil\<close> case and a
  \<open>Cons\<close> case (with induction hypothesis available);
  \<^verbatim>\<open>ASM_REWRITE_TAC\<close> rewrites with \<open>LEN\<close>/\<open>APPEND\<close> and the
  hypothesis, playing the role of Isar's calculational chain.\<close>

end_slide
(*>*)

slide \<open>Locales: parametrised theory sections\<close>

text \<open>A \<^bold>\<open>locale\<close> is a named, reusable bundle of \<^bold>\<open>parameters\<close> and
  \<^bold>\<open>assumptions\<close>. Example:\<close>

locale toy_monoid =
  fixes mul :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixl \<open>\<otimes>\<close> 70)
    and one :: \<open>'a\<close>
  assumes assoc:    \<open>(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)\<close>
      and ident_l:  \<open>one \<otimes> x = x\<close>
      and ident_r:  \<open>x \<otimes> one = x\<close>

text \<open>Inside \<open>context toy_monoid begin \<dots> end\<close> the parameters and
  assumptions are in scope; outside, every \<open>toy_monoid\<close>-statement is
  implicitly universally quantified over them.\<close>

text \<open>Alternatively, use \<open>(in locale)\<close> to enter a locale context for
  a single command. E.g.:\<close>

text_raw \<open>\isakeeptag{proof}\<close>

lemma (in toy_monoid) example: \<open>(x \<otimes> one) \<otimes> y = x \<otimes> y\<close>
  by (simp add: ident_r)

text_raw \<open>\isadroptag{proof}\<close>

end_slide


slide \<open>Locales vs. type classes\<close>

text \<open>Isabelle has both. Both are mechanisms for parametrised
  reasoning; they differ in what they parametrise over.

  \<^bold>\<open>Type classes\<close> parametrise over a \<^bold>\<open>single type variable\<close> and use
  automatic resolution: \<open>'a :: monoid\<close> means ``\<open>'a\<close> happens to be a
  monoid'', and the typechecker dispatches operations like \<open>\<otimes>\<close>
  silently. Good for hierarchies of types (\<open>monoid\<close>, \<open>group\<close>, \<open>ring\<close>, ...).

  \<^bold>\<open>Locales\<close> parametrise over \<^bold>\<open>an arbitrary signature\<close>: any number
  of fixes plus assumptions, no automatic resolution. Better for
  abstract interfaces with multiple parameters of unrelated types.

  Convenient, though HOL-Light proves one can be successful
  without them.\<close>

end_slide


slide \<open>Locales in AutoCorrode\<close>

text \<open>AutoCorrode involves various locale interfaces; a few
  representative examples:

  \<^item> \<open>sepalg\<close> -- the abstract \<^bold>\<open>separation algebra\<close>: a partial
    commutative monoid. Carrier type, \<open>+\<close>, \<open>0\<close>, disjointness.
    Almost all SL theorems are stated in this locale.

  \<^item> \<open>reference\<close> -- the abstract \<^bold>\<open>heap interface\<close>: allocate,
    dereference, update typed references. Multiple interpretations
    ship (abstract heap, physical-memory byte arrays, ...).\<close>

text \<open>\<^bold>\<open>Pattern.\<close> State the verification once in the abstract locale;
  \<^bold>\<open>interpret\<close> it for each concrete heap. The same proof works against
  the abstract heap and against the physical-memory model.\<close>

end_slide


slide \<open>Document preparation\<close>

text \<open>Isabelle ships a \<^bold>\<open>document preparation system\<close>: every \<open>.thy\<close>
  file is also a typeset document. \<open>text \<open>...\<close>\<close> blocks are prose;
  \<^bold>\<open>antiquotations\<close> like \<open>@{thm name}\<close>, \<open>@{term \<dots>}\<close>, \<open>@{datatype t}\<close>
  splice the \<^emph>\<open>real, type-checked\<close> theorem / term / datatype into the
  prose at build time.\<close>

text \<open>Concretely: this slide's source contains the antiquotation
  \<open>@{thm double_thm}\<close>, and yields\<close>

text \<open>@{thm double_thm}\<close>

text \<open>-- the proven statement, type-checked at build time. If
  \<open>double\<close> is renamed, the slide breaks. If the lemma stops being
  true, the slide doesn't build. \<^bold>\<open>These slides were produced this
  way\<close>: every formal artifact you have seen and will see is live.\<close>

end_slide


end

