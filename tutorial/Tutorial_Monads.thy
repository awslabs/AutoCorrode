theory Tutorial_Monads
  imports
    Main
    "HOL-Library.Monad_Syntax"
    Slides
    Shallow_Micro_Rust.Core_Expression
begin

slide \<open>Why monads?\<close>

text \<open>\<^bold>\<open>Goal:\<close> model imperative programs in HOL -- a pure, total,
  logical setting -- without losing:\<close>

text \<open>
  \<^item> sequential composition (``do this, then that'');

  \<^item> intermediate values getting \<^bold>\<open>named\<close>;

  \<^item> separation of concerns: the threading of effects (state,
    exceptions, ...) does not pollute the program's logic.\<close>

text \<open>\<^bold>\<open>Monads\<close> are the abstraction that makes this work.\<close>

end_slide


slide \<open>Pure computation: just \<open>let\<close>-binding\<close>

text \<open>Suppose our toy language has \<^emph>\<open>no state, no errors, no
  side-effects\<close> -- just pure computation with immutable variables.
  Then a program can be modeled as a sequence of \<open>let\<close>-bindings, with
  each \<open>let\<close> playing the role of a semicolon:\<close>

text_raw \<open>%
\begin{minipage}[t]{0.48\linewidth}\centering
\textbf{Imperative}\\[1mm]
\begin{minipage}{\linewidth}\small\ttfamily
const T0 a = head(xs);\\
const T1 b = encrypt(k, a);\\
const T2 c = encode(b);\\
return c;
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.48\linewidth}\centering
\textbf{HOL}\\[1mm]
\begin{minipage}{\linewidth}\small\ttfamily
\<open>let a = head xs in\<close>\\
\<open>let b = encrypt k a in\<close>\\
\<open>let c = encode b in\<close>\\
\<open>c\<close>
\end{minipage}
\end{minipage}%
\<close>

text \<open>\<^bold>\<open>Type:\<close> a program with input \<open>'a\<close> and output \<open>'b\<close> is just
  @{typ \<open>'a \<Rightarrow> 'b\<close>}.\<close>

end_slide


slide \<open>+ scratch state: thread it through\<close>

text \<open>Now suppose programs may \<^bold>\<open>read and write\<close> a global
  ``scratch space'' \<open>'s\<close>. Each step receives the previous step's
  state and returns an updated one:\<close>

text_raw \<open>%
\begin{minipage}[t]{0.48\linewidth}\centering
\textbf{Imperative}\\[1mm]
\begin{minipage}{\linewidth}\small\ttfamily
const T0 a = read();\\
write(hash(a));\\
const T0 b = read();\\
return b;
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.48\linewidth}\centering
\textbf{HOL (let-threaded)}\\[1mm]
\begin{minipage}{\linewidth}\scriptsize\ttfamily
\<open>let (a, s\<^sub>1) = read s\<^sub>0   in\<close>\\
\<open>let (h, s\<^sub>2) = hash a s\<^sub>1 in\<close>\\
\<open>let ((), s\<^sub>3) = write h s\<^sub>2 in\<close>\\
\<open>let (b, s\<^sub>4) = read s\<^sub>3   in\<close>\\
\<open>(b, s\<^sub>4)\<close>
\end{minipage}
\end{minipage}%
\<close>

text \<open>\<^bold>\<open>Type:\<close> a program with input \<open>'a\<close>, output \<open>'b\<close>, threading state
  \<open>'s\<close> is @{typ \<open>'a \<Rightarrow> 's \<Rightarrow> 's \<times> 'b\<close>}.\<close>

text \<open>\<^bold>\<open>Question:\<close> Can we hide the threading of the state?\<close>

end_slide


slide \<open>+ scratch state: hiding the threading\<close>

text \<open>Define combinator \<open>state_bind\<close> that runs a step and threads the
  result into the next:\<close>

(*<*)experiment begin(*>*) (* Local; re-stated later for the example slide *)
definition state_return :: \<open>'a \<Rightarrow> 's \<Rightarrow> 'a \<times> 's\<close> where
  \<open>state_return x s = (x, s)\<close>

definition state_bind ::
    \<open>('s \<Rightarrow> 'a \<times> 's) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'b \<times> 's) \<Rightarrow> ('s \<Rightarrow> 'b \<times> 's)\<close> where
  \<open>state_bind f g s = (let (x, s') = f s in g x s')\<close>
(*<*)end(*>*)

text \<open>The same program in both styles -- the right column has \<^emph>\<open>no\<close> \<open>s\<^sub>i\<close>:\<close>

text_raw \<open>%
\begin{minipage}[t]{0.48\linewidth}\centering
\textbf{HOL (let-threaded)}\\[1mm]
\begin{minipage}{\linewidth}\scriptsize\ttfamily
\<open>let (a, s\<^sub>1) = read s\<^sub>0   in\<close>\\
\<open>let (h, s\<^sub>2) = hash a s\<^sub>1 in\<close>\\
\<open>let ((), s\<^sub>3) = write h s\<^sub>2 in\<close>\\
\<open>let (b, s\<^sub>4) = read s\<^sub>3   in\<close>\\
\<open>(b, s\<^sub>4)\<close>
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.48\linewidth}\centering
\textbf{Compact (\<open>state_bind\<close>)}\\[1mm]
\begin{minipage}{\linewidth}
\begin{alltt}\scriptsize
\<open>state_bind read       (\<lambda>a.\<close>
\<open>state_bind (hash a)   (\<lambda>h.\<close>
\<open>state_bind (write h)  (\<lambda>_.\<close>
\<open>state_bind read       (\<lambda>b.\<close>
\<open>state_return b))))\<close>
\end{alltt}
\end{minipage}
\end{minipage}%
\<close>

end_slide


slide \<open>+ errors: \<open>None\<close> short-circuits\<close>

text \<open>Drop the state again. Suppose programs may \<^bold>\<open>abort\<close> -- e.g.\
  divide-by-zero, missing key. Represent ``maybe a result'' by
  @{typ \<open>'b option\<close>}. Chaining means: if the previous step
  succeeded, continue; otherwise propagate the abort:\<close>

text_raw \<open>%
\begin{minipage}[t]{0.26\linewidth}\centering
\textbf{Imperative}\\[1mm]
\begin{minipage}{\linewidth}\scriptsize\ttfamily
const T0 a = lookup(k);\\
const T1 b = decrypt(a, ct);\\
return verify(b);
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.32\linewidth}\centering
\textbf{HOL (case)}\\[1mm]
\begin{minipage}{\linewidth}
\begin{alltt}\tiny
\<open>case lookup k of\<close>
  \<open>None \<Rightarrow> None\<close>
\<open>|\<close> \<open>Some a \<Rightarrow>\<close>
    \<open>case decrypt a ct of\<close>
      \<open>None \<Rightarrow> None\<close>
    \<open>|\<close> \<open>Some b \<Rightarrow> Some (verify b)\<close>
\end{alltt}
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.40\linewidth}\centering
\textbf{Compact (\<open>option_bind\<close>)}\\[1mm]
\begin{minipage}{\linewidth}
\begin{alltt}\tiny
\<open>option_bind (lookup k) (\<lambda>a.\<close>
\<open>option_bind (decrypt a ct) (\<lambda>b.\<close>
\<open>Some (verify b)))\<close>
\end{alltt}
\end{minipage}
\end{minipage}%
\<close>

text \<open>\<^bold>\<open>Type:\<close> @{typ \<open>'a \<Rightarrow> 'b option\<close>}. Combinator hides case-bookkeeping
  (also available in HOL as @{const Option.bind}):\<close>

(*<*)experiment begin(*>*) (* Local; re-stated later if needed *)
definition option_bind :: \<open>'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option\<close> where
  \<open>option_bind f g = (case f of None \<Rightarrow> None | Some x \<Rightarrow> g x)\<close>
(*<*)end(*>*)

end_slide


slide \<open>+ non-determinism: a list of outcomes\<close>

text \<open>Drop state and errors. Suppose programs may \<^bold>\<open>fork\<close> -- i.e.\
  return any of several possible results. Represent ``possible
  outcomes'' as a \<^emph>\<open>list\<close>:\<close>

text_raw \<open>%
\begin{minipage}[t]{0.30\linewidth}\centering
\textbf{Imperative}\\[1mm]
\begin{minipage}{\linewidth}\scriptsize\ttfamily
let a = pick \{1,2\};\\
let b = pick \{10,20\};\\
return a + b
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.36\linewidth}\centering
\textbf{HOL (\<open>concat \<circ> map\<close>)}\\[1mm]
\begin{minipage}{\linewidth}
\begin{alltt}\scriptsize
\<open>concat (map\<close>
  \<open>(\<lambda>a. concat (map\<close>
    \<open>(\<lambda>b. [a + b])\<close>
    \<open>[10,20]))\<close>
  \<open>[1,2])\<close>
\end{alltt}
\end{minipage}
\end{minipage}\hfill
\begin{minipage}[t]{0.32\linewidth}\centering
\textbf{Compact (\<open>list_bind\<close>)}\\[1mm]
\begin{minipage}{\linewidth}
\begin{alltt}\scriptsize
\<open>list_bind [1,2]   (\<lambda>a.\<close>
\<open>list_bind [10,20] (\<lambda>b.\<close>
\<open>[a + b]))\<close>
\end{alltt}
\end{minipage}
\end{minipage}%
\<close>

text \<open>\<^bold>\<open>Type:\<close> @{typ \<open>'a \<Rightarrow> 'b list\<close>}. The combinator hides flattening
  (also available in HOL as @{const List.bind}):\<close>

(*<*)experiment begin(*>*) (* Local; re-stated later for the example slide *)
definition list_bind :: \<open>'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list\<close> where
  \<open>list_bind f g = concat (map g f)\<close>
(*<*)end(*>*)

end_slide


slide \<open>The common shape\<close>

text \<open>All four cases share the \<^bold>\<open>same skeleton\<close>:
  programs are \<open>'a \<Rightarrow> 'b M\<close> for some wrapper \<open>M\<close>; sequencing is
  ``unwrap previous, run next, re-wrap''. Reading down the column \<open>'b M\<close>:\<close>

text_raw \<open>%
\begin{center}\small
\begin{tabular}{l l l l}
\textbf{Effect} & \textbf{Wrapper \<open>'b M\<close>} & \textbf{Sequencing} & \textbf{Combinator} \\\hline
none            & \<open>'b\<close>          & nothing -- just \<open>let\<close>          & \<open>let\<close> \\
state \<open>'s\<close>      & \<open>'s \<Rightarrow> 's \<times> 'b\<close> & thread the state              & \<open>state_bind\<close> \\
errors          & \<open>'b option\<close>   & short-circuit on \<open>None\<close>     & \<open>Option.bind\<close> \\
non-determinism & \<open>'b list\<close>     & flatten over outcomes          & \<open>List.bind\<close> \\
\end{tabular}
\end{center}
\<close>

text \<open>Each row hides bookkeeping behind a single combinator. \<^bold>\<open>That
  combinator -- one \<open>return\<close>, one \<open>bind\<close>, three laws -- is a
  monad.\<close>\<close>

end_slide


slide \<open>What a monad is\<close>

text %internal \<open>Abstract shape -- a type constructor with two operations,
  declared so the antiquotations on this slide are type-checked.\<close>

typedecl %internal 'a M

consts %internal m_return :: \<open>'a \<Rightarrow> 'a M\<close>
consts %internal m_bind   :: \<open>'a M \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> 'b M\<close>  (infixl \<open>\<bind>\<close> 54)

text \<open>\<^bold>\<open>The shape:\<close> a type constructor @{typ \<open>'a M\<close>} -- ``a composable
  operation that produces a value of type @{typ \<open>'a\<close>}''.\<close>

text \<open>Two operations:

  \<^item> \<open>m_return\<close> \<open>::\<close> @{typeof \<open>m_return\<close>} \<comment> \<open>inject a pure value\<close>

  \<^item> \<open>(\<bind>)\<close> \<open>::\<close> @{typeof \<open>(\<bind>) :: 'a M \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> 'b M\<close>}
    \<comment> \<open>run, then hand the result to the next\<close>\<close>

text \<open>\<^bold>\<open>Special case:\<close> when the first result is \<open>()\<close>, \<open>\<bind>\<close> drops
  it -- pure \<^bold>\<open>sequencing\<close> \<open>f ; g\<close>.\<close>

text \<open>\<^bold>\<open>Monad laws.\<close> Three equational laws govern \<open>return\<close> and \<open>\<bind>\<close>
  -- left unit, right unit, associativity. The first reads:\<close>

text \<open>\quad @{term \<open>m_return x \<bind> g = g x\<close>}\<close>

text \<open>We prove all three for each instance below.\<close>

end_slide


slide \<open>do-notation\<close>

text \<open>Isabelle's \<open>HOL-Library.Monad_Syntax\<close> gives us a Haskell-style
  \<open>do\<close>-block once we register a \<open>bind\<close> for our monad. Schematically:

  \<^item> \<open>do { x \<leftarrow> f; g x }\<close> means \<open>f \<bind> (\<lambda>x. g x)\<close>.

  \<^item> \<open>do { f; g }\<close> drops the result -- pure sequencing.

  \<^item> \<open>do { return x }\<close> = \<open>return x\<close>.\<close>

text \<open>We will write all monadic programs in this notation.\<close>

end_slide


slide \<open>Example: state monad\<close>

text \<open>Threads a read/write state of type \<open>'s\<close>:\<close>

type_synonym ('s, 'a) state = \<open>'s \<Rightarrow> 'a \<times> 's\<close>

text \<open>The combinators we introduced earlier, retyped via this synonym:\<close>

definition state_return :: \<open>'a \<Rightarrow> ('s, 'a) state\<close> where
  \<open>state_return x s = (x, s)\<close>
    \<comment> \<open>\<open>s\<close> unchanged; result \<open>x\<close>\<close>

definition state_bind :: 
  \<open>('s, 'a) state \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state) \<Rightarrow> ('s, 'b) state\<close>
  where \<open>state_bind f g s = (let (x, s') = f s in g x s')\<close>
    \<comment> \<open>run \<open>f\<close> on \<open>s\<close>; thread the resulting \<open>s'\<close> into \<open>g\<close>\<close>

lemma %internal state_left_unit: \<open>state_bind (state_return x) g = g x\<close>
  by (simp add: state_return_def state_bind_def fun_eq_iff)

lemma %internal state_right_unit: \<open>state_bind f state_return = f\<close>
  by (auto simp: state_return_def state_bind_def split: prod.splits)

lemma %internal state_assoc:
  \<open>state_bind (state_bind f g) h = state_bind f (\<lambda>x. state_bind (g x) h)\<close>
  by (auto simp: state_bind_def split: prod.splits)

end_slide


slide \<open>Example: list monad\<close>

text \<open>The motivating non-determinism case from earlier, fully formalised
  -- ``a program returning \<open>'a\<close> is a list of possible outcomes'':\<close>

definition list_return :: \<open>'a \<Rightarrow> 'a list\<close> where
  \<open>list_return x = [x]\<close>
    \<comment> \<open>exactly one outcome\<close>

definition list_bind :: \<open>'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list\<close> where
  \<open>list_bind f g = concat (map g f)\<close>
    \<comment> \<open>for every outcome of \<open>f\<close>, run \<open>g\<close>; flatten the lists\<close>

lemma %internal list_left_unit: \<open>list_bind (list_return x) g = g x\<close>
  by (simp add: list_return_def list_bind_def)

lemma %internal list_right_unit: \<open>list_bind f list_return = f\<close>
  by (induction f) (auto simp: list_return_def list_bind_def)

lemma %internal list_assoc:
  \<open>list_bind (list_bind f g) h = list_bind f (\<lambda>x. list_bind (g x) h)\<close>
  by (induction f) (auto simp: list_bind_def)

end_slide


slide \<open>Example: reader monad\<close>

text \<open>Threads a read-only environment of type \<open>'r\<close>:\<close>

type_synonym ('r, 'a) reader = \<open>'r \<Rightarrow> 'a\<close>
  \<comment> \<open>an \<open>'a\<close>-valued op in the reader monad for \<open>'r\<close> produces an \<open>'a\<close>
      given access to the read-only environment \<open>'r\<close>\<close>

definition reader_return :: \<open>'a \<Rightarrow> ('r, 'a) reader\<close> where
  \<open>reader_return x r = x\<close>
    \<comment> \<open>ignore the environment \<open>r\<close>; return \<open>x\<close>\<close>

definition reader_bind ::
    \<open>('r, 'a) reader \<Rightarrow> ('a \<Rightarrow> ('r, 'b) reader) \<Rightarrow> ('r, 'b) reader\<close> where
  \<open>reader_bind f g r = g (f r) r\<close>
    \<comment> \<open>read \<open>r\<close>, run \<open>f\<close> on it, hand the result \<^emph>\<open>and the same \<open>r\<close>\<close> to \<open>g\<close>\<close>

lemma %internal reader_left_unit: \<open>reader_bind (reader_return x) g = g x\<close>
  by (simp add: reader_return_def reader_bind_def fun_eq_iff)

lemma %internal reader_right_unit: \<open>reader_bind f reader_return = f\<close>
  by (simp add: reader_return_def reader_bind_def fun_eq_iff)

lemma %internal reader_assoc:
  \<open>reader_bind (reader_bind f g) h = reader_bind f (\<lambda>x. reader_bind (g x) h)\<close>
  by (simp add: reader_bind_def fun_eq_iff)

end_slide


slide \<open>Example: error monad\<close>

text \<open>Aborts computation once an error (\<open>Inr\<close>) is hit; chains
  values (\<open>Inl\<close>) otherwise:\<close>

type_synonym ('e, 'a) error = \<open>'a + 'e\<close>

definition error_return :: \<open>'a \<Rightarrow> ('e, 'a) error\<close> where
  \<open>error_return x = Inl x\<close>
    \<comment> \<open>success, value \<open>x\<close>\<close>

definition error_bind ::
    \<open>('e, 'a) error \<Rightarrow> ('a \<Rightarrow> ('e, 'b) error) \<Rightarrow> ('e, 'b) error\<close> where
  \<open>error_bind f g = (case f of Inl x \<Rightarrow> g x | Inr e \<Rightarrow> Inr e)\<close>
    \<comment> \<open>continue with \<open>g\<close> on success; propagate the error otherwise\<close>

text \<open>Specialising \<open>'e = unit\<close> recovers the familiar \<open>'a option\<close>:
  \<open>Inl x = Some x\<close>, \<open>Inr () = None\<close>. A richer \<open>'e\<close> lets you
  distinguish multiple error reasons.\<close>

lemma %internal error_left_unit: \<open>error_bind (error_return x) g = g x\<close>
  by (simp add: error_return_def error_bind_def)

lemma %internal error_right_unit: \<open>error_bind f error_return = f\<close>
  by (auto simp: error_return_def error_bind_def split: sum.splits)

lemma %internal error_assoc:
  \<open>error_bind (error_bind f g) h = error_bind f (\<lambda>x. error_bind (g x) h)\<close>
  by (auto simp: error_bind_def split: sum.splits)

end_slide


slide \<open>Example: non-determinism + state\<close>

text \<open>State monad, but each step may return \<^bold>\<open>several\<close> possible
  outcomes -- a set of (value, next-state) pairs instead of a single
  pair:\<close>

type_synonym ('s, 'a) nondet = \<open>'s \<Rightarrow> ('a \<times> 's) set\<close>

definition nondet_return :: \<open>'a \<Rightarrow> ('s, 'a) nondet\<close> where
  \<open>nondet_return x s = {(x, s)}\<close>
    \<comment> \<open>exactly one outcome: \<open>x\<close>, state unchanged\<close>

definition nondet_bind ::
    \<open>('s, 'a) nondet \<Rightarrow> ('a \<Rightarrow> ('s, 'b) nondet) \<Rightarrow> ('s, 'b) nondet\<close> where
  \<open>nondet_bind f g s = (\<Union>(x, s')\<in>f s. g x s')\<close>
    \<comment>\<open>pick one outcome \<open>(x, s')\<close> of \<open>f\<close> from \<open>s\<close>;\<close>
    \<comment>\<open>then one outcome \<open>(y, s'')\<close> of \<open>g x\<close> from \<open>s'\<close>;\<close>
    \<comment>\<open>keep all such \<open>(y, s'')\<close>\<close>

lemma %internal nondet_left_unit: \<open>nondet_bind (nondet_return x) g = g x\<close>
  by (simp add: nondet_return_def nondet_bind_def fun_eq_iff)

lemma %internal nondet_right_unit: \<open>nondet_bind f nondet_return = f\<close>
  by (auto simp: nondet_return_def nondet_bind_def fun_eq_iff)

lemma %internal nondet_assoc:
  \<open>nondet_bind (nondet_bind f g) h
     = nondet_bind f (\<lambda>x. nondet_bind (g x) h)\<close>
  by (auto simp: nondet_bind_def fun_eq_iff)

end_slide


slide \<open>Example: state + error monad\<close>

text \<open>Monads compose. A program that both threads a state \<^emph>\<open>and\<close>
  may abort with an error: combine state with error in the
  result type.\<close>

type_synonym ('s, 'e, 'a) state_err = \<open>'s \<Rightarrow> ('a \<times> 's) + 'e\<close>
  \<comment> \<open>given a state, either return a value with an updated state
      (\<open>Inl\<close>) or fail with an error and discard the state (\<open>Inr\<close>)\<close>

definition state_err_return :: \<open>'a \<Rightarrow> ('s, 'e, 'a) state_err\<close> where
  \<open>state_err_return x s = Inl (x, s)\<close>
    \<comment> \<open>state \<open>s\<close> unchanged; success with value \<open>x\<close>\<close>

definition state_err_bind where
  \<open>state_err_bind f g s = (case f s of Inl (x, s') \<Rightarrow> g x s' | Inr e \<Rightarrow> Inr e)\<close>
    \<comment> \<open>run \<open>f\<close> on \<open>s\<close>; on success thread \<open>(x, s')\<close> into \<open>g\<close>; on error propagate\<close>

text \<open>\<^bold>\<open>Foreshadow:\<close> this is the shape AutoCorrode's
  \<open>continuation\<close> datatype generalises -- \<open>Inl\<close> = \<open>Success\<close>,
  \<open>Inr\<close> = \<open>Abort\<close>, plus a third \<open>Return\<close> branch for early-return,
  plus a \<open>Yield\<close> for system calls.\<close>

lemma %internal state_err_left_unit:
    \<open>state_err_bind (state_err_return x) g = g x\<close>
  by (simp add: state_err_return_def state_err_bind_def fun_eq_iff)

lemma %internal state_err_right_unit:
    \<open>state_err_bind f state_err_return = f\<close>
  by (auto simp: state_err_return_def state_err_bind_def
           fun_eq_iff split: sum.splits)

lemma %internal state_err_assoc:
    \<open>state_err_bind (state_err_bind f g) h
       = state_err_bind f (\<lambda>x. state_err_bind (g x) h)\<close>
  by (auto simp: state_err_bind_def fun_eq_iff split: sum.splits)

end_slide


slide \<open>Example: continuation (CPS) monad\<close>

text_raw \<open>\begin{center}\<close>

text \<open>``\<^emph>\<open>Tell me how you continue once you have the return value,
  and I'll tell you the result\<close>''\<close>

text_raw \<open>\end{center}\<close>

text \<open>The computation only sees its caller's continuation; the
  eventual answer has type \<open>'r\<close>:\<close>

type_synonym ('r, 'a) cps = \<open>('a \<Rightarrow> 'r) \<Rightarrow> 'r\<close>

definition cps_return :: \<open>'a \<Rightarrow> ('r, 'a) cps\<close> where
  \<open>cps_return x k = k x\<close>
    \<comment> \<open>hand \<open>x\<close> to the continuation \<open>k\<close>\<close>

definition cps_bind :: \<open>('r, 'a) cps \<Rightarrow> ('a \<Rightarrow> ('r, 'b) cps) \<Rightarrow> ('r, 'b) cps\<close>
  where \<open>cps_bind f g k = f (\<lambda>x. g x k)\<close>
    \<comment> \<open>run \<open>f\<close> with the continuation: ``name its result \<open>x\<close>, then run \<open>g x\<close> with \<open>k\<close>''\<close>

text \<open>CPS is normally introduced for compilers (passing
  ``what-to-do-next'' explicitly). We will see another use: when
  \<open>'r\<close> is specialised to a state-predicate type, the CPS monad
  becomes a weakest-precondition transformer.\<close>

lemma %internal cps_left_unit: \<open>cps_bind (cps_return x) g = g x\<close>
  by (simp add: cps_return_def cps_bind_def fun_eq_iff)

lemma %internal cps_right_unit: \<open>cps_bind f cps_return = f\<close>
  by (simp add: cps_return_def cps_bind_def fun_eq_iff)

lemma %internal cps_assoc:
  \<open>cps_bind (cps_bind f g) h = cps_bind f (\<lambda>x. cps_bind (g x) h)\<close>
  by (simp add: cps_bind_def fun_eq_iff)

end_slide




interlude \<open>Putting it together: the uRust monad\<close>

text \<open>AutoCorrode's uRust packs state, two notions of completion,
  abort, and a callback into one datatype. Verbatim, from
  \<open>Shallow_Micro_Rust.Core_Expression\<close>:\<close>

text \<open>@{datatype [display] continuation}\<close>

text \<open>And the corresponding expression type:\<close>

text \<open>@{datatype [display] expression}\<close>

text \<open>\<^bold>\<open>Two notions of success.\<close> \<open>Success\<close> and \<open>Return\<close> both end with
  value+state -- but \<open>;\<close> threads through \<open>Success\<close>, while \<open>Return\<close> short-circuits the enclosing function body.\<close>

text \<open>\<^bold>\<open>Abort\<close> is the error-monad case: uncaught, bubbles all the way
  up. \<^bold>\<open>Yield\<close> models system calls -- prompt \<open>\<pi>\<close> out, response in via \<open>k\<close>.\<close>

end_interlude

end

