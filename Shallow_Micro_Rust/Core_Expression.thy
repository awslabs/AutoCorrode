(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Core_Expression
  imports
    \<comment> \<open>This needs to come before the theories below for some reason otherwise Isabelle goes berserk
        with \<^verbatim>\<open>SIMPLIFIER\<close> exceptions raised about congruences.\<close>
    "Misc.Debug_Logging"
    "HOL-Library.Word"
    "HOL-Eisbach.Eisbach"
    Basic_Case_Expression
begin
(*>*)

section\<open>Core Micro Rust\<close>

named_theorems micro_rust_simps

subsection\<open>Runtime aborts\<close>

text\<open>This describes the different ways that a runtime abort may have come about.  We have:
\begin{enumerate*}
\item A runtime panic, caused by the programmer making an explicit call to the \<^verbatim>\<open>panic!\<close> macro, or a
similar construct in Rust.
\item A programmer-facing assertion failed dynamically at runtime.
\item A dangling pointer.
\end{enumerate*}\<close>
datatype 'abort abort
  = Panic \<open>String.literal\<close>
  | Unimplemented \<open>String.literal\<close>
  | AssertionFailed
  | DanglingPointer
  | TypeError
  | ResumedFromFatal
  | UnexpectedYield
  | CustomAbort 'abort

subsection\<open>Continuations\<close>

text\<open>When working towards embedding \<^verbatim>\<open>\<mu>Rust\<close> in Isabelle, we define all of the different ways that
a computation can end, using a dedicated \<^bold>\<open>continuation\<close> type.  In particular, in Rust, we can:
\begin{enumerate*}
\item Compute a value successfully,
\item Panic at runtime, raising a runtime exception,
\item Return early, with a value, from a computation.
\end{enumerate*}
These are captured below:\<close>

datatype ('s, 'v, 'r, 'abort, 'i, 'o) continuation
  = Success \<open>'v\<close> \<open>'s\<close> \<comment> \<open>A successful, state-modifying computation, producing a value\<close>
  | Return \<open>'r\<close> \<open>'s\<close>  \<comment> \<open>Return from the command early with a value, and the current state.\<close>
  | Abort \<open>'abort abort\<close> \<open>'s\<close>
  | Yield \<open>'i\<close> \<open>'s\<close> \<open>'o \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  and ('s, 'v, 'r, 'abort, 'i, 'o) expression
  = Expression \<open>'s \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close>

text\<open>Explicitly define a well-founded relation on continuations which makes continuations wrapped
in a \<^term>\<open>Yield\<close> larger than any of the values of the continuations.\<close>

subsection\<open>The type of shallow-embedded Micro Rust expressions\<close>

text\<open>Rust is an expression-oriented language, and expressions can have side-effects, with function
calls modifying the global state, and otherwise-imperative features like variable assignment also
treated as unit-valued expressions.  Moreover, expressions can fail for a variety of reasons, most
notably a call to the \<^verbatim>\<open>panic!\<close> macro, or some other similar macro that induces a runtime abort.  As
a result of this, we model expressions as maps from some abstract \<^emph>\<open>state\<close> type, \<^typ>\<open>'s\<close>, to values
of \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close>.  Moreover, note that our embedding of Rust expressions
is typed, piggy-backing off the HOL type system:\<close>

text\<open>We can \<^emph>\<open>evaluate\<close> an expression by simply "feeding it" a state, getting a continuation back:\<close>
definition evaluate :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>Micro Rust expression to evaluate\<close>
                        's \<Rightarrow>                      \<comment> \<open>State to evaluate expression in\<close>
                        ('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close> where
  \<open>evaluate e s \<equiv> case e of Expression f \<Rightarrow> f s\<close>

text\<open>The definitions of \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> and \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close> are
mutually recursive, with recursion under a binder. As a consequence, inductive constructions on
continuations and expressions require a non-trivial termination proof. The following definition
captures the (soon proved to be) well-founded termination relation for those proofs.\<close>

definition expression_wf_base :: \<open>(('s, 'v, 'r, 'abort, 'i, 'o) expression \<times> ('s, 'v, 'r, 'abort, 'i, 'o) expression) set\<close> where
  \<open>expression_wf_base = {(f, e). \<exists>\<sigma> \<sigma>' e' \<pi> \<rho>. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<and> f = e' \<rho>}\<close>

text\<open>The reflexive-transitive closure of \<^term>\<open>expression_wf_base\<close>:\<close>
definition expression_wf :: \<open>(('s, 'v, 'r, 'abort, 'i, 'o) expression \<times> ('s, 'v, 'r, 'abort, 'i, 'o) expression) set\<close> where
  \<open>expression_wf \<equiv> expression_wf_base\<^sup>+\<close>

definition lift_prop_to_cont :: \<open>(('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> bool) \<Rightarrow>
      ('s, 'v, 'r, 'abort, 'i, 'o) continuation \<Rightarrow> bool\<close> where
  \<open>lift_prop_to_cont P c \<equiv> \<forall>\<pi> \<sigma> c'. c = Yield \<pi> \<sigma> c' \<longrightarrow> (\<forall>e\<in>range c'. P e)\<close>

lemma expression_wf_base_is_wf:
  shows \<open>wf expression_wf_base\<close> (is ?wf_base)
proof(unfold wf_def, safe)
     fix P :: \<open>('a, 'b, 'c, 'd, 'e, 'f) expression \<Rightarrow> bool\<close>
     and x :: \<open>('a, 'b, 'c, 'd, 'e, 'f) expression\<close>
  assume *: \<open>\<forall>x. (\<forall>y. (y, x) \<in> expression_wf_base \<longrightarrow> P y) \<longrightarrow> P x\<close>
  {
    fix x y
    have \<open>P x \<and> (lift_prop_to_cont P) y\<close>
    using * proof(induct_tac x and y)
      fix x1 x2
      show \<open>lift_prop_to_cont P (Success x1 x2)\<close>
        by (clarsimp simp add: lift_prop_to_cont_def)
    next
      fix x1 x2
      show \<open>lift_prop_to_cont P (Return x1 x2)\<close>
        by (clarsimp simp add: lift_prop_to_cont_def)
    next
      fix a \<sigma>
      show \<open>lift_prop_to_cont P (Abort a \<sigma>)\<close>
        by (clarsimp simp add: lift_prop_to_cont_def)
    next
      fix x y x1 x2 and x3 :: \<open>'f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) expression\<close>
      assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> expression_wf_base \<longrightarrow> P y) \<longrightarrow> P x\<close>
         and \<open>\<And>x4. x4 \<in> range x3 \<Longrightarrow> P x4\<close>
      from this show \<open>lift_prop_to_cont P (Yield x1 x2 x3)\<close>
        by (clarsimp simp add: lift_prop_to_cont_def)
    next
         fix x :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) continuation\<close>
      assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> expression_wf_base \<longrightarrow> P y) \<longrightarrow> P x\<close>
         and \<open>(\<And>x4. x4 \<in> range x \<Longrightarrow> lift_prop_to_cont P x4)\<close>
      from this show \<open>P (Expression x)\<close>
        by (clarsimp simp add: lift_prop_to_cont_def expression_wf_base_def)
          (metis evaluate_def expression.case rangeI)
    qed
  }
  from this show \<open>P x\<close>
    by auto
qed

lemma expression_wf_is_wf[intro]:
  shows \<open>wf expression_wf\<close>
by (auto simp add: expression_wf_def intro: wf_trancl[OF expression_wf_base_is_wf])

subsection\<open>Deep evaluation of Micro Rust expressions\<close>

text\<open>Evaluation via \<^term>\<open>evaluate\<close> need not produce a result (\<^verbatim>\<open>Literal\<close>,\<^term>\<open>Return\<close> or
 \<^verbatim>\<open>Abort\<close>), but can also \<^verbatim>\<open>Yield\<close>. In this section, we define various 'deep' evaluation 
functions for \<^verbatim>\<open>\<mu>Rust\<close> expressions, resolving yields by means of 'yield handlers'.\<close>

subsubsection\<open>Yield handlers\<close>

text\<open>A \<^emph>\<open>yield handler\<close> is a means to continue evaluation of a uRust program when its evaluation
via \<^verbatim>\<open>evaluate\<close> produces a \<^term>\<open>Yield\<close>. It receives the yield prompt, the current state, and the
continuation of the program, and makes a decision on how to continue evaluation.

We consider multiple definitions trading simplicity and generality -- their equivalence is proved 
in \<^file>\<open>Core_Expression_Lemmas.thy\<close>\<close> 

text\<open>First, a \<^emph>\<open>deterministic\<close> yield handler takes a prompt input as well as a continuation parametrized
by a prompt output, and deterministically return a continuation expression. Note, however, that 
non-determinism may still be modelled by incorporating the necessary random coins in the state
itself.\<close>

type_synonym ('s, 'v, 'r, 'abort, 'i, 'o) yield_handler_det = 
  \<open>'i \<Rightarrow> ('o \<Rightarrow> 's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation) \<Rightarrow>
     's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close>

text\<open>The following is the deep evaluation function for deterministic yield handlers:\<close>

function deep_evaluate_det :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) yield_handler_det \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close> where
  \<open>deep_evaluate_det y e \<sigma> = (case evaluate e \<sigma> of
      Success v \<sigma>' \<Rightarrow> Success v \<sigma>'
    | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
    | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
    | Yield \<pi> \<sigma>' e' \<Rightarrow> y \<pi> (\<lambda>\<omega>. deep_evaluate_det y (e' \<omega>)) \<sigma>')\<close>
by pat_completeness auto

termination
  deep_evaluate_det
proof(relation \<open>inv_image expression_wf (\<lambda>c. fst (snd c))\<close>)
  show \<open>wf (inv_image expression_wf (\<lambda>c. fst (snd c)))\<close>
    by force
next
  fix y :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> ('c, 'd, 'e, 'abort, 'a, 'b) continuation) \<Rightarrow> 'c \<Rightarrow>
      ('c, 'd, 'e, 'abort, 'a, 'b) continuation\<close> and e :: \<open>('c, 'd, 'e, 'abort, 'a, 'b) expression\<close> and \<sigma> x1 x2 x3 x a
  assume \<open>evaluate e \<sigma> = Yield x1 x2 x3\<close>
  from this show \<open>((y, x3 x, a), y, e, \<sigma>) \<in> inv_image expression_wf (\<lambda>c. fst (snd c))\<close>
    by (force simp add: expression_wf_def expression_wf_base_def)
qed

declare deep_evaluate_det.simps[simp del]

text\<open>The most basic non-deterministic yield handler is one which takes a prompt input as well as
the current system state, and returns a set of \<^emph>\<open>yield continuations\<close>: A yield continuation is either
an \<^verbatim>\<open>Abort\<close>, or the decision to continue evaluation with a prompt return value and a potentially
modified new state.\<close>

datatype ('s, 'abort, 'o) yield_handler_nondet_basic_result
  = YieldContinue \<open>'o \<times> 's\<close>
  | YieldAbort    \<open>'abort abort\<close> \<open>'s\<close>

type_synonym ('s, 'abort, 'i, 'o) yield_handler_nondet_basic =
  \<open>'i \<Rightarrow> 's \<Rightarrow> ('s, 'abort, 'o) yield_handler_nondet_basic_result set\<close>

function deep_evaluates_nondet_basic :: \<open>('i \<Rightarrow> 's \<Rightarrow> ('s, 'abort, 'o) yield_handler_nondet_basic_result set)
     \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation set\<close> where
  \<open>deep_evaluates_nondet_basic y e \<sigma> = (case evaluate e \<sigma> of
      Success v \<sigma>'  \<Rightarrow> {Success v \<sigma>'}
    | Return r \<sigma>'   \<Rightarrow> {Return r \<sigma>'}
    | Abort a \<sigma>'     \<Rightarrow> {Abort a \<sigma>'}
    | Yield \<pi> \<sigma>' e' \<Rightarrow> (
        let handle_yield_result = \<lambda>yield_result.
          case yield_result of 
            YieldContinue (\<omega>, \<sigma>'') \<Rightarrow> deep_evaluates_nondet_basic y (e' \<omega>) \<sigma>''
          | YieldAbort a \<sigma>'        \<Rightarrow> {Abort a \<sigma>'}
        in \<Union> (handle_yield_result ` (y \<pi> \<sigma>'))))\<close>
by pat_completeness auto

termination
  deep_evaluates_nondet_basic
proof (relation \<open>inv_image expression_wf (\<lambda>c. fst (snd c))\<close>)
  show \<open>wf (inv_image expression_wf (\<lambda>c. fst (snd c)))\<close>
    by force
next
     fix y :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('b, 'c, 'd) yield_handler_nondet_basic_result set\<close>
     and e :: \<open>('b, 'e, 'f, 'c, 'a, 'd) expression\<close>
     and \<sigma> x1 x2 x3 x a
  assume \<open>evaluate e \<sigma> = Yield x1 x2 x3\<close>
  from this show \<open>((y, x3 x, a), y, e, \<sigma>) \<in> inv_image expression_wf (\<lambda>c. fst (snd c))\<close>
    by (force simp add: expression_wf_def expression_wf_base_def)
qed

declare deep_evaluates_nondet_basic.simps [simp del]

text\<open>The most general notion of a yield handler takes a prompt input, a system state, as well as
\<^emph>\<open>sets\<close> of possible continuations parametrized by prompt outputs and new states, and itself returns
a set of possible continuations.\<close>

type_synonym ('s, 'v, 'r, 'abort, 'i, 'o) yield_handler_nondet =  \<open>'i \<Rightarrow>
    ('o \<Rightarrow> 's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation set) \<Rightarrow> 's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation set\<close>

function deep_evaluates_nondet :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) yield_handler_nondet \<Rightarrow>
      ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 's \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation set\<close> where
  \<open>deep_evaluates_nondet y e \<sigma> = (case evaluate e \<sigma> of
      Success v \<sigma>' \<Rightarrow> {Success v \<sigma>'}
    | Return r \<sigma>' \<Rightarrow> {Return r \<sigma>'}
    | Abort a \<sigma>' \<Rightarrow> {Abort a \<sigma>'}
    | Yield \<pi> \<sigma>' e' \<Rightarrow> y \<pi> (\<lambda>\<omega> \<sigma>'. deep_evaluates_nondet y (e' \<omega>) \<sigma>') \<sigma>')\<close>
by pat_completeness auto

termination
  deep_evaluates_nondet
proof(relation \<open>inv_image expression_wf (\<lambda>c. fst (snd c))\<close>)
  show \<open>wf (inv_image expression_wf (\<lambda>c. fst (snd c)))\<close>
    by force
next
     fix y :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> ('c, 'd, 'e, 'f, 'a,
                       'b) continuation set)
         \<Rightarrow> 'c \<Rightarrow> ('c, 'd, 'e, 'f, 'a, 'b) continuation set\<close>
     and e :: \<open>('c, 'd, 'e, 'f, 'a, 'b) expression\<close>
     and \<sigma> x1 x2 x3 x a
  assume \<open>evaluate e \<sigma> = Yield x1 x2 x3\<close>
  from this show \<open>((y, x3 x, a), y, e, \<sigma>) \<in> inv_image expression_wf (\<lambda>c. fst (snd c))\<close>
    by (force simp add: expression_wf_def expression_wf_base_def)
qed

text\<open>Next, we connect restricted and general yield handlers.

First, a basic non-deterministic yield handler gives a general one as follows:\<close>

definition yield_handler_nondet_basic_to_nondet :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow>
      ('s, 'b, 'c, 'abort, 'i, 'o) yield_handler_nondet\<close> where
  \<open>yield_handler_nondet_basic_to_nondet y \<pi> e \<sigma> \<equiv> \<Union> ( 
     let handle_yield_result = \<lambda>res.
       case res of
         YieldContinue (\<omega>, \<sigma>') \<Rightarrow> e \<omega> \<sigma>'
       | YieldAbort a \<sigma>' \<Rightarrow> {Abort a \<sigma>'}
      in handle_yield_result ` (y \<pi> \<sigma>))\<close>

text\<open>Second, every deterministic yield handler gives rise to a general non-deterministic 
yield handler:\<close>

definition yield_handler_det_to_nondet :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) yield_handler_det \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) yield_handler_nondet\<close> where
  \<open>yield_handler_det_to_nondet y \<pi> e \<sigma> \<equiv>
     (\<lambda>e_choice. y \<pi> e_choice \<sigma>) ` ({e'. \<forall>\<omega> \<sigma>. e' \<omega> \<sigma> \<in> e \<omega> \<sigma>})\<close>

text\<open>We will prove in \<^file>\<open>Core_Expression_Lemmas.thy\<close> that the conversions between the different 
yield handlers intertwine the various deep evaluation functions.\<close>

paragraph\<open>Some examples and properties of non-deterministic basic yield handlers:\<close>

text\<open>A \<^emph>\<open>non-empty\<close> yield handler is one which always returns at least one continuation.
We will show below that deep evaluatin for non-empty yield handlers always produces at least
one result:\<close>

definition is_nonempty_yield_handler :: \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> bool\<close> where
  \<open>is_nonempty_yield_handler y \<equiv> (\<forall>a b. y a b \<noteq> {})\<close>
  
subsection\<open>More basic material\<close>

text\<open>A \<^text>\<open>function_body\<close> represents a callable function which has already had all arguments
applied and returns \<^typ>\<open>'b\<close>, while operating on machine state typ\<open>'s\<close>.\<close>
datatype ('s, 'b, 'abort, 'i, 'o) function_body
  = FunctionBody (function_body: \<open>('s, 'b, 'b, 'abort, 'i, 'o) expression\<close>)

lemma function_body_simp [simp, micro_rust_simps]:
  shows \<open>function_body (FunctionBody f) = f\<close>
by (simp add: function_body_def)

text\<open>A \<^bold>\<open>literal\<close> value does not depend on the state at all.  Note that the type of the literal is
reflected in the type of the expression:\<close>
definition literal :: \<open>'v \<Rightarrow> \<comment> \<open>HOL value to lift into an expression\<close>
                       ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>literal v \<equiv> Expression (Success v)\<close>

definition deep_compose1 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('t0 \<Rightarrow> 'b) \<Rightarrow> ('t0 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose1 g f \<equiv> \<lambda>t0. (g (f t0))\<close>
definition deep_compose2 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 'b) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose2 g f \<equiv> \<lambda>t0 t1. (g (f t0 t1))\<close>
definition deep_compose3 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 'b) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose3 g f \<equiv> \<lambda>t0 t1 t2. (g (f t0 t1 t2))\<close>
definition deep_compose4 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 'b) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose4 g f \<equiv> \<lambda>t0 t1 t2 t3. (g (f t0 t1 t2 t3))\<close>
definition deep_compose5 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose5 g f \<equiv> \<lambda>t0 t1 t2 t3 t4. (g (f t0 t1 t2 t3 t4))\<close>
definition deep_compose6 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose6 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5. (g (f t0 t1 t2 t3 t4 t5))\<close>
definition deep_compose7 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose7 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6. (g (f t0 t1 t2 t3 t4 t5 t6))\<close>
definition deep_compose8 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose8 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7. (g (f t0 t1 t2 t3 t4 t5 t6 t7))\<close>
definition deep_compose9 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose9 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8))\<close>
definition deep_compose10 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose10 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9))\<close>
definition deep_compose11 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose11 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10))\<close>
definition deep_compose12 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose12 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11))\<close>
definition deep_compose13 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose13 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12))\<close>
definition deep_compose14 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose14 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13))\<close>
definition deep_compose15 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose15 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14))\<close>
definition deep_compose16 :: \<open>('b \<Rightarrow> 'c) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> 't15 \<Rightarrow> 'b) \<Rightarrow>
                             ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> 't15 \<Rightarrow> 'c)\<close>
  where [micro_rust_simps]: \<open>deep_compose16 g f \<equiv> \<lambda>t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15. (g (f t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15))\<close>

text\<open>A bunch of convenience functions for lifting pure functions to Micro Rust expressions:\<close>

abbreviation (input) lift_exp0 :: \<open>'v \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>lift_exp0 \<equiv> literal\<close>
definition lift_exp1 :: \<open>('a \<Rightarrow> 'b) \<Rightarrow>
                         ('a \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp1 \<equiv> deep_compose1 literal\<close>
definition lift_exp2 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>
                         ('a \<Rightarrow> 'b \<Rightarrow> ('s, 'c, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp2 \<equiv> deep_compose2 literal\<close>
definition lift_exp3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
                         ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('s, 'd, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp3 \<equiv> deep_compose3 literal\<close>
definition lift_exp4 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow>
                         ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> ('s, 'e, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp4 \<equiv> deep_compose4 literal\<close>
definition lift_exp5 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp5 \<equiv> deep_compose5 literal\<close>
definition lift_exp6 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp6 \<equiv> deep_compose6 literal\<close>
definition lift_exp7 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp7 \<equiv> deep_compose7 literal\<close>
definition lift_exp8 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression)\<close>
  where [micro_rust_simps]: \<open>lift_exp8 \<equiv> deep_compose8 literal\<close>

text\<open>A \<^bold>\<open>function literal\<close> lifts a value as a Micro Rust \<^typ>\<open>('s, 'v, 'abort, 'i, 'o) function_body\<close>.\<close>
definition fun_literal :: \<open>'v \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>fun_literal v \<equiv> FunctionBody (literal v)\<close>

text\<open>More convenience functions for lifting pure functions to Micro Rust functions, i.e. values
of type \<^typ>\<open>('s, 'v, 'abort, 'i, 'o) function_body\<close>.\<close>

definition lift_fun0 :: \<open>'v \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>
  where [micro_rust_simps]: \<open>lift_fun0 \<equiv> fun_literal\<close>
definition lift_fun1 :: \<open>('a \<Rightarrow> 'b) \<Rightarrow>
                         ('a \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun1 \<equiv> deep_compose1 fun_literal\<close>
definition lift_fun2 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>
                         ('a \<Rightarrow> 'b \<Rightarrow> ('s, 'c, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun2 \<equiv> deep_compose2 fun_literal\<close>
definition lift_fun3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
                         ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('s, 'd, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun3 \<equiv> deep_compose3 fun_literal\<close>
definition lift_fun4 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow>
                         ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> ('s, 'e, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun4 \<equiv> deep_compose4 fun_literal\<close>
definition lift_fun5 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun5 \<equiv> deep_compose5 fun_literal\<close>
definition lift_fun6 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun6 \<equiv> deep_compose6 fun_literal\<close>
definition lift_fun7 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun7 \<equiv> deep_compose7 fun_literal\<close>
definition lift_fun8 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun8 \<equiv> deep_compose8 fun_literal\<close>
definition lift_fun9 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun9 \<equiv> deep_compose9 fun_literal\<close>
definition lift_fun10 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 'v) \<Rightarrow>
                         ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body)\<close>
  where [micro_rust_simps]: \<open>lift_fun10 \<equiv> deep_compose10 fun_literal\<close>

text\<open>As an example of a \<^term>\<open>fun_literal\<close> Micro Rust expression, we introduce the \<^emph>\<open>skip\<close> command:
This is just an abbreviation for the unit literal, though with a more suggestive name for when we
use it later.  Though this looks useless, it will prove useful later when we come to \<^emph>\<open>derive\<close> new
expressions from old:\<close>
abbreviation (input) skip :: \<open>('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>skip \<equiv> literal ()\<close>

text\<open>An \<^emph>\<open>abort\<close> expression aborts computation at runtime with the given abort type.\<close>
definition abort :: \<open>'abort abort \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>abort a \<equiv> Expression (Abort a)\<close>

text\<open>A \<^emph>\<open>panic\<close> expression aborts computation at runtime with a defined error message.  Note that
the panic message must be a string literal:\<close>
abbreviation panic :: \<open>String.literal \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>panic msg \<equiv> abort (Panic msg)\<close>

text \<open>An \<^emph>\<open>unimplemented\<close> expression aborts a computation at runtime, indicating that some
function is not implemented. The given string should indicate the name of the unimplemented function.
This is the same as a \<^emph>\<open>panic\<close> in most ways, but conformance testing will end early with a warning,
instead of an error, if it encounters an unimplemented abort.\<close>
abbreviation unimplemented :: \<open>String.literal \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>unimplemented nm \<equiv> abort (Unimplemented nm)\<close>

text\<open>This will sometimes prove useful to help disambiguate complex expressions, making it look like
we are introducing a new stack scope:\<close>
abbreviation (input) scoped :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>scoped e \<equiv> e\<close>

subsection\<open>Monadic computation\<close>

text\<open>We now develop some infrastructure related to the type of expressions, which will be
generally useful all over the place.  This is the \<^emph>\<open>monadic bind\<close> construct: note that it is
essentially a generalized form of \<^emph>\<open>let\<close>, and in fact this is the syntax which we will assign it in
Micro Rust, rather than working in the \<^emph>\<open>do-block\<close> style familiar from Haskell (though we will often
use this style when providing \<^emph>\<open>definitions\<close> of Micro Rust expressions).  Note that sequencing
(i.e., the semicolon from Rust) is also a degenerate form of this construct where the unit-valued
result of the first expression in the sequence is bound to a variable name which is never used in
the second expression:\<close>
function bind :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>         \<comment> \<open>Expression to bind to variable\<close>
                    ('v \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression) \<Rightarrow> \<comment> \<open>Body of let construct, with new binding\<close>
                    ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>bind e f = Expression (\<lambda>\<sigma>. case evaluate e \<sigma> of
      Success v \<sigma>' \<Rightarrow> evaluate (f v) \<sigma>'
    | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
    | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
    | Yield \<pi> \<sigma>' e' \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<rho>. bind (e' \<rho>) f))\<close>
by pat_completeness auto

termination
  bind
proof (relation \<open>inv_image expression_wf fst\<close>)
  show \<open>wf (inv_image expression_wf fst)\<close>
    by force
next
     fix e :: \<open>('a, 'b, 'c, 'd, 'e, 'f) expression\<close>
     and f :: \<open>'b \<Rightarrow> ('a, 'g, 'c, 'd, 'e, 'f) expression\<close>
     and x x1 x2 x3 a
  assume \<open>evaluate e x = Yield x1 x2 x3\<close>
  from this show \<open>((x3 a, f), e, f) \<in> inv_image expression_wf fst\<close>
    by (force simp add: expression_wf_def expression_wf_base_def)
qed

lemma bind_evaluate:
  shows \<open>evaluate (bind e f) \<sigma> = 
     (case evaluate e \<sigma> of
      Success v \<sigma>' \<Rightarrow> evaluate (f v) \<sigma>'
    | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
    | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
    | Yield \<pi> \<sigma>' e' \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<rho>. bind (e' \<rho>) f))\<close>
by (simp add: evaluate_def)

text\<open>Contrary to definitions by \<^verbatim>\<open>Definition\<close>, the definition of \<^term>\<open>bind\<close> is marked as \<^verbatim>\<open>simp\<close> 
by default. Removing it to keep the default behaviour of \<^verbatim>\<open>definitions\<close> of not being unfolded 
automatically.\<close>
declare Core_Expression.bind.simps[simp del]

text\<open>The following is the sequencing operator (the semicolon), familiar from C-language family
programming languages.  Note that it is again well-typed: both expressions being sequenced must be
unit-valued.  It is also a degenerate form of the monadic bind operator, as previously mentioned:\<close>
definition sequence :: \<open>('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>First expression to execute\<close>
                        ('s, 'b, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>Second expression to execute\<close>
                        ('s, 'b, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>sequence e f \<equiv> bind e (\<lambda>_. f)\<close>

subsection\<open>Extracting and modifying state\<close>

text\<open>The following functions are utility functions, or basic building blocks, that we will use when
defining the semantics of larger, more complex expressions.  Note that the
\<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> is a form of \<^emph>\<open>state monad\<close>, which "bundles" along an implicit machine
state (of type \<^typ>\<open>'s\<close>).  We will frequently need to observe some aspect of the machine during the
course of a computation: for example reading from a register file, or checking whether a page is
mapped within the address space of a principal, or similar.  The following definition provides a
generic method for querying such elements:\<close>
definition get :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>get f \<equiv> Expression (\<lambda>\<sigma>. Success (f \<sigma>) \<sigma>)\<close>

text\<open>Moreover, the following function provides a generic method for \<^emph>\<open>modifying\<close> elements of the
underlying machine state, for example writing to a file, or moving pages between principals, or
similar:\<close>
definition put :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>put f \<equiv> Expression (\<lambda>\<sigma>. Success () (f \<sigma>))\<close>

definition put_assert :: \<open>('a \<Rightarrow> 'a option) \<Rightarrow> 'abort abort \<Rightarrow> ('a, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>put_assert f a \<equiv> Expression (\<lambda>\<sigma>. case f \<sigma> of None \<Rightarrow> Abort a \<sigma> | Some \<sigma>' \<Rightarrow> Success () \<sigma>')\<close>

subsection\<open>Evaluation of lists of expressions\<close>

text\<open>Given a list of expressions, evaluate them each in order and return
a list of the resulting values.\<close>

fun list_sequence :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression list \<Rightarrow> ('s, 'v list, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>list_sequence []     = literal []\<close> |
  \<open>list_sequence (x#xs) =
     bind x (\<lambda>v.
     bind (list_sequence xs) (\<lambda>vs.
       literal (v#vs)))\<close>

subsection\<open>Return expressions\<close>

text\<open>The \<^verbatim>\<open>return_func\<close> command returns a value from a function early, capturing the current state
in doing so.  Note that the \<^emph>\<open>return\<close> command can appear in lots of unexpected places in Rust.
Partly, this is why our \<^typ>\<open>('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close> type is so complex, accepting an extra type
parameter, \<^typ>\<open>'r\<close>, compared to what one may normally expect from a state monad.  This is because
there is a distinction between the type of \<^verbatim>\<open>return_func\<close>, which can be used at type \<^verbatim>\<open>bool\<close> when it
appears as the "test" expression in a conditional, and the type of the value that it returns, namely
the expected return type of the enclosing function.\<close>

definition return_val :: \<open>'r \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>return_val r \<equiv> Expression (\<lambda>\<sigma>. Return r \<sigma>)\<close>

definition return_func :: \<open>('s, 'r, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>return_func v \<equiv> bind v return_val\<close>

text\<open>Note that \<^term>\<open>return_func\<close> is not the \<^emph>\<open>unit\<close> of the expression monad, as one may expect from
the name if you are coming from Haskell!  That is \<^term>\<open>literal\<close>.\<close>

subsection \<open>Calling functions\<close>

text \<open>Execute a Rust function.\<close>
function call_function_body :: \<open>('s, 'b, 'b, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>call_function_body e =
    Expression (\<lambda>\<sigma>.
          (case evaluate e \<sigma> of
             Success x \<sigma>' \<Rightarrow> Success x \<sigma>'
           | Return x \<sigma>'  \<Rightarrow> Success x \<sigma>'
           | Yield \<pi> \<sigma>' e' \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<omega>. call_function_body (e' \<omega>))
           | Abort abt \<sigma>'  \<Rightarrow> Abort abt \<sigma>'))\<close>
by pat_completeness auto

termination
  call_function_body
proof(relation \<open>expression_wf\<close>)
  show \<open>wf expression_wf\<close>
    by force
next
     fix e :: \<open>('a, 'b, 'b, 'c, 'd, 'e) expression\<close>
     and x x1 x2 x3 a
  assume \<open>evaluate e x = Yield x1 x2 x3\<close>
  from this show \<open>(x3 a, e) \<in> expression_wf\<close>
    by (force simp add: expression_wf_def expression_wf_base_def)
qed

declare Core_Expression.call_function_body.simps[simp del]

text \<open>Execute a Rust function.\<close>
definition call :: \<open>('s, 'b, 'abort, 'i, 'o) function_body \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>call fn \<equiv> case fn of FunctionBody body \<Rightarrow> call_function_body body\<close>

subsection\<open>Binary operations\<close>

text\<open>A bit of sugar to reduce the typing burden for binary operations on expressions.\<close>

type_synonym ('s, 'a, 'b, 'c, 'r, 'abort, 'i, 'o) urust_binop3 =
  \<open>('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'c, 'r, 'abort, 'i, 'o) expression\<close>
type_synonym ('s, 'a,         'r, 'abort, 'i, 'o) urust_binop  =
  \<open>('s, 'a, 'a, 'a, 'r, 'abort, 'i, 'o) urust_binop3\<close>
type_synonym ('s, 'a,     'c, 'r, 'abort, 'i, 'o) urust_binop2 =
  \<open>('s, 'a, 'a, 'c, 'r, 'abort, 'i, 'o) urust_binop3\<close>

subsection \<open>Derived constructions\<close>

definition bind1
   :: \<open>('arg0 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind1 f e0 \<equiv> bind e0 (\<lambda>v0. f v0)\<close>

definition bind2
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind2 f e0 e1 \<equiv> bind e0 (\<lambda>v0. bind e1 (\<lambda>v1. (f v0 v1)))\<close>

definition bind3
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind3 f e0 \<equiv> \<lambda>e1 e2. bind e0 (\<lambda>v0. bind2 (f v0) e1 e2)\<close>

definition bind4
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind4 f e0 \<equiv> \<lambda>e1 e2 e3. bind e0 (\<lambda>v0. bind3 (f v0) e1 e2 e3)\<close>

definition bind5
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind5 f e0 \<equiv> \<lambda>e1 e2 e3 e4. bind e0 (\<lambda>v0. bind4 (f v0) e1 e2 e3 e4)\<close>

definition bind6
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind6 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5. bind e0 (\<lambda>v0. bind5 (f v0) e1 e2 e3 e4 e5)\<close>

definition bind7
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind7 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6. bind e0 (\<lambda>v0. bind6 (f v0) e1 e2 e3 e4 e5 e6)\<close>

definition bind8
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7  \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind8 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7. bind e0 (\<lambda>v0. bind7 (f v0) e1 e2 e3 e4 e5 e6 e7)\<close>

definition bind9
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind9 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8. bind e0 (\<lambda>v0. bind8 (f v0) e1 e2 e3 e4 e5 e6 e7 e8)\<close>

definition bind10
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind10 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9. bind e0 (\<lambda>v0. bind9 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9)\<close>

definition bind11
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind11 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9 e10. bind e0 (\<lambda>v0. bind10 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)\<close>

definition bind12
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind12 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11. bind e0 (\<lambda>v0. bind11 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)\<close>

definition bind13
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind13 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12. bind e0 (\<lambda>v0. bind12 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)\<close>

definition bind14
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> 'arg13 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind14 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13. bind e0 (\<lambda>v0. bind13 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)\<close>

definition bind15
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> 'arg13 \<Rightarrow> 'arg14 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg14, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind15 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14. bind e0 (\<lambda>v0. bind14 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)\<close>

definition bind16
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> 'arg13 \<Rightarrow> 'arg14 \<Rightarrow> 'arg15 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg14, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg15, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bind16 f e0 \<equiv> \<lambda>e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15. bind e0 (\<lambda>v0. bind15 (f v0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15)\<close>

definition bindlift1
   :: \<open>('arg0 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift1 \<equiv> bind1 \<circ> lift_exp1\<close>

definition bindlift2
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift2 \<equiv> bind2 \<circ> lift_exp2\<close>

definition bindlift3
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift3 \<equiv> bind3 \<circ> lift_exp3\<close>

definition bindlift4
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift4 \<equiv> bind4 \<circ> lift_exp4\<close>

definition bindlift5
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift5 \<equiv> bind5 \<circ> lift_exp5\<close>

definition bindlift6
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift6 \<equiv> bind6 \<circ> lift_exp6\<close>

definition bindlift7
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift7 \<equiv> bind7 \<circ> lift_exp7\<close>

definition bindlift8
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'v) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>bindlift8 \<equiv> bind8 \<circ> lift_exp8\<close>

abbreviation call_deep1 :: \<open>('t0 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow> ('t0 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep1 \<equiv> deep_compose1 call\<close>
abbreviation call_deep2 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep2 \<equiv> deep_compose2 call\<close>
abbreviation call_deep3 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep3 \<equiv> deep_compose3 call\<close>
abbreviation call_deep4 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow> ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep4 \<equiv> deep_compose4 call\<close>
abbreviation call_deep5 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep5 \<equiv> deep_compose5 call\<close>
abbreviation call_deep6 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep6 \<equiv> deep_compose6 call\<close>
abbreviation call_deep7 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep7 \<equiv> deep_compose7 call\<close>
abbreviation call_deep8 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep8 \<equiv> deep_compose8 call\<close>
abbreviation call_deep9 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep9 \<equiv> deep_compose9 call\<close>
abbreviation call_deep10 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep10 \<equiv> deep_compose10 call\<close>
abbreviation call_deep11 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep11 \<equiv> deep_compose11 call\<close>
abbreviation call_deep12 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep12 \<equiv> deep_compose12 call\<close>
abbreviation call_deep13 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep13 \<equiv> deep_compose13 call\<close>
abbreviation call_deep14 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep14 \<equiv> deep_compose14 call\<close>
abbreviation call_deep15 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep15 \<equiv> deep_compose15 call\<close>
abbreviation call_deep16 :: \<open>('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> 't15 \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
                            ('t0 \<Rightarrow> 't1 \<Rightarrow> 't2 \<Rightarrow> 't3 \<Rightarrow> 't4 \<Rightarrow> 't5 \<Rightarrow> 't6 \<Rightarrow> 't7 \<Rightarrow> 't8 \<Rightarrow> 't9 \<Rightarrow> 't10 \<Rightarrow> 't11 \<Rightarrow> 't12 \<Rightarrow> 't13 \<Rightarrow> 't14 \<Rightarrow> 't15 \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression)\<close> where
  \<open>call_deep16 \<equiv> deep_compose16 call\<close>

definition funcall0
   :: \<open>('s, 'b, 'abort, 'i, 'o) function_body \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall0 f \<equiv> call f\<close>

definition funcall1
   :: \<open>('arg0 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall1 f e0 \<equiv> bind1 (call_deep1 f) e0\<close>

definition funcall2
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall2 f e0 e1 \<equiv> bind2 (call_deep2 f) e0 e1\<close>

definition funcall3
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall3 f e0 e1 e2 \<equiv> bind3 (call_deep3 f) e0 e1 e2\<close>

definition funcall4
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall4 f e0 e1 e2 e3 \<equiv> bind4 (call_deep4 f) e0 e1 e2 e3\<close>

definition funcall5
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall5 f e0 e1 e2 e3 e4 \<equiv> bind5 (call_deep5 f) e0 e1 e2 e3 e4\<close>

definition funcall6
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall6 f e0 e1 e2 e3 e4 e5 \<equiv> bind6 (call_deep6 f) e0 e1 e2 e3 e4 e5\<close>

definition funcall7
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
\<open>funcall7 f e0 e1 e2 e3 e4 e5 e6 \<equiv> bind7 (call_deep7 f) e0 e1 e2 e3 e4 e5 e6\<close>

definition funcall8
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall8 f e0 e1 e2 e3 e4 e5 e6 e7 \<equiv> bind8 (call_deep8 f) e0 e1 e2 e3 e4 e5 e6 e7\<close>

definition funcall9
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall9 f e0 e1 e2 e3 e4 e5 e6 e7 e8 \<equiv> bind9 (call_deep9 f) e0 e1 e2 e3 e4 e5 e6 e7 e8\<close>

definition funcall10
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall10 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 \<equiv> bind10 (call_deep10 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9\<close>

definition funcall11
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall11 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 \<equiv> bind11 (call_deep11 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10\<close>

definition funcall12
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall12 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 \<equiv> bind12 (call_deep12 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11\<close>

definition funcall13
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall13 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 \<equiv> bind13 (call_deep13 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12\<close>

definition funcall14
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> 'arg13 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall14 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 \<equiv> bind14 (call_deep14 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13\<close>

definition funcall15
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> 'arg13 \<Rightarrow> 'arg14 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg14, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall15 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 \<equiv> bind15 (call_deep15 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14\<close>

definition funcall16
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> 'arg2 \<Rightarrow> 'arg3 \<Rightarrow> 'arg4 \<Rightarrow> 'arg5 \<Rightarrow> 'arg6 \<Rightarrow> 'arg7 \<Rightarrow> 'arg8 \<Rightarrow> 'arg9 \<Rightarrow> 'arg10 \<Rightarrow> 'arg11 \<Rightarrow> 'arg12 \<Rightarrow> 'arg13 \<Rightarrow> 'arg14 \<Rightarrow> 'arg15 \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg14, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'arg15, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> where [micro_rust_simps]:
   \<open>funcall16 f e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 \<equiv> bind16 (call_deep16 f) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15\<close>

(*<*)
end
(*>*)
