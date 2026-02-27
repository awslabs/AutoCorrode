(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Prompts_And_Responses
  imports Core_Expression
begin
(*>*)

section\<open>Prompts and responses\<close>

subsection\<open>Primitive prompts and responses\<close>

text\<open>This is the priority of the log message.  Separating this allows us to control log output and
filter different types of messages in the prompt handler.\<close>
datatype log_priority
    \<comment> \<open>Trace log level for function-call tracing\<close>
  = Trace
    \<comment> \<open>Debug log level\<close>
  | Debug
    \<comment> \<open>Error log level for error state printing\<close>
  | Error
    \<comment> \<open>Info log level for informational messages\<close>
  | Info
    \<comment> \<open>Fatal log level for fatal error states\<close>
  | Fatal

text\<open>These are the various requests that a \<^verbatim>\<open>\<mu>Rust\<close> program can make to its environment, and are
intuitively somewhat akin to \<^emph>\<open>system calls\<close> or similar:\<close>
datatype 'a prompt
    \<comment> \<open>Yield to the environment; return value will be ignored; state must not be changed\<close>
  = Pause
    \<comment> \<open>Yield logging data to the environment with a given priority: return value will be ignored,
        state must not be changed\<close>
  | Log \<open>log_priority\<close> \<open>log_data\<close>
    \<comment> \<open>This signals that a fatal hardware error has occurred outside of the ``closed world'' of the
        \<^verbatim>\<open>\<mu>Rust\<close> program\<close>
  | FatalError \<open>String.literal\<close>
    \<comment> \<open>Internal nondeterministic branch choice used by the semantics layer\<close>
  | NondetOrder
    \<comment> \<open>Something entirely domain specific specified later\<close>
  | DomainSpecificPrompt \<open>'a\<close>

text\<open>These are the various responses that a yield handler can give back a \<^verbatim>\<open>\<mu>Rust\<close> program in
response to a yield to its environment:\<close>
datatype 'a prompt_output
    \<comment> \<open>Generic acknowledgement reply for commands expecting no answer back from the environment\<close>
  = Ack
    \<comment> \<open>Internal branch choices used for @{term NondetOrder}\<close>
  | NondetLeft
  | NondetRight
    \<comment> \<open>Something entirely domain specific specified later\<close>
  | DomainSpecificResponse \<open>'a\<close>

subsection\<open>Calling primitive prompts from Micro Rust\<close>

text\<open>A generic yield:\<close>

definition yield :: \<open>'i prompt \<Rightarrow> ('s, 'o prompt_output, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>yield \<omega> \<equiv> Expression (\<lambda>\<sigma>. Yield \<omega> \<sigma> literal)\<close>

text\<open>The following is a yield to the external environment for informational purposes. The value
returned from the environment is ignored and should be an \<^verbatim>\<open>Ack\<close>.\<close>

definition pause :: \<open>('s, unit, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>pause \<equiv> Expression (\<lambda>\<sigma>. Yield Pause \<sigma> (\<lambda>_. skip))\<close>

text\<open>A \<^emph>\<open>fatal\<close> expression yields to the environment with a defined error message. Fatal errors
represent an irrecoverable error condition, similar to a panic; however, unlike panic,
we cannot prove that fatal errors will not happen. They are modeled here as a yield to the
environment, which abstracts some mechanism where we expect the entire system to be abruptly
shut down. In particular, we do not expect our continuation to be scheduled again.\<close>
definition fatal :: \<open>String.literal \<Rightarrow> ('s, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>fatal msg \<equiv> Expression (\<lambda>\<sigma>. Yield (FatalError msg) \<sigma> (\<lambda>_. abort ResumedFromFatal))\<close>

text\<open>The \<^verbatim>\<open>log\<close> construct grants us access to the primitive logging machinery from \<^verbatim>\<open>\<mu>Rust\<close>:\<close>
definition log :: \<open>log_priority \<Rightarrow> log_data \<Rightarrow> ('s, unit, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>log p d \<equiv> Expression (\<lambda>\<sigma>. Yield (Log p d) \<sigma> (\<lambda>_. skip))\<close>

text\<open>Internal nondeterministic branch choice. The branch is selected by the yield handler via
\<^term>\<open>NondetLeft\<close> or \<^term>\<open>NondetRight\<close>.\<close>
definition nondet_choice ::
  \<open>('s, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where [micro_rust_simps]:
  \<open>nondet_choice l r \<equiv>
     bind (yield NondetOrder) (\<lambda>resp.
       if resp = NondetLeft then l else r)\<close>

definition bind2_unseq
   :: \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow> ('s, 'v, 'c, 'abort, 'i prompt, 'o prompt_output) expression) \<Rightarrow>
      ('s, 'arg0, 'c, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
      ('s, 'arg1, 'c, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i prompt, 'o prompt_output) expression\<close> where [micro_rust_simps]:
   \<open>bind2_unseq f e0 e1 \<equiv>
      nondet_choice
        (bind e0 (\<lambda>v0. bind e1 (\<lambda>v1. f v0 v1)))
        (bind e1 (\<lambda>v1. bind e0 (\<lambda>v0. f v0 v1)))\<close>

subsection\<open>Some properties of specialized yield-handlers\<close>

text\<open>A \<^emph>\<open>log-transparent\<close> yield handler ignores \<^term>\<open>Pause\<close> and \<^term>\<open>Log\<close> prompts.\<close>

definition is_log_prompt :: \<open>'a prompt \<Rightarrow> bool\<close> where
  \<open>is_log_prompt \<pi> \<equiv> case \<pi> of
     Pause   \<Rightarrow> True
   | Log _ _ \<Rightarrow> True
   | _       \<Rightarrow> False\<close>

lemma is_log_prompt_simps [simp]:
  shows \<open>is_log_prompt Pause     = True\<close>
    and \<open>is_log_prompt (Log p l) = True\<close>
    and \<open>is_log_prompt NondetOrder = False\<close>
by (auto simp add: is_log_prompt_def)

definition is_log_transparent_yield_handler :: \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow> bool\<close> where
  \<open>is_log_transparent_yield_handler y \<equiv> \<forall>\<sigma> \<pi>. is_log_prompt \<pi> \<longrightarrow> y \<pi> \<sigma> = { YieldContinue (Ack, \<sigma>) }\<close>

definition is_nondet_order_yield_handler ::
  \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow> bool\<close> where
  \<open>is_nondet_order_yield_handler y \<equiv>
     \<forall>\<sigma>. y NondetOrder \<sigma> = {YieldContinue (NondetLeft, \<sigma>), YieldContinue (NondetRight, \<sigma>)}\<close>

text\<open>Once we encounter functions throwing \<^verbatim>\<open>FatalError\<close> that we don't control, we will need to further
impose the condition that a yield handler does not continue afterwards:\<close>

definition is_aborting_yield_handler :: \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow> bool\<close> where
  \<open>is_aborting_yield_handler y \<equiv>
    \<comment> \<open>The environment does not reschedule a thread after a fatal error.\<close>
    \<forall>\<sigma> msg. y (FatalError msg) \<sigma> = {}\<close>

text\<open>Validity of a specification with respect to the following \<^emph>\<open>no-yield\<close> yield handler significies 
that no yields can happen except for \<^verbatim>\<open>Log\<close> and \<^verbatim>\<open>Pause\<close>:\<close>

definition yield_handler_no_yield :: \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic\<close> where
  \<open>yield_handler_no_yield \<equiv> \<lambda>p \<sigma>. 
     if is_log_prompt p then
        { YieldContinue (Ack, \<sigma>) }
     else if p = NondetOrder then
        { YieldContinue (NondetLeft, \<sigma>), YieldContinue (NondetRight, \<sigma>) }
     else
        { YieldAbort UnexpectedYield \<sigma> }\<close>

definition yield_handler_det_no_yield :: \<open>('s, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) yield_handler_det\<close> where
  \<open>yield_handler_det_no_yield \<equiv> \<lambda>p c \<sigma>. 
     if is_log_prompt p then
       c Ack \<sigma>
     else if p = NondetOrder then
       c NondetLeft \<sigma>
     else
       Abort UnexpectedYield \<sigma>\<close>

lemma yield_handler_no_yield_is_log_transparent [simp]:
  shows \<open>is_log_transparent_yield_handler yield_handler_no_yield\<close>
by (auto simp add: is_log_transparent_yield_handler_def yield_handler_no_yield_def)

lemma yield_handler_no_yield_is_nonempty [simp]:
  shows \<open>is_nonempty_yield_handler yield_handler_no_yield\<close>
by (auto simp add: is_nonempty_yield_handler_def yield_handler_no_yield_def)  

lemma yield_handler_no_yield_is_nondet_order [simp]:
  shows \<open>is_nondet_order_yield_handler yield_handler_no_yield\<close>
  by (auto simp add: is_nondet_order_yield_handler_def yield_handler_no_yield_def)

text\<open>Correctness of a \<^verbatim>\<open>\<mu>Rust\<close> program with respect to pre/post conditions and a yield
handler entails that \<^verbatim>\<open>Abort\<close> will never happen. In particular, if a program is correct with
respect to a yield handler that may \<^emph>\<open>YieldAbort\<close>, it will also be correct with respect to any
other yield handler which choses a different set of actions at the respective yield prompt. We
encapsulate this in the following partial order on yield handlers:\<close>

definition yield_handler_no_abort_at :: \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow>
      'i prompt \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>yield_handler_no_abort_at y \<pi> \<sigma> \<equiv> \<forall>a \<sigma>'. YieldAbort a \<sigma>' \<notin> y \<pi> \<sigma>\<close>

abbreviation yield_handler_abort_at :: \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow>
      'i prompt \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>yield_handler_abort_at y \<pi> \<sigma> \<equiv> \<not> yield_handler_no_abort_at y \<pi> \<sigma>\<close>

definition yield_handler_nondet_basic_refines :: \<open>('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow>
    ('s, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic \<Rightarrow> bool\<close> where
  \<open>yield_handler_nondet_basic_refines y x \<equiv> \<forall>\<pi> \<sigma>. yield_handler_no_abort_at x \<pi> \<sigma> \<longrightarrow> y \<pi> \<sigma> = x \<pi> \<sigma>\<close>

lemma yield_handler_no_yield_abort_at:
  shows \<open>yield_handler_no_abort_at yield_handler_no_yield p \<sigma> = (is_log_prompt p \<or> p = NondetOrder)\<close>
by (simp add: yield_handler_no_yield_def yield_handler_no_abort_at_def)

text\<open>Every log-transparent yield handler refines the no-yield yield handler:\<close>

lemma yield_handler_nondet_basic_refines_top:
  assumes \<open>is_log_transparent_yield_handler y\<close>
      and \<open>is_nondet_order_yield_handler y\<close>
    shows \<open>yield_handler_nondet_basic_refines y yield_handler_no_yield\<close>
using assms by (clarsimp simp add: yield_handler_nondet_basic_refines_def
  is_log_transparent_yield_handler_def is_nondet_order_yield_handler_def
  yield_handler_no_yield_abort_at) (auto simp add:
  yield_handler_no_yield_def)

(*<*)
end
(*>*)
