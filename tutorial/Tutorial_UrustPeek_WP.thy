theory Tutorial_UrustPeek_WP
  imports
    Slides
    Shallow_Separation_Logic.Weakest_Precondition
begin

(*<*) context sepalg begin (*>*)

text \<open>AutoCorrode + uRust heavily rely on a WP calculus along the above lines. Some examples:\<close>

text \<open>\<^bold>\<open>Early return\<close> delivers to the \<^emph>\<open>early-return\<close> post \<open>\<rho>\<close>: @{thm [source] Weakest_Precondition.wp_returnI}\<close>

text \<open>@{thm [display, show_question_marks=false] wp_returnI}\<close>

text \<open>\<^bold>\<open>Panic\<close> delivers to the \<^emph>\<open>abort\<close> post \<open>\<theta>\<close>: @{thm [source] Weakest_Precondition.wp_panicI}\<close>

text \<open>@{thm [display, show_question_marks=false] wp_panicI}\<close>

text \<open>Recall: uRust's \<^emph>\<open>three\<close> postconditions \<open>\<psi>\<close> / \<open>\<rho>\<close> / \<open>\<theta>\<close> separate value/return/abort.\<close>

text \<open>\<^bold>\<open>Word addition\<close> -- arithmetic operators get WP rules, with appropriate constraints:\<close>

text \<open>@{thm [display, show_question_marks=false] wp_word_add_no_wrap}\<close>

text \<open>The constraint that rules out wrap-around appears as a factor \<open>\<langle>_\<rangle>\<close> of the
  precondition: a \<^emph>\<open>pure\<close> assertion, recording a fact about the values and owning
  none of the machine state. \<open>\<star>\<close> and \<open>\<langle>_\<rangle>\<close> are the subject of the second half.\<close>

text \<open>The full set lives in \<open>Weakest_Precondition.thy\<close> (literals,
  conditionals, calls, assert, yield, ...).\<close>

(*<*) end (*>*)

end
