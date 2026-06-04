theory Tutorial_UrustPeek_Triple
  imports
    Slides
    Shallow_Separation_Logic.Weak_Triple
begin

text \<open>AutoCorrode builds triples in a 3-step fashion. First, for pairs of states ("assertion triple"):\<close>

(*<*) context sepalg begin (*>*)

text \<open>@{thm [display, show_question_marks=false] atriple_def}\<close>

(*<*) end (*>*)

text \<open>Second, the weak triple for uRust expressions, which applies the assertion triple to the
  value/return/abort transitions associated with the program:\<close>

(*<*) context sepalg begin (*>*)

text \<open>@{thm [display, show_question_marks=false] striple_def}\<close>

(*<*) end (*>*)

text \<open>Finally, there is a \<^emph>\<open>strong\<close> triple which adds \<^bold>\<open>locality\<close>: Anything outside the frame does not
influence the execution of the program. \<^bold>\<open>This is not automatic!\<close>. We don't consider it here.\<close>

end
