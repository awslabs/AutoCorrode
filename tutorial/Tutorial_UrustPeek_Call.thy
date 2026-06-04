theory Tutorial_UrustPeek_Call
  imports
    Slides
    Shallow_Separation_Logic.Weakest_Precondition
begin

text \<open>uRust's call-by-contract rule has the same shape, but with the
  three postconditions and a magic-wand encoding of the
  ``post-implies-frame'' obligation:\<close>

(*<*) context sepalg begin (*>*)

text \<open>@{thm [show_question_marks=false] wp_callI}\<close>

(*<*) end (*>*)

text \<open>Again the wand \<open>\<phi> \<Zsurj> \<psi>\<close> reads ``swap a state satisfying \<open>\<phi>\<close> for one
  satisfying \<open>\<psi>\<close>'' -- exactly the consequence step the toy version's
  third premise expresses pointwise.\<close>

end
