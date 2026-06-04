theory Tutorial_UrustPeek_Eval
  imports
    Slides
    Shallow_Micro_Rust.Eval
begin

text \<open>uRust has \<^emph>\<open>three\<close> evaluation relations -- \<open>\<leadsto>\<^sub>v\<close>, \<open>\<leadsto>\<^sub>r\<close>, \<open>\<leadsto>\<^sub>a\<close> for value, return, and abort.\<close>

text \<open>\<^bold>\<open>Early return\<close> -- delivers to the early-return arrow \<open>\<leadsto>\<^sub>r\<close>:
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_return(1)}
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_return(2)}
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_return(3)}\<close>

text \<open>\<^bold>\<open>Word addition\<close> -- the no-overflow guard shows up as a hypothesis on
  the value arrow \<open>\<leadsto>\<^sub>v\<close>:
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_add_no_wrap(1)}
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_add_no_wrap(2)}
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_add_no_wrap(3)}\<close>

text\<open>\<^bold>\<open>Function calls\<close> merge the value and return paths:
\<^item> @{thm [show_question_marks=false] urust_eval_predicate_call(1)}\<close>

end
