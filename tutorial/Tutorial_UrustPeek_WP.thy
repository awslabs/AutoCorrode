theory Tutorial_UrustPeek_WP
  imports
    Slides
    Shallow_Separation_Logic.Weakest_Precondition
begin

(*<*)
\<comment>\<open>We want to drop the \<^term>\<open>ucincl\<close> premises from the theorems below to avoid visual clutter
that we don't want to explain at this point. Register a custom term-printing binding to drop the
first premise of term.\<close>
  setup \<open>
    let
      fun is_ucincl_prem t =
        (case t of
          \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>Separation_Algebra.sepalg.ucincl _\<close> $ _ $ _ $ _) => true
        | _ => false);

      fun drop_ucincl _ t =
        Logic.list_implies
          (filter_out is_ucincl_prem (Logic.strip_imp_prems t),
           Logic.strip_imp_concl t);
    in
      Term_Style.setup \<^binding>\<open>drop_ucincl\<close> (Scan.succeed drop_ucincl)
    end
  \<close>

context sepalg begin (*>*)

text \<open>AutoCorrode + uRust heavily rely on a WP calculus along the above lines. Some examples:\<close>

text \<open>\<^bold>\<open>Early return\<close> delivers to the \<^emph>\<open>early-return\<close> post \<open>\<rho>\<close>: @{thm [source] Weakest_Precondition.wp_returnI}\<close>

text \<open>@{thm [display, show_question_marks=false] (drop_ucincl) wp_returnI}\<close>

text \<open>\<^bold>\<open>Panic\<close> delivers to the \<^emph>\<open>abort\<close> post \<open>\<theta>\<close>: @{thm [source] Weakest_Precondition.wp_panicI}\<close>

text \<open>@{thm [display, show_question_marks=false] (drop_ucincl) wp_panicI}\<close>

text \<open>Recall: uRust's \<^emph>\<open>three\<close> postconditions \<open>\<psi>\<close> / \<open>\<rho>\<close> / \<open>\<theta>\<close> separate value/return/abort.\<close>

text \<open>\<^bold>\<open>Word addition\<close> -- arithmetic operators get WP rules, with appropriate constraints:\<close>

text \<open>@{thm [display, show_question_marks=false] (drop_ucincl) wp_word_add_no_wrap}\<close>

text \<open>The full set lives in \<open>Weakest_Precondition.thy\<close> (literals,
  conditionals, calls, assert, yield, ...).\<close>

(*<*) end (*>*)

end
