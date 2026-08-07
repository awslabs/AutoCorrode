(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Base
  imports Main
  keywords
    "enable_print_timings" "disable_print_timings" "enable_timings" "disable_timings"
    "reset_timelogs" "show_timelogs" "apply\<tau>" "step" :: prf_script % "proof"
begin

subsection \<open>Configuration\<close>

ML_file "config.ML"

subsection \<open>Base material\<close>

ML_file "base.ML"
ML\<open>open Crush_Base\<close>

subsection\<open>Parsers\<close>

ML_file "parsers.ML"

subsection \<open>Tactic profiling\<close>

ML_file "time.ML"
ML\<open>open Crush_Time\<close>


subsection\<open>Meng-Paulson filter for premises\<close>

definition IGNORE :: \<open>prop \<Rightarrow> prop\<close> where
  \<open>IGNORE (PROP x) \<equiv> (PROP x)\<close>

lemma IGNORE_splitE:
  assumes \<open>PROP IGNORE (PROP P &&& PROP Q)\<close>
     and \<open>PROP IGNORE P \<Longrightarrow> PROP IGNORE Q \<Longrightarrow> PROP R\<close>
   shows \<open>PROP R\<close>
  using assms apply -
  apply (simp add: IGNORE_def conjunction_imp)
  apply (rule revcut_rl; assumption)
  done

definition IGNORE_imp :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close> where
  \<open>IGNORE_imp (PROP P) (PROP Q) \<equiv> (PROP (IGNORE (PROP P)) \<Longrightarrow> (PROP Q))\<close>
notation IGNORE_imp ("_ \<Longrightarrow>'' _")

lemma IGNORE_imp_mergeI:
  assumes \<open>(PROP P &&& PROP Q) \<Longrightarrow>' PROP R\<close>
  shows \<open>PROP P \<Longrightarrow>' (PROP Q \<Longrightarrow>' PROP R)\<close>
  using assms apply -
  apply (simp add: IGNORE_def IGNORE_imp_def conjunction_imp)
  apply (rule revcut_rl; assumption)
  done

lemma IGNORE_imp_cong [cong]:
  assumes \<open>PROP Q0 \<equiv> PROP Q1\<close>
  shows \<open>PROP IGNORE_imp (PROP P) (PROP Q0) \<equiv> PROP IGNORE_imp (PROP P) (PROP Q1)\<close>
  using assms unfolding IGNORE_imp_def by simp

lemma IGNORE_imp_ignoreE:
  assumes \<open>PROP P\<close>
  and \<open>PROP P \<Longrightarrow>' PROP R\<close>
  shows \<open>PROP R\<close>
  using assms unfolding IGNORE_def IGNORE_imp_def apply -
  apply (rule revcut_rl; assumption)
  done

lemma IGNORE_imp_unwrapI:
  assumes \<open>PROP IGNORE (PROP P) \<Longrightarrow> PROP R\<close>
  shows \<open>PROP P \<Longrightarrow>' PROP R\<close>
  using assms unfolding IGNORE_imp_def apply -
  apply (rule revcut_rl; assumption)
  done

lemma IGNORE_unwrapE:
  assumes \<open>PROP IGNORE (PROP P)\<close>
  and \<open>PROP P \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
  using assms unfolding IGNORE_def apply -
  apply (rule revcut_rl; assumption)
  done

lemma IGNORE_cong [cong]:
  shows \<open>PROP (IGNORE P) \<equiv> PROP (IGNORE P)\<close>
  unfolding IGNORE_def by simp

syntax (output) "_premise_elided" :: \<open>prop \<Rightarrow> prop\<close> ("\<dots>'(ignored')\<dots> \<Longrightarrow> _")
translations
  "_premise_elided z" \<leftharpoondown> "CONST Pure.imp (CONST IGNORE y) z"
  "_premise_elided z" \<leftharpoondown> "_premise_elided (_premise_elided z)"

ML_file "mepo_core.ML"
ML_file "mepo_prem.ML"

subsection \<open>Various tacticals\<close>

ML_file "tacticals.ML"
ML\<open>open Crush_Tacticals\<close>

end
(*>*)
