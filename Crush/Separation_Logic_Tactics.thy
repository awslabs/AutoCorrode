(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Separation_Logic_Tactics
  imports
    Base
    Misc.WordAdditional
    Shallow_Separation_Logic.Assertion_Language
    Shallow_Separation_Logic.Weakest_Precondition
    Micro_Rust_Interfaces_Core.References
  keywords
    "ucincl_proof" "ucincl_auto" :: thy_goal
begin

section\<open>Crush\<close>

ML\<open>
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_constants"}         "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_specs"}             "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_contract_defs"}     "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_inline"}            "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_intros"}            "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_cong"}              "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_cong_default_del"}  "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_early_simps"}       "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_late_simps"}        "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_prems_simps"}       "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_concls_simps"}      "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_aentails_cond_rules"}    "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_aentails_rules"}    "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_aentails_cond_drules"}   "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_aentails_drules"}   "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_wp_split_simps"}    "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_aentails_cond_crules"}   "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_aentails_crules"}   "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_asepconj_simp"}     "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_specs_eager"}       "" #> snd |> Named_Target.theory_map)
   val _ =  Theory.setup (Named_Theorems.declare @{binding "crush_specs_eager_unfold"}"" #> snd |> Named_Target.theory_map)
\<close>

declare function_contract.sel[crush_specs_eager_unfold]
declare Let_def[crush_specs_eager_unfold, crush_early_simps]

subsection\<open>Guards\<close>

definition GUARD where \<open>GUARD x y \<equiv> y\<close>
syntax "_guarded" :: \<open>'a \<Rightarrow> 'a\<close> ("\<parallel>/ _/ \<parallel>")
translations "_guarded x" \<leftharpoondown> "CONST GUARD g x"

lemma ucincl_guard [ucincl_intros]:
  assumes \<open>ucincl \<xi>\<close>
  shows \<open>ucincl (GUARD t \<xi>)\<close>
  using assms by (auto simp add: GUARD_def)

named_theorems add_guards

ML_file "guards.ML"

lemma focus_is_view_guard:
  shows \<open>focus_is_view f x y \<equiv> GUARD x (focus_is_view f x y)\<close>
  by (simp only: GUARD_def)

declare focus_is_view_guard[add_guards]

subsection\<open>Premise unfolding\<close>

definition UNFOLDED :: \<open>bool \<Rightarrow> bool\<close> where \<open>UNFOLDED x \<equiv> x\<close>
lemma UNFOLDED_as_imp: \<open>UNFOLDED a \<Longrightarrow> a\<close> using UNFOLDED_def by auto

ML_file "unfold_prems.ML"

subsection\<open>Separation Logic Tactics\<close>

ML_file "seplog.ML"

subsection\<open>Crush\<close>

ML_file "crush.ML"

ML\<open>open Crush_Tacticals\<close>
ML\<open>open Crush_Time\<close>

subsection\<open>Arithmetic\<close>

ML_file "arith.ML"
ML\<open>open Crush_Arith\<close>

subsection\<open>Debugging\<close>

ML_file "debug.ML"

method_setup aentails_float_pure_concls = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_pure_concls_tac)
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_pure_assms = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_pure_assms_tac)
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_pure_concls' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_pure_concls_tac')
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_pure_assms' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_pure_assms_tac')
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_multi_assms = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_multi_assms_tac)
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_multi_concls = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_multi_concls_tac)
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_multi_assms' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_multi_assms_tac')
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_multi_concls' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_multi_concls_tac')
\<close> "primitive separating conjunction rotation method"

method_setup aentails_float_pure = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (fn i => Separation_Logic_Tactics.aentails_float_pure_tac ctxt i))
\<close> "primitive separating conjunction rotation method"

method_setup asepconj_match_float_asepconj_multi = \<open>
    Scan.succeed (SIMPLE_METHOD' o (Separation_Logic_Tactics.aentails_float_matching_iterated_asepconj))
\<close>

method_setup aentails_cancel_asepconj_multi = \<open>
    Scan.succeed (SIMPLE_METHOD' o (Separation_Logic_Tactics.aentails_cancel_asepconj_multi))
\<close>

method_setup aentails_cancel_once  = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_cancel_core_tac)
\<close> "find and eliminate a pair of unifiable assertions in the assumptions and conclusions of an entailment"

\<comment> \<open>Cancel all matching formulae appearing in a separating conjunction of the premise and
    conclusion of an entailment.\<close>
method aentails_cancel = (aentails_cancel_once+)?

method_setup aentails_float_points_to_raw_assms = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_raw_assms_tac)
\<close>

method_setup aentails_float_points_to_raw_assms' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_raw_assms_tac')
\<close>

method_setup aentails_float_points_to_assms = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_assms_tac)
\<close>

method_setup aentails_float_points_to_assms' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_assms_tac')
\<close>

method_setup aentails_float_points_to_raw_concls = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_raw_concls_tac)
\<close>

method_setup aentails_float_points_to_raw_concls' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_raw_concls_tac')
\<close>

method_setup aentails_float_points_to_concls = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_concls_tac)
\<close>

method_setup aentails_float_points_to_concls' = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_float_points_to_concls_tac')
\<close>

method aentails_split_top_points_to_assm =
  ((intro reference.aentails_split_single_points_to_assm; (solves\<open>rule_tac reference_axioms\<close>)?) |
   (intro reference.aentails_split_top_points_to_assm; (solves\<open>rule_tac reference_axioms\<close>| asepconj_rotate_assms)))

method aentails_split_points_to_assms =
  (aentails_float_points_to_assms', aentails_split_top_points_to_assm)+

method_setup asepconj_match_float_points_to_raw' = \<open>
  let fun is_points_to_raw (Const (@{const_name reference_defs.points_to_raw}, _)) = true
        | is_points_to_raw _ = false in
    Scan.succeed (SIMPLE_METHOD' o (Separation_Logic_Tactics.aentails_cancel_injective is_points_to_raw [2]))
  end
\<close>

method aentails_cancel_points_to_raw = guard \<open>K Separation_Logic_Tactics.is_entailment\<close> \<open>
  asepconj_match_float_points_to_raw', (intro reference.points_to_raw_aentails; (solves\<open>rule_tac reference_axioms\<close>)?)
\<close>

method_setup asepconj_match_float_points_to' = \<open>
  let fun is_points_to (Const (@{const_name reference_defs.points_to}, _)) = true
        | is_points_to _ = false in
    Scan.succeed (SIMPLE_METHOD' o (Separation_Logic_Tactics.aentails_cancel_injective is_points_to [2,3]))
  end
\<close>

method aentails_cancel_points_to = guard \<open>K Separation_Logic_Tactics.is_entailment\<close> \<open>
  asepconj_match_float_points_to', (intro reference.points_to_aentails; (solves\<open>rule_tac reference_axioms\<close>)?)
\<close>

method aentails_cancel_points_to_raw_with_typed = guard \<open>K Separation_Logic_Tactics.is_entailment\<close> \<open>
  aentails_float_points_to_concls', aentails_float_points_to_raw_assms',
    (rule reference.aentails_cancel_points_to_raw_with_typed
          reference.aentails_cancel_points_to_raw_with_typed_0LR
          reference.aentails_cancel_points_to_raw_with_typed_0L
          reference.aentails_cancel_points_to_raw_with_typed_0R,
      (solves\<open>rule reference_axioms\<close>)?,
           solves\<open>time "aentails_cancel_points_to_raw_with_typed_simp" \<open>rule refl | simp\<close>\<close>,
           (rule refl | simp)?)
\<close>

\<comment>\<open>Turn pure separating conclusions into pure HOL subgoals\<close>
method aentails_hoist_pure_concls =
  (aentails_float_pure_concls?, intro apure_entailsR)

(* TODO: This is out of sync with the _tactic_ `aentails_simp_core_tac` *)
method aentails_simp_core = (
  time "aentails_simp_core_float" aentails_float_pure
| time "aentails_simp_core_intro_pure_assms" \<open>ucincl_discharge \<open>intro apure_entailsL0 apure_entailsL\<close>\<close>
| time "aentails_simp_core_intro_pure_concls" \<open>ucincl_discharge \<open>intro apure_entailsR\<close>\<close>
| time "aentails_simp_core_intro_others" \<open>ucincl_discharge \<open>intro
                                            aforall_entailsL aforall_entailsR aexists_entailsL aentails_refl
                                            aentails_top_L aentails_top_R bot_aentails_all all_aentails_true\<close>\<close>
| time "aentails_simp_core_simps" \<open>ucincl_discharge \<open>simp (no_asm_simp) only: asepconj_simp\<close>\<close>
| guard \<open>fn ctxt => K (Config.get ctxt Crush_Config.enable_branch_split)\<close> \<open>
     time "aentails_simp_core_split" \<open>intro aentails_disj_L0\<close>
  \<close>
)

method_setup aentails_cancel_tac = \<open>
  Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_cancel_tac)
\<close>

method aentails_simp_step = ( aentails_simp_core | aentails_cancel_tac )

method aentails_simp_basic = aentails_simp_step+

section\<open>Contracts\<close>

method contract uses f contract =
  (ucincl_discharge \<open>intro satisfies_function_contractI\<close>,
     unfold f,
     subst wp_sstriple_iff,
   ( simp (no_asm) only: contract )? )

method crush_boot uses f contract simp =
  (contract f:f contract:contract,
   micro_rust_ssa_wp_normalize,
   (clarsimp simp add: Let_def simp)?,
   aentails_hoist_pure_assms?)

section\<open>\<^verbatim>\<open>crush\<close>\<close>

declare asepconj_assoc          [crush_asepconj_simp]
declare aentails_disj_distR     [crush_asepconj_simp]
declare aentails_disj_distL     [crush_asepconj_simp]
declare asepconj_multi_empty    [crush_asepconj_simp]
declare asepconj_multi_split'   [crush_asepconj_simp]
declare asepconj_Inf_distrib    [crush_asepconj_simp]
declare asepconj_Inf_distrib2   [crush_asepconj_simp]
declare asepconj_UNIV_idempotent[crush_asepconj_simp]
declare awand_pure_false        [crush_asepconj_simp]

declare refl[crush_intros add]

end
(*>*)
