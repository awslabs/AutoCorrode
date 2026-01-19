(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Configuration options for the crush proof automation *)

signature CRUSH_CONFIG =
sig
  (* profile time of entire crush steps *)
  val time_steps : bool Config.T
  (* profile time of individual crush branches *)
  val time_toplevel : bool Config.T
  (* profile time of guard updates *)
  val time_guards : bool Config.T
  (* profile time of ucincl discharge *)
  val time_ucincl : bool Config.T
  (* profile time of separating entailment cancellation *)
  val time_aentails_cancel : bool Config.T
  (* profile time of separating entailment core tactic *)
  val time_aentails_core : bool Config.T
  (* profile time simplification branch *)
  val time_clarsimp : bool Config.T
  (* profile time of premise unfolding *)
  val time_unfold_prems : bool Config.T
  (* profile time of transaction tactic *)
  val time_transactions : bool Config.T
  (* profile time spent in uRust function invocations *)
  val time_calls : bool Config.T
  val time_base_simps : bool Config.T
  (* profile time spent on initialization crush step tactic *)
  val time_step_instantiation : bool Config.T
  val time_step_instantiation_by_branch : bool Config.T
  (* profile time spent on passing logger to crush step tactic *)
  val time_step_log_instantiation : bool Config.T

  val simp_general_implies_prems : bool Config.T
  val simp_general_implies_concls : bool Config.T

  val time_pagetac : bool Config.T
  val log_pagetac : bool Config.T

  (* log individual crush branches *)
  val log_toplevel : bool Config.T
  (* log sub-branches of simplification branch *)
  val log_clarsimp : bool Config.T
  (* log function calls *)
  val log_calls : bool Config.T
  (* log ucincl discharge *)
  val log_ucincl : bool Config.T
  (* log sub-branches of transaction tactic *)
  val log_transactions : bool Config.T
  (* log crush setup time *)
  val log_aentails_cancel : bool Config.T
  val log_aentails_core : bool Config.T
  val log_base_simps : bool Config.T

  val log_goal : bool Config.T

  val enable_branch_safe : bool Config.T
  val enable_branch_clarsimp : bool Config.T
  val enable_branch_clarsimp_warn_at_success : bool Config.T
  val enable_branch_clarsimp_stop_at_success : bool Config.T
  val enable_branch_filtered_clarsimp : bool Config.T
  val enable_branch_reduced_clarsimp : bool Config.T
  val enable_schematics : bool Config.T
  val enable_branch_split : bool Config.T

  val enable_base_simps_detect_aentails_contradiction : bool Config.T
  val enable_base_simps_early_unfold : bool Config.T

  (* This option enables/disables custom automation for points-to in crush.
     Ultimately, this should be removed, and all reasoning about points-to
     expressed in terms of suitable rules/drules/crules. *)
  val enable_legacy_points_to_tactics: bool Config.T

  val enable_urust_split_branch : bool Config.T
  val enable_urust_determine_branch : bool Config.T

  val debug_level : int Config.T
  val do_big_steps : bool Config.T
  val prioritize_changed_goals : bool Config.T
  val gas : int Config.T
  val keep_history : bool Config.T
  val stepwise : bool Config.T

  val cancel_pure : bool Config.T
  val step_time_bound_ms : int Config.T

  val relevance_filter_max_facts : int Config.T

  val crush_simp_trace_enable : bool Config.T

  val crush_force_inline : bool Config.T
  val fail_on_bad_schematic : bool Config.T

end;

structure Crush_Config: CRUSH_CONFIG =
struct

  val crush_simp_trace_enable =
    Attrib.setup_config_bool @{binding "crush_simp_trace_enable"} (K false)

  val time_toplevel = Attrib.setup_config_bool @{binding "crush_time_toplevel"} (K true)
  val time_steps = Attrib.setup_config_bool @{binding "crush_time_steps"} (K false)
  val time_guards = Attrib.setup_config_bool @{binding "crush_time_guards"} (K false)
  val time_ucincl = Attrib.setup_config_bool @{binding "crush_time_ucincl"} (K false)
  val time_clarsimp = Attrib.setup_config_bool @{binding "crush_time_clarsimp"} (K false)
  val time_aentails_cancel = Attrib.setup_config_bool @{binding "crush_time_aentails_cancel"} (K false)
  val time_aentails_core = Attrib.setup_config_bool @{binding "crush_time_aentails_core"} (K false)
  val time_unfold_prems = Attrib.setup_config_bool @{binding "crush_time_unfold_prems"} (K false)
  val time_calls = Attrib.setup_config_bool @{binding "crush_time_calls"} (K false)
  val time_base_simps = Attrib.setup_config_bool @{binding "crush_time_base_simps"} (K false)
  val time_step_instantiation = Attrib.setup_config_bool @{binding "crush_time_instantiation"} (K false)
  val time_step_instantiation_by_branch = Attrib.setup_config_bool @{binding "crush_time_instantiation_by_branch"} (K false)
  val time_step_log_instantiation = Attrib.setup_config_bool @{binding "crush_time_log_instantiation"} (K false)

  val time_pagetac = Attrib.setup_config_bool @{binding "crush_time_pagetac"} (K false)
  val log_pagetac = Attrib.setup_config_bool @{binding "crush_log_pagetac"} (K false)

  val log_toplevel = Attrib.setup_config_bool @{binding "crush_log_toplevel"} (K false)
  val log_clarsimp = Attrib.setup_config_bool @{binding "crush_log_clarsimp"} (K false)
  val log_calls = Attrib.setup_config_bool @{binding "crush_log_calls"} (K true)
  val log_ucincl = Attrib.setup_config_bool @{binding "crush_log_ucincl"} (K false)
  val log_aentails_cancel = Attrib.setup_config_bool @{binding "crush_log_aentails_cancel"} (K false)
  val log_aentails_core = Attrib.setup_config_bool @{binding "crush_log_aentails_core"} (K false)
  val log_base_simps = Attrib.setup_config_bool @{binding "crush_log_base_simps"} (K false)

  val log_goal = Attrib.setup_config_bool @{binding "crush_log_goal"} (K false)

  val enable_branch_safe = Attrib.setup_config_bool @{binding "use_safe"} (K true)
  val enable_branch_clarsimp = Attrib.setup_config_bool @{binding "crush_use_clarsimp"} (K true)
  val enable_branch_clarsimp_stop_at_success = Attrib.setup_config_bool @{binding "crush_stop_at_full_blown_clarsimp"} (K false)
  val enable_branch_clarsimp_warn_at_success = Attrib.setup_config_bool @{binding "crush_warn_at_full_blown_clarsimp"} (K true)
  (* TODO: Consider enabling this by default *)
  val enable_branch_filtered_clarsimp = Attrib.setup_config_bool @{binding "crush_use_filtered_clarsimp"} (K false)
  (* TODO: Consider enabling this by default *)
  val enable_branch_reduced_clarsimp = Attrib.setup_config_bool @{binding "crush_use_reduced_clarsimp"} (K false)
  val enable_schematics = Attrib.setup_config_bool @{binding "crush_allow_schematics"} (K true)
  val enable_urust_split_branch = Attrib.setup_config_bool @{binding "crush_urust_split_branch"} (K true)
  val enable_urust_determine_branch = Attrib.setup_config_bool @{binding "crush_urust_determine_branch"} (K true)
  val enable_branch_split = Attrib.setup_config_bool @{binding "crush_do_split"}  (K false)

  val time_transactions = Attrib.setup_config_bool @{binding "crush_time_transactions"} (K false)
  val log_transactions = Attrib.setup_config_bool @{binding "crush_log_transactions"} (K false)

  val debug_level = Attrib.setup_config_int @{binding "crush_debug_level"} (K ~1)
  val do_big_steps = Attrib.setup_config_bool @{binding "crush_do_big_steps"} (K true)
  val gas = Attrib.setup_config_int @{binding "crush_gas"} (K 100000)
  val keep_history = Attrib.setup_config_bool @{binding "crush_keep_history"} (K false)
  val stepwise = Attrib.setup_config_bool @{binding "crush_stepwise"} (K false)
  val prioritize_changed_goals = Attrib.setup_config_bool @{binding "crush_prioritize_changed_goals"} (K false)

  val crush_force_inline = Attrib.setup_config_bool @{binding "crush_force_inline"} (K false)

  val cancel_pure = Attrib.setup_config_bool @{binding "crush_cancel_pure"} (K false)
  val step_time_bound_ms = Attrib.setup_config_int @{binding "crush_time_step_bound_ms"} (K 10000)

  val fail_on_bad_schematic = Attrib.setup_config_bool @{binding "crush_fail_on_bad_schematic"} (K true)

  val enable_base_simps_early_unfold = Attrib.setup_config_bool @{binding "crush_enable_early_unfold"} (K true)
  val enable_base_simps_detect_aentails_contradiction = Attrib.setup_config_bool @{binding "crush_enable_contradiction_detection"} (K true)

  val relevance_filter_max_facts = Attrib.setup_config_int @{binding "crush_relevance_filter_max_facts"} (K 20)

  val simp_general_implies_prems = Attrib.setup_config_bool @{binding "crush_simp_general_implies_prems"} (K false)
  val simp_general_implies_concls = Attrib.setup_config_bool @{binding "crush_simp_general_implies_concls"} (K false)

  val enable_legacy_points_to_tactics = Attrib.setup_config_bool @{binding "crush_enable_legacy_points_to_tactic"} (K true)

end;
