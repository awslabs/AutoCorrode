(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*
The `crush` family of tactics.

`crush` is a high-level tactic for dealing with goals in classical and
separation logic. `crush` is never trying to be 'clever'. Its goal, instead,
is to do the 'obvious' thing, reliably, and to discharge hundreds or thousands
of elementary reasoning steps at once. The proof author is left with the
tasks of calling `crush` suitably, and filling in the steps that `crush`
cannot solve (such as providing loop invariants, for example).

The birds'-eye view of `crush` is that of a long disjunction of different branches.
That is, try branch A; if it fails, try branch B; if it fails, try branch C, and so on.
Care is taken to choose the order of branches correctly, which matters both for correctness
and for performance: Regarding correctness, for example, introducing schematic variables must
be handled with a lower priority than operations introducing free variables -- otherwise, the
schematic variables may not instantiate correctly. Regarding performance, powerful tactics
such as a plain `simp` or `clarsimp` have to be called with low priority, or otherwise `crush`
will be too slow for highly complex goals that it aims to be usable for. Even more powerful tactics
such as `force`, `blast` or `auto` are not considered at all. Instead, branches aim to implement
their solution strategy through a mixture of standard tactics `simp only`, `elim`, and `intro`,
or custom ML.

`crush` is highly configurable and shares part of its configuration mechanism with the classical
reasonders such as `clarsimp`, `force` or `auto`: That is, simplification rules can be added/removed
via `simp add/del: ...`, introduction, split and elimination rules can be added via `intro: ...`,
`elim: ...` or `split: ...`. However, there are various other configuration options that the user
needs to be aware of, some specific to separation logic, some refining the classical reasoning.
Those configuration options are described in `config.ML`. It is essential that the users familiarizes
themselves with the configurations, as a bare `apply crush` is rarely getting far.

`crush` comes in three variants:

- `crush_base_step`: A single iteration of the `crush` loop
- `fastcrush_base`: Run the `crush` loop on the current goal and all emerging goals, until no
   progress can be made anymore.
- `crush_base`: Run the `crush` loop on all goals and all emerging goals, until no progress
   can be made anymore.

Since, like `auto` for example, `crush_base` can affect the entire goal set, using it in the middle
of proofs can make them harder to maintain. Relying on `fastcrush_base` usually leads to more robust
proofs. Finally, `crush_base_step` is mostly useful for debugging purposes; complex proofs require
hundreds of iterations of the `crush` loop, so manual invocation of `crush_base_step` is typically
not useful.

*)

signature CRUSH =
sig
  exception CRUSH of string

  (* Run a single step of the `crush` loop on the given goal *)
  val crush_base_step_tac : Proof.context -> logger -> int -> tactic
  (* Repeatedly run `crush` on all goals *)
  val crush_base_tac : Proof.context -> tactic
  (* Repeatedly run `crush` on the current and all emerging goals *)
  val fastcrush_base_tac : Proof.context -> tactic

  val crush_modifiers : Method.modifier parser list

  (* Tactical wrapping `crush` core into various pre/post processing and timing operations
     Variants/extensions of `crush` will likely want to keep this and merely adjust the core. *)
  val crush_step_tac_frame : (Proof.context -> logger -> int -> tactic) -> (Proof.context -> logger -> int -> tactic)
  (* The core of each `crush` iteration: Long disjunction of various tactics. *)
  val crush_base_step_tac_core : Proof.context -> logger -> int -> tactic

  val crush_base_unfold_contract_tac : Proof.context -> int -> tactic

  (* Various branches of crush *)
  val crush_branch_base_simps_tac : Proof.context -> int -> tactic
  val crush_branch_destruct_tac : Proof.context -> int -> tactic
  val crush_branch_wp_intros_tac : Proof.context -> int -> tactic
  val crush_branch_call_tac : Proof.context -> bool -> (int -> tactic) -> int -> tactic
  val crush_branch_wp_case_split_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_cancel_tac : Proof.context -> int -> tactic
  val crush_branch_unfold_prems_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_core_tac : Proof.context -> int -> tactic
  val crush_branch_determine_branch : Proof.context -> int -> tactic
  val crush_branch_aentails_drule_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_crule_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_rule_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_cond_drule_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_cond_rule_tac : Proof.context -> int -> tactic
  val crush_branch_aentails_cond_crule_tac : Proof.context -> int -> tactic
  val crush_branch_focus_core_tac : Proof.context -> int -> tactic
  val crush_branch_focus_tac : Proof.context -> int -> tactic
  val crush_branch_unfold_concls_tac : Proof.context -> int -> tactic
  val crush_branch_schematics_tac : Proof.context -> (int -> tactic) -> int -> tactic
  val crush_branch_intro_pure_aentails_tac : Proof.context -> int -> tactic
  val crush_branch_clarsimp_tac : Proof.context -> int -> tactic
  val crush_branch_clarsimp_fallback_tac : Proof.context -> int -> tactic
  val crush_branch_filtered_clarsimp_tac : Proof.context -> int -> tactic
  val crush_branch_urust_simps_tac : Proof.context -> int -> tactic
  val crush_branch_misc_tac : Proof.context -> int -> tactic
  val crush_branch_ucincl_tac : Proof.context -> int -> tactic
  val crush_branch_additional_tactic : Proof.context -> int -> tactic
  val crush_branch_additional_method : Proof.context -> int -> tactic
  val crush_branch_safe_tac : Proof.context -> int -> tactic

  val crush_register_contract_attrib: bool -> attribute

  val crush_base_simpset : simpset

  exception ABORT of string
end;

structure Crush: CRUSH =
struct

  exception ABORT of string
  exception CRUSH of string

  (* This seems hacky... I essentially want HOL_ss without if_split, but I don't know
     how to remove a split rule from the simpset directly. *)
  val crush_base_simpset = @{context}
                           |> put_simpset HOL_ss
                           |> Splitter.del_split @{thm if_split}
                           |> simpset_of

  structure URustContractSimps = Generic_Data
  (
    type T = simpset;
    val empty = crush_base_simpset
    val merge = merge_ss;
  );

  fun register_contracts (cs : thm list) : Context.generic -> Context.generic =
    fn ctxt => ctxt |> (
       curry ((op addsimps) o swap) cs
    |> simpset_map (Context.proof_of ctxt)
    |> URustContractSimps.map)

  fun unregister_contracts (cs : thm list) : Context.generic -> Context.generic =
    fn ctxt => ctxt |> (
       curry ((op delsimps) o swap) cs
    |> simpset_map (Context.proof_of ctxt)
    |> URustContractSimps.map)

  fun crush_register_contract_attrib (del : bool) = Thm.declaration_attribute (fn t => fn ctxt =>
    let val t' = rewrite_rule (Context.proof_of ctxt) [@{thm Let_def}] t in ctxt |> (
    if del then
      unregister_contracts [t']
      #> Named_Theorems.del_thm @{named_theorems "crush_contract_defs"} t
      #> Named_Theorems.del_thm @{named_theorems "no_atp"} t
    else
      register_contracts [t']
      #> Named_Theorems.add_thm @{named_theorems "crush_contract_defs"} t
      #> Named_Theorems.add_thm @{named_theorems "no_atp"} t
    )
    end
  )

  val get_urust_contract_simpset = Context.Proof #> URustContractSimps.get

  val crush_register_wp_split_attrib = Thm.declaration_attribute (fn t => fn ctxt =>
    let val t' = Separation_Logic_Tactics.specialize_split_rule_to_wp_single
                   (Context.proof_of ctxt) t
    in ctxt |> Named_Theorems.add_thm @{named_theorems "crush_wp_split_simps"} t'
    end
  )  

  val crush_base_unfold_contract_tac : Proof.context -> int -> tactic = fn ctxt =>
    let
      val congs = Named_Theorems.get ctxt @{named_theorems "crush_cong"}
      val  contract_ctxt = ctxt |> put_simpset (get_urust_contract_simpset ctxt)
        |> fold Simplifier.add_cong congs
    in
      CHANGED_PROP o safe_simp_tac contract_ctxt
    end

  val crush_branch_base_simps_early_unfold : Proof.context -> int -> tactic = fn ctxt =>
    let val early_simps = Named_Theorems.get ctxt @{named_theorems crush_early_simps}
      val congs = Named_Theorems.get ctxt @{named_theorems "crush_cong"}      
    in
      if Config.get ctxt Crush_Config.enable_base_simps_early_unfold then
        safe_unfold_tac' ctxt congs early_simps
      else
        K no_tac
    end

  val crush_branch_base_detect_aentails_contradiction: Proof.context -> int -> tactic = fn ctxt =>
    if Config.get ctxt Crush_Config.enable_base_simps_detect_aentails_contradiction then
      IF' Separation_Logic_Tactics.is_entailment (
        let val congs = Named_Theorems.get ctxt @{named_theorems "crush_cong"} in
        CHANGED_PROP o (safe_simp_no_asm_only_tac' ctxt congs @{thms asepconj_bot_zero asepconj_bot_zero2})
        THEN' TRY o resolve_tac ctxt @{thms bot_aentails_all} end
      )
    else
      K no_tac

  val crush_branch_base_simps_tac : Proof.context -> int -> tactic = fn ctxt =>
    let val crush_intros = Named_Theorems.get ctxt @{named_theorems crush_intros}
    fun NOTE msg =  TIME' ctxt (Config.get ctxt Crush_Config.time_base_simps) msg
      #> LOG' ctxt  (Config.get ctxt Crush_Config.log_base_simps) msg
    in
              NOTE "crush_base_simps_schematic" (instantiate_schematic_from_equality ctxt)
      ORELSE' NOTE "crush_base_simps_unused_quantifier" (remove_unneeded_meta_quantification ctxt)
      ORELSE' NOTE "crush_base_simps_assumption" (assm_tac ctxt)
      ORELSE' NOTE "crush_base_simps_remove_duplicates" (remove_duplicate_pure_premises ctxt)
      ORELSE' NOTE "crush_base_simps_subst_bound" (Hypsubst.bound_hyp_subst_tac ctxt)
      ORELSE' NOTE "crush_base_simps_intro"  (intro_tac crush_intros ctxt)
      ORELSE' NOTE "crush_base_simps_unfold" (crush_branch_base_simps_early_unfold ctxt)
      ORELSE' NOTE "crush_base_simps_contr"  (crush_branch_base_detect_aentails_contradiction ctxt)
    end

  val crush_branch_wp_intros_tac_core : Proof.context -> int -> tactic = fn ctxt =>
    let val wp_intros = Named_Theorems.get ctxt @{named_theorems micro_rust_wp_intros}
    in
      intro_tac wp_intros ctxt
    end

  val crush_branch_wp_intros_tac : Proof.context -> int -> tactic = fn ctxt =>
    IF' Separation_Logic_Tactics.is_wp_entailment
      (crush_branch_wp_intros_tac_core ctxt)

  val crush_branch_determine_branch : Proof.context -> int -> tactic = fn ctxt =>
    if Config.get ctxt Crush_Config.enable_urust_determine_branch then
      let val max_facts = Config.get ctxt Crush_Config.relevance_filter_max_facts in
        (* Use back-tracking to pick the right branch *)
        resolve_tac ctxt @{thms wp_two_armed_conditional_thenI wp_two_armed_conditional_elseI}
        THEN' SOLVED' (MePo_Prem.reduced_clarsimp ctxt max_facts false)
      end
    else
      K no_tac

  val crush_branch_wp_case_split_tac_core : Proof.context -> int -> tactic = fn ctxt =>
    if not (Config.get ctxt Crush_Config.enable_urust_split_branch) then K no_tac else
    let val wp_split_intros = Named_Theorems.get ctxt @{named_theorems micro_rust_wp_case_splits}
      val wp_split_simps = Named_Theorems.get ctxt @{named_theorems crush_wp_split_simps}
        |> force_meta_eqs
    in
      intro_tac wp_split_intros ctxt ORELSE' 
      CONVERSION (Conv.params_conv ~1 (fn _ => (Conv.concl_conv ~1 (prop_conv (Conv.rewrs_conv wp_split_simps)))) ctxt)
    end

  val crush_branch_wp_case_split_tac : Proof.context -> int -> tactic = fn ctxt =>
    IF' Separation_Logic_Tactics.is_wp_entailment
      (crush_branch_wp_case_split_tac_core ctxt)

  val crush_branch_urust_simps_tac : Proof.context -> int -> tactic = fn ctxt =>
    let val congs = Named_Theorems.get ctxt @{named_theorems "crush_cong"}
      val urust_simps = Named_Theorems.get ctxt @{named_theorems "micro_rust_simps"}
    in
      safe_simp_no_asm_only_tac' ctxt congs urust_simps
    end

  fun crush_get_specs (ctxt : Proof.context) (with_schematics : bool) (eager : bool) : thm list =
    let val specs = Named_Theorems.get ctxt @{named_theorems crush_specs}
    val spec_filter_schematic =
      if with_schematics then
        K true
      else
        not o Separation_Logic_Tactics.is_schematic_spec
    fun spec_filter_eager (t: thm): bool =
      Named_Theorems.member ctxt @{named_theorems crush_specs_eager} t = eager
    in
      specs |> filter spec_filter_schematic |> filter spec_filter_eager
    end

  fun crush_branch_call_tac_core (ctxt: Proof.context) (func_name : string) (with_schematics: bool)
    (eager: bool) (unfold_contract_tac : int -> tactic) : int -> tactic =
    let val LOG : string -> int -> tactic =
      if Config.get ctxt Crush_Config.log_calls then log_tac #> K else K (K all_tac)
    val eager_schematic_str = " (" ^ (eager |> Bool.toString) ^ "," ^ (with_schematics |> Bool.toString) ^ ")"
    fun TIME msg = TIME' ctxt (Config.get ctxt Crush_Config.time_calls) (msg ^ eager_schematic_str)
    fun TIME_IT msg = time_and_report ctxt msg (Config.get ctxt Crush_Config.time_calls)
    val specs = TIME_IT "crush_branch_call_init_get_specs" (fn _ => crush_get_specs ctxt with_schematics eager)
    val unfold_contract_tac = TIME "crush_branch_call_intro_find_contract" unfold_contract_tac
    val confirm_no_abort_tac = TIME "crush_branch_call_confirm_no_abort" (
           (SOLVED' (TRY o unfold_contract_tac THEN' safe_asm_simp_tac (ctxt addsimps @{thms Let_def}))) ORELSE'
           (LOG ("Failed to show that " ^ func_name ^ " has trivial abort-postcondition") THEN' K no_tac))

    val post_call_simp = TIME "crush_branch_post_call_simp" (TIME_IT "crush_branch_call_init_post_call_simp"
      (fn _ => if eager then
        let val post_call_unfold_thms = Named_Theorems.get ctxt @{named_theorems crush_specs_eager_unfold}
        in TRY o safe_simp_no_asm_simp_only_tac ctxt post_call_unfold_thms end
      else
        K all_tac))
    val find_spec = TIME "crush_branch_call_intro_find_spec" (TIME_IT "crush_branch_call_init_find_spec"
      (fn _ => (resolve_tac ctxt specs
        (* When working with dependent specifications, the proof author has to ensure that the
           assumptions of the specification are present as pure premises. *)
        THEN_ALL_NEW assm_tac ctxt)
      ORELSE' assm_tac ctxt))
    val call_without_abort =
       TIME "crush_branch_call_intro" (intro_tac @{thms wp_callI} ctxt)
       THEN'
        ( find_spec
          THEN' confirm_no_abort_tac
          THEN' (
            ( (unfold_contract_tac ORELSE' (LOG ("No contract for: " ^ func_name)))
              THEN' post_call_simp
              THEN' (LOG ("Call function: " ^ func_name) ) )
            ORELSE' (LOG ("Failed to call function: " ^ func_name) ) ) )
    val call_with_abort =
       TIME "crush_branch_call_intro_with_abort" (intro_tac @{thms wp_call_with_abortI} ctxt)
       THEN'
        ( find_spec
          THEN' (
            ( (unfold_contract_tac ORELSE' (LOG ("No contract for: " ^ func_name)))
              THEN' post_call_simp
              THEN' (LOG ("Call function: " ^ func_name) ) )
            ORELSE' (LOG ("Failed to call function: " ^ func_name) ) ) )
    in
      call_without_abort ORELSE' call_with_abort
    end

  fun crush_branch_inline_call_tac (ctxt : Proof.context) (func_name : string) =
    let
      val TIME = TIME' ctxt (Config.get ctxt Crush_Config.time_calls)
       val LOG : string -> int -> tactic =
        if Config.get ctxt Crush_Config.log_calls then log_tac #> K else K (K all_tac)
      fun pure_eta_expand thm =
        thm |> single |> curry (op OF) @{thm meta_fun_cong} |> pure_eta_expand
        handle THM _ => thm
      fun make_wp_call_rule thm =
         (@{thm wp_call_inlineI} OF [thm]) handle THM _ => (@{thm wp_call_inline'I} OF [thm])
      val inlined_fun_defs = Named_Theorems.get ctxt @{named_theorems crush_inline}
      val inlined_call_rules = inlined_fun_defs |> List.map (pure_eta_expand #> make_wp_call_rule)
    in TIME "crush_branch_inline_call" (
      intro_tac inlined_call_rules ctxt
      THEN' Separation_Logic_Tactics.aentails_wp_ssa_normalize_tac ctxt
      THEN' LOG ("Call function: " ^ func_name ^ " (inlined)")
    ) end

  fun crush_branch_call_tac (ctxt : Proof.context) (with_schematics : bool)
     (unfold_contract_tac : int -> tactic): int -> tactic =
     IF_with_param' (Separation_Logic_Tactics.find_wp_call_function) (fn func =>
               (if not with_schematics then crush_branch_inline_call_tac ctxt func else K no_tac)
       ORELSE' crush_branch_call_tac_core ctxt func with_schematics true unfold_contract_tac
       ORELSE' crush_branch_call_tac_core ctxt func with_schematics false unfold_contract_tac)

  val crush_branch_aentails_core_tac : Proof.context -> int -> tactic = fn ctxt =>
    DWELL' ( IF' Separation_Logic_Tactics.is_entailment (
      Separation_Logic_Tactics.aentails_simp_core_tac ctxt
    ) )

  val crush_branch_aentails_cancel_tac : Proof.context -> int -> tactic = fn ctxt =>
    IF' Separation_Logic_Tactics.is_entailment (Separation_Logic_Tactics.aentails_cancel_tac ctxt)

  fun crush_branch_schematics_tac (ctxt: Proof.context) (unfold_contract_tac: int -> tactic) : int -> tactic =
    let val ex_intros = intro_tac (Named_Theorems.get ctxt @{named_theorems micro_rust_wp_ex_intros}) ctxt
    val ex_specs = crush_branch_call_tac ctxt true unfold_contract_tac
    val aexists_entailsR = intro_tac @{thms aexists_entailsR} ctxt
    in
      if not (Config.get ctxt Crush_Config.enable_schematics) then K no_tac else
        (IF' Separation_Logic_Tactics.is_wp_entailment (ex_intros ORELSE' ex_specs))
      ORELSE' (IF' Separation_Logic_Tactics.is_entailment aexists_entailsR)
    end

  val crush_branch_destruct_tac : Proof.context -> int -> tactic = fn ctxt =>
             intro_tac @{thms aforall_entailsR aexists_entailsL} ctxt
     ORELSE' elim_tac @{thms Set.bexE exE} ctxt

  val crush_branch_safe_tac : Proof.context -> int -> tactic =
    fn ctxt =>
      if Config.get ctxt Crush_Config.enable_branch_safe then
        REPEAT_ALL_NEW (safe_step_tac (ctxt delrules @{thms impCE HOL.iffI Set.equalityI}))
      else
        K no_tac

  val update_guards_tac = Crush_Guards.update_guards_shallow_tac

  val crush_branch_reduced_clarsimp_tac : Proof.context -> int -> tactic =
    fn ctxt => let fun NOTE msg =  TIME' ctxt (Config.get ctxt Crush_Config.time_clarsimp) msg
                                #> LOG' ctxt  (Config.get ctxt Crush_Config.log_clarsimp) msg
    in
      if Config.get ctxt Crush_Config.enable_branch_reduced_clarsimp then
               NOTE "lazy_clarsimp_relevance_filter_drop" (MePo_Prem.drop_irrelevant_prems_tac ctxt (Config.get ctxt Crush_Config.relevance_filter_max_facts))
        THEN' (NOTE "lazy_clarsimp_unsafe_reduced_clarsimp" (SOLVED' (clarsimp_tac ctxt)))
      else
        K no_tac
    end

  val crush_branch_filtered_clarsimp_tac : Proof.context -> int -> tactic =
    fn ctxt => let fun NOTE msg =  TIME' ctxt (Config.get ctxt Crush_Config.time_clarsimp) msg
                                #> LOG' ctxt  (Config.get ctxt Crush_Config.log_clarsimp) msg
    in
      if Config.get ctxt Crush_Config.enable_branch_filtered_clarsimp then
          NOTE "lazy_clarsimp_relevance_filter_ignore" (MePo_Prem.ignore_irrelevant_prems_tac ctxt (Config.get ctxt Crush_Config.relevance_filter_max_facts))
          THEN' NOTE "lazy_clarsimp_filtered_clarsimp" (CHANGED_PROP o clarsimp_tac ctxt)
          THEN_ALL_NEW (MePo_Prem.unignore_tac ctxt)
      else
        K no_tac
    end

  val crush_branch_clarsimp_tac : Proof.context -> int -> tactic =
    fn ctxt => let fun NOTE msg =  TIME' ctxt (Config.get ctxt Crush_Config.time_clarsimp) msg
                                #> LOG' ctxt  (Config.get ctxt Crush_Config.log_clarsimp) msg
        val congs = Named_Theorems.get ctxt @{named_theorems crush_cong}
        val ctxt_hol_ss = ctxt
          |> put_simpset crush_base_simpset
          |> fold Raw_Simplifier.add_cong congs
      in
              NOTE "lazy_clarsimp_reduced"            (crush_branch_reduced_clarsimp_tac ctxt)
      ORELSE' NOTE "lazy_clarsimp_simp"               (CHANGED_PROP o safe_full_simp_tac ctxt)
      ORELSE' NOTE "lazy_clarsimp_clarsimp_hol_ss"    (CHANGED_PROP o safe_asm_full_simp_tac ctxt_hol_ss)
      ORELSE'
      (if Config.get ctxt Crush_Config.enable_branch_clarsimp then
         NOTE "lazy_clarsimp_clarify" (CHANGED_PROP o clarify_tac ctxt)
       else
         K no_tac)
    end

  val crush_branch_focus_core_tac : Proof.context -> int -> tactic = fn ctxt =>
    let val focus_intros =
      Named_Theorems.get ctxt @{named_theorems focus_intros} @
      Named_Theorems.get ctxt @{named_theorems micro_rust_record_intros}
    val focus_rules = Named_Theorems.get ctxt @{named_theorems focus_rules}
    val focus_elims  = Named_Theorems.get ctxt @{named_theorems focus_elims}
    val focus_elims2  = Named_Theorems.get ctxt @{named_theorems focus_elims2}
    in 
         ((REPEAT_ALL_NEW (intro_tac (focus_rules @ focus_intros) ctxt))
             THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (update_guards_tac ctxt THEN' (
                 assm_tac ctxt ORELSE' 
                 crush_branch_base_simps_tac ctxt ORELSE' 
                 crush_branch_clarsimp_tac ctxt))))
         ORELSE' elim_tac  focus_elims  ctxt
         ORELSE' (eresolve_tac ctxt focus_elims2 THEN' assm_tac ctxt)
    end

  fun crush_branch_focus_tac ctxt = REPEAT_ALL_NEW (crush_branch_focus_core_tac ctxt)

  val crush_branch_clarsimp_fallback_tac = fn ctxt =>
   let fun log_before_after old_goal new_goal_opt =
      (let val old_txt = 
             [Pretty.str "Needed to apply full-blown clarsimp to progress the following pure goal:", Pretty.brk 1,
              Syntax.pretty_term ctxt old_goal, Pretty.fbrk] in
       if Config.get ctxt Crush_Config.enable_branch_clarsimp_stop_at_success then
         ((old_txt @ [Pretty.fbrk, Pretty.str "Aborting as requested by `crush_stop_at_full_blown_clarsimp` option"]
          |> Pretty.block |> Pretty.string_of |> Output.warning);
          raise SMART "Stopping after successful clarsimp -- consider debugging why MePo-filtered clarsimp didn't work!")
       else if old_goal |> Separation_Logic_Tactics.is_entailment |> not
         andalso Config.get ctxt Crush_Config.enable_branch_clarsimp_warn_at_success then 
         let 
           val new_txt = case new_goal_opt of 
              NONE => [Pretty.str "Goal was solved"]
            | SOME new_goal => [Pretty.str "New goal: ", Pretty.fbrk,
                                Syntax.pretty_term ctxt new_goal]
         in
           old_txt @ new_txt @ 
            [Pretty.fbrk, Pretty.str "Consider debugging why MePo-filtered clarsimp is not successful here.", Pretty.fbrk,
             Pretty.str "If you want to stop `crush` at this point, set `crush_stop_at_full_blown_clarsimp=true` and `crush_do_big_steps=false`"]
           |> Pretty.block |> Pretty.string_of |> Output.warning
         end
      else () end)
   in
     if Config.get ctxt Crush_Config.enable_branch_clarsimp then
       DEBUG_BEFORE_AFTER' log_before_after (CHANGED_PROP o clarsimp_tac ctxt)
     else K no_tac
   end

  val crush_branch_misc_tac : Proof.context -> int -> tactic = fn ctxt =>
             intro_tac @{thms mset_sub_drop_nth word_unat_lt} ctxt
     ORELSE' (EqSubst.eqsubst_tac ctxt [0] @{thms mset_minus_drop_nth}
              THEN' (simp_tac ctxt |> SOLVED'))

  fun filter_no_prems t =
     t |> Thm.prop_of |> Term.strip_abs |> snd |> Logic.no_prems

  val crush_branch_unfold_concls_tac : Proof.context -> int -> tactic = fn ctxt =>
    let val concls_simps = Named_Theorems.get ctxt @{named_theorems crush_concls_simps}
    in
      CHANGED o (
             TRY o (Crush_Unfold.assumption_unfolded_tac ctxt)
       THEN' TRY o (Separation_Logic_Tactics.simp_concls_tac concls_simps ctxt)
       THEN' TRY o (Separation_Logic_Tactics.aentails_simp_concls_tac concls_simps ctxt))
    end

  val crush_branch_unfold_prems_tac = fn ctxt =>
    let val crush_prems_simps = (Named_Theorems.get ctxt @{named_theorems crush_prems_simps})
    in
      Separation_Logic_Tactics.unfold_prems_tac crush_prems_simps ctxt
    end

  val crush_branch_intro_pure_aentails_tac : Proof.context -> int -> tactic = fn ctxt =>
    Separation_Logic_Tactics.ucincl_discharge_tac ctxt (intro_tac @{thms apure_entailsR0} ctxt)

  val crush_branch_aentails_cond_drule_tac =
     fn ctxt => Separation_Logic_Tactics.aentails_cond_drule_tac (Named_Theorems.get ctxt @{named_theorems crush_aentails_cond_drules}) ctxt

  val crush_branch_aentails_cond_crule_tac =
     fn ctxt => Separation_Logic_Tactics.aentails_cond_crule_tac (Named_Theorems.get ctxt @{named_theorems crush_aentails_cond_crules}) ctxt

  val crush_branch_aentails_drule_tac =
     fn ctxt => Separation_Logic_Tactics.aentails_drule_tac (Named_Theorems.get ctxt @{named_theorems crush_aentails_drules}) ctxt

  val crush_branch_aentails_crule_tac =
     fn ctxt => Separation_Logic_Tactics.aentails_crule_tac (Named_Theorems.get ctxt @{named_theorems crush_aentails_crules}) ctxt

  val crush_branch_aentails_cond_rule_tac =
     fn ctxt => Separation_Logic_Tactics.aentails_cond_rule_tac (Named_Theorems.get ctxt @{named_theorems crush_aentails_cond_rules}) ctxt

  val crush_branch_aentails_rule_tac =
     fn ctxt => Separation_Logic_Tactics.aentails_rule_tac (Named_Theorems.get ctxt @{named_theorems crush_aentails_rules}) ctxt

  structure CrushData = Proof_Data (
    type T = {
      additional_tac : (Proof.context -> int -> tactic) option,
      additional_method : (Proof.context -> Method.method) option,
      abort_before_condition : (Proof.context -> term -> bool) option,
      post_step_tac : (Proof.context -> int -> tactic) option
    };
    val init = K {additional_tac = NONE, additional_method = NONE, abort_before_condition = NONE,
      post_step_tac = NONE }
  );

  val crush_branch_ucincl_tac = Separation_Logic_Tactics.ucincl_solve_tac

  val crush_branch_additional_tactic: Proof.context -> int -> tactic = fn ctxt =>
     Option.getOpt((CrushData.get ctxt |> #additional_tac),  K (K no_tac)) ctxt

  val crush_post_step_tac: Proof.context -> int -> tactic = fn ctxt =>
     Option.getOpt((CrushData.get ctxt |> #post_step_tac),  K (K all_tac)) ctxt

  val crush_abort_condition: Proof.context -> term -> bool = fn ctxt =>
     Option.getOpt ((CrushData.get ctxt |> #abort_before_condition), K (K false)) ctxt

  val crush_branch_additional_method: Proof.context -> int -> tactic = fn ctxt =>
      let val m = CrushData.get ctxt |> #additional_method in
         K (case m of SOME f => (f ctxt |> method_to_tac) ctxt | NONE => no_tac) end

  val crush_base_step_tac_core = fn ctxt =>
     let
         fun NOTE' log (msg, pos, tac') = let
           val msg' = "crush_branch_" ^ msg
           in
               tac'
            |> TIME_pos' ctxt pos (Config.get ctxt Crush_Config.time_toplevel) msg' log
            |> LOG_pos' ctxt pos (Config.get ctxt Crush_Config.log_toplevel) msg' log
           end
         (* We are hoisting this out because it dominates the runtime of very short
            crush calls, and is used 4 times in the branches below; we also defer
            evaluation to when we actually need it *)
         val unfold_contract_tac = LAZY' (fn _ =>
             time_and_report ctxt "crush_instantiation_step_unfold_contract"
             (Config.get ctxt Crush_Config.time_step_instantiation_by_branch)
             (fn _ => crush_base_unfold_contract_tac ctxt))
         val post_step_tac = crush_post_step_tac ctxt 
         val branches = [
            ("base_simps_tac"          , \<^here>, (fn _ => crush_branch_base_simps_tac ctxt)),
            ("destruct_tac"            , \<^here>, (fn _ => crush_branch_destruct_tac ctxt)),
            ("focus_tac"               , \<^here>, (fn _ => crush_branch_focus_tac ctxt)),
            ("wp_intros_tac"           , \<^here>, (fn _ => crush_branch_wp_intros_tac ctxt)),
            ("urust_determine_branch"  , \<^here>, (fn _ => crush_branch_determine_branch ctxt)),
            ("call_tac (no schematics)", \<^here>, (fn _ => crush_branch_call_tac ctxt false unfold_contract_tac)),
            ("aentails_cancel_tac"     , \<^here>, (fn _ => crush_branch_aentails_cancel_tac ctxt)),
            ("unfold_prems_tac"        , \<^here>, (fn _ => crush_branch_unfold_prems_tac ctxt)),
            ("aentails_core_tac"       , \<^here>, (fn _ => crush_branch_aentails_core_tac ctxt)),
            ("aentails_cond_drule_tac" , \<^here>, (fn _ => crush_branch_aentails_cond_drule_tac ctxt)),
            ("aentails_drule_tac"      , \<^here>, (fn _ => crush_branch_aentails_drule_tac ctxt)),
            ("aentails_cond_crule_tac" , \<^here>, (fn _ => crush_branch_aentails_cond_crule_tac ctxt)),
            ("aentails_crule_tac"      , \<^here>, (fn _ => crush_branch_aentails_crule_tac ctxt)),
            ("aentails_cond_rule_tac"  , \<^here>, (fn _ => crush_branch_aentails_cond_rule_tac ctxt)),
            ("aentails_rule_tac"       , \<^here>, (fn _ => crush_branch_aentails_rule_tac ctxt)),
            ("unfold_concls_tac"       , \<^here>, (fn _ => crush_branch_unfold_concls_tac ctxt)),
            ("schematics_tac"          , \<^here>, (fn _ => crush_branch_schematics_tac ctxt unfold_contract_tac)),
            ("intro_pure_aentails_tac" , \<^here>, (fn _ => crush_branch_intro_pure_aentails_tac ctxt)),
            ("urust_simps_tac"         , \<^here>, (fn _ => crush_branch_urust_simps_tac ctxt)),
            ("clarsimp_tac"            , \<^here>, (fn _ => crush_branch_clarsimp_tac ctxt)),
            ("misc_tac"                , \<^here>, (fn _ => crush_branch_misc_tac ctxt)),
            ("ucincl_tac"              , \<^here>, (fn _ => crush_branch_ucincl_tac ctxt)),
            ("additional_tac"          , \<^here>, (fn _ => crush_branch_additional_tactic ctxt)),
            ("additional_method"       , \<^here>, (fn _ => crush_branch_additional_method ctxt)),
            ("wp_case_split_tac"       , \<^here>, (fn _ => crush_branch_wp_case_split_tac ctxt)),
            ("safe_tac"                , \<^here>, (fn _ => crush_branch_safe_tac ctxt)),
            ("clarsimp_filtered"       , \<^here>, (fn _ => crush_branch_filtered_clarsimp_tac ctxt)),
            ("clarsimp_fallback"       , \<^here>, (fn _ => crush_branch_clarsimp_fallback_tac ctxt))
           ] |>
         List.map (fn (msg, pos, lazy_tac') => (msg, pos, LAZY' (fn _ =>
           time_and_report ctxt ("crush_instantiation_step_" ^ msg)
             (Config.get ctxt Crush_Config.time_step_instantiation_by_branch) lazy_tac')))
     in fn log =>
       let val branches = List.map (NOTE' log) branches in
       fn i => fn st => (FIRST' branches THEN_ALL_NEW (TRY o post_step_tac)) i st
         handle ABORT msg => ("Early abort of crush step: " ^ msg |> Pretty.text |> Pretty.block |> Pretty.writeln; Seq.empty)
     end end

  (* Note: It is important for performance to initialize as much as possible once the context is known,
     and _before_ the logger is passed. This is because the logger will change with every crush step,
     but most of the tactic initialization is independent of it. *)
  fun crush_step_tac_frame (t : Proof.context -> logger -> int -> tactic) (ctxt : Proof.context) =
    let val NOTE_GUARD' = TIME' ctxt (Config.get ctxt Crush_Config.time_guards) "crush_update_guards"
        val NOTE_CHECK' = TIME' ctxt (Config.get ctxt Crush_Config.time_guards) "crush_bad_schematic_check"
        val fail_on_bad_schematic = Config.get ctxt Crush_Config.fail_on_bad_schematic
        val step_time_bound = Time.fromMilliseconds (Config.get ctxt Crush_Config.step_time_bound_ms)
        fun step_cb (_ : thm) (_ : thm option) (timing : Timing.timing) (_ : bool) =
          let val t = #elapsed timing in
            if t <= step_time_bound then () else
              (("step time bound exceeded: " ^ Time.fmt 6 t ^ "s" |> tracing);
               raise SMART "crush step time bound exceeded")
          end
        val time_and_report_log_instantiation = time_and_report ctxt "crush_step_log_instantiation"
           (Config.get ctxt Crush_Config.time_step_log_instantiation)
        val time_step = TIME_CB' ctxt Position.none (Config.get ctxt Crush_Config.time_steps) "crush_step"
        val check_schematic_equality_tac' = check_bad_schematic_equality_tac ctxt fail_on_bad_schematic |> K
        val crush_abort_condition = crush_abort_condition ctxt

        val _ = if not (Config.get ctxt Crush_Config.crush_force_inline) then () else
          let
            (* Check that function specifications are not passed via `simp add: ...` but via `inline: ...` *)
            fun is_urust_function_def thms =
              (case (thms |> Thm.prop_of |> Logic.dest_equals |> fst |> strip_comb |> fst) of
                 Const (_, T) =>
                    (case Term.body_type T of Type (@{type_name function_body}, _) => true | _ => false)
                 | _ => false)
              handle TERM _ => false
            val function_defs = Named_Theorems.get ctxt @{named_theorems crush_late_simps}
              |> List.filter is_urust_function_def
          in
            if List.length function_defs = 0 then () else (
              [Pretty.text "The following definitions of to-be-inlined functions should not be passed via `simp add: ...` but via `inline: ...`" |> Pretty.block]
              @ List.map (Thm.prop_of #> Syntax.pretty_term ctxt #> single #> Pretty.item) function_defs
              |> Pretty.chunks |> Pretty.writeln;
              raise CRUSH "Invalid configuration")
          end

        val ctxt' = fold Raw_Simplifier.del_cong (Named_Theorems.get ctxt @{named_theorems crush_cong_default_del}) ctxt
        val ctxt' = fold Raw_Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems crush_cong}) ctxt'
        val ctxt' = ctxt' delsimps @{thms HOL.True_implies_equals}
                          addsimps (Named_Theorems.get ctxt @{named_theorems crush_late_simps})
                          addsimps (Named_Theorems.get ctxt @{named_theorems focus_simps})
                          addsimps (Named_Theorems.get ctxt @{named_theorems focus_components})

        (* We use the original context where possible, for better parallelism *)
        val guards_tac' = time_and_report ctxt "crush_step_instantiation_guards" (Config.get ctxt Crush_Config.time_step_instantiation)
           (fn _ => update_guards_tac ctxt)
        val ucincl_tac' = time_and_report ctxt "crush_step_instantiation_ucincl" (Config.get ctxt Crush_Config.time_step_instantiation)
           (fn _ => Separation_Logic_Tactics.ucincl_discharge_tac ctxt)
        val step_tac_log = time_and_report ctxt "crush_step_instantiation_step" (Config.get ctxt Crush_Config.time_step_instantiation)
           (fn _ => t ctxt')
    in fn log =>
      let
        val step_tac' = time_and_report_log_instantiation (fn _ => step_tac_log log)
        val NOTE_STEP' = time_step log step_cb
      in
        IF_ANY_GOAL' crush_abort_condition (K (fn _ => raise SMART "abort condition hit"))
        ORELSE' (NOTE_CHECK' check_schematic_equality_tac'
           THEN' NOTE_GUARD' guards_tac'
           THEN' ucincl_tac' (NOTE_STEP' step_tac')
        )
      end
    end

  val crush_base_step_tac = crush_step_tac_frame crush_base_step_tac_core

  fun make_modifier_parser name action pos = let
     val dummy_attrib : attribute = K (NONE, NONE) in
       Args.$$$ name >> K { init = action, attribute = dummy_attrib, pos = pos }
     end

  fun make_arg_parser' name_parser value_parser action pos = let
     val dummy_attrib : attribute = K (NONE, NONE) in
       name_parser |-- Args.colon |-- value_parser >> (fn v => { init = action v, attribute = dummy_attrib, pos = pos })
     end

 val additional_tac_parser = make_arg_parser' (Args.$$$ "branch" -- Args.$$$ "tactic" -- Args.add) Parser.parse_tactic
     (fn tac => fn ctxt => ctxt |> CrushData.map (fn v => { abort_before_condition = #abort_before_condition v,
                                                            additional_tac = SOME tac,
                                                            additional_method = #additional_method v,
                                                            post_step_tac = #post_step_tac v } ) ) \<^here>

 val post_step_tac_parser = make_arg_parser' (Args.$$$ "post" -- Args.$$$ "tactic") Parser.parse_tactic
     (fn tac => fn ctxt => ctxt |> CrushData.map (fn v => { abort_before_condition = #abort_before_condition v,
                                                            additional_tac = #additional_tac v,
                                                            additional_method = #additional_method v,
                                                            post_step_tac = SOME tac } ) ) \<^here>

 val additional_method_parser = make_arg_parser' (Args.$$$ "branch" -- Args.add) Parser.parse_method
     (fn method => fn ctxt => ctxt |> CrushData.map (fn v => { abort_before_condition = #abort_before_condition v,
                                                               additional_method = SOME method,
                                                               additional_tac = #additional_tac v,
                                                               post_step_tac = #post_step_tac v} ) ) \<^here>

 val abort_at_filter_parser = make_arg_parser' (Args.$$$ "abort" -- Args.$$$ "at" -- Args.$$$ "filter") Parser.parse_term_filter
     (fn cond => fn ctxt => ctxt |> CrushData.map (fn v => { abort_before_condition = SOME cond,
                                                             additional_method = #additional_method v,
                                                             additional_tac = #additional_tac v,
                                                             post_step_tac = #post_step_tac v } ) ) \<^here>

 val abort_at_pattern_parser = make_arg_parser' (Args.$$$ "abort" -- Args.$$$ "at" -- Args.$$$ "pattern") Parser.parse_goal_filter_pattern
     (fn cond => fn ctxt => ctxt |> CrushData.map (fn v => { abort_before_condition = SOME cond,
                                                             additional_method = #additional_method v,
                                                             additional_tac = #additional_tac v,
                                                             post_step_tac = #post_step_tac v} ) ) \<^here>

 val add_del_parser = (Args.add >> K false) || (Args.del >> K true)

 fun make_time_parser category config =
     make_arg_parser' (Args.$$$ "time" -- Args.$$$ category) Parser.parse_bool (Config.put config) \<^here>

  fun make_log_parser category config =
     make_arg_parser' (Args.$$$ "log" -- Args.$$$ category) Parser.parse_bool (Config.put config) \<^here>

  fun make_arg_parser name = make_arg_parser' (Args.$$$ name)

  fun make_attrib_parser parser pos attrib = parser --| Args.colon >> (fn t => { init=I, attribute = attrib t, pos=pos })

  fun make_del_parser_core parser thms pos = make_attrib_parser parser pos (Named_Theorems.del thms |> K)
  fun make_add_parser_core parser thms pos = make_attrib_parser parser pos (Named_Theorems.add thms |> K)

  fun make_add_del_many_attrib (thms : Proof.context -> (string * (thm -> bool)) list) (del : bool) : attribute =
    let
      fun modifier (name:string, filter: thm -> bool) (thm : thm) =
        if not (filter thm) then I else
        if del then
          Named_Theorems.del_thm name thm
        else
          Named_Theorems.add_thm name thm
      fun decl_thm (t : thm) : Context.generic -> Context.generic = fn ctxt => ctxt |> (
       List.map modifier (thms (Context.proof_of ctxt))
      |> List.map (curry (op |>) t)
      |> fold I)
    in
      Thm.declaration_attribute decl_thm
    end

  val simp_modifier_prems = Args.$$$ "prems"
  val simp_modifier_concls = Args.$$$ "concls"
  val simp_modifier_generic = Args.$$$ "generic"

  val simp_modifier_single = simp_modifier_prems || simp_modifier_concls || simp_modifier_generic
  val simp_modifier =
       Args.bracks (Parse.list simp_modifier_single >> SOME)
    || (simp_modifier_prems >> (SOME o single))
    || (simp_modifier_concls >> (SOME o single))
    || Scan.succeed NONE

  fun lookup_simp_set "prems" = (@{named_theorems crush_prems_simps}, filter_no_prems)
   | lookup_simp_set "concls" = (@{named_theorems crush_concls_simps}, filter_no_prems)
   | lookup_simp_set "generic" = (@{named_theorems crush_late_simps}, K true)
   | lookup_simp_set _ = raise CRUSH "Invalid simp set"

  fun simp_parser pos =
    let
      fun attrib (del, simpset_list_opt) : attribute = let
        fun thms (ctxt : Proof.context) : (string * (thm -> bool)) list =
          let
            val prems = if Config.get ctxt Crush_Config.simp_general_implies_prems then SOME "prems" else NONE
            val concls = if Config.get ctxt Crush_Config.simp_general_implies_concls then SOME "concls" else NONE
            val generic = SOME "generic"
            val default = [prems, concls, generic] |> List.mapPartial I
          in (simpset_list_opt, default)
           |> Option.getOpt
           |> List.map lookup_simp_set
          end
        in
          make_add_del_many_attrib thms del
        end
      val parser = Args.$$$ "simp" |-- simp_modifier -- add_del_parser >> swap
    in
      make_attrib_parser parser pos attrib
    end

  fun make_del_parser' name_parser = name_parser -- Args.del |> make_del_parser_core
  fun make_add_parser' name_parser = name_parser -- Args.add |> make_add_parser_core
  fun make_del_parser config_name = make_del_parser' (Args.$$$ config_name)
  fun make_add_parser config_name = make_add_parser' (Args.$$$ config_name)

  val opt_parsers = [make_arg_parser "gas"     Parse.int   (Config.put Crush_Config.gas) \<^here>,
                     make_arg_parser "dbg"     Parse.int   (Config.put Crush_Config.debug_level) \<^here>,
                     make_arg_parser "bigstep" Parser.parse_bool  (Config.put Crush_Config.do_big_steps) \<^here>,
                     make_modifier_parser "stepwise" (Config.put Crush_Config.stepwise true #>
                                                      Config.put Crush_Config.log_toplevel true #>
                                                      Config.put Crush_Config.do_big_steps false) \<^here>,
                     make_modifier_parser "history"  (Config.put Crush_Config.keep_history true #>
                                                      Config.put Crush_Config.do_big_steps false) \<^here>,
                     make_modifier_parser "no_safe"        (Config.put Crush_Config.enable_branch_safe false) \<^here>,
                     make_modifier_parser "do_safe"        (Config.put Crush_Config.enable_branch_safe true) \<^here>,
                     make_modifier_parser "no_clarsimp"    (Config.put Crush_Config.enable_branch_clarsimp false) \<^here>,
                     make_modifier_parser "no_schematics"  (Config.put Crush_Config.enable_schematics false) \<^here>,
                     make_modifier_parser "do_split"       (Config.put Crush_Config.enable_branch_split true) \<^here>,
                     make_modifier_parser "no_urust_case_split" (Config.put Crush_Config.enable_urust_split_branch false) \<^here>,
                     post_step_tac_parser,
                     additional_tac_parser, additional_method_parser,
                     abort_at_filter_parser, abort_at_pattern_parser]
  val time_parsers = [make_time_parser "steps"    Crush_Config.time_steps,
                      make_time_parser "clarsimp" Crush_Config.time_clarsimp,
                      make_time_parser "toplevel" Crush_Config.time_toplevel]
  val log_parsers = [make_log_parser "toplevel" Crush_Config.log_toplevel,
                     make_log_parser "clarsimp" Crush_Config.log_clarsimp,
                     make_log_parser "calls"    Crush_Config.log_calls,
                     make_log_parser "ucincl"   Crush_Config.log_ucincl]

  val add_del_parsers = [
     make_add_parser' (Args.$$$ "seplog" -- Args.$$$ "cond" -- Args.$$$ "drule") @{named_theorems crush_aentails_cond_drules} \<^here>,
     make_del_parser' (Args.$$$ "seplog" -- Args.$$$ "cond" -- Args.$$$ "drule") @{named_theorems crush_aentails_cond_drules} \<^here>,
     make_add_parser' (Args.$$$ "seplog" -- Args.$$$ "drule") @{named_theorems crush_aentails_drules} \<^here>,
     make_del_parser' (Args.$$$ "seplog" -- Args.$$$ "drule") @{named_theorems crush_aentails_drules} \<^here>,
     make_add_parser' (Args.$$$ "seplog" -- Args.$$$ "cond" -- Args.$$$ "crule") @{named_theorems crush_aentails_cond_crules} \<^here>,
     make_del_parser' (Args.$$$ "seplog" -- Args.$$$ "cond" -- Args.$$$ "crule") @{named_theorems crush_aentails_cond_crules} \<^here>,
     make_add_parser' (Args.$$$ "seplog" -- Args.$$$ "crule") @{named_theorems crush_aentails_crules} \<^here>,
     make_del_parser' (Args.$$$ "seplog" -- Args.$$$ "crule") @{named_theorems crush_aentails_crules} \<^here>,
     make_add_parser' (Args.$$$ "seplog" -- Args.$$$ "rule")  @{named_theorems crush_aentails_rules}  \<^here>,
     make_del_parser' (Args.$$$ "seplog" -- Args.$$$ "rule")  @{named_theorems crush_aentails_rules}  \<^here>,
     make_add_parser' (Args.$$$ "seplog" -- Args.$$$ "cond" -- Args.$$$ "rule")  @{named_theorems crush_aentails_cond_rules}  \<^here>,
     make_del_parser' (Args.$$$ "seplog" -- Args.$$$ "cond" -- Args.$$$ "rule")  @{named_theorems crush_aentails_cond_rules}  \<^here>,
     simp_parser \<^here>,
     make_add_parser' (Args.$$$ "simp" -- Args.$$$ "prems")   @{named_theorems crush_prems_simps} \<^here>,
     make_del_parser' (Args.$$$ "simp" -- Args.$$$ "prems")   @{named_theorems crush_prems_simps} \<^here>,
     make_add_parser' (Args.$$$ "simp" -- Args.$$$ "concls")  @{named_theorems crush_concls_simps} \<^here>,
     make_del_parser' (Args.$$$ "simp" -- Args.$$$ "concls")  @{named_theorems crush_concls_simps} \<^here>,
     make_add_parser' (Args.$$$ "simp" -- Args.$$$ "early")   @{named_theorems crush_early_simps} \<^here>,
     make_del_parser' (Args.$$$ "simp" -- Args.$$$ "early")   @{named_theorems crush_early_simps} \<^here>,
     make_add_parser' (Args.$$$ "wp" -- Args.$$$ "intro") @{named_theorems micro_rust_wp_intros} \<^here>,
     make_del_parser' (Args.$$$ "wp" -- Args.$$$ "intro") @{named_theorems micro_rust_wp_intros} \<^here>,
     make_add_parser_core (Args.$$$ "inline") @{named_theorems crush_inline} \<^here>,
     make_add_parser_core (Args.$$$ "cong" -- Args.$$$ "default" -- Args.del) @{named_theorems crush_cong_default_del} \<^here>,
     make_add_parser "guards"    @{named_theorems add_guards} \<^here>,
     make_del_parser "guards"    @{named_theorems add_guards} \<^here>,
     make_add_parser "intro"     @{named_theorems crush_intros} \<^here>,
     make_del_parser "intro"     @{named_theorems crush_intros} \<^here>,
     make_add_parser "specs"     @{named_theorems crush_specs} \<^here>,
     make_del_parser "specs"     @{named_theorems crush_specs} \<^here>,
     make_attrib_parser (Args.$$$ "wp" -- Args.$$$ "split") \<^here> (K crush_register_wp_split_attrib),
     make_attrib_parser (Args.$$$ "contracts" -- Args.add) \<^here> (K (crush_register_contract_attrib false)),
     make_attrib_parser (Args.$$$ "contracts" -- Args.del) \<^here> (K (crush_register_contract_attrib true)),
     make_add_parser "cong"     @{named_theorems crush_cong} \<^here>,
     make_del_parser "cong"     @{named_theorems crush_cong} \<^here>]

  val crush_modifiers = log_parsers @ time_parsers @ add_del_parsers @ opt_parsers @
                        Clasimp.clasimp_modifiers @          (* Pre-existing modifiers *)
                        Splitter.split_modifiers

  val crush_base_tac : Proof.context -> tactic = fn ctxt =>
     REPEAT_SMART ctxt default_logger true (HEADGOAL o (crush_base_step_tac ctxt))

  val fastcrush_base_tac : Proof.context -> tactic = fn ctxt =>
     REPEAT_SMART ctxt default_logger false (HEADGOAL o (crush_base_step_tac ctxt))

  val _ = Theory.setup (Attrib.setup @{binding "crush_contracts"}
    (Scan.lift (Scan.optional add_del_parser false >> crush_register_contract_attrib))
    "add/delete a crush contract"
  )

end;

(* Isar *)

local
  val _ = Theory.setup (Method.setup @{binding "crush_base"}
          (Method.sections Crush.crush_modifiers |-- Scan.succeed (SIMPLE_METHOD o Crush.crush_base_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "fastcrush_base"}
          (Method.sections Crush.crush_modifiers |-- Scan.succeed (SIMPLE_METHOD o Crush.fastcrush_base_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "crush_base_step"}
          (Method.sections Crush.crush_modifiers |--
            Scan.succeed (SIMPLE_METHOD o HEADGOAL o (fn ctxt => Crush.crush_base_step_tac ctxt default_logger))) "")

in end
