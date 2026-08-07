(* Original Copyright (c) 1986-2023,
            University of Cambridge,
            Technische Universitaet Muenchen,
            and contributors
   under the ISABELLE COPYRIGHT LICENSE

   Modifications Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *)

(*
  MePo premise filter — tactic layer.

  Builds on the standalone ranking engine in mepo_core.ML (which must be loaded
  first). This file adds the Isabelle/Isar tactics and proof methods that apply
  the MePo ranking to modify a goal's premises:

  - `ignore_irrelevant_prems_tac`: wrap irrelevant premises in IGNORE
    (recoverable; the simplifier's cong rule skips them).
  - `drop_irrelevant_prems_tac`: delete irrelevant premises via thin_tac.
  - Methods: `rclarsimp`, `fclarsimp`, `mepo_focus`, `mepo_unfocus`.

  Depends on Crush/Base.thy for the IGNORE definition and related lemmas, and
  on Crush_Config for default max_facts.
*)

signature MEPO_PREM =
sig
 (* Re-export core types so callers need not open MePo_Core separately. *)
 type relevance_fudge = MePo_Core.relevance_fudge
 type prem_prep = MePo_Core.prem_prep

 (* --- Tactics --- *)

 (* Wrap the j-th premise of subgoal i in IGNORE (recoverable). *)
 val ignore_tac0 : Proof.context -> int -> tactic
 val ignore_tac_idx : Proof.context -> int -> int -> tactic
 val ignore_tac_idxs : Proof.context -> int list -> int -> tactic

 (* Undo IGNORE wrapping on subgoal i. *)
 val unignore_tac : Proof.context -> int -> tactic

 (* MePo-filter premises of subgoal i, then IGNORE the irrelevant ones. *)
 val ignore_irrelevant_prems_core_tac : Proof.context -> int ->
    relevance_fudge option -> int -> tactic
 val ignore_irrelevant_prems_tac : Proof.context -> int -> int -> tactic

 (* MePo-filter premises of subgoal i, then DELETE the irrelevant ones. *)
 val drop_irrelevant_prems_tac : Proof.context -> int -> int -> tactic

 (* Filter + run clarsimp/simp on the reduced premise set (unsafe: premises
    are deleted before the method runs). `dry_run = true` only filters. *)
 val reduced_clarsimp : Proof.context -> int -> bool -> int -> tactic
 val reduced_simp : Proof.context -> int -> bool -> int -> tactic

 (* Filter + run clarsimp/simp with irrelevant premises IGNORED (safe:
    premises are recoverable via `unignore_tac`). *)
 val filtered_clarsimp : Proof.context -> int -> bool -> int -> tactic
 val filtered_simp : Proof.context -> int -> bool -> int -> tactic

end;

structure MePo_Prem: MEPO_PREM =
struct

  type relevance_fudge = MePo_Core.relevance_fudge
  type prem_prep = MePo_Core.prem_prep

  val ignore_tac0 : Proof.context -> int -> tactic = fn ctxt =>
    DETERM o (eresolve_tac ctxt [@{thm IGNORE_imp_ignoreE}])

  val ignore_tac_idx = fn ctxt => fn j =>
     if j = 0 then ignore_tac0 ctxt else
     rotate_tac j THEN' ignore_tac0 ctxt THEN' rotate_tac (~j)

  val ignore_tac_idxs = fn ctxt => fn js =>
     EVERY' (List.map (fn j =>
        ignore_tac_idx ctxt j
        THEN' (TRY o (intro_tac @{thms IGNORE_imp_mergeI} ctxt))) (rev js))
     THEN' (TRY o (intro_tac @{thms IGNORE_imp_unwrapI} ctxt))

  val unignore_tac = fn ctxt =>
    TRY o (elim_tac @{thms IGNORE_splitE} ctxt)
    THEN' TRY o (elim_tac @{thms IGNORE_unwrapE} ctxt)

  fun ignore_irrelevant_prems_core_tac ctxt max_facts fudge i thm =
    let
      val (_, drop) = MePo_Core.irrelevant_prems_in_goal ctxt max_facts fudge i thm
    in
      ignore_tac_idxs ctxt drop i thm
    end
    handle THM _ => all_tac thm

  fun drop_irrelevant_prems_core_tac ctxt max_facts fudge i thm =
    let
      val (_, drop) = MePo_Core.irrelevant_prems_in_goal ctxt max_facts fudge i thm
    in
      thin_tac_idxs ctxt drop i thm
    end
    handle THM _ => all_tac thm

  fun ignore_irrelevant_prems_tac ctxt max_facts =
    ignore_irrelevant_prems_core_tac ctxt max_facts NONE

  fun drop_irrelevant_prems_tac ctxt max_facts =
    drop_irrelevant_prems_core_tac ctxt max_facts NONE

  fun reduced_clarsimp ctxt max_facts dry_run =
    drop_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else CHANGED_PROP o clarsimp_tac ctxt)

  fun reduced_simp ctxt max_facts dry_run =
    drop_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else CHANGED_PROP o simp_tac ctxt)

  fun filtered_clarsimp ctxt max_facts dry_run =
    ignore_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else
      CHANGED_PROP o clarsimp_tac ctxt
      THEN_ALL_NEW (unignore_tac ctxt)
    )

  fun filtered_simp ctxt max_facts dry_run =
    ignore_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else
      CHANGED_PROP o simp_tac ctxt
      THEN_ALL_NEW (unignore_tac ctxt)
    )

  val _ = Theory.setup (Method.setup @{binding "rclarsimp"}
    (Method.sections Clasimp.clasimp_modifiers |-- (Scan.lift (Scan.optional (Parse.nat >> SOME) NONE --
                 Scan.optional (Args.$$$ "dry_run" >> (K true)) false)) >>
      (fn (max_facts_opt, dry_run) => fn ctxt => SIMPLE_METHOD (
      let
        val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
      in
        reduced_clarsimp ctxt max_facts dry_run 1
      end
    ))) "Apply clarsimp after reducing premises via MePo filter (unsafe)")

  val _ = Theory.setup (Method.setup @{binding "fclarsimp"}
    (Method.sections Clasimp.clasimp_modifiers |-- (Scan.lift (Scan.optional (Parse.nat >> SOME) NONE --
                 Scan.optional (Args.$$$ "dry_run" >> (K true)) false)) >>
      (fn (max_facts_opt, dry_run) => fn ctxt => SIMPLE_METHOD (
      let
        val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
      in
        filtered_clarsimp ctxt max_facts dry_run 1
      end
    ))) "Apply clarsimp after ignoring premises via MePo filter (safe)")

  val _ = Theory.setup (Method.setup @{binding "mepo_focus"}
    ((Scan.lift (Scan.optional (Parse.nat >> SOME) NONE --
                 Scan.optional (Args.$$$ "drop" >> (K true)) false)) >>
      (fn (max_facts_opt, drop) => fn ctxt => SIMPLE_METHOD (
      let
        val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
      in
        if drop then
          drop_irrelevant_prems_tac ctxt max_facts 1
        else
          ignore_irrelevant_prems_tac ctxt max_facts 1
      end
    ))) "Drop or ignore premises deemed irrelevant according to MePo relevance filter")

  val _ = Theory.setup (Method.setup @{binding "mepo_unfocus"}
     (Scan.succeed (fn ctxt => SIMPLE_METHOD (unignore_tac ctxt 1)))
     "Recover premises previously ignored via mepo_focus")

end;
