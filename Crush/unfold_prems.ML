(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Semantically transparent marker for definitions which have been unfolded

   We commonly have to unfold premises but also keep their original folded form
   for quick discharge in case the folded form comes up as a subgoal. To avoid an
   infinite cycle, we have to keep track of which premises have already been unfolded
   and not unfold them again. One way would be to check if unfolding leads to duplicates,
   but that is brittle because further simplification might have changed the goal, and
   a doing a full `simp` prior to checking for duplicates is overkill.

   Here, we are pursuing a simpler strategy which adds a dummy guard around every unfolded
   definition, thereby preventing it from being unfolded again, and also allowing for
   discharge-by-assumption in case the folded form of the definition comes up as a subgoal. *)

signature CRUSH_UNFOLD =
sig  
 val sat_unfold_tac : thm list -> Proof.context -> int -> tactic 
 val assumption_unfolded_tac : Proof.context -> int -> tactic
 val pure_eq_unfold_elim_attrib : attribute
end;

structure Crush_Unfold: CRUSH_UNFOLD =
struct
  val pure_eq_to_unfolded_elim =
       @{lemma \<open>(\<alpha> \<equiv> \<beta>) \<Longrightarrow> \<alpha> \<Longrightarrow> (UNFOLDED \<alpha> \<Longrightarrow> \<beta> \<Longrightarrow> R) \<Longrightarrow> R\<close>
               by (auto simp add: UNFOLDED_def)}

  fun pure_eq_thm_to_unfold_elim (t : thm) : thm = (pure_eq_to_unfolded_elim OF [t])

  fun try_pure_eq_thm_to_unfold_elim (t : thm) : thm option =
    SOME (pure_eq_thm_to_unfold_elim t) handle THM _ => NONE
  val pure_eq_thms_to_unfold_elim = List.mapPartial try_pure_eq_thm_to_unfold_elim

  \<comment>\<open>Attribute converting a pure equality into an elimination rule for
     safe saturating unfolding.\<close>
  val pure_eq_unfold_elim_attrib : attribute = Thm.rule_attribute [] (K pure_eq_thm_to_unfold_elim)

  \<comment>\<open>Safe saturating unfolding of pure premises\<close>
  fun sat_unfold_tac (ts : thm list) (ctxt : Proof.context) : int -> tactic =
    let val ts_meta = ts |> force_meta_eqs |> eta_expands
        val ts_elims = pure_eq_thms_to_unfold_elim ts_meta in
      elim_tac ts_elims ctxt
    end

  val assumption_unfolded_tac : Proof.context -> int -> tactic = fn ctxt =>
      eresolve_tac ctxt @{thms UNFOLDED_as_imp}

end;

(* Isar extensions *)

local
  val _ = Theory.setup (Method.setup @{binding "assumption_unfolded"}
          (Scan.succeed (fn ctxt => SIMPLE_METHOD' (Crush_Unfold.assumption_unfolded_tac ctxt))) "")

  val _ = Theory.setup (Method.setup @{binding "sat_unfold"} (Attrib.thms >> (fn thms => 
             K (context_tactic_to_method (fn ctxt => Crush_Unfold.sat_unfold_tac thms ctxt 1)))) "")

  val _ = Theory.setup (Attrib.setup @{binding "unfold_elim"} 
                       (Scan.succeed Crush_Unfold.pure_eq_unfold_elim_attrib) "")
in end
