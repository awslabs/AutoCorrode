(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*
  Core ML implementation for the proof shelving mechanism.

  Shelved goals are accumulated in a right-nested chain:
    OPAQUE_SHELVE (SHELVE_CONJ P (SHELVE_CONJ Q ... ?tail))
  The trailing schematic ?tail allows appending new goals via unification.

  To shelve a goal, we:
    1. Fold meta-level quantifiers and premises into object-level
       SHELVE_ALL / SHELVE_IMP (preserving variable names).
    2. Rotate past already-shelved goals in the chain.
    3. Instantiate ?tail with SHELVE_CONJ <current_goal> ?new_tail.

  The Shelve_Data proof data (defined in Shelver.thy before this file is loaded)
  stores "known premises" that should not be folded into shelved goals.
*)

signature SHELVER =
sig
  (* Shelve the current subgoal: fold its quantifiers/premises into object-level
     form, then append it to the shelved conjunction chain. *)
  val shelve_tac : Proof.context -> int -> tactic
  (* Detect whether a premise is a shelf: OPAQUE_SHELVE _ *)
  val is_shelve_prem : term -> bool
  (* Decompose SHELVE_CONJ P (SHELVE_CONJ Q ... tail) into [P, Q, ..., tail] *)
  val decompose_shelve_conj : term -> term list
  (* Fold meta-quantifiers and meta-premises back into object-level
     SHELVE_ALL / SHELVE_IMP, suitable for shelving. *)
  val fold_prems_tac : Proof.context -> int -> tactic
end;

structure Shelver: SHELVER =
struct

(* Decompose a SHELVE_CONJ chain into a list of its conjuncts. *)
fun decompose_shelve_conj (Const (@{const_name SHELVE_CONJ}, _) $ l $ r) = l :: decompose_shelve_conj r
  | decompose_shelve_conj t = [t];

(* Count how many goals have already been shelved (= number of SHELVE_CONJ nodes). *)
fun count_shelve_conjs (Const (@{const_name OPAQUE_SHELVE}, _) $ body) =
      let fun count (Const (@{const_name SHELVE_CONJ}, _) $ _ $ r) = 1 + count r
            | count _ = 0
      in count body end
  | count_shelve_conjs _ = 0;

(* Check whether a premise is a shelf premise (i.e. has head OPAQUE_SHELVE). *)
fun is_shelve_prem p =
  case try HOLogic.dest_Trueprop p of
    SOME (Const (@{const_name OPAQUE_SHELVE}, _) $ _) => true
  | _ => false;

(* Given the premises of a goal, find the shelf and return
   how many SHELVE_ROTATE applications are needed to reach its tail. *)
fun find_shelve_rotations prems =
  let val p = the (find_first is_shelve_prem prems)
  in count_shelve_conjs (HOLogic.dest_Trueprop p) end;

(* A premise is "known" if it was registered via setup_shelving's `premises` keyword,
   or if it is the shelf itself. Known premises are not folded into shelved goals. *)
fun is_known_prem known_prems p =
  exists (fn k => k aconv p) known_prems
  orelse is_shelve_prem p;

(* Instantiate SHELVE_ALL_spec with a given abstraction body, then alpha-rename
   the resulting theorem so the bound variable keeps its original name.
   Without this, all variables would be named 'x' (from spec's assumption). *)
fun named_spec ctxt (abs_body as Abs (name, _, _)) =
      let
        val spec_inst = Drule.infer_instantiate ctxt
          [(("P", 0), Thm.cterm_of ctxt abs_body)] @{thm SHELVE_ALL_spec};
        val prop = Thm.prop_of spec_inst;
        val (quant_prem, concl) = Logic.dest_implies prop;
        val (all_const, T, inner) =
          (case Term.dest_comb (HOLogic.dest_Trueprop quant_prem) of
            (c, Abs (_, T, inner)) => (c, T, inner)
          | (_, t) => raise TERM ("named_spec: expected Abs in quantifier", [t]));
        val fixed_prem = HOLogic.mk_Trueprop (all_const $ Abs (name, T, inner));
      in Thm.renamed_prop (Logic.mk_implies (fixed_prem, concl)) spec_inst end
  | named_spec _ t = raise TERM ("named_spec: expected Abs", [t]);

(* Fold one meta-quantified parameter back into object-level SHELVE_ALL.
   Abstracts the conclusion over the given free variable, then applies named_spec.
   Inference rule (where x is a fixed free variable from FOCUS_PARAMS):
     \<And>x. SHELVE_ALL (\<lambda>x. P x)
     --------------------------
     \<And>x. P x                    *)
fun fold_one_quant_tac ctxt (name, cparam) = SUBGOAL (fn (goal, i) =>
  let
    val free = Thm.term_of cparam;
    val concl = Logic.strip_assums_concl goal;
    val concl_body = HOLogic.dest_Trueprop concl;
    val abstracted = Term.abstract_over (free, concl_body);
    val abs_body = Abs (name, fastype_of free, abstracted);
  in resolve_tac ctxt [named_spec ctxt abs_body] i end);

(* Fold all meta-quantified parameters into object-level SHELVE_ALL, in order.
   Inference rule (applied repeatedly for each parameter):
     \<And>x y. SHELVE_ALL (\<lambda>x. SHELVE_ALL (\<lambda>y. P x y))
     ------------------------------------------------
     \<And>x y. P x y                                     *)
fun fold_quant_tac ctxt params =
  EVERY (rev (map (fn p => fold_one_quant_tac ctxt p 1) params));

(* Fold non-known meta-premises into object-level SHELVE_IMP.
   Operates on a goal whose parameters have already been fixed via FOCUS_PARAMS.
   Repeatedly applies SHELVE_IMP_rev_mp (P \<Longrightarrow> SHELVE_IMP P Q \<Longrightarrow> Q) to consume
   each non-known premise and embed it into the conclusion.
   Inference rule:
     \<And>x y. SHELVE_IMP P1 (SHELVE_IMP P2 (... (SHELVE_IMP Pn G)...))
     -----------------------------------------------------------------
     \<And>x y. P1 \<Longrightarrow> P2 \<Longrightarrow> ... \<Longrightarrow> Pn \<Longrightarrow> G                                *)
fun fold_prems_flat_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val known_prems = the_default [] (Shelve_Data.get ctxt);
    val assums = Logic.strip_assums_hyp goal;
    val new_assums = rev (filter_out (is_known_prem known_prems) assums);
    val inst_rules = map (fn a =>
      let val ct = Thm.cterm_of ctxt (HOLogic.dest_Trueprop a)
      in Drule.infer_instantiate ctxt [(("P", 0), ct)] @{thm SHELVE_IMP_rev_mp} end) new_assums;
  in
    EVERY (map (fn rule => eresolve_tac ctxt [rule] i) inst_rules)
  end);

(* Fold both meta-quantifiers and meta-premises into object-level form.
   Uses FOCUS_PARAMS to access parameters as certified terms, then:
   1. Folds premises via fold_prems_flat_tac
   2. Folds quantifiers via fold_quant_tac
   3. Prunes leftover parameters

   Net inference rule:
     SHELVE_ALL (\<lambda>x. SHELVE_ALL (\<lambda>y. SHELVE_IMP P (SHELVE_IMP Q (G x y))))
     -----------------------------------------------------------------------
     \<And>x y. P \<Longrightarrow> Q \<Longrightarrow> G x y                                                    *)
fun fold_prems_tac ctxt = SUBGOAL (fn (_, i) =>
  Subgoal.FOCUS_PARAMS (fn {context = ctxt', params, ...} =>
    fold_prems_flat_tac ctxt' 1
    THEN fold_quant_tac ctxt' params) ctxt i
  THEN Raw_Simplifier.prune_params_tac ctxt);

(* Instantiate the shelf with the current (folded) goal.
   Rotates past already-shelved goals via SHELVE_ROTATE, then
   applies FROM_SHELVE to unify ?tail with SHELVE_CONJ <goal> ?new_tail. *)
fun shelve_instantiate_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val from_shelve = @{thm FROM_SHELVE}
    val shelve_rotate = @{thm SHELVE_ROTATE}
    val prems = Logic.strip_imp_prems goal
    val n_rotations = find_shelve_rotations prems
  in
    EVERY (replicate n_rotations (eresolve_tac ctxt [shelve_rotate] i))
    THEN eresolve_tac ctxt [from_shelve] i
  end);

(* The main shelving tactic: fold the goal into object-level form,
   then append it to the shelf. *)
fun shelve_tac ctxt =
  fold_prems_tac ctxt
  THEN' shelve_instantiate_tac ctxt

end;
