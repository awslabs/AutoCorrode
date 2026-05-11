(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*

Guards are a mechanism aimed at preventing bad instantiation of schematics.

A guard is a semantically transparent wrapper around a term which prevents it
from being considered by unification procedures until a specified schematic
variable has been assigned.

Guards are added by registering guard theorems to the add_guards named theorem
list. See the examples.

*)

signature CRUSH_GUARDS =
sig  

  val try_remove_guard_conv : cterm list -> conv

  val update_guard_single_conv : cterm list -> Proof.context -> thm list -> conv
  val update_guards_shallow_conv : Proof.context -> conv
  val update_guards_deep_conv : cterm list -> Proof.context -> conv

  val update_guards_shallow_tac : Proof.context -> int -> tactic
  val update_guards_deep_tac : Proof.context -> int -> tactic
  val update_guards_tac : bool -> Proof.context -> int -> tactic

  \<comment>\<open>Succeeds without change on guards, fails otherwise.\<close>
  val is_guard_conv : conv
  \<comment>\<open>Fails on guards, succeeds without change otherwise.\<close>
  val is_no_guard_conv : conv

  \<comment>\<open>Applies a conversion expected to result in a term with head \<^term>\<open>guard\<close>,
     but only accepts the result if the guard is actually necessary.\<close>
  val conv_guard_if_necessary : (Proof.context -> conv) -> cterm list -> Proof.context -> conv

  \<comment>\<open>Remove guard(s), regardless of whether they are needed.\<close>
  val remove_guard_conv : conv
  val remove_all_guards_conv : Proof.context -> conv

  \<comment>\<open>Add guard(s), regardless of whether they are needed.\<close>
  val add_guard_conv : Proof.context -> thm list -> conv 
  val add_guards_conv : Proof.context -> thm list -> conv 
  val guard_conv_raw : conv

end;

structure Crush_Guards: CRUSH_GUARDS =
struct

  fun term_in_list (x : term) (xs : term list) : bool =
    List.exists (fn y => x = y) xs

  \<comment>\<open>Fails on unnecessary guards, succeeds otherwise.\<close>
  fun check_guard_with_bounded (bounded_vars : cterm list) (t : cterm) : bool =
    case (t |> Thm.term_of) of
      (Const (@{const_name GUARD}, _)) $ lhs $ _ =>
        if lhs |> Term.strip_comb |> fst |> Term.is_Var then
          \<comment>\<open>Guarded term \<^emph>\<open>is\<close> schematic... keep guard\<close>
          true
        else
          \<comment>\<open>LHS is not schematic.\<close>
          if term_in_list lhs (List.map Thm.term_of bounded_vars) then
            \<comment>\<open>LHS is a bounded variable -- keep it\<close>
            true
          else
            \<comment>\<open>LHS is neither schematic nor bound -- guard not needed.\<close>
            false
      | _ => true

  \<comment>\<open>Checks if a term is a guard\<close>
  fun is_guard (t : cterm) : bool =
    case (t |> Thm.term_of) of
      (Const (@{const_name GUARD}, _)) $ _ $ _ => true
      | _ => false

  \<comment>\<open>\<^term>\<open>check_guard\<close> as a dummy 'conversion', failing on unnecessary guards
     and keeping the term as is otherwise.\<close>
  fun check_guard_with_bounded_conv (bounded_vars : cterm list) : conv =
    check_guard_with_bounded bounded_vars |> filter_to_conv

  val check_guard_conv : conv = check_guard_with_bounded_conv []

  \<comment>\<open>Succeeds without change on guards, fails otherwise.\<close>
  val is_guard_conv : conv = is_guard |> filter_to_conv
  \<comment>\<open>Fails on guards, succeeds without change otherwise.\<close>
  val is_no_guard_conv : conv = (is_guard #> not) |> filter_to_conv

  \<comment>\<open>Applies a conversion expected to result in a term with head \<^term>\<open>guard\<close>,
     but only accepts the result if the guard is actually necessary.\<close>
  fun conv_guard_if_necessary (c : Proof.context -> conv)
    (bounded_vars : cterm list) (ctxt : Proof.context) : conv =
    (c ctxt) then_conv (check_guard_with_bounded_conv bounded_vars)

  \<comment>\<open>Remove guard(s), regardless of whether they are needed.\<close>
  val remove_guard_conv : conv = Conv.rewr_conv @{thm GUARD_def}
  val remove_all_guards_conv : Proof.context -> conv = Conv.top_conv (K remove_guard_conv)

  \<comment>\<open>Add guard(s), regardless of whether they are needed.\<close>
  fun add_guard_conv (_: Proof.context) (add_guard_thms : thm list) : conv = fn ct =>
    if ct |> Thm.term_of |> Term.exists_subterm Term.is_Var then
      Conv.rewrs_conv add_guard_thms ct
    else
      Conv.no_conv ct

  fun add_guards_conv (ctxt: Proof.context) (add_guard_thms : thm list) : conv = fn ct =>
    if ct |> Thm.term_of |> Term.is_schematic then
      Conv.top_sweep_rewrs_conv add_guard_thms ctxt ct
    else
      Conv.no_conv ct

  \<comment>\<open>Removes a redundant guards or leaves the term unchanged otherwise; always succeeds.\<close>
  val guard_conv_raw : conv = check_guard_conv else_conv remove_guard_conv

  \<comment>\<open>Remove an unnecessary guard.\<close>
  fun try_remove_guard_conv (vs : cterm list) : conv = (check_guard_with_bounded_conv vs) else_conv remove_guard_conv

  \<comment>\<open>Add/Remove guard around the current term (outermost layer only). Always succceeds.\<close>
  fun update_guard_single_conv (vs : cterm list) (ctxt : Proof.context) (add_guard_thms : thm list) : conv =
    Conv.try_conv (add_guard_conv ctxt add_guard_thms)
    then_conv (try_remove_guard_conv vs)

  \<comment>\<open>Update guards up to the first binder or (legitimate) guard\<close>
  fun update_guards_shallow_conv (ctxt : Proof.context) =
    let val add_guard_thms = Named_Theorems.get ctxt @{named_theorems add_guards}
    val update_single = update_guard_single_conv [] ctxt add_guard_thms
    fun core (t : cterm) =
      (update_single then_conv 
       (is_guard_conv
        else_conv (Conv.abs_conv (K Conv.all_conv) ctxt)
        else_conv (Conv.comb_conv core)
        else_conv Conv.all_conv)
      ) t
    in core end

  \<comment>\<open>Update guards recursively, stopping only at (legitimate) guards\<close>
  fun update_guards_deep_conv (vs : cterm list) (ctxt : Proof.context) =
    let val add_guard_thms = Named_Theorems.get ctxt @{named_theorems add_guards}
    fun core (t : cterm) =
      (update_guard_single_conv vs ctxt add_guard_thms
       then_conv (is_guard_conv
         else_conv (Conv.abs_conv (fn (v, ctxt') => fn t' => update_guards_deep_conv (v :: vs) ctxt' t') ctxt)
         else_conv (Conv.comb_conv (update_guards_deep_conv vs ctxt))
        else_conv Conv.all_conv)
      ) t
    in core end

  fun update_guards_shallow_tac (ctxt : Proof.context) : int -> tactic =
    \<comment>\<open>We always want to ignore top-level pure binders\<close>
    let
      val add_guard_thms = Named_Theorems.get ctxt @{named_theorems add_guards}
      fun conv_with_thms ctxt' =
        let val update_single = update_guard_single_conv [] ctxt' add_guard_thms
            fun core (t : cterm) =
              (update_single then_conv
               (is_guard_conv
                else_conv (Conv.abs_conv (K Conv.all_conv) ctxt')
                else_conv (Conv.comb_conv core)
                else_conv Conv.all_conv)
              ) t
        in core end
    in CONVERSION (Conv.params_conv ~1 conv_with_thms ctxt) end
  fun update_guards_deep_tac (ctxt : Proof.context) : int -> tactic =
    \<comment>\<open>We always want to ignore top-level pure binders\<close>
    let
      val add_guard_thms = Named_Theorems.get ctxt @{named_theorems add_guards}
      fun core_conv (vs : cterm list) (ctxt' : Proof.context) =
        let fun core (t : cterm) =
          (update_guard_single_conv vs ctxt' add_guard_thms
           then_conv (is_guard_conv
             else_conv (Conv.abs_conv (fn (v, ctxt'') => fn t' => core_conv (v :: vs) ctxt'' t') ctxt')
             else_conv (Conv.comb_conv core)
            else_conv Conv.all_conv)
          ) t
        in core end
    in CONVERSION (Conv.params_conv ~1 (core_conv []) ctxt) end
  fun update_guards_tac (deep : bool) : Proof.context -> int -> tactic =
    if deep then update_guards_deep_tac else update_guards_shallow_tac

end;

(* Isar *)

local
  val _ = Theory.setup (Method.setup @{binding "update_guards"}
          (Scan.succeed (SIMPLE_METHOD' o Crush_Guards.update_guards_tac false)) "" )

  val _ = Theory.setup (Method.setup @{binding "update_guards_deep"}
          (Scan.succeed (SIMPLE_METHOD' o Crush_Guards.update_guards_tac true)) "" )
in end
