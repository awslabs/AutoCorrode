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

named_theorems asepconj_pick_thms
named_theorems asepconj_rotate_thms

ML_file "seplog.ML"

text\<open>Pre-generate cached picker and rotation theorems for separating conjunctions.
For indices beyond this limit, \<^verbatim>\<open>asepconj_pick_conv\<close> in \<^file>\<open>seplog.ML\<close> uses
chunked composition instead of ad-hoc generation.\<close>
local_setup\<open>prove_register_asepconj_pick_upto 75\<close>
local_setup\<open>prove_register_asepconj_rotate_upto 25\<close>

text\<open>Pre-generate cached hoist-existential theorems for separating conjunctions.
For positions beyond this limit, \<^verbatim>\<open>asepconj_hoist_conv\<close> in \<^file>\<open>seplog.ML\<close> builds
the conversion on the fly from distrib + distrib_right.\<close>
local_setup\<open>prove_register_asepconj_hoist_upto 75\<close>

text\<open>Tests for existential hoisting out of separating conjunctions.

Three implementations are provided in \<^file>\<open>seplog.ML\<close>:

\<^item> \<^bold>\<open>Pre-generated\<close> (\<^verbatim>\<open>asepconj_hoist_existential_pregen_conv\<close>):
  Scans the right spine for \<open>\<Squnion>(range ...)\<close> components and hoists each one
  using cached theorems.  For positions within the cache limit (set above via
  \<^verbatim>\<open>prove_register_asepconj_hoist_upto\<close>), each hoist is a single rewrite; beyond
  the limit it falls back to chunked composition.
  Total cost: O(N) scan + O(K) hoists, each O(1) within the cache or O(i/L)
  beyond it, where L is the cache limit.

\<^item> \<^bold>\<open>Binary tree\<close> (\<^verbatim>\<open>asepconj_hoist_existential_tree_conv\<close>):
  Re-associates the right-associated chain into a balanced binary tree of
  depth \<^verbatim>\<open>O(log\<^sub>2 N)\<close>, distributes \<open>\<Squnion>\<close> bottom-up at each internal node using
  \<^verbatim>\<open>asepconj_Inf_distrib\<close> / \<^verbatim>\<open>asepconj_Inf_distrib_right\<close>, and re-flattens.
  Total cost: O(N log N), independent of the cache limit.

\<^item> \<^bold>\<open>4-ary tree\<close> (\<^verbatim>\<open>asepconj_hoist_existential_tree4_conv\<close>):
  Same approach as the binary tree, but re-associates into a 4-ary tree
  of depth \<^verbatim>\<open>O(log\<^sub>4 N)\<close>.  Each internal node is a right-associated chain of
  up to 4 children; hoisting uses 4-ary distrib theorems
  (\<^verbatim>\<open>asepconj_Inf_distrib4_1\<close> through \<^verbatim>\<open>_4\<close>) plus the 2-ary and 3-ary
  variants for nodes with fewer children.  The shallower tree reduces the
  number of \<^verbatim>\<open>abs_conv\<close> binder-descent levels during the merge phase.

The tree versions are asymptotically better than the pre-generated approach,
but have higher constant factors due to balancing and re-flattening.
With a cache limit of 25, the pre-generated version is faster for small
chains; the tree versions win for larger N.\<close>

ML\<open>
local
  open Separation_Logic_Tactics

  val T = @{typ "'s::sepalg assert"}
  val fT = @{typ "'s"} --> T

  fun mk_sup_range i =
    Const (@{const_name Sup}, HOLogic.mk_setT T --> T) $
     (Const (@{const_name image}, fT --> HOLogic.mk_setT @{typ "'s"} --> HOLogic.mk_setT T) $
      Free ("R" ^ Int.toString i, fT) $
      Const (@{const_name top}, HOLogic.mk_setT @{typ "'s"}))
  fun mk_plain i = Free ("A" ^ Int.toString i, T)

  fun mk_test_chain ctxt n every =
    let
      val terms = List.tabulate (n, fn i =>
        if i mod every = 0 then mk_sup_range i else mk_plain i) @ [Free ("tail", T)]
    in Thm.cterm_of ctxt (mk_asepconj terms) end

  fun elapsed f =
    let val start = Timing.start ()
        val x = f ()
        val t = Timing.result start
    in (x, #elapsed t |> Time.toMilliseconds) end

  fun assert_top_is_Sup name result =
    let val rhs = Thm.rhs_of result |> Thm.term_of
    in (case rhs of Const (@{const_name Sup}, _) $ _ => ()
         | _ => error ("FAILED " ^ name ^ ": top of RHS is not Sup.\nGot: " ^
                       Syntax.string_of_term @{context} rhs))
    end

  (* Positional hoist tests (pre-generated approach) *)
  fun test_hoist_conv ctxt i =
    let
      val prefix = List.tabulate (i, mk_plain)
      val ct = Thm.cterm_of ctxt (mk_asepconj (prefix @ [mk_sup_range 99, Free ("tail", T)]))
      val (_, t) = elapsed (fn () => asepconj_hoist_conv ctxt i ct)
      val _ = tracing ("  hoist_conv(" ^ Int.toString i ^ "): " ^ Int.toString t ^ "ms")
    in () end

  fun test_hoist_tail_conv ctxt i =
    let
      val prefix = List.tabulate (i + 1, mk_plain)
      val ct = Thm.cterm_of ctxt (mk_asepconj (prefix @ [mk_sup_range 99]))
      val (_, t) = elapsed (fn () => asepconj_hoist_tail_conv ctxt i ct)
      val _ = tracing ("  hoist_tail_conv(" ^ Int.toString i ^ "): " ^ Int.toString t ^ "ms")
    in () end

  (* Correctness test: mixed chain with both plain and Sup components *)
  fun test_correctness label conv ctxt terms =
    let
      val ct = Thm.cterm_of ctxt (mk_asepconj terms)
      val (result, t) = elapsed (fn () => conv ctxt ct)
      val _ = tracing ("  " ^ label ^ ": " ^ Int.toString t ^ "ms")
      val _ = assert_top_is_Sup label result
    in () end

  val mixed_terms = [mk_sup_range 1, mk_plain 0, mk_sup_range 2,
                     mk_plain 1, mk_plain 2, mk_sup_range 3, Free ("tail", T)]
  val tail_terms  = [mk_plain 0, mk_plain 1, mk_sup_range 1]
  val tail2_terms = [mk_sup_range 1, mk_plain 0, mk_sup_range 2]

  (* Comparative benchmark *)
  fun bench ctxt n every =
    let
      val ct = mk_test_chain ctxt n every
      val (_, t_pregen) = elapsed (fn () => asepconj_hoist_existential_pregen_conv ctxt ct)
                          handle CTERM _ => (Thm.reflexive ct, ~1)
      val (_, t_tree) = elapsed (fn () => asepconj_hoist_existential_tree_conv ctxt ct)
                        handle CTERM _ => (Thm.reflexive ct, ~1)
      val (_, t_tree4) = elapsed (fn () => asepconj_hoist_existential_tree4_conv ctxt ct)
                         handle CTERM _ => (Thm.reflexive ct, ~1)
      val _ = tracing ("  n=" ^ Int.toString n ^
                        " every=" ^ Int.toString every ^
                        "  pregen=" ^ Int.toString t_pregen ^ "ms" ^
                        "  tree2=" ^ Int.toString t_tree ^ "ms" ^
                        "  tree4=" ^ Int.toString t_tree4 ^ "ms")
    in () end
in
  (* Pre-generated: positional hoist within and beyond cache *)
  val _ = tracing "=== hoist_conv (within cache) ===";
  val _ = List.app (test_hoist_conv @{context}) [0, 5, 24];
  val _ = tracing "=== hoist_conv (beyond cache, chunked) ===";
  val _ = List.app (test_hoist_conv @{context}) [75, 200];
  val _ = tracing "=== hoist_tail_conv (within cache) ===";
  val _ = List.app (test_hoist_tail_conv @{context}) [0, 5, 24];
  val _ = tracing "=== hoist_tail_conv (beyond cache, chunked) ===";
  val _ = List.app (test_hoist_tail_conv @{context}) [75, 200];

  (* Correctness: pre-generated bulk *)
  val _ = tracing "=== Correctness: pre-generated ===";
  val _ = test_correctness "pregen/mixed" asepconj_hoist_existential_pregen_conv @{context} mixed_terms;
  val _ = test_correctness "pregen/tail"  asepconj_hoist_existential_pregen_conv @{context} tail_terms;
  val _ = test_correctness "pregen/tail2" asepconj_hoist_existential_pregen_conv @{context} tail2_terms;

  (* Correctness: binary tree *)
  val _ = tracing "=== Correctness: tree2 ===";
  val _ = test_correctness "tree2/mixed" asepconj_hoist_existential_tree_conv @{context} mixed_terms;
  val _ = test_correctness "tree2/tail"  asepconj_hoist_existential_tree_conv @{context} tail_terms;
  val _ = test_correctness "tree2/tail2" asepconj_hoist_existential_tree_conv @{context} tail2_terms;

  (* Correctness: 4-ary tree *)
  val _ = tracing "=== Correctness: tree4 ===";
  val _ = test_correctness "tree4/mixed" asepconj_hoist_existential_tree4_conv @{context} mixed_terms;
  val _ = test_correctness "tree4/tail"  asepconj_hoist_existential_tree4_conv @{context} tail_terms;
  val _ = test_correctness "tree4/tail2" asepconj_hoist_existential_tree4_conv @{context} tail2_terms;

  (* Comparative benchmark: pregen vs tree2 vs tree4 at varying sizes and densities *)
  val _ = tracing "=== Comparison: all Sup (every=1) ===";
  val tests = [10, 20, 30, 40, 50, 70, 80, 90, 100, 200, 300, 400, 500, 600, 750, 1000]
  val _ = List.app (fn n => bench @{context} n 1) tests;
  val _ = tracing "=== Comparison: every 4th ===";
  val _ = List.app (fn n => bench @{context} n 4) tests

end
\<close>

ML\<open>
  \<comment>\<open>Stress test for chunked pick composition beyond the cached range.\<close>
local
  open Separation_Logic_Tactics
  val T = @{typ "'s::sepalg assert"}
  fun mk_var i = Free ("a" ^ Int.toString i, T)
  fun mk_conj n = mk_asepconj (List.tabulate (n, mk_var))

  fun elapsed f =
    let val start = Timing.start ()
        val x = f ()
        val t = Timing.result start
    in (x, #elapsed t |> Time.toMilliseconds) end

  fun test_pick ctxt n i =
    let
      val ct = Thm.cterm_of ctxt (mk_conj n)
      val (result, t_conv) = elapsed (fn () => asepconj_pick_conv ctxt n i ct)
      val (lhs_term, rhs_term) = result |> Thm.prop_of |> Logic.dest_equals
      val lhs = split_asepconj lhs_term
      val rhs = split_asepconj rhs_term
      val expected_hd = List.nth (lhs, i)
      val expected_rest = List.take (lhs, i) @ List.drop (lhs, i + 1)
      val _ =
        if hd rhs = expected_hd andalso tl rhs = expected_rest then
          tracing ("pick(" ^ Int.toString n ^ "," ^ Int.toString i ^ "): "
                   ^ Int.toString t_conv ^ "ms")
        else error ("FAILED for pick(" ^ Int.toString n ^ "," ^ Int.toString i ^ ")")
    in () end

  fun test_rotate ctxt n =
    let
      val ct = Thm.cterm_of ctxt (mk_conj n)
      val (result, t_conv) = elapsed (fn () => asepconj_rotate_conv ctxt ct)
      val (lhs_term, rhs_term) = result |> Thm.prop_of |> Logic.dest_equals
      val lhs = split_asepconj lhs_term
      val rhs = split_asepconj rhs_term
      val expected = tl lhs @ [hd lhs]
      val _ =
        if rhs = expected then
          tracing ("rotate(" ^ Int.toString n ^ "): "
                   ^ Int.toString t_conv ^ "ms")
        else error ("FAILED for rotate(" ^ Int.toString n ^ ")")
    in () end

  fun test_range ctxt =
    let val is = List.tabulate (50, fn k => (k + 1) * 50)
    in List.app (fn i =>
         (test_pick ctxt (i + 1) i;
          test_rotate ctxt (i + 1))
       ) is
    end
in
  val _ = test_range @{context}
end
\<close>

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

lemma wp_cong[crush_cong]:
  assumes \<open>\<phi> = \<phi>'\<close>
      and \<open>e = e'\<close>
    shows \<open>(\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) \<longleftrightarrow> (\<phi>' \<longlongrightarrow> \<W>\<P> \<Gamma> e' \<psi> \<rho> \<theta>)\<close>
using assms by auto

lemma wp_cong'[crush_cong]:
  assumes \<open>\<phi> = \<phi>'\<close>
    shows \<open>(\<phi> \<Zsurj> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = (\<phi>' \<Zsurj> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>)\<close>
using assms by auto

end
(*>*)
