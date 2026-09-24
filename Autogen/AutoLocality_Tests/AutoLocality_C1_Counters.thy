(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_C1_Counters
  imports Autogen.AutoLocality
begin
(*>*)

section\<open>AutoLocality legacy counter smoke\<close>

datatype_record c1_counter_state =
  c1_counter_a :: nat
  c1_counter_b :: nat
  c1_counter_c :: nat
  c1_counter_d :: nat

locality_init for c1_counter_state

definition c1_counter_block_a ::
    \<open>nat \<Rightarrow> c1_counter_state \<Rightarrow> c1_counter_state\<close> where
  \<open>c1_counter_block_a n R \<equiv>
    update_c1_counter_a (\<lambda>old. old + n + c1_counter_a R) R\<close>

definition c1_counter_front_cd ::
    \<open>c1_counter_state \<Rightarrow> c1_counter_state\<close> where
  \<open>c1_counter_front_cd R \<equiv>
    update_c1_counter_c Suc (update_c1_counter_d Suc R)\<close>

definition c1_counter_attr_a :: \<open>c1_counter_state \<Rightarrow> bool\<close> where
  \<open>c1_counter_attr_a R \<equiv> c1_counter_a R > 0\<close>

definition c1_lifecycle_attr :: \<open>c1_counter_state \<Rightarrow> bool\<close> where
  \<open>c1_lifecycle_attr R \<equiv> c1_counter_b R > 0\<close>

lemma c1_lifecycle_attr_update_a:
  shows \<open>c1_lifecycle_attr (update_c1_counter_a f R) =
    c1_lifecycle_attr R\<close>
  by (simp add: c1_lifecycle_attr_def)

lemma c1_lifecycle_attr_update_c:
  shows \<open>c1_lifecycle_attr (update_c1_counter_c f R) =
    c1_lifecycle_attr R\<close>
  by (simp add: c1_lifecycle_attr_def)

lemma c1_lifecycle_attr_update_d:
  shows \<open>c1_lifecycle_attr (update_c1_counter_d f R) =
    c1_lifecycle_attr R\<close>
  by (simp add: c1_lifecycle_attr_def)

locality_lemma for c1_counter_state:
  \<open>c1_counter_block_a\<close> footprint [c1_counter_a] .
locality_lemma for c1_counter_state:
  \<open>c1_counter_front_cd\<close>
  footprint [c1_counter_c, c1_counter_d] .
locality_lemma for c1_counter_state:
  \<open>c1_counter_attr_a\<close> footprint [c1_counter_a] .

ML\<open>
structure AutoLocality_C1_Counter_Smoke =
struct

open AutoLocality_Instrumentation

fun assert label condition =
  if condition then ()
  else error ("AutoLocality C1 counter smoke failed: " ^ label)

fun simplify_term ctxt source =
  let
    val cterm = Thm.cterm_of ctxt (Syntax.read_term ctxt source)
    val rewrite = Simplifier.rewrite ctxt cterm
  in Thm.term_of (Thm.rhs_of rewrite) end

fun the_snapshot label result =
  (case result of
    SOME snapshot => snapshot
  | NONE => error ("AutoLocality C1 counter smoke missing snapshot: " ^ label))

fun counters_are_zero snapshot =
  forall (fn (_, value) => value = 0) (snapshot_counters snapshot)

fun assert_term label ctxt actual expected =
  let val expected_term = Syntax.read_term ctxt expected in
    if Term.aconv (actual, expected_term) then ()
    else
      error ("AutoLocality C1 counter smoke failed: " ^ label
        ^ "\nActual: " ^ Syntax.string_of_term ctxt actual
        ^ "\nExpected: " ^ Syntax.string_of_term ctxt expected_term)
  end

fun assert_counter_positive label snapshot counter =
  assert label (snapshot_counter snapshot counter > 0)

fun assert_counter_zero label snapshot counter =
  assert label (snapshot_counter snapshot counter = 0)

val cache_counters =
  [Cache_Lookups,
   Cache_Hits,
   Cache_Misses,
   Cache_Insertions,
   Cache_Persistent_Events]

fun assert_cache_counters_zero label snapshot =
  List.app (fn counter =>
    assert_counter_zero
      (label ^ ": " ^ counter_name counter)
      snapshot counter) cache_counters

val reserved_future_counters =
  [Record_Index_Probes,
   Canonicalization_Requests,
   Canonicalization_Nodes,
   Canonicalization_Edges,
   Canonicalization_Individualizations,
   Canonicalization_Backtracks,
   Canonicalization_Serializations]

fun assert_reserved_zero label snapshot =
  List.app (fn counter =>
    assert_counter_zero
      (label ^ ": reserved " ^ counter_name counter)
      snapshot counter) reserved_future_counters

fun finish_run label run_id =
  let
    val snapshot = the_snapshot label (freeze_run run_id)
    val _ = assert (label ^ ": callbacks drained")
      (snapshot_active_callbacks snapshot = 0)
    val _ = assert (label ^ ": leases drained")
      (snapshot_async_leases snapshot = 0)
    val _ = assert (label ^ ": dropped") (drop_run run_id)
  in snapshot end

end
\<close>

ML\<open>
local

open AutoLocality_Instrumentation
open AutoLocality_C1_Counter_Smoke

val depth = 16
val head = \<^term>\<open>Not\<close>
val body = \<^term>\<open>True\<close>
val decomp = (replicate depth ((), (head, [], [])), body)

in

val _ =
  let
    val (run_id, ctxt) = start_run \<^context>
    val _ =
      op_term_with_gap_conv_with
        (locality_direct_counter ctxt) decomp Conv.all_conv I
    val snapshot = finish_run "linear conversion construction" run_id
    val recursive_nodes =
      snapshot_counter snapshot Planner_Recursive_Node_Builds
  in
    assert "conversion construction visits each telescope node once"
      (recursive_nodes = IntInf.fromInt depth)
  end

end
\<close>

ML\<open>
local

open AutoLocality_C1_Counter_Smoke

val depth = 16
val head = \<^term>\<open>Not\<close>
val body = \<^term>\<open>True\<close>
val decomp = (replicate depth ((), (head, [], [])), body)

in

val _ =
  let
    val node_executions = Unsynchronized.ref 0
    val late_failures = Unsynchronized.ref 0

    fun count_node ctm =
      (node_executions := !node_executions + 1;
       Conv.all_conv ctm)

    fun fail_late ctm =
      (late_failures := !late_failures + 1;
       Conv.no_conv ctm)

    fun fail_after_child child =
      Conv.arg_conv child then_conv fail_late

    val ctm =
      decomp
      |> recombine_decomposed_comb
      |> Thm.cterm_of \<^context>
    val conversion =
      op_term_with_gap_conv_with locality_no_count
        decomp count_node fail_after_child
    val result = conversion ctm
    val _ =
      assert "late-failure fallback returns reflexivity"
        (Thm.is_reflexive result)
    val _ =
      assert ("each conversion node executes once: "
        ^ Int.toString (!node_executions))
        (!node_executions = depth)
  in
    assert ("late failure occurs once per node: "
      ^ Int.toString (!late_failures))
      (!late_failures = depth)
  end

end
\<close>

locale c1_lifecycle_counter_target =
  fixes c1_lifecycle_witness :: unit
begin

local_setup \<open>fn lthy =>
  let
    open AutoLocality_Instrumentation
    open AutoLocality_C1_Counter_Smoke

    val grouped_lthy = Local_Theory.new_group lthy
    val local_fact_name = "c1_lifecycle_local_fact"
    val configured_lthy =
      grouped_lthy
      |> Proof_Context.put_thms false
           (local_fact_name, SOME [@{thm TrueI}])
      |> Config.put locality_trace_level (~1)
      |> Config.put locality_timing true
      |> Config.put locality_cancel_enabled false
    val group_before =
      Name_Space.get_group
        (Local_Theory.background_naming_of configured_lthy)
    val (run_id, counted_lthy) = start_run configured_lthy
    val target_run_before =
      current_run_id (Local_Theory.target_of counted_lthy)
    val (_, rec_name) =
      prepare_rec_name counted_lthy "c1_counter_state"
    val pattern =
      Syntax.read_term counted_lthy "c1_lifecycle_attr"
    val entry =
      make_locality_entry rec_name Locality_Attribute
        (extract_const pattern) pattern []
        ["c1_counter_b"] 1 0 false
        [@{thm c1_lifecycle_attr_update_a},
         @{thm c1_lifecycle_attr_update_c},
         @{thm c1_lifecycle_attr_update_d}]
        [] NONE
    val dispatch_key =
      locality_dispatch_key_of_entry counted_lthy entry
    val registered_lthy =
      add_record_locality_entry
        counted_lthy rec_name entry counted_lthy
    val dispatcher_name =
      (case LocalityDispatchKeyTable.lookup
              (LocalityDispatcherInventory.get
                (Context.Proof registered_lthy))
              dispatch_key of
         SOME entry => #source_name entry
       | _ =>
           error "First lifecycle installation has no inventory entry")
    fun raw_count ctxt =
      Raw_Simplifier.simpset_of ctxt
      |> Raw_Simplifier.dest_ss
      |> #simprocs
      |> filter (fn (name, _) => name = dispatcher_name)
      |> length
    val first_raw_count = raw_count registered_lthy
    val disabled_result =
      locality_cancellation_simproc_for_dispatch
        dispatch_key registered_lthy
        (Thm.cterm_of registered_lthy
          \<^term>\<open>c1_lifecycle_attr
            (c1_counter_front_cd R)\<close>)
    val repeated_lthy =
      add_record_locality_entry
        registered_lthy rec_name entry registered_lthy
    val repeated_raw_count = raw_count repeated_lthy
    val group_after =
      Name_Space.get_group
        (Local_Theory.background_naming_of repeated_lthy)
    val local_fact_preserved =
      (case Proof_Context.get_thms repeated_lthy local_fact_name of
         [thm] =>
           Term.aconv (Thm.prop_of thm, Thm.prop_of @{thm TrueI})
       | _ => false)
    val _ = assert
      "local installation preserves run selection at each level"
      (current_run_id repeated_lthy = run_id
       andalso current_run_id (Local_Theory.target_of repeated_lthy) =
         target_run_before)
    val _ = assert "first installation preserves command group"
      (Option.isSome group_before andalso group_after = group_before)
    val _ = assert "first installation preserves proof-local named facts"
      local_fact_preserved
    val _ = assert "first installation preserves trace configuration"
      (Config.get repeated_lthy locality_trace_level = ~1)
    val _ = assert "first installation preserves timing configuration"
      (Config.get repeated_lthy locality_timing)
    val _ = assert "first installation preserves cancellation opt-out"
      (not (Config.get repeated_lthy locality_cancel_enabled))
    val _ = assert "disabled installation keeps one raw dispatcher"
      (first_raw_count = 1)
    val _ = assert "disabled callback declines without lookup"
      (case disabled_result of NONE => true | SOME _ => false)
    val _ = assert "same-family registration does not duplicate dispatch"
      (repeated_raw_count = 1)
    val snapshot =
      finish_run "first dispatcher lifecycle" run_id
    val _ =
      assert_counter_positive "dispatcher insertion accounting"
        snapshot Lifecycle_Dispatcher_Insertions
    val _ =
      assert_counter_positive "duplicate dispatcher accounting"
        snapshot Lifecycle_Duplicate_Dispatchers
    val _ =
      assert_counter_positive "semantic insertion accounting"
        snapshot Lifecycle_Semantic_Insertions
    val _ =
      assert_counter_positive "index node accounting"
        snapshot Index_Nodes
    val _ =
      assert_counter_positive "secondary index accounting"
        snapshot Index_Secondary_Insertions
  in
    repeated_lthy
    |> Config.put locality_trace_level 0
    |> Config.put locality_timing false
    |> disable_run
  end\<close>

context
  notes [[locality_cancel]]
begin

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_C1_Counters.c1_counter_state"
  val entry =
    (case select_locality_entry_for_pattern
            ctxt rec_name "attribute"
            \<^term>\<open>c1_lifecycle_attr\<close> of
       SOME value => value
     | NONE => error "Missing lifecycle entry after explicit re-enable")
  val dispatch_key = locality_dispatch_key_of_entry ctxt entry
  val dispatcher_name =
    (case LocalityDispatchKeyTable.lookup
            (LocalityDispatcherInventory.get (Context.Proof ctxt))
            dispatch_key of
       SOME entry => #source_name entry
     | _ => error "Missing lifecycle inventory after explicit re-enable")
  val raw_count =
    Raw_Simplifier.simpset_of ctxt
    |> Raw_Simplifier.dest_ss
    |> #simprocs
    |> filter (fn (name, _) => name = dispatcher_name)
    |> length
  val _ =
    AutoLocality_C1_Counter_Smoke.assert
      "explicit re-enable retains one local raw dispatcher"
      (Config.get ctxt locality_cancel_enabled
       andalso raw_count = 1)
\<close>

lemma c1_lifecycle_explicit_reenable:
  shows \<open>c1_lifecycle_attr (c1_counter_front_cd R) =
    c1_lifecycle_attr R\<close>
  by simp

end

end

ML\<open>
local

open AutoLocality_Instrumentation
open AutoLocality_C1_Counter_Smoke

val success_source =
  "c1_counter_attr_a \
  \(c1_counter_block_a n (c1_counter_front_cd R))"
val success_expected =
  "c1_counter_attr_a (c1_counter_block_a n R)"
val identity_source =
  "c1_counter_attr_a (c1_counter_front_cd R)"
val identity_expected =
  "c1_counter_attr_a R"
val field_identity_source =
  "c1_counter_a (c1_counter_front_cd R)"
val field_identity_expected =
  "c1_counter_a R"
val deep_identity_depth = 40
val deep_identity_source =
  fold (fn _ => fn body =>
      "c1_counter_front_cd (" ^ body ^ ")")
    (1 upto deep_identity_depth) "R"
  |> enclose "c1_counter_attr_a (" ")"
val decline_source =
  "c1_counter_attr_a (c1_counter_block_a n R)"

fun assert_enabled_exact_work snapshot =
  (assert_counter_positive "lookup requests" snapshot Lookup_Requests;
   assert_counter_positive "lookup index probes" snapshot
     Lookup_Index_Probes;
   assert_counter_positive "lookup entries" snapshot Lookup_Entries_Examined;
   assert "lookup comparisons are final-candidate bounded"
     (snapshot_counter snapshot Lookup_Comparisons <=
      snapshot_counter snapshot Lookup_Candidates_Returned);
   assert_counter_positive "lookup specialization" snapshot
     Lookup_Specializations;
   assert_counter_zero "whole-registry scans" snapshot
     Lookup_Whole_Registry_Scans;
   assert_counter_zero "lookup sorts" snapshot Lookup_Sort_Calls;
   assert_counter_zero "whole-family rebuilds" snapshot
     Index_Whole_Family_Rebuilds;
   assert_counter_positive "planner request" snapshot Planner_Requests;
   assert_counter_zero "exact swap has no planner base child" snapshot
     Planner_Base_Child_Builds;
   assert_counter_positive "exact swap recursive nodes" snapshot
     Planner_Recursive_Node_Builds;
   assert_counter_positive "exact swap context lifts" snapshot
     Planner_Context_Lifts;
   assert_counter_positive "exact swap application frames" snapshot
     Planner_Application_Frames;
   assert_counter_positive "planner swaps" snapshot Planner_Swaps;
   assert_counter_positive "planner swap applications" snapshot
     Planner_Swap_Applications;
   assert_counter_positive "planner cancellations" snapshot
     Planner_Cancellations;
   assert_counter_positive "scheduled root rewrites" snapshot
     Planner_Root_Rewrites;
   assert_counter_zero "no root rescans" snapshot
     Planner_Root_Rescans;
   assert_counter_positive "exact swap tail copies" snapshot
     Planner_Tail_Copies;
   assert_counter_positive "proof cterms" snapshot Proof_Cterms;
   assert_counter_positive "proof compositions" snapshot Proof_Compositions;
   assert_counter_positive "proof results" snapshot Proof_Results;
   assert_counter_positive "record preparation sentinel" snapshot
     Record_Preparations;
   assert_counter_positive "record rules selected" snapshot
     Record_Rules_Selected;
   assert_counter_positive "record simpset rebuild sentinel" snapshot
     Record_Simpset_Builds;
   assert_counter_zero "no fallback request" snapshot
     Fallback_Requests;
   assert_counter_zero "no fallback crossings" snapshot Fallback_Crossings;
   assert_counter_zero "no fallback whole-term rewrites" snapshot
     Fallback_Whole_Term_Rewrites)

fun assert_root_schedule label expected snapshot =
  (assert
     (label ^ ": exact scheduled root rewrites")
     (snapshot_counter snapshot Planner_Root_Rewrites =
       IntInf.fromInt expected);
   assert_counter_zero
     (label ^ ": no cancellation simpset")
     snapshot Record_Simpset_Builds;
   assert_counter_zero
     (label ^ ": no fallback request")
     snapshot Fallback_Requests;
   assert_counter_zero
     (label ^ ": no whole-term fallback")
     snapshot Fallback_Whole_Term_Rewrites)

in

val _ =
  let
    val base_context = \<^context>

    val (identity_run, identity_context) = start_run base_context
    val identity_result = simplify_term identity_context identity_source
    val identity_snapshot =
      finish_run "already-hoisted cancellation" identity_run
    val _ = assert_term "already-hoisted cancellation result"
      identity_context identity_result identity_expected
    val _ = assert_counter_positive "already-hoisted planner request"
      identity_snapshot Planner_Requests
    val _ = assert_counter_positive "already-hoisted cancellation"
      identity_snapshot Planner_Cancellations
    val _ = assert_root_schedule
      "already-hoisted cancellation" 1 identity_snapshot

    val (field_identity_run, field_identity_context) = start_run base_context
    val field_identity_result =
      simplify_term field_identity_context field_identity_source
    val field_identity_snapshot =
      finish_run "field-selector cancellation" field_identity_run
    val _ = assert_term "field-selector cancellation result"
      field_identity_context field_identity_result field_identity_expected
    val _ = assert_counter_positive "field-selector planner request"
      field_identity_snapshot Planner_Requests
    val _ = assert_counter_positive "field-selector cancellation"
      field_identity_snapshot Planner_Cancellations
    val _ = assert_root_schedule
      "field-selector cancellation" 1 field_identity_snapshot

    val (deep_identity_run, deep_identity_context) = start_run base_context
    val deep_identity_result =
      simplify_term deep_identity_context deep_identity_source
    val deep_identity_snapshot =
      finish_run "depth-40 already-hoisted cancellation" deep_identity_run
    val _ = assert_term "depth-40 already-hoisted cancellation result"
      deep_identity_context deep_identity_result identity_expected
    val deep_identity_cancellations =
      snapshot_counter deep_identity_snapshot Planner_Cancellations
    val _ = assert
      ("depth-40 cancellation visits every front operation: "
        ^ IntInf.toString deep_identity_cancellations)
      (deep_identity_cancellations = IntInf.fromInt deep_identity_depth)
    val _ = assert_root_schedule
      "depth-40 cancellation" deep_identity_depth deep_identity_snapshot

    val (first_run, first_context) = start_run base_context
    val first_result = simplify_term first_context success_source
    val first_snapshot =
      finish_run "first successful simplification" first_run
    val _ = assert_term "first installed simproc result"
      first_context first_result success_expected
    val _ = assert_counter_positive "first callback" first_snapshot
      Callback_Invocations
    val _ = assert_counter_positive "first SOME outcome" first_snapshot
      Callback_Some_Results
    val _ = assert_counter_positive "first callback-local work" first_snapshot
      Callback_Work_Units
    val _ = assert_enabled_exact_work first_snapshot
    val _ =
      assert_cache_counters_zero "first simplification" first_snapshot
    val _ = assert_reserved_zero "first simplification" first_snapshot

    val (repeated_run, repeated_context) = start_run base_context
    val repeated_result = simplify_term repeated_context success_source
    val repeated_snapshot =
      finish_run "repeated successful simplification" repeated_run
    val _ = assert_term "repeated installed simproc result"
      repeated_context repeated_result success_expected
    val _ = assert_counter_positive "repeated callback" repeated_snapshot
      Callback_Invocations
    val _ = assert_counter_positive "repeated proof results"
      repeated_snapshot Proof_Results
    val _ =
      assert_cache_counters_zero "repeated simplification" repeated_snapshot

    val (decline_run, decline_context) = start_run base_context
    val decline_result = simplify_term decline_context decline_source
    val decline_snapshot = finish_run "triggered decline" decline_run
    val _ = assert_term "triggered decline preserves term"
      decline_context decline_result decline_source
    val _ = assert_counter_positive "decline callback" decline_snapshot
      Callback_Invocations
    val _ = assert_counter_positive "decline NONE outcome" decline_snapshot
      Callback_None_Results
    val _ = assert_counter_zero "decline has no SOME outcome" decline_snapshot
      Callback_Some_Results
    val _ = assert_counter_positive "decline callback-local work"
      decline_snapshot Callback_Work_Units

    val (disabled_source_run, selected_context) = start_run base_context
    val disabled_context = disable_run selected_context
    val disabled_result = simplify_term disabled_context success_source
    val disabled_snapshot =
      finish_run "run-ID-zero production path" disabled_source_run
    val _ = assert_term "run-ID-zero preserves cancellation"
      disabled_context disabled_result success_expected
    val _ = assert "run-ID-zero leaves collector untouched"
      (counters_are_zero disabled_snapshot)

    val (config_run, config_context0) = start_run base_context
    val config_context =
      Config.put locality_cancel_enabled false config_context0
    val config_result = simplify_term config_context success_source
    val config_snapshot =
      finish_run "Config-disabled production path" config_run
    val _ = assert_term "Config false preserves the redex"
      config_context config_result success_source
    val _ = assert "Config false precedes callback instrumentation"
      (counters_are_zero config_snapshot)

    val (reenabled_run, reenabled_context0) = start_run base_context
    val reenabled_context =
      reenabled_context0
      |> Config.put locality_cancel_enabled false
      |> Config.put locality_cancel_enabled true
    val reenabled_result = simplify_term reenabled_context success_source
    val reenabled_snapshot =
      finish_run "inner Config re-enable" reenabled_run
    val _ = assert_term "inner Config re-enable restores cancellation"
      reenabled_context reenabled_result success_expected
    val _ = assert_counter_positive "inner Config re-enable callback"
      reenabled_snapshot Callback_Invocations
  in () end

end
\<close>

context
  notes [[locality_no_cancel]]
begin

ML\<open>
local

open AutoLocality_Instrumentation
open AutoLocality_C1_Counter_Smoke

val source =
  "c1_counter_attr_a \
  \(c1_counter_block_a n (c1_counter_front_cd R))"

in

val _ =
  let
    val (run_id, ctxt) = start_run \<^context>
    val result = simplify_term ctxt source
    val snapshot = finish_run "scoped locality_no_cancel" run_id
    val _ = assert_term "scoped locality_no_cancel preserves the redex"
      ctxt result source
    val _ = assert "scoped locality_no_cancel leaves counters zero"
      (counters_are_zero snapshot)
  in () end

end
\<close>

lemma c1_counter_explicit_fact_ignores_ambient_opt_out:
  shows \<open>c1_counter_attr_a (c1_counter_front_cd R) =
    c1_counter_attr_a R\<close>
  by (rule [[locality_autocancellation
    (c1_counter_state) c1_counter_front_cd c1_counter_attr_a 0]])

context
  notes [[locality_cancel]]
begin

ML\<open>
local

open AutoLocality_Instrumentation
open AutoLocality_C1_Counter_Smoke

val source =
  "c1_counter_attr_a \
  \(c1_counter_block_a n (c1_counter_front_cd R))"
val expected =
  "c1_counter_attr_a (c1_counter_block_a n R)"

in

val _ =
  let
    val (run_id, ctxt) = start_run \<^context>
    val result = simplify_term ctxt source
    val snapshot = finish_run "public inner re-enable" run_id
    val _ = assert_term "public locality_cancel restores cancellation"
      ctxt result expected
    val _ = assert_counter_positive "public re-enable callback"
      snapshot Callback_Invocations
  in () end

end
\<close>

end

end

(*<*)
end
(*>*)
