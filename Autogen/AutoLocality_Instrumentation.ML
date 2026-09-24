(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature AUTOLOCALITY_INSTRUMENTATION =
sig
  type run_id = int

  datatype phase = Open | Frozen

  datatype counter =
      Callback_Invocations
    | Callback_Some_Results
    | Callback_None_Results
    | Callback_Exceptions
    | Callback_Interrupts
    | Callback_Work_Units
    | Lookup_Requests
    | Lookup_Index_Probes
    | Lookup_Prefix_Alternatives
    | Lookup_Equality_Attempts
    | Lookup_Candidates_Returned
    | Lookup_Entries_Examined
    | Lookup_Comparisons
    | Lookup_Sort_Calls
    | Lookup_Specializations
    | Lookup_Whole_Registry_Scans
    | Index_Nodes
    | Index_Secondary_Insertions
    | Index_Whole_Family_Rebuilds
    | Planner_Requests
    | Planner_Base_Child_Builds
    | Planner_Recursive_Node_Builds
    | Planner_Context_Lifts
    | Planner_Application_Frames
    | Planner_Swaps
    | Planner_Swap_Applications
    | Planner_Cancellations
    | Planner_Root_Rescans
    | Planner_Root_Rewrites
    | Planner_Tail_Copies
    | Proof_Cterms
    | Proof_Fresh_Nodes
    | Proof_Control_Nodes
    | Proof_Compositions
    | Proof_Results
    | Record_Preparations
    | Record_Index_Probes
    | Record_Rules_Selected
    | Record_Hierarchy_Scans
    | Record_Simpset_Builds
    | Fallback_Requests
    | Fallback_Crossings
    | Fallback_Whole_Term_Rewrites
    | Cache_Lookups
    | Cache_Hits
    | Cache_Misses
    | Cache_Insertions
    | Cache_Persistent_Events
    | Lifecycle_Registration_Attempts
    | Lifecycle_Semantic_Insertions
    | Lifecycle_Replays
    | Lifecycle_Conflicts
    | Lifecycle_Dispatcher_Insertions
    | Lifecycle_Duplicate_Dispatchers
    | Canonicalization_Requests
    | Canonicalization_Nodes
    | Canonicalization_Edges
    | Canonicalization_Individualizations
    | Canonicalization_Backtracks
    | Canonicalization_Serializations
    | Resource_Future_Joins
    | Resource_Reference_Drops
    | Resource_Full_GCs
    | Resource_Samples

  datatype resource =
      Elapsed_Microseconds
    | Allocated_Bytes
    | Live_Bytes
    | Peak_Bytes
    | Resident_Bytes

  type scenario_label = string * string
  type snapshot

  val disabled_run_id: run_id
  val all_counters: counter list
  val counter_name: counter -> string
  val all_resources: resource list
  val resource_name: resource -> string

  val current_run_id: Proof.context -> run_id
  val disable_run: Proof.context -> Proof.context
  val restore_run_selection:
    Proof.context -> Proof.context -> Proof.context
  val start_run: Proof.context -> run_id * Proof.context
  val start_run_with_labels:
    scenario_label list -> Proof.context -> run_id * Proof.context
  val reset_run: Proof.context -> run_id * Proof.context

  val phase_of: run_id -> phase option
  val active_callbacks_of: run_id -> int option
  val async_leases_of: run_id -> int option
  val await_frozen: run_id -> bool

  val record_counter: Proof.context -> counter -> IntInf.int -> unit
  val record_counters:
    Proof.context -> (unit -> (counter * IntInf.int) list) -> unit
  val set_resource: Proof.context -> resource -> IntInf.int -> unit
  val set_resources:
    Proof.context -> (unit -> (resource * IntInf.int) list) -> unit

  val with_callback:
    Proof.context -> (unit -> IntInf.int) ->
    (unit -> 'a option) -> 'a option
  val fork_with_lease:
    Proof.context -> (Proof.context -> 'a) -> 'a future

  val freeze_run: run_id -> snapshot option
  val drop_run: run_id -> bool

  val snapshot_run_id: snapshot -> run_id
  val snapshot_phase: snapshot -> phase
  val snapshot_active_callbacks: snapshot -> int
  val snapshot_async_leases: snapshot -> int
  val snapshot_scenario_labels: snapshot -> scenario_label list
  val snapshot_counter: snapshot -> counter -> IntInf.int
  val snapshot_counters: snapshot -> (counter * IntInf.int) list
  val snapshot_resource: snapshot -> resource -> IntInf.int
  val snapshot_resources: snapshot -> (resource * IntInf.int) list
  val snapshot_xml: snapshot -> XML.tree
  val snapshot_yxml: snapshot -> string
end

structure AutoLocality_Instrumentation: AUTOLOCALITY_INSTRUMENTATION =
struct

type run_id = int

datatype phase = Open | Frozen

datatype counter =
    Callback_Invocations
  | Callback_Some_Results
  | Callback_None_Results
  | Callback_Exceptions
  | Callback_Interrupts
  | Callback_Work_Units
  | Lookup_Requests
  | Lookup_Index_Probes
  | Lookup_Prefix_Alternatives
  | Lookup_Equality_Attempts
  | Lookup_Candidates_Returned
  | Lookup_Entries_Examined
  | Lookup_Comparisons
  | Lookup_Sort_Calls
  | Lookup_Specializations
  | Lookup_Whole_Registry_Scans
  | Index_Nodes
  | Index_Secondary_Insertions
  | Index_Whole_Family_Rebuilds
  | Planner_Requests
  | Planner_Base_Child_Builds
  | Planner_Recursive_Node_Builds
  | Planner_Context_Lifts
  | Planner_Application_Frames
  | Planner_Swaps
  | Planner_Swap_Applications
  | Planner_Cancellations
  | Planner_Root_Rescans
  | Planner_Root_Rewrites
  | Planner_Tail_Copies
  | Proof_Cterms
  | Proof_Fresh_Nodes
  | Proof_Control_Nodes
  | Proof_Compositions
  | Proof_Results
  | Record_Preparations
  | Record_Index_Probes
  | Record_Rules_Selected
  | Record_Hierarchy_Scans
  | Record_Simpset_Builds
  | Fallback_Requests
  | Fallback_Crossings
  | Fallback_Whole_Term_Rewrites
  | Cache_Lookups
  | Cache_Hits
  | Cache_Misses
  | Cache_Insertions
  | Cache_Persistent_Events
  | Lifecycle_Registration_Attempts
  | Lifecycle_Semantic_Insertions
  | Lifecycle_Replays
  | Lifecycle_Conflicts
  | Lifecycle_Dispatcher_Insertions
  | Lifecycle_Duplicate_Dispatchers
  | Canonicalization_Requests
  | Canonicalization_Nodes
  | Canonicalization_Edges
  | Canonicalization_Individualizations
  | Canonicalization_Backtracks
  | Canonicalization_Serializations
  | Resource_Future_Joins
  | Resource_Reference_Drops
  | Resource_Full_GCs
  | Resource_Samples

datatype resource =
    Elapsed_Microseconds
  | Allocated_Bytes
  | Live_Bytes
  | Peak_Bytes
  | Resident_Bytes

type scenario_label = string * string

val disabled_run_id = 0

val all_counters =
  [Callback_Invocations,
   Callback_Some_Results,
   Callback_None_Results,
   Callback_Exceptions,
   Callback_Interrupts,
   Callback_Work_Units,
   Lookup_Requests,
   Lookup_Index_Probes,
   Lookup_Prefix_Alternatives,
   Lookup_Equality_Attempts,
   Lookup_Candidates_Returned,
   Lookup_Entries_Examined,
   Lookup_Comparisons,
   Lookup_Sort_Calls,
   Lookup_Specializations,
   Lookup_Whole_Registry_Scans,
   Index_Nodes,
   Index_Secondary_Insertions,
   Index_Whole_Family_Rebuilds,
   Planner_Requests,
   Planner_Base_Child_Builds,
   Planner_Recursive_Node_Builds,
   Planner_Context_Lifts,
   Planner_Application_Frames,
   Planner_Swaps,
   Planner_Swap_Applications,
   Planner_Cancellations,
   Planner_Root_Rescans,
   Planner_Root_Rewrites,
   Planner_Tail_Copies,
   Proof_Cterms,
   Proof_Fresh_Nodes,
   Proof_Control_Nodes,
   Proof_Compositions,
   Proof_Results,
   Record_Preparations,
   Record_Index_Probes,
   Record_Rules_Selected,
   Record_Hierarchy_Scans,
   Record_Simpset_Builds,
   Fallback_Requests,
   Fallback_Crossings,
   Fallback_Whole_Term_Rewrites,
   Cache_Lookups,
   Cache_Hits,
   Cache_Misses,
   Cache_Insertions,
   Cache_Persistent_Events,
   Lifecycle_Registration_Attempts,
   Lifecycle_Semantic_Insertions,
   Lifecycle_Replays,
   Lifecycle_Conflicts,
   Lifecycle_Dispatcher_Insertions,
   Lifecycle_Duplicate_Dispatchers,
   Canonicalization_Requests,
   Canonicalization_Nodes,
   Canonicalization_Edges,
   Canonicalization_Individualizations,
   Canonicalization_Backtracks,
   Canonicalization_Serializations,
   Resource_Future_Joins,
   Resource_Reference_Drops,
   Resource_Full_GCs,
   Resource_Samples]

fun counter_name Callback_Invocations = "callback.invocations"
  | counter_name Callback_Some_Results = "callback.some_results"
  | counter_name Callback_None_Results = "callback.none_results"
  | counter_name Callback_Exceptions = "callback.exceptions"
  | counter_name Callback_Interrupts = "callback.interrupts"
  | counter_name Callback_Work_Units = "callback.work_units"
  | counter_name Lookup_Requests = "lookup.requests"
  | counter_name Lookup_Index_Probes = "lookup.index_probes"
  | counter_name Lookup_Prefix_Alternatives = "lookup.prefix_alternatives"
  | counter_name Lookup_Equality_Attempts = "lookup.equality_attempts"
  | counter_name Lookup_Candidates_Returned = "lookup.candidates_returned"
  | counter_name Lookup_Entries_Examined = "lookup.entries_examined"
  | counter_name Lookup_Comparisons = "lookup.comparisons"
  | counter_name Lookup_Sort_Calls = "lookup.sort_calls"
  | counter_name Lookup_Specializations = "lookup.specializations"
  | counter_name Lookup_Whole_Registry_Scans = "lookup.whole_registry_scans"
  | counter_name Index_Nodes = "index.nodes"
  | counter_name Index_Secondary_Insertions = "index.secondary_insertions"
  | counter_name Index_Whole_Family_Rebuilds = "index.whole_family_rebuilds"
  | counter_name Planner_Requests = "planner.requests"
  | counter_name Planner_Base_Child_Builds = "planner.base_child_builds"
  | counter_name Planner_Recursive_Node_Builds = "planner.recursive_node_builds"
  | counter_name Planner_Context_Lifts = "planner.context_lifts"
  | counter_name Planner_Application_Frames = "planner.application_frames"
  | counter_name Planner_Swaps = "planner.swaps"
  | counter_name Planner_Swap_Applications = "planner.swap_applications"
  | counter_name Planner_Cancellations = "planner.cancellations"
  | counter_name Planner_Root_Rescans = "planner.root_rescans"
  | counter_name Planner_Root_Rewrites = "planner.root_rewrites"
  | counter_name Planner_Tail_Copies = "planner.tail_copies"
  | counter_name Proof_Cterms = "proof.cterms"
  | counter_name Proof_Fresh_Nodes = "proof.fresh_nodes"
  | counter_name Proof_Control_Nodes = "proof.control_nodes"
  | counter_name Proof_Compositions = "proof.compositions"
  | counter_name Proof_Results = "proof.results"
  | counter_name Record_Preparations = "record.preparations"
  | counter_name Record_Index_Probes = "record.index_probes"
  | counter_name Record_Rules_Selected = "record.rules_selected"
  | counter_name Record_Hierarchy_Scans = "record.hierarchy_scans"
  | counter_name Record_Simpset_Builds = "record.simpset_builds"
  | counter_name Fallback_Requests = "fallback.requests"
  | counter_name Fallback_Crossings = "fallback.crossings"
  | counter_name Fallback_Whole_Term_Rewrites = "fallback.whole_term_rewrites"
  | counter_name Cache_Lookups = "cache.lookups"
  | counter_name Cache_Hits = "cache.hits"
  | counter_name Cache_Misses = "cache.misses"
  | counter_name Cache_Insertions = "cache.insertions"
  | counter_name Cache_Persistent_Events = "cache.persistent_events"
  | counter_name Lifecycle_Registration_Attempts = "lifecycle.registration_attempts"
  | counter_name Lifecycle_Semantic_Insertions = "lifecycle.semantic_insertions"
  | counter_name Lifecycle_Replays = "lifecycle.replays"
  | counter_name Lifecycle_Conflicts = "lifecycle.conflicts"
  | counter_name Lifecycle_Dispatcher_Insertions = "lifecycle.dispatcher_insertions"
  | counter_name Lifecycle_Duplicate_Dispatchers = "lifecycle.duplicate_dispatchers"
  | counter_name Canonicalization_Requests = "canonicalization.requests"
  | counter_name Canonicalization_Nodes = "canonicalization.nodes"
  | counter_name Canonicalization_Edges = "canonicalization.edges"
  | counter_name Canonicalization_Individualizations =
      "canonicalization.individualizations"
  | counter_name Canonicalization_Backtracks = "canonicalization.backtracks"
  | counter_name Canonicalization_Serializations = "canonicalization.serializations"
  | counter_name Resource_Future_Joins = "resource.future_joins"
  | counter_name Resource_Reference_Drops = "resource.reference_drops"
  | counter_name Resource_Full_GCs = "resource.full_gcs"
  | counter_name Resource_Samples = "resource.samples"

val all_resources =
  [Elapsed_Microseconds,
   Allocated_Bytes,
   Live_Bytes,
   Peak_Bytes,
   Resident_Bytes]

fun resource_name Elapsed_Microseconds = "elapsed_microseconds"
  | resource_name Allocated_Bytes = "allocated_bytes"
  | resource_name Live_Bytes = "live_bytes"
  | resource_name Peak_Bytes = "peak_bytes"
  | resource_name Resident_Bytes = "resident_bytes"

fun index_of what eq value values =
  let
    fun find _ [] = raise Fail ("Missing " ^ what ^ " in fixed vocabulary")
      | find i (x :: xs) = if eq (value, x) then i else find (i + 1) xs
  in find 0 values end

fun counter_index counter = index_of "counter" (op =) counter all_counters
fun resource_index resource = index_of "resource" (op =) resource all_resources

fun phase_name Open = "open"
  | phase_name Frozen = "frozen"

structure Run_Selection = Proof_Data
(
  type T = run_id
  fun init _ = disabled_run_id
)

(* The dynamic callback capability is scalar and exists only while an admitted
   callback is executing.  It cannot be recovered from a stale proof context. *)
val callback_run = Thread_Data.var (): run_id Thread_Data.var

(* Collector and snapshot payloads contain only fixed enums, integers, and
   bounded strings. *)
type run_state =
 {phase: phase,
  active_callbacks: int,
  async_leases: int,
  counters: IntInf.int Inttab.table,
  resources: IntInf.int Inttab.table,
  scenario_labels: scenario_label list}

type collector_state =
 {last_run_id: run_id,
  runs: run_state Inttab.table}

datatype snapshot = Snapshot of
 {run_id: run_id,
  phase: phase,
  active_callbacks: int,
  async_leases: int,
  counters: (counter * IntInf.int) list,
  resources: (resource * IntInf.int) list,
  scenario_labels: scenario_label list}

val collector =
  Synchronized.var "AutoLocality instrumentation collector"
    ({last_run_id = disabled_run_id, runs = Inttab.empty}: collector_state)

fun make_run_state phase active_callbacks async_leases counters resources scenario_labels :
    run_state =
  {phase = phase,
   active_callbacks = active_callbacks,
   async_leases = async_leases,
   counters = counters,
   resources = resources,
   scenario_labels = scenario_labels}

fun map_run run_id f ({last_run_id, runs}: collector_state) =
  {last_run_id = last_run_id,
   runs =
     (case Inttab.lookup runs run_id of
       NONE => runs
     | SOME run => Inttab.update (run_id, f run) runs)}

fun update_run run_id run ({last_run_id, runs}: collector_state) =
  {last_run_id = last_run_id,
   runs = Inttab.update (run_id, run) runs}

fun current_run_id ctxt = Run_Selection.get ctxt
fun disable_run ctxt = Run_Selection.put disabled_run_id ctxt
fun restore_run_selection source =
  Run_Selection.put (current_run_id source)

val max_scenario_labels = 32
val max_scenario_string_size = 256

fun check_scenario_string kind text =
  if size text > max_scenario_string_size then
    error ("AutoLocality instrumentation " ^ kind ^ " exceeds "
      ^ Int.toString max_scenario_string_size ^ " bytes")
  else if String.isSubstring YXML.X text orelse String.isSubstring YXML.Y text then
    error ("AutoLocality instrumentation " ^ kind ^ " contains YXML control bytes")
  else text

fun canonical_scenario_labels labels =
  let
    val _ =
      if length labels <= max_scenario_labels then ()
      else error ("AutoLocality instrumentation accepts at most "
        ^ Int.toString max_scenario_labels ^ " scenario labels")
    val labels' =
      labels
      |> map (fn (axis, value) =>
           (check_scenario_string "scenario axis" axis,
            check_scenario_string "scenario value" value))
      |> sort (prod_ord string_ord string_ord)
    fun check_unique [] = ()
      | check_unique [_] = ()
      | check_unique ((axis0, _) :: (entry1 as (axis1, _)) :: rest) =
          if axis0 = axis1 then
            error ("Duplicate AutoLocality instrumentation scenario axis " ^ quote axis0)
          else check_unique (entry1 :: rest)
    val _ = check_unique labels'
  in labels' end

fun next_run_id last_run_id =
  (case Int.maxInt of
    SOME max_int =>
      if last_run_id = max_int then
        error "AutoLocality instrumentation exhausted monotonically increasing run IDs"
      else last_run_id + 1
  | NONE => last_run_id + 1)

fun start_run_with_labels labels ctxt =
  let
    val scenario_labels = canonical_scenario_labels labels
    val run_id =
      Synchronized.change_result collector
        (fn {last_run_id, runs} =>
          let
            val run_id = next_run_id last_run_id
            val run =
              make_run_state Open 0 0 Inttab.empty Inttab.empty scenario_labels
          in
            (run_id,
             {last_run_id = run_id,
              runs = Inttab.update_new (run_id, run) runs})
          end)
  in (run_id, Run_Selection.put run_id ctxt) end

fun start_run ctxt = start_run_with_labels [] ctxt

fun phase_of run_id =
  Synchronized.value collector
  |> #runs
  |> (fn runs => Inttab.lookup runs run_id)
  |> Option.map #phase

fun active_callbacks_of run_id =
  Synchronized.value collector
  |> #runs
  |> (fn runs => Inttab.lookup runs run_id)
  |> Option.map #active_callbacks

fun async_leases_of run_id =
  Synchronized.value collector
  |> #runs
  |> (fn runs => Inttab.lookup runs run_id)
  |> Option.map #async_leases

fun await_frozen run_id =
  Synchronized.guarded_access collector
    (fn state as {runs, ...} =>
      (case Inttab.lookup runs run_id of
        NONE => SOME (false, state)
      | SOME {phase = Frozen, ...} => SOME (true, state)
      | SOME {phase = Open, ...} => NONE))

fun thread_has_run data run_id =
  (case Thread_Data.get data of
    SOME active_run_id => active_run_id = run_id
  | NONE => false)

fun state_allows_recording run_id
      ({phase, active_callbacks, ...}: run_state) =
  phase = Open orelse
  (thread_has_run callback_run run_id andalso active_callbacks > 0)

fun recording_available run_id =
  if run_id = disabled_run_id then false
  else
    (case Inttab.lookup (#runs (Synchronized.value collector)) run_id of
      SOME run => state_allows_recording run_id run
    | NONE => false)

fun add_value index amount values =
  if amount = 0 then values
  else Inttab.map_default (index, 0) (fn old => old + amount) values

fun check_nonnegative what amount =
  if amount < 0 then
    error ("AutoLocality instrumentation " ^ what ^ " must be nonnegative")
  else amount

fun callback_counter Callback_Invocations = true
  | callback_counter Callback_Some_Results = true
  | callback_counter Callback_None_Results = true
  | callback_counter Callback_Exceptions = true
  | callback_counter Callback_Interrupts = true
  | callback_counter Callback_Work_Units = true
  | callback_counter _ = false

fun check_explicit_counter counter =
  if callback_counter counter then
    error ("AutoLocality callback counter " ^ quote (counter_name counter)
      ^ " is owned by with_callback")
  else counter

fun add_counter_values deltas counters =
  fold (fn (counter, amount) =>
    add_value (counter_index counter) amount) deltas counters

fun set_resource_values values resources =
  fold (fn (resource, amount) =>
    Inttab.update (resource_index resource, amount)) values resources

fun record_counters ctxt make_deltas =
  let val run_id = current_run_id ctxt in
    if not (recording_available run_id) then ()
    else
      let
        val deltas =
          make_deltas ()
          |> map (fn (counter, amount) =>
               (check_explicit_counter counter,
                check_nonnegative "counter delta" amount))
      in
        Synchronized.change collector
          (fn state =>
            map_run run_id
              (fn run as
                  {phase, active_callbacks, async_leases, counters, resources,
                   scenario_labels} =>
                if state_allows_recording run_id run then
                  make_run_state phase active_callbacks async_leases
                    (add_counter_values deltas counters) resources scenario_labels
                else run)
              state)
      end
  end

fun record_counter ctxt counter amount =
  let val run_id = current_run_id ctxt in
    if run_id = disabled_run_id then ()
    else
      record_counters ctxt
        (fn () => [(counter, check_nonnegative "counter delta" amount)])
  end

fun set_resources ctxt make_values =
  let val run_id = current_run_id ctxt in
    if not (recording_available run_id) then ()
    else
      let
        val values =
          make_values ()
          |> map (fn (resource, amount) =>
               (resource, check_nonnegative "resource value" amount))
      in
        Synchronized.change collector
          (fn state =>
            map_run run_id
              (fn run as
                  {phase, active_callbacks, async_leases, counters, resources,
                   scenario_labels} =>
                if state_allows_recording run_id run then
                  make_run_state phase active_callbacks async_leases counters
                    (set_resource_values values resources) scenario_labels
                else run)
              state)
      end
  end

fun set_resource ctxt resource amount =
  let val run_id = current_run_id ctxt in
    if run_id = disabled_run_id then ()
    else
      set_resources ctxt
        (fn () => [(resource, check_nonnegative "resource value" amount)])
  end

fun admit_callback run_id =
  if run_id = disabled_run_id then false
  else
    Synchronized.change_result collector
      (fn state as {runs, ...} =>
        (case Inttab.lookup runs run_id of
          NONE => (false, state)
        | SOME
            {phase, active_callbacks, async_leases, counters, resources,
             scenario_labels} =>
            if phase = Open then
              (true,
               update_run run_id
                 (make_run_state phase (active_callbacks + 1) async_leases
                   counters resources scenario_labels)
                 state)
            else (false, state)))

fun callback_outcome_counter (Exn.Res (SOME _)) = Callback_Some_Results
  | callback_outcome_counter (Exn.Res NONE) = Callback_None_Results
  | callback_outcome_counter (Exn.Exn exn) =
      if Exn.is_interrupt exn then Callback_Interrupts
      else Callback_Exceptions

fun finish_callback run_id result make_work =
  let
    val work =
      (case Exn.capture0 make_work () of
        Exn.Res amount => if amount < 0 then 0 else amount
      | Exn.Exn _ => 0)
    val deltas =
      [(Callback_Invocations, 1),
       (callback_outcome_counter result, 1),
       (Callback_Work_Units, work)]
  in
    Synchronized.change collector
      (fn state =>
        map_run run_id
          (fn run as
              {phase, active_callbacks, async_leases, counters, resources,
               scenario_labels} =>
            if active_callbacks <= 0 then run
            else
              make_run_state phase (active_callbacks - 1) async_leases
                (add_counter_values deltas counters) resources scenario_labels)
          state)
  end

fun with_callback ctxt make_work callback =
  let val run_id = current_run_id ctxt in
    (* Keep the disabled path free of synchronized access, metadata forcing,
       result capture, and event construction. *)
    if run_id = disabled_run_id then callback ()
    else
      Thread_Attributes.uninterruptible_body
        (fn run =>
          if not (admit_callback run_id) then run callback ()
          else
            let
              val result =
                Exn.capture_body
                  (run (fn () =>
                    Thread_Data.setmp callback_run (SOME run_id) callback ()))
              val _ = finish_callback run_id result make_work
            in Exn.release result end)
  end

fun acquire_lease run_id =
  if run_id = disabled_run_id then false
  else
    Synchronized.change_result collector
      (fn state as {runs, ...} =>
        (case Inttab.lookup runs run_id of
          SOME
            {phase = Open, active_callbacks, async_leases, counters, resources,
             scenario_labels} =>
              (true,
               update_run run_id
                 (make_run_state Open active_callbacks (async_leases + 1)
                   counters resources scenario_labels)
                 state)
        | _ => (false, state)))

fun release_lease run_id =
  Synchronized.change collector
    (fn state =>
      map_run run_id
        (fn run as
            {phase, active_callbacks, async_leases, counters, resources,
             scenario_labels} =>
          if async_leases <= 0 then run
          else
            make_run_state phase active_callbacks (async_leases - 1)
              counters resources scenario_labels)
        state)

fun release_once released run_id =
  Thread_Attributes.uninterruptible_body
    (fn _ =>
      ignore
        (Exn.capture0
          (fn () =>
            if Synchronized.change_result released
                 (fn already_released => (not already_released, true))
            then release_lease run_id
            else ())
          ()))

fun fork_in_group name group interrupts body =
  (singleton o Future.forks)
    {name = name, group = SOME group, deps = [], pri = 0,
     interrupts = interrupts}
    body

fun fork_with_lease ctxt body =
  let
    val run_id = current_run_id ctxt
    fun fork_target target_ctxt =
      Context.setmp_generic_context (SOME (Context.Proof target_ctxt))
        (fn () => Future.fork (fn () => body target_ctxt)) ()
  in
    Thread_Attributes.uninterruptible_body
      (fn _ =>
        if run_id = disabled_run_id then fork_target ctxt
        else
          if not (acquire_lease run_id) then
            fork_target (disable_run ctxt)
          else
            let
              val released =
                Synchronized.var "AutoLocality instrumentation lease" false
              fun release () = release_once released run_id
              val future_result =
                Exn.capture_body
                  (fn () => fork_target ctxt)
            in
              (case future_result of
                Exn.Exn exn => (release (); Exn.reraise exn)
              | Exn.Res future =>
                  let
                    (* The separately rooted watcher is the sole normal release
                       owner.  It retains only the target handle, run_id, and
                       one local Boolean until the target has terminated. *)
                    fun cleanup_body () =
                      Isabelle_Thread.try_finally
                        (fn () => ignore (Future.join_result future))
                        release
                    val cleanup_result =
                      Exn.capture_body
                        (fn () =>
                          Context.setmp_generic_context NONE
                            (fn () =>
                              let val cleanup_group = Future.new_group NONE in
                                fork_in_group
                                  "AutoLocality instrumentation lease cleanup"
                                  cleanup_group false cleanup_body
                              end)
                            ())
                  in
                    (case cleanup_result of
                      Exn.Res _ => future
                    | Exn.Exn exn =>
                        (ignore (Exn.capture0 Future.cancel future);
                         Isabelle_Thread.try_finally
                           (fn () => ignore (Future.join_result future))
                           release;
                         Exn.reraise exn))
                  end)
            end)
  end

fun value_of values index =
  the_default 0 (Inttab.lookup values index)

fun sorted_counters counters =
  all_counters
  |> map (fn counter => (counter, value_of counters (counter_index counter)))
  |> sort (string_ord o apply2 (counter_name o fst))

fun sorted_resources resources =
  all_resources
  |> map (fn resource => (resource, value_of resources (resource_index resource)))
  |> sort (string_ord o apply2 (resource_name o fst))

fun make_snapshot run_id
      ({phase, active_callbacks, async_leases, counters, resources,
        scenario_labels}: run_state) =
  Snapshot
    {run_id = run_id,
     phase = phase,
     active_callbacks = active_callbacks,
     async_leases = async_leases,
     counters = sorted_counters counters,
     resources = sorted_resources resources,
     scenario_labels = scenario_labels}

fun close_run run_id =
  Synchronized.change_result collector
    (fn state as {runs, ...} =>
      (case Inttab.lookup runs run_id of
        NONE => (false, state)
      | SOME {phase = Frozen, ...} => (true, state)
      | SOME
          {phase = Open, active_callbacks, async_leases, counters, resources,
           scenario_labels} =>
            (true,
             update_run run_id
               (make_run_state Frozen active_callbacks async_leases
                 counters resources scenario_labels)
               state)))

fun freeze_run run_id =
  if run_id = disabled_run_id orelse not (close_run run_id) then NONE
  else
    Synchronized.guarded_access collector
      (fn state as {runs, ...} =>
        (case Inttab.lookup runs run_id of
          NONE => SOME (NONE, state)
        | SOME (run as
            {phase = Frozen, active_callbacks = 0, async_leases = 0, ...}) =>
              SOME (SOME (make_snapshot run_id run), state)
        | SOME _ => NONE))

fun drop_run run_id =
  if run_id = disabled_run_id then false
  else
    Synchronized.change_result collector
      (fn state as {last_run_id, runs} =>
        (case Inttab.lookup runs run_id of
          SOME {phase = Frozen, active_callbacks = 0, async_leases = 0, ...} =>
            (true,
             {last_run_id = last_run_id,
              runs = Inttab.delete run_id runs})
        | _ => (false, state)))

fun reset_run ctxt =
  let
    val run_id = current_run_id ctxt
    val _ =
      if run_id = disabled_run_id then ()
      else
        (case freeze_run run_id of
          NONE => ()
        | SOME _ => ignore (drop_run run_id))
  in start_run (disable_run ctxt) end

fun snapshot_run_id
      (Snapshot {run_id, ...}) = run_id

fun snapshot_phase
      (Snapshot {phase, ...}) = phase

fun snapshot_active_callbacks
      (Snapshot {active_callbacks, ...}) = active_callbacks

fun snapshot_async_leases
      (Snapshot {async_leases, ...}) = async_leases

fun snapshot_scenario_labels
      (Snapshot {scenario_labels, ...}) = scenario_labels

fun snapshot_counters
      (Snapshot {counters, ...}) = counters

fun snapshot_counter snapshot counter =
  snapshot_counters snapshot
  |> get_first (fn (counter', value) =>
       if counter = counter' then SOME value else NONE)
  |> the_default 0

fun snapshot_resources
      (Snapshot {resources, ...}) = resources

fun snapshot_resource snapshot resource =
  snapshot_resources snapshot
  |> get_first (fn (resource', value) =>
       if resource = resource' then SOME value else NONE)
  |> the_default 0

fun snapshot_xml snapshot =
  let
    fun counter_xml (counter, value) =
      XML.Elem
        (("counter",
          [("name", counter_name counter),
           ("value", IntInf.toString value)]), [])
    fun resource_xml (resource, value) =
      XML.Elem
        (("resource",
          [("name", resource_name resource),
           ("value", IntInf.toString value)]), [])
    fun scenario_xml (axis, value) =
      XML.Elem
        (("scenario_label",
          [("axis", axis),
           ("value", value)]), [])
  in
    XML.Elem
      (("autolocality_instrumentation_snapshot",
        [("active_callbacks", Int.toString (snapshot_active_callbacks snapshot)),
         ("async_leases", Int.toString (snapshot_async_leases snapshot)),
         ("phase", phase_name (snapshot_phase snapshot)),
         ("run_id", Int.toString (snapshot_run_id snapshot))]),
       [XML.Elem (("counters", []), map counter_xml (snapshot_counters snapshot)),
        XML.Elem (("resources", []), map resource_xml (snapshot_resources snapshot)),
        XML.Elem
          (("scenario_labels", []),
           map scenario_xml (snapshot_scenario_labels snapshot))])
  end

val snapshot_yxml = YXML.string_of o snapshot_xml

end
