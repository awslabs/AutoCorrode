(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_C1_Instrumentation
  imports Autogen.AutoLocality
begin
(*>*)

section\<open>AutoLocality instrumentation lifecycle smoke tests\<close>

ML\<open>
local

open AutoLocality_Instrumentation

exception Smoke_Exception

fun assert label condition =
  if condition then ()
  else error ("AutoLocality C1 instrumentation smoke test failed: " ^ label)

fun the_snapshot label result =
  (case result of
    SOME snapshot => snapshot
  | NONE => error ("AutoLocality C1 instrumentation missing snapshot: " ^ label))

fun latch name = Synchronized.var name false

fun signal barrier = Synchronized.change barrier (K true)

fun await barrier =
  Synchronized.guarded_access barrier
    (fn ready => if ready then SOME ((), ready) else NONE)

fun fork_thread name body =
  let
    val result = Synchronized.var name NONE
    val _ =
      Isabelle_Thread.fork (Isabelle_Thread.params name)
        (fn () =>
          Synchronized.change result
            (K (SOME (Exn.capture_body body))))
  in result end

fun join_thread result =
  Synchronized.guarded_access result
    (fn state =>
      (case state of
        NONE => NONE
      | SOME value => SOME (value, state)))
  |> Exn.release

fun strictly_increasing [] = true
  | strictly_increasing [_] = true
  | strictly_increasing (x :: y :: rest) =
      x < y andalso strictly_increasing (y :: rest)

fun finish_run label run_id =
  let
    val snapshot = the_snapshot label (freeze_run run_id)
    val _ = assert (label ^ ": frozen") (snapshot_phase snapshot = Frozen)
    val _ = assert (label ^ ": callbacks drained")
      (snapshot_active_callbacks snapshot = 0)
    val _ = assert (label ^ ": leases drained")
      (snapshot_async_leases snapshot = 0)
    val _ = assert (label ^ ": dropped") (drop_run run_id)
  in snapshot end

val base_context = \<^context>

val _ = assert "default run is disabled"
  (current_run_id base_context = disabled_run_id)

val (selection_run, selection_source) = start_run base_context
val rebuilt_context =
  Proof_Context.init_global (Proof_Context.theory_of base_context)
val restored_selection =
  restore_run_selection selection_source rebuilt_context
val restored_disabled =
  restore_run_selection base_context restored_selection
val _ = assert "active run selection restores onto a rebuilt context"
  (current_run_id restored_selection = selection_run)
val _ = assert "disabled run selection restores onto a rebuilt context"
  (current_run_id restored_disabled = disabled_run_id)
val _ = record_counter restored_selection Lookup_Requests 1
val selection_snapshot =
  finish_run "restored run selection" selection_run
val _ = assert "restored selection records against the original run"
  (snapshot_counter selection_snapshot Lookup_Requests = 1)

val disabled_work_forced = Unsynchronized.ref false
val disabled_counter_forced = Unsynchronized.ref false
val disabled_resource_forced = Unsynchronized.ref false
val disabled_result =
  with_callback base_context
    (fn () => (disabled_work_forced := true; 1))
    (fn () => SOME 7)
val _ =
  record_counters base_context
    (fn () => (disabled_counter_forced := true; [(Lookup_Requests, 1)]))
val _ =
  set_resources base_context
    (fn () => (disabled_resource_forced := true; [(Live_Bytes, 1)]))
val _ = assert "disabled callback result"
  (disabled_result = SOME 7)
val _ = assert "disabled callback does not force work"
  (not (! disabled_work_forced))
val _ = assert "disabled counters do not force payload"
  (not (! disabled_counter_forced))
val _ = assert "disabled resources do not force payload"
  (not (! disabled_resource_forced))

val (outcome_run, outcome_context) =
  start_run_with_labels
    [("provenance", "original"), ("position", "root")]
    base_context
val some_result =
  with_callback outcome_context (fn () => 2) (fn () => SOME 11)
val none_result =
  with_callback outcome_context (fn () => 3) (fn () => NONE)
val cleanup_result =
  with_callback outcome_context (fn () => raise Smoke_Exception)
    (fn () => SOME 13)
val exception_result =
  Exn.capture_body
    (fn () =>
      with_callback outcome_context (fn () => 5)
        (fn () => raise Smoke_Exception))
val interrupt_result =
  Exn.capture_body
    (fn () =>
      with_callback outcome_context (fn () => 7)
        Isabelle_Thread.raise_interrupt)
val outcome_snapshot =
  the_snapshot "callback outcomes" (freeze_run outcome_run)
val _ = assert "SOME result preserved" (some_result = SOME 11)
val _ = assert "NONE result preserved" (is_none none_result)
val _ = assert "cleanup failure does not replace callback result"
  (cleanup_result = SOME 13)
val _ = assert "ordinary exception preserved"
  (case exception_result of
    Exn.Exn Smoke_Exception => true
  | _ => false)
val _ = assert "interrupt preserved"
  (case interrupt_result of
    Exn.Exn Exn.Interrupt_Break => true
  | _ => false)
val _ = assert "callback count"
  (snapshot_counter outcome_snapshot Callback_Invocations = 5)
val _ = assert "SOME count"
  (snapshot_counter outcome_snapshot Callback_Some_Results = 2)
val _ = assert "NONE count"
  (snapshot_counter outcome_snapshot Callback_None_Results = 1)
val _ = assert "exception count"
  (snapshot_counter outcome_snapshot Callback_Exceptions = 1)
val _ = assert "interrupt count"
  (snapshot_counter outcome_snapshot Callback_Interrupts = 1)
val _ = assert "callback work"
  (snapshot_counter outcome_snapshot Callback_Work_Units = 17)
val _ = assert "future counters default to zero"
  (snapshot_counter outcome_snapshot Planner_Root_Rescans = 0 andalso
   snapshot_counter outcome_snapshot Cache_Persistent_Events = 0 andalso
   snapshot_counter outcome_snapshot Canonicalization_Backtracks = 0)
val _ = assert "outcome run drops" (drop_run outcome_run)

val (callback_race_run, callback_race_context) = start_run base_context
val callback_entered = latch "AutoLocality C1 callback entered"
val callback_release = latch "AutoLocality C1 callback release"
val frozen_work_forced = Unsynchronized.ref false
val callback_thread =
  fork_thread "AutoLocality C1 callback thread"
    (fn () =>
      with_callback callback_race_context (fn () => 1)
        (fn () =>
          (signal callback_entered;
           await callback_release;
           SOME ())))
val _ = await callback_entered
val callback_releaser =
  fork_thread "AutoLocality C1 callback releaser"
    (fn () =>
      Isabelle_Thread.try_finally
        (fn () =>
          let
            val _ = assert "callback race reaches Frozen"
              (await_frozen callback_race_run)
            val result =
              with_callback callback_race_context
                (fn () => (frozen_work_forced := true; 1))
                (fn () => SOME 19)
            val _ = assert "closed admission preserves callback result"
              (result = SOME 19)
          in
            assert "closed admission does not force work"
              (not (! frozen_work_forced))
          end)
        (fn () => signal callback_release))
val callback_race_snapshot =
  the_snapshot "freeze/callback race" (freeze_run callback_race_run)
val _ = join_thread callback_thread
val _ = join_thread callback_releaser
val _ = assert "freeze waited for active callback"
  (snapshot_counter callback_race_snapshot Callback_Invocations = 1)
val _ = assert "callback race drops" (drop_run callback_race_run)

val (lease_run, lease_context) = start_run base_context
val leased_callback_entered = latch "AutoLocality C1 leased callback entered"
val leased_body_release = latch "AutoLocality C1 leased body release"
val leased_work_forced = Unsynchronized.ref false
val leased_future =
  fork_with_lease lease_context
    (fn leased_context =>
      let
        val _ = assert "leased future sees Frozen" (await_frozen lease_run)
        val result =
          with_callback leased_context
            (fn () => (leased_work_forced := true; 9))
            (fn () => (signal leased_callback_entered; SOME 29))
        val _ = await leased_body_release
      in result end)
val lease_releaser =
  fork_thread "AutoLocality C1 lease releaser"
    (fn () =>
      Isabelle_Thread.try_finally
        (fn () =>
          (await leased_callback_entered;
           assert "lease remains active while body is blocked"
             (async_leases_of lease_run = SOME 1)))
        (fn () => signal leased_body_release))
val lease_freezer =
  fork_thread "AutoLocality C1 lease freezer"
    (fn () => freeze_run lease_run)
val leased_result = Future.join leased_future
val lease_snapshot =
  the_snapshot "blocked leased future" (join_thread lease_freezer)
val _ = join_thread lease_releaser
val _ = assert "leased callback after freeze preserves result"
  (leased_result = SOME 29)
val _ = assert "leased callback after freeze does not force work"
  (not (! leased_work_forced))
val _ = assert "leased callback after freeze is not admitted"
  (snapshot_counter lease_snapshot Callback_Invocations = 0 andalso
   snapshot_counter lease_snapshot Callback_Some_Results = 0 andalso
   snapshot_counter lease_snapshot Callback_None_Results = 0 andalso
   snapshot_counter lease_snapshot Callback_Exceptions = 0 andalso
   snapshot_counter lease_snapshot Callback_Interrupts = 0 andalso
   snapshot_counter lease_snapshot Callback_Work_Units = 0)
val _ = assert "blocked leased future drains"
  (snapshot_async_leases lease_snapshot = 0)
val _ = assert "lease run drops" (drop_run lease_run)

val (cancelled_lease_run, cancelled_lease_context) = start_run base_context
val cancelled_lease_entered = latch "AutoLocality C1 cancelled lease entered"
val cancelled_lease_block = latch "AutoLocality C1 cancelled lease block"
val cancelled_lease_future =
  fork_with_lease cancelled_lease_context
    (fn _ =>
      (signal cancelled_lease_entered;
       await cancelled_lease_block))
val cancelled_lease_canceller =
  fork_thread "AutoLocality C1 lease canceller"
    (fn () =>
      (await cancelled_lease_entered;
       Future.cancel cancelled_lease_future))
val cancelled_lease_result = Future.join_result cancelled_lease_future
val _ = join_thread cancelled_lease_canceller
val _ = assert "leased future cancellation is observable"
  (Exn.is_interrupt_exn cancelled_lease_result)
val cancelled_lease_snapshot =
  the_snapshot "cancelled leased future" (freeze_run cancelled_lease_run)
val _ = assert "cancelled leased future releases its lease"
  (snapshot_async_leases cancelled_lease_snapshot = 0)
val _ = assert "cancelled lease run drops" (drop_run cancelled_lease_run)

val (retry_run, retry_context) = start_run base_context
val retry_callback_entered = latch "AutoLocality C1 retry callback entered"
val retry_callback_release = latch "AutoLocality C1 retry callback release"
val retry_callback_thread =
  fork_thread "AutoLocality C1 retry callback"
    (fn () =>
      with_callback retry_context (fn () => 1)
        (fn () =>
          (signal retry_callback_entered;
           await retry_callback_release;
           SOME ())))
val _ = await retry_callback_entered
val interrupted_freeze =
  Future.fork (fn () => freeze_run retry_run)
val freeze_canceller =
  fork_thread "AutoLocality C1 freeze canceller"
    (fn () =>
      Isabelle_Thread.try_finally
        (fn () =>
          assert "interrupted freeze closed admission" (await_frozen retry_run))
        (fn () => Future.cancel interrupted_freeze))
val interrupted_freeze_result = Future.join_result interrupted_freeze
val _ = join_thread freeze_canceller
val _ = assert "freeze interruption is observable"
  (Exn.is_interrupt_exn interrupted_freeze_result)
val _ = assert "interrupted freeze remains Frozen"
  (phase_of retry_run = SOME Frozen)
val _ = signal retry_callback_release
val _ = join_thread retry_callback_thread
val retry_snapshot =
  the_snapshot "interrupted freeze retry" (freeze_run retry_run)
val _ = assert "freeze retry drains callback"
  (snapshot_counter retry_snapshot Callback_Invocations = 1)
val _ = assert "retry run drops" (drop_run retry_run)

val (stale_run, stale_context) = start_run base_context
val _ = finish_run "stale context setup" stale_run
val stale_work_forced = Unsynchronized.ref false
val stale_counter_forced = Unsynchronized.ref false
val stale_result =
  with_callback stale_context
    (fn () => (stale_work_forced := true; 1))
    (fn () => SOME 23)
val _ =
  record_counters stale_context
    (fn () => (stale_counter_forced := true; [(Lookup_Requests, 1)]))
val stale_future =
  fork_with_lease stale_context current_run_id
val _ = assert "stale callback remains functional"
  (stale_result = SOME 23)
val _ = assert "stale callback does not force work"
  (not (! stale_work_forced))
val _ = assert "stale counter payload is inert"
  (not (! stale_counter_forced))
val _ = assert "stale future context is disabled"
  (Future.join stale_future = disabled_run_id)
val _ = assert "stale freeze is inert" (is_none (freeze_run stale_run))
val _ = assert "stale drop is inert" (not (drop_run stale_run))

fun start_drop 0 ids = rev ids
  | start_drop n ids =
      let
        val (run_id, _) = start_run base_context
        val _ = finish_run "repeated start/drop" run_id
      in start_drop (n - 1) (run_id :: ids) end

val repeated_ids = start_drop 16 []
val _ = assert "run IDs are strictly monotonic"
  (strictly_increasing repeated_ids)
val _ = assert "run IDs are never reused"
  (length repeated_ids = length (distinct (op =) repeated_ids))

val (reset_source_run, reset_source_context) = start_run base_context
val (reset_run_id, reset_context) = reset_run reset_source_context
val _ = assert "reset allocates a fresh ID"
  (reset_run_id > reset_source_run andalso
   current_run_id reset_context = reset_run_id)
val _ = assert "reset physically removes its source run"
  (phase_of reset_source_run = NONE)
val _ = finish_run "reset target" reset_run_id

val (encoding_run, encoding_context) =
  start_run_with_labels [("zeta", "last"), ("alpha", "first")] base_context
val _ = record_counter encoding_context Lookup_Requests 3
val _ = record_counter encoding_context Planner_Requests 2
val _ = set_resource encoding_context Resident_Bytes 4096
val _ = set_resource encoding_context Elapsed_Microseconds 17
val encoding_snapshot =
  the_snapshot "deterministic encoding" (freeze_run encoding_run)
val encoding1 = snapshot_yxml encoding_snapshot
val encoding2 = snapshot_yxml encoding_snapshot
val counter_names = map (counter_name o fst) (snapshot_counters encoding_snapshot)
val resource_names = map (resource_name o fst) (snapshot_resources encoding_snapshot)
val _ = assert "scenario labels are sorted"
  (snapshot_scenario_labels encoding_snapshot =
    [("alpha", "first"), ("zeta", "last")])
val _ = assert "counter encoding order is sorted"
  (counter_names = sort_strings counter_names)
val _ = assert "resource encoding order is sorted"
  (resource_names = sort_strings resource_names)
val _ = assert "snapshot encoding is deterministic"
  (encoding1 = encoding2 andalso YXML.is_wellformed encoding1)
val _ = assert "snapshot carries all fixed counters"
  (length (snapshot_counters encoding_snapshot) = length all_counters)
val _ = assert "snapshot carries all fixed resources"
  (length (snapshot_resources encoding_snapshot) = length all_resources)
val _ = assert "encoding run drops" (drop_run encoding_run)

in

val _ = writeln "AutoLocality C1 instrumentation lifecycle smoke tests passed"

end
\<close>

(*<*)
end
(*>*)
