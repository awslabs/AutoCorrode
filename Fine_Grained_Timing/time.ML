(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*
Fine-grained timing for custom tactics
======================================

This file has three jobs:

  1. measure named operations only when at least one sink wants the sample;
  2. deliver each sample to all active sinks; and
  3. let `profile` bundle PIDE samples into invocation snapshots.

Sink factories are stored in the proof context. A factory receives the current
context and returns either an active callback or `NONE`. The two default
factories are:

  - the PIDE sink, active when `fine_grained_timing` is enabled and `profile`
    has pushed an accumulator into the context; and
  - the output sink, active when `fine_grained_timing_output` is enabled.

`time` resolves the factories before doing any measurement. With no callbacks,
it runs the wrapped operation unchanged. Otherwise it measures one lazy
sequence pull and sends the same result to every callback.

For example, output can be enabled without opening a PIDE profile:

  declare [[fine_grained_timing_output = true]]
  apply (time "normalization" ‹simp›)

A producer can add another destination in a derived context:

  fun file_sink ctxt =
    if my_option ctxt then
      SOME (fn {name, success, timing} => write_sample name success timing)
    else NONE

  val timed_ctxt =
    Fine_Grained_Timing.add_sink "file" file_sink ctxt

The factory, rather than the callback, receives the proof context. This lets a
sink inspect configuration once for each `time` wrapper. If the factory returns
`NONE`, that destination adds no measurement overhead beyond sink resolution.

`profile` pushes a fresh synchronized PIDE accumulator and measures each pull
of its wrapped sequence. The report header carries the accumulated invocation
time, while the body contains samples produced by nested `time` wrappers.
Lazy methods may emit updated snapshots when later pulls add samples or change
the invocation outcome.

Nested profiles push another accumulator. The PIDE sink writes only to the top
stack frame, so the inner samples are not counted again by the outer profile.
After the inner profile returns, later samples go to the outer frame.

Reports are complete snapshots, not increments. Consumers keep the newest
snapshot of each invocation instead of adding snapshots together.
*)

signature FINE_GRAINED_TIMING =
sig
  type logger = Pretty.T -> unit
  type timing_result = {
    name: string,
    success: bool,
    timing: Timing.timing
    }
  type sink = timing_result -> unit
  type sink_factory = Proof.context -> sink option

  val add_sink :
    string -> sink_factory -> Proof.context -> Proof.context
  val remove_sink :
    string -> Proof.context -> Proof.context

  (* Time a tactic and record the result under the supplied sample name.
     The boolean is a cheap producer-side switch: false runs the tactic
     unchanged. The primed form decorates an int-indexed tactic. *)
  val TIME : Proof.context -> bool -> string -> tactic -> tactic
  val TIME' : Proof.context -> bool -> string -> (int -> tactic) -> (int -> tactic)

  (* Compatibility variants for callers that already carry positions,
     loggers, or a callback. The extra arguments remain useful to existing
     tactic instrumentation. *)
  val TIME_pos : Proof.context -> Position.T -> bool -> string -> logger -> tactic -> tactic
  val TIME_pos' : Proof.context -> Position.T -> bool -> string -> logger
    -> (int -> tactic) -> (int -> tactic)

  val TIME_CB : Proof.context -> Position.T -> bool -> string -> logger
    -> (thm -> thm option -> Timing.timing -> bool -> unit)
    -> tactic -> tactic
  val TIME_CB' : Proof.context -> Position.T -> bool -> string -> logger
    -> (thm -> thm option -> Timing.timing -> bool -> unit)
    -> (int -> tactic) -> (int -> tactic)

  val report : Proof.context -> timing_result -> unit

  (* `measure_seq` always measures one lazy pull and invokes its callback.
     `time_seq` first resolves the context sinks and remains transparent when
     none are active. *)
  val measure_seq : ('b -> 'a option -> Timing.timing -> bool -> unit)
    -> ('b -> 'a Seq.seq) -> 'b -> 'a Seq.seq
  val time_seq :
    Proof.context -> string -> ('b -> 'a Seq.seq) -> 'b -> 'a Seq.seq
  val time_method :
    string -> (Proof.context -> Method.method) -> Method.method

  val enabled : bool Config.T
  val output_enabled : bool Config.T
  val timing_threshold_us : int Config.T
  val active : Proof.context -> bool

  (* Divert invocation reports away from PIDE markup, for tests. *)
  val set_report_observer :
    (Position.T -> Properties.T -> string -> unit)
    -> Proof.context -> Proof.context

  val time_it : (unit -> 'a) -> (unit -> Timing.timing * 'a)
  val time_and_report : Proof.context -> string -> bool -> (unit -> 'a) -> 'a
  val time_it_with_status : (unit -> 'a) -> ('a -> bool)
    -> (unit -> (Timing.timing * bool) * 'a)

  (* Create one PIDE aggregation boundary around an arbitrary lazy sequence.
     The string is the invocation label shown in the report header. The
     predicate decides whether a pulled element counts as a successful
     outcome; element types that cannot carry failure use `K true`. *)
  val profile_seq : ('a -> bool)
    -> string -> Proof.context -> (Proof.context -> 'a Seq.seq) -> 'a Seq.seq

  val profile_tactic :
    string -> Proof.context -> (Proof.context -> tactic) -> tactic

  val profile_method :
    string -> (Proof.context -> Method.method) -> Method.method
end;

(*
The accumulator stores already-merged statistics, not raw samples.

For example, three successful "normalize" samples and two failed ones
produce two AggregateStatistics records under the same name. This split is
important for tactics: a branch that fails is often expected control flow,
but its cost still matters.

`Synchronized.var` makes updates safe when a tactic forks worker futures.
The outer tactic is expected to join its ordinary worker activity before
returning. Detached work is outside the invocation lifetime and must not
continue recording after the outer sequence has finished.
*)
structure Fine_Grained_Timing_Accumulator =
struct
  (* Histogram keys are floor(log2(elapsed microseconds)). Thus bucket 10
     represents samples whose elapsed time is around 2^10 microseconds.
     Fixed buckets are cheap to merge and allow the Scala side to estimate
     percentiles without retaining every sample. *)
  type AggregateStatistics = {
    samples: int,
    total_elapsed: Time.time,
    total_cpu: Time.time,
    total_gc: Time.time,
    min_elapsed: Time.time option,
    max_elapsed: Time.time option,
    histogram: int Inttab.table
    }

  type IndividualStatistics = {
    successes: AggregateStatistics,
    failures: AggregateStatistics
    }

  type Statistics = IndividualStatistics Symtab.table
  type T = Statistics Synchronized.var

  val aggregate_statistics_empty: AggregateStatistics = {
    samples = 0,
    total_elapsed = Time.zeroTime,
    total_cpu = Time.zeroTime,
    total_gc = Time.zeroTime,
    min_elapsed = NONE,
    max_elapsed = NONE,
    histogram = Inttab.empty
    }

  val individual_statistics_empty: IndividualStatistics = {
    successes = aggregate_statistics_empty,
    failures = aggregate_statistics_empty
    }

  fun create name = Synchronized.var name Symtab.empty

  (* Zero and one microsecond both land in bucket zero. Larger values use
     their integer base-2 logarithm. *)
  fun elapsed_bucket (timing: Timing.timing) =
    let
      fun log2 n acc =
        if n <= 1 then acc
        else log2 (n div 2) (acc + 1)
    in log2 (Time.toMicroseconds (#elapsed timing)) 0 end

  fun add_aggregate_timing (timing: Timing.timing) ({
      samples,
      total_elapsed,
      total_cpu,
      total_gc,
      min_elapsed,
      max_elapsed,
      histogram
      }: AggregateStatistics) =
    let
      val elapsed = #elapsed timing
      val min_elapsed' =
        (case min_elapsed of
          NONE => SOME elapsed
        | SOME t => SOME (if Time.< (elapsed, t) then elapsed else t))
      val max_elapsed' =
        (case max_elapsed of
          NONE => SOME elapsed
        | SOME t => SOME (if Time.< (t, elapsed) then elapsed else t))
      val histogram' =
        Inttab.map_default (elapsed_bucket timing, 0) (fn n => n + 1) histogram
    in
      {
        samples = samples + 1,
        total_elapsed = total_elapsed + elapsed,
        total_cpu = total_cpu + #cpu timing,
        total_gc = total_gc + #gc timing,
        min_elapsed = min_elapsed',
        max_elapsed = max_elapsed',
        histogram = histogram'
        }
    end

  fun add_report (name, success, timing: Timing.timing) =
    Symtab.map_default (name, individual_statistics_empty)
      (fn ({successes, failures}: IndividualStatistics) =>
        if success then
          {successes = add_aggregate_timing timing successes, failures = failures}
        else
          {successes = successes, failures = add_aggregate_timing timing failures})

  fun add accumulator timing_report =
    Synchronized.change accumulator (add_report timing_report)

  (* Reading is synchronized as well. Final PIDE encoding sees one complete
     snapshot of all updates that happened before this call. *)
  val value = Synchronized.value

  fun total_samples (statistics: Statistics) =
    Symtab.fold
      (fn (_, {successes, failures}: IndividualStatistics) =>
        fn total => total + #samples successes + #samples failures)
      statistics 0

  fun encode_time t = Value.print_int (Time.toMicroseconds t)

  (*
  Aggregate body format, shared by report schemas 1 and 2:

    <fine_grained_timing_entry
        name="normalize"
        success="true"
        count="3"
        elapsed_us="120"
        cpu_us="100"
        gc_us="0"
        min_elapsed_us="20"
        max_elapsed_us="60">
      <fine_grained_timing_bucket bucket="4" count="1"/>
      <fine_grained_timing_bucket bucket="5" count="2"/>
    </fine_grained_timing_entry>

  There is one entry for each (sample name, success) pair with a non-zero
  count. Times in an entry are totals except for the explicit minimum and
  maximum fields.
  *)
  fun encode_aggregate name success ({
      samples,
      total_elapsed,
      total_cpu,
      total_gc,
      min_elapsed,
      max_elapsed,
      histogram
      }: AggregateStatistics) =
    if samples = 0 then []
    else
      let
        val properties = [
          ("name", name),
          ("success", Bool.toString success),
          ("count", Value.print_int samples),
          ("elapsed_us", encode_time total_elapsed),
          ("cpu_us", encode_time total_cpu),
          ("gc_us", encode_time total_gc),
          ("min_elapsed_us", encode_time (the min_elapsed)),
          ("max_elapsed_us", encode_time (the max_elapsed))
          ]
        val buckets =
          Inttab.dest histogram
          |> map (fn (bucket, count) =>
              XML.Elem (("fine_grained_timing_bucket", [
                ("bucket", Value.print_int bucket),
                ("count", Value.print_int count)
                ]), []))
      in [XML.Elem (("fine_grained_timing_entry", properties), buckets)] end

  fun encode statistics =
    Symtab.dest statistics
    |> maps (fn (name, {successes, failures}: IndividualStatistics) =>
        encode_aggregate name true successes @
        encode_aggregate name false failures)
end;

(*
`Fine_Grained_Timing` is the producer-facing API. Invocation names and sample
names are opaque labels: the timing layer records and transports them without
assigning producer-specific meaning.
*)
structure Fine_Grained_Timing: FINE_GRAINED_TIMING =
struct
  type logger = Pretty.T -> unit
  type timing_result = {
    name: string,
    success: bool,
    timing: Timing.timing
    }
  type sink = timing_result -> unit
  type sink_factory = Proof.context -> sink option

  (* Registered components supply the system defaults. Importing only the
     session remains safe: an unknown option falls back to false. *)
  val enabled =
    Attrib.setup_config_bool @{binding "fine_grained_timing"}
      (fn _ =>
        Options.default_bool "fine_grained_timing"
          handle ERROR _ => false)

  val output_enabled =
    Attrib.setup_config_bool @{binding "fine_grained_timing_output"}
      (fn _ =>
        Options.default_bool "fine_grained_timing_output"
          handle ERROR _ => false)

  val timing_threshold_us =
    Attrib.setup_config_int @{binding "fine_grained_timing_threshold"} (K 2000)

  type pide_invocation = {
    id: int,
    invocation_name: string,
    position: Position.T,
    statistics: Fine_Grained_Timing_Accumulator.T,
    timing: Timing.timing Synchronized.var
    }

  (* The stack itself is immutable context data. Each entry is a fresh
     synchronized accumulator, so parallel commands cannot interfere and a
     nested profile can shadow its parent without clearing parent state. *)
  structure PIDE_Profiles = Proof_Data (
    type T = Fine_Grained_Timing_Accumulator.T list
    val init = K [])

  fun active ctxt = not (null (PIDE_Profiles.get ctxt))

  (* Report emission is context-local so that tests can observe it directly.
     `Context_Position.report_text` is silent whenever the context is
     invisible, as it is in a batch build, which would otherwise leave the
     report schedule untestable. *)
  structure Report_Observer = Proof_Data (
    type T = (Position.T -> Properties.T -> string -> unit) option
    val init = K NONE)

  fun set_report_observer observe = Report_Observer.put (SOME observe)

  (*
  PIDE report schema version 2:

    <fine_grained_timing
        version="2"
        invocation="42"
        method="my_tactic"
        success="false">
      ...encoded aggregate entries...
    </fine_grained_timing>

  The header carries the cumulative time spent pulling results from the
  profiled sequence. The aggregate entries describe named work recorded by
  nested `time` wrappers and may overlap with each other and with the outer
  timing.

  The aggregate entries are passed as YXML text because report markup has a
  text payload. The Scala decoder accepts this representation and the nested
  XML form used by tests. Position-attached markup follows PIDE document
  lifetime, so edited commands do not leave stale reports.
  *)
  fun encode_time time = Value.print_int (Time.toMicroseconds time)

  fun emit_pide_report ctxt
      ({id, invocation_name, position, statistics, timing}: pide_invocation)
      success =
    let
      val total = Synchronized.value timing
      val properties = [
        ("version", "2"),
        ("invocation", Value.print_int id),
        ("method", invocation_name),
        ("success", Bool.toString success),
        ("elapsed_us", encode_time (#elapsed total)),
        ("cpu_us", encode_time (#cpu total)),
        ("gc_us", encode_time (#gc total))
        ]
      val body = Fine_Grained_Timing_Accumulator.encode
        (Fine_Grained_Timing_Accumulator.value statistics)
      val text = YXML.string_of_body body
    in
      (case Report_Observer.get ctxt of
        SOME observe => observe position properties text
      | NONE =>
          Context_Position.report_text ctxt position
            ("fine_grained_timing", properties) text)
    end

  (* `timing_threshold_us` gates every sink, not just PIDE: it is the
     user-facing statement that samples below it are noise. Filtering in the
     PIDE sink alone would make `fine_grained_timing_output` trace every
     sub-microsecond sample. *)
  fun above_threshold ctxt ({timing, ...}: timing_result) =
    let val threshold = Time.fromMicroseconds (Config.get ctxt timing_threshold_us)
    in #elapsed timing > threshold end

  fun pide_sink_factory ctxt =
    if not (Config.get ctxt enabled) then NONE
    else
      (case PIDE_Profiles.get ctxt of
        [] => NONE
      | statistics :: _ =>
          SOME (fn result as {name, success, timing} =>
            if above_threshold ctxt result then
              Fine_Grained_Timing_Accumulator.add statistics
                (name, success, timing)
            else ()))

  fun output_sink_factory ctxt =
    if Config.get ctxt output_enabled then
      SOME (fn result as {name, success, timing} =>
        if above_threshold ctxt result then
          tracing ("fine-grained timing " ^ quote name ^ " " ^
            (if success then "success" else "failure") ^ ": " ^
            Timing.message timing)
        else ())
    else NONE

  structure Sink_Data = Proof_Data (
    type T = sink_factory Symtab.table
    val init = K (Symtab.make [
      ("pide", pide_sink_factory),
      ("output", output_sink_factory)
      ]))

  fun add_sink name factory =
    Sink_Data.map (Symtab.update (name, factory))

  fun remove_sink name =
    Sink_Data.map (Symtab.delete_safe name)

  fun resolve_sinks ctxt =
    Sink_Data.get ctxt
    |> Symtab.dest
    |> map_filter (fn (_, factory) => factory ctxt)

  fun dispatch sinks result =
    List.app (fn sink => sink result) sinks

  fun report ctxt result =
    dispatch (resolve_sinks ctxt) result

  fun time_it_with_status f is_good () =
    let
      val start = Timing.start ()
      val result = f ()
      val timing = Timing.result start
    in ((timing, is_good result), result) end

  fun time_it f =
    time_it_with_status f (K true) #> apfst fst

  fun add_timing (delta: Timing.timing) (total: Timing.timing) : Timing.timing =
    {
      elapsed = #elapsed total + #elapsed delta,
      cpu = #cpu total + #cpu delta,
      gc = #gc total + #gc delta
      }

  fun time_and_report ctxt name producer_enabled f =
    if not producer_enabled then f ()
    else
      (case resolve_sinks ctxt of
        [] => f ()
      | sinks =>
          let
            val (timing, result) = time_it f ()
            val _ = dispatch sinks {
              name = name,
              success = true,
              timing = timing
              }
          in result end)

  (*
  `measure_seq` is the unconditional low-level timing primitive retained for
  callers that need theorem-aware callbacks. `time_seq` is the sink-aware
  public operation: it resolves callbacks before constructing the wrapper and
  leaves the original sequence untouched when none are active.

  Both wrappers measure one pull only. A pull searches until the sequence
  yields its first result or is exhausted; the returned tail remains lazy and
  untouched.
  *)
  fun measure_seq callback sequence =
    fn input => Seq.make (fn _ =>
      let
        val ((timing, success), output) =
          time_it_with_status (fn _ => Seq.pull (sequence input)) is_some ()
        val _ = callback input (Option.map fst output) timing success
      in output end)

  fun time_seq ctxt name sequence input =
    (case resolve_sinks ctxt of
      [] => sequence input
    | sinks =>
        let
          fun callback _ _ timing success =
            dispatch sinks {
              name = name,
              success = success,
              timing = timing
              }
        in measure_seq callback sequence input end)

  fun time_method name make_method facts context =
    let
      val ctxt = fst context
      val method = make_method ctxt
    in time_seq ctxt name (method facts) context end

  fun TIME_CB ctxt _ producer_enabled name _ user_callback tactic theorem =
    if not producer_enabled then tactic theorem
    else
      let
        val sinks = resolve_sinks ctxt
        fun callback input output timing success =
          (user_callback input output timing success;
           dispatch sinks {
             name = name,
             success = success,
             timing = timing
             })
      in measure_seq callback tactic theorem end

  fun TIME ctxt producer_enabled name tactic =
    if producer_enabled then time_seq ctxt name tactic
    else tactic

  fun TIME' ctxt producer_enabled =
    if not producer_enabled then K I
    else fn msg => fn tactic => TIME ctxt true msg o tactic

  fun TIME_pos ctxt _ producer_enabled name _ =
    TIME ctxt producer_enabled name

  fun TIME_pos' ctxt position producer_enabled =
    if not producer_enabled then K (K I)
    else fn msg => fn logger => fn tactic =>
      TIME_pos ctxt position true msg logger o tactic

  fun TIME_CB' ctxt position producer_enabled =
    if not producer_enabled then K (K (K I))
    else fn msg => fn logger => fn user_callback => fn tactic =>
      TIME_CB ctxt position true msg logger user_callback o tactic

  (*
  `profile_seq` is independent of the sequence element type. It creates one
  PIDE stack frame and performs a plain pull. Nested `time` operations resolve
  the statically registered PIDE sink against that frame.
  *)
  fun profile_seq element_success invocation_name ctxt make_sequence =
    if not (Config.get ctxt enabled) then
      make_sequence ctxt
    else
      let
        val id = serial ()
        val statistics =
          Fine_Grained_Timing_Accumulator.create
            ("Fine-grained timing invocation " ^ Value.print_int id)
        val invocation_timing =
          Synchronized.var
            ("Fine-grained timing total " ^ Value.print_int id)
            Timing.zero
        val invocation = {
          id = id,
          invocation_name = invocation_name,
          position = Position.thread_data (),
          statistics = statistics,
          timing = invocation_timing
          }
        val profiles = PIDE_Profiles.get ctxt
        val ctxt' = PIDE_Profiles.put (statistics :: profiles) ctxt
        (*
        Every pull can contribute samples: the profiled method may backtrack,
        and nested `time` wrappers keep writing to `statistics` while it does.
        Reporting after the first pull only would discard everything a caller
        reaches by backtracking, so wrap the tail and report again whenever a
        pull actually added samples.

        Each report is a complete snapshot of the accumulator and all reports
        of one invocation share its id, so a consumer must keep the newest
        report per id rather than summing them. The outer timing changes even
        when no nested sample clears the threshold, so it is part of the
        snapshot state as well.
        *)
        fun timing_key ({elapsed, cpu, gc}: Timing.timing) =
          (Time.toMicroseconds elapsed,
           Time.toMicroseconds cpu,
           Time.toMicroseconds gc)
        fun report succeeded
              (reported_samples, reported_success, reported_timing) =
          let
            val samples =
              Fine_Grained_Timing_Accumulator.total_samples
                (Fine_Grained_Timing_Accumulator.value statistics)
            val current_timing =
              timing_key (Synchronized.value invocation_timing)
          in
            if samples = reported_samples andalso
                reported_success = SOME succeeded andalso
                reported_timing = SOME current_timing
            then (reported_samples, reported_success, reported_timing)
            else
              (emit_pide_report ctxt' invocation succeeded;
               (samples, SOME succeeded, SOME current_timing))
          end
        fun wrap succeeded reported make =
          Seq.make (fn _ =>
            let
              val start = Timing.start ()
              val pulled = Exn.capture (fn _ => Seq.pull (make ())) ()
              val pull_timing = Timing.result start
              val _ =
                Synchronized.change invocation_timing
                  (add_timing pull_timing)
            in
              case pulled of
                Exn.Exn exn =>
                  (report false reported;
                   Exn.reraise exn)
              | Exn.Res output =>
                  let
                    val succeeded' =
                      succeeded orelse
                        (case output of
                          NONE => false
                        | SOME (element, _) => element_success element)
                    val reported' = report succeeded' reported
                  in
                    Option.map
                      (fn (element, tail) =>
                        (element, wrap succeeded' reported' (fn _ => tail)))
                      output
                  end
            end)
      in wrap false (~1, NONE, NONE) (fn _ => make_sequence ctxt') end

  fun profile_tactic invocation_name ctxt make_tactic state =
    profile_seq (K true) invocation_name ctxt
      (fn ctxt' => make_tactic ctxt' state)

  (* Methods additionally return proof contexts. Restore the caller's profile
     stack in each result while preserving every unrelated context update. *)
  fun profile_method invocation_name make_method facts context =
    let
      val ctxt = fst context
      val profiles = PIDE_Profiles.get ctxt
    in
      profile_seq
        (fn Seq.Result _ => true | Seq.Error _ => false)
        invocation_name ctxt
        (fn ctxt' => make_method ctxt' facts (ctxt', snd context))
      |> Seq.map_result (fn (result_ctxt, result) =>
          (PIDE_Profiles.put profiles result_ctxt, result))
    end
end;

(*
The generic Isar wrappers expose the two levels of the timing model:

  apply (profile ‹time "normalization" ‹simp››)

`profile` creates and finalizes one invocation. Nested `time` methods add
named samples to its PIDE accumulator. A standalone `time` method still
serves the output sink or any custom sink; with no active sink it runs its
embedded method unchanged.

Both wrappers accept an optional string before the embedded method. For
`profile`, it names the invocation in the report header. For `time`, it names
the sample. Without a string, the embedded method text is used.
*)
local
  val parse_message =
    Scan.optional (Parse.string >> SOME) NONE
  val parse_method =
    Parse.embedded_input >>
      (fn source =>
        (Input.string_of source,
          fn ctxt =>
            Method.evaluate
              (Method.read_closure_input ctxt source |> fst) ctxt))
  val parser =
    Scan.lift (parse_message -- parse_method) >>
      (fn (message, (method_name, method)) =>
        (the_default method_name message, method))
in
  val _ = Theory.setup
    (Method.setup @{binding "profile"}
      (parser >> (fn (name, method) => fn _ =>
        Fine_Grained_Timing.profile_method name method))
      "profile a method and emit bundled fine-grained timing snapshots")

  val _ = Theory.setup
    (Method.setup @{binding "time"}
      (parser >> (fn (name, method) => fn _ =>
        Fine_Grained_Timing.time_method name method))
      "record one named sample for all active fine-grained timing sinks")
end;
