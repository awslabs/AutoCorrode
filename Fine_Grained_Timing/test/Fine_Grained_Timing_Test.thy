(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Fine_Grained_Timing_Test
  imports "Fine_Grained_Timing.Fine_Grained_Timing"
begin

ML \<open>
  val reports = 256
  val accumulator = Fine_Grained_Timing_Accumulator.create "concurrent timing test"
  val timing: Timing.timing = {
    elapsed = Time.fromMicroseconds 1,
    cpu = Time.zeroTime,
    gc = Time.zeroTime
    }
  val futures =
    map (fn _ =>
      Future.fork (fn () =>
        Fine_Grained_Timing_Accumulator.add accumulator ("test", true, timing)))
      (1 upto reports)
  val _ = List.app Future.join futures
  val actual =
    accumulator
    |> Fine_Grained_Timing_Accumulator.value
    |> Fine_Grained_Timing_Accumulator.total_samples
  val _ =
    if actual = reports then ()
    else error ("Lost concurrent timing reports: expected " ^
      Value.print_int reports ^ ", got " ^ Value.print_int actual)

  val first_samples =
    Synchronized.var "first timing test sink"
      ([]: (string * bool) list)
  val second_samples =
    Synchronized.var "second timing test sink"
      ([]: (string * bool) list)

  fun test_sink samples _ =
    SOME (fn {name, success, ...}: Fine_Grained_Timing.timing_result =>
      Synchronized.change samples (cons (name, success)))

  val sink_context =
    @{context}
    |> Fine_Grained_Timing.add_sink "test_first"
        (test_sink first_samples)
    |> Fine_Grained_Timing.add_sink "test_inactive" (K NONE)
    |> Fine_Grained_Timing.add_sink "test_second"
        (test_sink second_samples)

  val sink_result =
    Fine_Grained_Timing.time_and_report sink_context "fanout" true
      (fn () => 42)
  val failed_sink_result =
    Fine_Grained_Timing.time_seq sink_context "failed_fanout"
      (K Seq.empty) ()
    |> Seq.pull

  val _ =
    if sink_result = 42 andalso is_none failed_sink_result andalso
       Synchronized.value first_samples =
         [("failed_fanout", false), ("fanout", true)] andalso
       Synchronized.value second_samples =
         [("failed_fanout", false), ("fanout", true)]
    then ()
    else error "Timing sample was not delivered once to every active sink"

  val removed_context =
    Fine_Grained_Timing.remove_sink "test_first" sink_context
  val _ =
    Fine_Grained_Timing.time_and_report removed_context "after_remove" true
      (fn () => ())
  val _ =
    if Synchronized.value first_samples =
         [("failed_fanout", false), ("fanout", true)] andalso
       Synchronized.value second_samples =
         [("after_remove", true), ("failed_fanout", false),
          ("fanout", true)]
    then ()
    else error "Removing a timing sink changed the wrong destination"

  val inactive_runs = Synchronized.var "inactive timing test" 0
  val inactive_context =
    @{context}
    |> Fine_Grained_Timing.add_sink "test_inactive_only" (K NONE)

  val inactive_result =
    Fine_Grained_Timing.time_and_report inactive_context "inactive" true
      (fn () =>
        (Synchronized.change inactive_runs (fn count => count + 1);
         "result"))

  val _ =
    if inactive_result = "result" andalso
       Synchronized.value inactive_runs = 1
    then ()
    else error "Timing without an active sink changed the wrapped operation"

  val profile_context =
    Config.put Fine_Grained_Timing.enabled true @{context}
  val profile_result =
    Fine_Grained_Timing.profile_seq (K true) "generic_profile" profile_context
      (fn ctxt => Seq.single (Fine_Grained_Timing.active ctxt))
    |> Seq.pull

  val _ =
    (case profile_result of
      SOME (true, _) => ()
    | _ => error "Generic profile did not install its accumulator context")
  val _ =
    if Fine_Grained_Timing.active profile_context then
      error "Generic profile changed its input context"
    else ()

  (* A profile reports again on every pull that added samples, so the wrapper
     around the tail must leave the sequence fully enumerable, and nested
     samples must keep reaching the accumulator while the caller backtracks. *)
  val backtrack_samples =
    Synchronized.var "backtracking timing test sink" ([]: string list)
  val backtrack_context =
    profile_context
    |> Fine_Grained_Timing.add_sink "test_backtrack"
        (fn _ =>
          SOME (fn {name, ...}: Fine_Grained_Timing.timing_result =>
            Synchronized.change backtrack_samples (cons name)))
  val backtrack_result =
    Fine_Grained_Timing.profile_seq (K true) "backtracking" backtrack_context
      (fn ctxt =>
        Seq.of_list [1, 2, 3]
        |> Seq.map (fn n =>
            Fine_Grained_Timing.time_and_report ctxt "element" true
              (fn () => n)))
    |> Seq.list_of

  val _ =
    if backtrack_result = [1, 2, 3] then ()
    else error "Profiling a sequence changed the elements it yields"
  val _ =
    let val collected = length (Synchronized.value backtrack_samples)
    in
      if collected = 3 then ()
      else error ("Backtracking past the first result lost nested samples: \
        \expected 3, got " ^ Value.print_int collected)
    end

  (* Samples gathered while backtracking are worthless unless they are also
     reported. Each pull that adds samples must emit a fresh snapshot, and
     every snapshot of one invocation must carry the same id. *)
  val observed_reports =
    Synchronized.var "profile report observer" ([]: Properties.T list)
  val observing_context =
    profile_context
    |> Config.put Fine_Grained_Timing.timing_threshold_us 0
    |> Fine_Grained_Timing.set_report_observer
        (fn _ => fn properties => fn _ =>
          Synchronized.change observed_reports (cons properties))
  val _ =
    Fine_Grained_Timing.profile_seq (K true) "observed" observing_context
      (fn ctxt =>
        Seq.of_list [1, 2, 3]
        |> Seq.map (fn n =>
            Fine_Grained_Timing.time_and_report ctxt "element" true
              (fn () =>
                (* Sleep so the sample clears the reporting threshold; a pure
                   computation can measure as zero elapsed time. *)
                (OS.Process.sleep (Time.fromMilliseconds 1); n))))
    |> Seq.list_of

  val _ =
    let
      val reported = Synchronized.value observed_reports
      val invocations =
        distinct (op =)
          (map_filter (fn properties =>
            Properties.get properties "invocation") reported)
    in
      if length reported < 3 then
        error ("A profile stopped reporting while the caller backtracked: \
          \expected at least 3 reports, got " ^
          Value.print_int (length reported))
      else if length invocations <> 1 then
        error ("Reports of one invocation disagreed on its id: " ^
          commas_quote invocations)
      else ()
    end

  (* An error result can be followed by a successful result without adding a
     timing sample. The changed outcome still needs a new snapshot. *)
  val outcome_reports =
    Synchronized.var "profile outcome observer" ([]: Properties.T list)
  val outcome_context =
    profile_context
    |> Fine_Grained_Timing.set_report_observer
        (fn _ => fn properties => fn _ =>
          Synchronized.change outcome_reports (cons properties))
  val outcome_result =
    Fine_Grained_Timing.profile_seq I "outcome" outcome_context
      (fn _ => Seq.of_list [false, true])
    |> Seq.list_of
  val _ =
    if outcome_result = [false, true] then ()
    else error "Profiling changed an outcome test sequence"
  val _ =
    let
      val reported = Synchronized.value outcome_reports
    in
      if length reported < 2 then
        error "An outcome change did not emit a second profile snapshot"
      else if
        Properties.get (hd reported) "success" = SOME "true" andalso
        is_some (Properties.get (hd reported) "elapsed_us") andalso
        exists
          (fn properties =>
            Properties.get properties "success" = SOME "false")
          (tl reported)
      then ()
      else error "Profile snapshots did not preserve the latest outcome"
    end

  (* Pulls without nested samples still contribute to the invocation total.
     They must publish a newer snapshot when the outcome is unchanged. *)
  val timing_reports =
    Synchronized.var "profile timing observer" ([]: Properties.T list)
  val timing_context =
    profile_context
    |> Fine_Grained_Timing.set_report_observer
        (fn _ => fn properties => fn _ =>
          Synchronized.change timing_reports (cons properties))
  fun delayed_sequence [] =
        Seq.make (fn _ =>
          (OS.Process.sleep (Time.fromMilliseconds 2); NONE))
    | delayed_sequence (value :: values) =
        Seq.make (fn _ =>
          (OS.Process.sleep (Time.fromMilliseconds 2);
           SOME (value, delayed_sequence values)))
  val timing_result =
    Fine_Grained_Timing.profile_seq (K true) "timing_only" timing_context
      (fn _ => delayed_sequence [1, 2])
    |> Seq.list_of
  val _ =
    if timing_result = [1, 2] then ()
    else error "Profiling changed a timing-only sequence"
  val _ =
    (case Synchronized.value timing_reports of
      latest :: earlier :: _ =>
        let
          val latest_elapsed =
            the_default 0
              (Properties.get latest "elapsed_us"
                |> Option.map Value.parse_int)
          val earlier_elapsed =
            the_default 0
              (Properties.get earlier "elapsed_us"
                |> Option.map Value.parse_int)
        in
          if latest_elapsed > earlier_elapsed then ()
          else error "A timing-only pull did not publish a newer snapshot"
        end
    | _ => error "Timing-only pulls did not emit repeated snapshots")

  (* Exceptions raised while pulling a profiled sequence must still publish
     the samples gathered before the exception, then escape unchanged. *)
  val raising_reports =
    Synchronized.var "profile exception observer" ([]: Properties.T list)
  val raising_context =
    profile_context
    |> Config.put Fine_Grained_Timing.timing_threshold_us 0
    |> Fine_Grained_Timing.set_report_observer
        (fn _ => fn properties => fn _ =>
          Synchronized.change raising_reports (cons properties))
  val raising_result =
    Exn.capture (fn () =>
      Fine_Grained_Timing.profile_seq (K true) "raising" raising_context
        (fn ctxt =>
          Seq.make (fn _ =>
            (Fine_Grained_Timing.time_and_report
               ctxt "before_raise" true (fn () => ());
             error "profile test exception")))
      |> Seq.pull) ()
  val _ =
    (case raising_result of
      Exn.Exn _ => ()
    | Exn.Res _ => error "Profiling swallowed a pull exception")
  val _ =
    (case Synchronized.value raising_reports of
      properties :: _ =>
        if Properties.get properties "success" = SOME "false" then ()
        else error "An exception report was not marked as failed"
    | [] => error "Profiling did not report a pull exception")

  (* `profile_method` distinguishes a failing method from one that yields no
     result at all, so the outcome predicate must see `Seq.Error`. *)
  val error_result =
    Fine_Grained_Timing.profile_seq
      (fn Seq.Result _ => true | Seq.Error _ => false)
      "error_profile" profile_context
      (fn _ => Seq.single (Seq.Error (fn () => "failed")))
    |> Seq.pull
  val _ =
    (case error_result of
      SOME (Seq.Error _, _) => ()
    | _ => error "Profiling dropped or rewrote a Seq.Error result")
\<close>

method_setup assert_no_fine_grained_profile =
  \<open>Scan.succeed (fn ctxt =>
    if Fine_Grained_Timing.active ctxt then Method.fail
    else Method.succeed)\<close>

lemma standalone_time_is_transparent:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (time "standalone_time" \<open>rule A\<close>)

lemma disabled_profile_is_transparent:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (profile "disabled_profile" \<open>rule A\<close>)

declare [[fine_grained_timing = true, fine_grained_timing_threshold = -1]]

lemma standalone_time_with_timing_enabled_is_transparent:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (time "standalone_time_enabled" \<open>rule A\<close>)

declare [[fine_grained_timing_output = true]]

lemma standalone_time_can_report_to_output:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (time "output_sample" \<open>rule A\<close>)

declare [[fine_grained_timing_output = false]]

lemma profile_without_inner_samples:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (profile "outer_only" \<open>rule A\<close>)

lemma profile_with_successful_sample:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (profile "nested_success"
      \<open>time "successful_sample" \<open>rule A\<close>\<close>)

lemma profile_with_failed_sample:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (profile "nested_failure"
      \<open>(time "failed_sample" \<open>fail\<close>) | rule A\<close>)

lemma nested_profiles_use_the_innermost_accumulator:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by (profile "nested_outer"
      \<open>time "outer_before" \<open>succeed\<close>,
       profile "nested_inner" \<open>time "inner_sample" \<open>succeed\<close>\<close>,
       time "outer_after" \<open>rule A\<close>\<close>)

lemma failed_profile_preserves_backtracking:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  by ((profile "failed_profile" \<open>fail\<close>) | rule A)

lemma profile_accumulator_does_not_escape:
  assumes A: \<open>PROP P\<close>
    shows \<open>PROP P\<close>
  apply (profile "context_scope" \<open>succeed\<close>)
  apply assert_no_fine_grained_profile
  apply (rule A)
  done

end
