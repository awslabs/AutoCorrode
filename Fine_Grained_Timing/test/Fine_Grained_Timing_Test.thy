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
    Fine_Grained_Timing.profile_seq "generic_profile" profile_context
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
