(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature CRUSH_TIME =
sig
  val TIME : Proof.context -> bool -> string -> tactic -> tactic
  val TIME' : Proof.context -> bool -> string -> (int -> tactic) -> (int -> tactic)

  val TIME_pos : Proof.context -> Position.T -> bool -> string -> logger -> tactic -> tactic
  val TIME_pos' : Proof.context -> Position.T -> bool -> string -> logger -> (int -> tactic) -> (int -> tactic)

  val TIME_CB : Proof.context -> Position.T -> bool -> string -> logger
    -> (thm -> thm option -> Timing.timing -> bool -> unit)
    -> tactic -> tactic
  val TIME_CB' : Proof.context -> Position.T -> bool -> string -> logger
    -> (thm -> thm option -> Timing.timing -> bool -> unit)
    -> (int -> tactic) -> (int -> tactic)

  type TimingReport = string * bool * Timing.timing
  val report : Proof.context -> TimingReport -> unit

  val time_method : logger -> string -> Position.T -> bool -> Method.method -> Method.method
  val time_seq : ('b -> 'a option -> Timing.timing -> bool -> unit) -> ('b -> 'a Seq.seq) -> 'b -> 'a Seq.seq

  val timing_enabled : bool Config.T
  val print_timings : bool Config.T
  val timing_threshold_us : int Config.T
  val hall_of_fame_size : int Config.T

  type TimingSummary
  type TimingStatistics
  val print_timing_summary : string -> TimingSummary -> unit
  val print_timing_statistics : Proof.context -> TimingStatistics -> unit

  val merge_statistics : TimingStatistics -> TimingStatistics -> TimingStatistics

  val get_stored_timing_statistics : Proof.context -> TimingStatistics

  val time_it : (unit -> 'a) -> (unit -> Timing.timing * 'a)
  val time_and_report : Proof.context -> string -> bool -> (unit -> 'a) -> 'a
  val time_it_with_status : (unit -> 'a) -> ('a -> bool) -> (unit -> (Timing.timing * bool) * 'a)
end;

structure Crush_Time: CRUSH_TIME =
struct
   val timing_enabled = Attrib.setup_config_bool @{binding "crush_timing_enabled"} (K false)
   val print_timings = Attrib.setup_config_bool @{binding "crush_print_timings"} (K false)
   val timing_threshold_us = Attrib.setup_config_int @{binding "crush_timing_threshold"} (K 2000)
   val hall_of_fame_size = Attrib.setup_config_int @{binding "crush_time_hall_of_fame"} (K 100)

   type TimingReport = string * bool * Timing.timing
   type IndividualStatistics = { successes: Timing.timing list, failures : Timing.timing list }
   type TimingStatistics = IndividualStatistics Symtab.table
   val timing_statistics_empty = Symtab.empty

   structure TimingData = Proof_Data (
     type T = {
       current_log: TimingStatistics Unsynchronized.ref option,
       stored_logs: TimingStatistics
       };
     val init = K {current_log = NONE,
                   stored_logs = timing_statistics_empty});

  fun merge_timing_lists tl0 tl1 = tl0 @ tl1

  val merge_success_stats = merge_timing_lists
  val merge_failure_stats = merge_timing_lists

  fun add_result_to_individual_statistics success timing {successes = s, failures = f} =
     if success then { successes = timing :: s, failures = f }
     else { successes = s, failures = timing :: f }

  val empty_individual_statistics = { successes = [], failures = [] }

  fun merge_individual_statistics { successes = s0, failures = f0 } { successes = s1, failures = f1 } =
     { successes = merge_success_stats s0 s1, failures = merge_failure_stats f0 f1 }

  fun add_report (t : TimingReport) =
      let val (name, success, timing) = t in
        (Symtab.default (name, empty_individual_statistics) #>
         Symtab.map_entry name (add_result_to_individual_statistics success timing))
       end

  fun int_list_0_to_n n =
      let fun core acc n = if n = 0 then acc else core ((n-1) :: acc) (n-1) in
        core [] n
      end

  type TimingSummary = { samples : int,
                         total_time : Time.time,
                         avg_time : Time.time,
                         median_time : Time.time,
                         percentiles : Time.time list }

  val timing_summary_empty = { samples = 0, total_time = Time.zeroTime, avg_time = Time.zeroTime, median_time = Time.zeroTime, percentiles = [] }

  val time_to_str = fn t => Time.fmt 6 t ^ "s"

  fun print_timing_summary (title : string) (t : TimingSummary) =
     let val timing_percentiles_str =
             fold (fn x => fn s => s ^ " " ^ (x |> time_to_str)) (t |> #percentiles) "" in (
     title |> tracing;
     "  * Number of time reports: " ^ (t |> #samples |> Int.toString) |> tracing;
     "  * " ^ "total "   ^ (t |> #total_time  |> time_to_str) ^ ", "
            ^ "average " ^ (t |> #avg_time    |> time_to_str) ^ ", "
            ^ "median "  ^ (t |> #median_time |> time_to_str) |> tracing;
     "  * Percentiles: " ^ timing_percentiles_str |> tracing
    ) end

    fun quicksort [] _ = []
          | quicksort (x :: xs) compare_le =
           let fun partition x ys compare_le =
                let fun core (left, right) [] = (left, right)
                      | core (left, right) (t :: ts) =
                         if compare_le (t, x) then
                           core (t :: left, right) ts
                         else
                           core (left, t :: right) ts in
                core ([],[]) ys end
               val (bot, top) = partition x xs compare_le in
           (quicksort bot compare_le) @ [x] @ (quicksort top compare_le)
      end

  fun make_timing_summary_core timings =
    let val num_timings = List.length timings in
    if num_timings = 0 then timing_summary_empty else let
        fun compare_elapsed (t0,t1) = Time.<= (#elapsed t0, #elapsed t1)
        val timings_sorted = quicksort timings compare_elapsed
        val total_time = fold (curry Time.+) (List.map #elapsed timings) Time.zeroTime
        val avgtime = (total_time |> Time.toMicroseconds) div num_timings |> Time.fromMicroseconds
        fun middle_entry ls = List.nth (ls, (List.length ls) div 2)
        fun percentiles xs num = let
           val len = List.length xs
           val nums = int_list_0_to_n num
           val idxs = List.map (fn i => (i * len) div num) nums in
             (List.map (fn idx => List.nth (xs, idx)) idxs) @ [List.last xs]
           end
        val percentile_granularity = 10
        val timing_percentiles = percentiles timings_sorted percentile_granularity
        val median_time = middle_entry timings_sorted in
             { samples = num_timings,
               total_time = total_time,
               avg_time = avgtime,
               median_time = median_time |> #elapsed,
               percentiles = List.map #elapsed timing_percentiles }
   end end

  type TimingSummaryToplevel = { name : string,
                          total_time_all : Time.time,
                          success_stats : TimingSummary,
                          failure_stats : TimingSummary }

  fun timing_summary_toplevel_comp ((t0,t1) : TimingSummaryToplevel * TimingSummaryToplevel): bool
     = Time.<= (t0 |> #total_time_all, t1 |> #total_time_all)

  fun make_timing_summary (name : string) (stats : IndividualStatistics) : TimingSummaryToplevel =
    let val success_stats = make_timing_summary_core (stats |> #successes)
        val failure_stats = make_timing_summary_core (stats |> #failures)
        val total = (success_stats |> #total_time) + (failure_stats |> #total_time) in
       { name = name,
         total_time_all = total,
         success_stats = success_stats,
         failure_stats = failure_stats }
     end

  fun print_timing_summary_toplevel (stats : TimingSummaryToplevel) =
     ("Timing statistics for: " ^ (stats |> #name) |> tracing;
      "- Total time: " ^ (stats |> #total_time_all |> time_to_str) |> tracing;
      print_timing_summary "- SUCCESSES" (stats |> #success_stats);
      print_timing_summary "- FAILURES"  (stats |> #failure_stats))

  fun print_time_list (ls : (string * Time.time * Time.time * Time.time) list) : unit =
    let fun print_time_list_entry (name, total_all, total_success, total_fail): unit =
           "- " ^ name ^ ": " ^ ( total_all |> time_to_str) ^
           " (" ^ (total_fail |> time_to_str) ^ " failing, " ^
           (total_success |> time_to_str) ^ " succeeding)" |> tracing in
      (List.map print_time_list_entry ls; ())
    end

  fun print_timing_statistics (ctxt : Proof.context) =
     let val num = Config.get ctxt hall_of_fame_size in
     fn (ts : TimingStatistics) =>
     let val stats = List.map (uncurry make_timing_summary) (Symtab.dest ts)
         val stats = quicksort stats timing_summary_toplevel_comp |> List.rev
         val top_time_sinks = List.map (fn s => (s |> #name,
                                                 s |> #total_time_all,
                                                 s |> #success_stats |> #total_time,
                                                 s |> #failure_stats |> #total_time)) stats
                              |> take num  in
     ("Top ten time sinks" |> tracing;
      print_time_list top_time_sinks;
      List.map print_timing_summary_toplevel stats; ()) end end

  val merge_statistics =
     Symtab.join (K (uncurry merge_individual_statistics)) |> curry

  fun map_current_log (f : TimingStatistics Unsynchronized.ref option ->
                           TimingStatistics Unsynchronized.ref option) =
     fn {current_log = cl, stored_logs = sl} =>  {current_log = f cl, stored_logs    = sl }

  fun map_stored_logs (f : TimingStatistics -> TimingStatistics) =
     fn {current_log = cl, stored_logs = sl} => {current_log = cl, stored_logs = f sl }

  fun print_timing (log : logger) (pos : Position.T) (msg, success, timing) =
    let val success_str = if success then "SUCCESS" else "FAIL" in
    ([Pretty.mark_str (Markup.properties (Position.properties_of pos) Markup.position, msg),
     Pretty.brk 1, Pretty.enclose "(" ")" (success_str |> Pretty.text), Pretty.brk 1,
     Pretty.str (Timing.message timing) ])
    |> Pretty.block |> log end

  fun filter_report (ctxt : Proof.context) =
     let val threshold = Time.fromMicroseconds (Config.get ctxt timing_threshold_us)
     in
        fn (_, _, t) : TimingReport => #elapsed t > threshold
     end

  fun time_it_with_status (f : unit -> 'a) (is_good: 'a -> bool) : unit -> (Timing.timing * bool) * 'a =
    (fn _ =>
      let val start = Timing.start ()
          val res = f ()
          val t = Timing.result start
      in
        ((t, is_good res), res)
      end)

  fun time_it (f : unit -> 'a) : unit -> Timing.timing * 'a =
     time_it_with_status f (K true) #> apfst fst

  val get_stored_timing_statistics = TimingData.get #> #stored_logs

  fun timelog_print (ctxt : Proof.context) =
     (get_stored_timing_statistics ctxt |> print_timing_statistics ctxt;
      ctxt)

  val timelog_start =
      (fn x => (
         if is_some x then x else SOME (Unsynchronized.ref Symtab.empty))
      )|> map_current_log |> TimingData.map

  val timelog_end = (fn {current_log = cl, stored_logs = sl} => (
     let val new_log_opt = cl |> Option.map Unsynchronized.!
         val sl_new = (case new_log_opt of
                        SOME new_log => merge_statistics new_log sl
                      | NONE => sl) in
       { current_log = NONE, stored_logs = sl_new }
     end)) |> TimingData.map

  val timelog_reset = K timing_statistics_empty |> map_stored_logs |> TimingData.map

  fun report_timing_in_context (ctxt : Proof.context) (p : Position.T) (log : logger) =
     let val filter_report = filter_report ctxt
         val print_timings = if Config.get ctxt print_timings then print_timing log p else K ()
     in fn (r : TimingReport) =>
     if filter_report r then (
       (print_timings r);
       let val ptr_opt = ctxt |> TimingData.get |> #current_log in
         case ptr_opt of
           SOME ptr => ptr := add_report r (Unsynchronized.! ptr )
         | NONE => ()
     end) else () end

  fun report (ctxt : Proof.context) = report_timing_in_context ctxt Position.none default_logger

  fun time_and_report (ctxt : Proof.context) (msg : string) (enabled : bool) (f : unit -> 'a) =
    if enabled then
      let
        val (time, result) = time_it f ()
        val _ = report ctxt (msg, true (* success *), time)
      in result end
    else
      f ()

  fun time_seq (cb : 'b -> 'a option -> Timing.timing -> bool -> unit) (s : 'b -> 'a Seq.seq): 'b -> 'a Seq.seq =
     fn b => Seq.make (fn _ =>
         let val ((timing, status), output) = time_it_with_status (fn _ => Seq.pull (s b)) is_some ()
             val _ = cb b (Option.map fst output) timing status in
         output end)

  fun time_method (log : logger) (msg: string) (p : Position.T) (force : bool) (method: Method.method) : Method.method =
    (fn thms => fn ctxt =>
       if force orelse Config.get (fst ctxt) timing_enabled then
         let fun cb _ _ timing success = (
              let val r = (msg, success, timing)
                  val _ = if force then print_timing log p r else () in
                report_timing_in_context (fst ctxt) p log r
              end) in
           time_seq cb (method thms) ctxt
         end
       else
         method thms ctxt
    )

  val TIME_CB : Proof.context -> Position.T -> bool -> string -> logger
    -> (thm -> thm option -> Timing.timing -> bool -> unit) -> tactic -> tactic =
    fn ctxt => fn p => let val report = report_timing_in_context ctxt p
                   val timing_enabled = Config.get ctxt timing_enabled in
    fn enabled => if not enabled then K (K (K I)) else fn msg => fn log => fn cb_user => fn t => fn thm =>
      let fun cb v out timing success = (cb_user v out timing success;
         if timing_enabled then report log (msg, success, timing) else ())
      in time_seq cb t thm end
    end

  val TIME : Proof.context -> bool -> string -> tactic -> tactic =
    fn ctxt => fn enabled =>
      if enabled andalso Config.get ctxt timing_enabled then
        fn msg => TIME_CB ctxt Position.none true msg default_logger
          (K (K (K (K ()))))
      else
        K I

  val TIME' : Proof.context -> bool -> string -> (int -> tactic) -> (int -> tactic) =
    fn ctxt => fn enabled =>
      if enabled andalso Config.get ctxt timing_enabled then
        fn msg => fn t => TIME_CB ctxt Position.none true msg default_logger
          (K (K (K (K ())))) o t
      else
        K I

  val TIME_pos : Proof.context -> Position.T -> bool -> string -> logger -> tactic -> tactic =
    fn ctxt => fn pos => fn enabled =>
      if enabled andalso Config.get ctxt timing_enabled then
        fn msg => fn log => TIME_CB ctxt pos true msg log
          (K (K (K (K ()))))
      else
        K (K I)

  val TIME_pos' : Proof.context -> Position.T -> bool -> string -> logger -> (int -> tactic) -> (int -> tactic) =
    fn ctxt => fn pos => fn enabled =>
      if enabled andalso Config.get ctxt timing_enabled then
        fn msg => fn log => fn t => TIME_CB ctxt pos true msg log
          (K (K (K (K ())))) o t
      else
        K (K I)

  fun TIME_CB' (ctxt: Proof.context) (pos: Position.T) (enabled: bool) :
       string
    -> logger
    -> (thm -> thm option -> Timing.timing -> bool -> unit)
    -> (int -> tactic)
    -> (int -> tactic) =
    if not enabled then K (K (K I)) else fn msg => fn log => fn user_cb => fn t =>
      TIME_CB ctxt pos true msg log user_cb o t

val timelog_start'' =
   (timelog_start #> (Config.put timing_enabled true))
   |> Proof.map_contexts #> Seq.single

fun timelog_end'' keep_timings_enabled =
   let val restore_timing =
     if keep_timings_enabled then I else Config.put timing_enabled false in
     (timelog_end #> restore_timing) |> Proof.map_contexts #> Seq.single
   end

val timelogs_reset' = timelog_reset |> Proof.map_contexts #> Seq.Result #> Seq.single
val timelogs_print' = timelog_print |> Proof.map_contexts #> Seq.Result #> Seq.single

val disable_print_timings' = Config.put timing_enabled false |> Proof.map_contexts #> Seq.Result #> Seq.single
val enable_print_timings' = Config.put timing_enabled true |> Proof.map_contexts #> Seq.Result #> Seq.single

val disable_timings' = Config.put timing_enabled false |> Proof.map_contexts #> Seq.Result #> Seq.single
val enable_timings' = Config.put timing_enabled true |> Proof.map_contexts #> Seq.Result #> Seq.single

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>show_timelogs\<close> "print timing report log"
    (Scan.succeed (timelogs_print' |> Toplevel.proofs))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>reset_timelogs\<close> "reset timing report log"
    (Scan.succeed (timelogs_reset' |> Toplevel.proofs))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>disable_print_timings\<close> "disable printing of time logs"
    (Scan.succeed (disable_print_timings' |> Toplevel.proofs))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>enable_print_timings\<close> "enable printing of time logs"
    (Scan.succeed (enable_print_timings' |> Toplevel.proofs))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>disable_timings\<close> "disable time logs"
    (Scan.succeed (disable_timings' |> Toplevel.proofs))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>enable_timings\<close> "enable time logs"
    (Scan.succeed (enable_timings' |> Toplevel.proofs))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply\<tau>\<close> "apply a method and create timing log for it"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs (fn ctxt =>
         let val m_seq = (Proof.apply m) #> Seq.filter_results
             val timings_enabled = Config.get (ctxt |> Proof.context_of) timing_enabled in
           (
                Seq.THEN (timelog_start'',
                Seq.THEN ((Seq.TRY m_seq), (* XXX Figure out how to retain the failure markup here *)
                          timelog_end'' timings_enabled))
           ) ctxt |> Seq.make_results
         end
    ))))


  local
    val time_parser_opt_force : bool parser = Scan.optional (Args.$$$ "force" >> K true) false
    val time_parser_opt_msg : string option parser = Scan.optional (Parse.string >> SOME) NONE
    val time_parser : (Proof.context -> Method.method) context_parser =
      Scan.lift (
         (time_parser_opt_force -- time_parser_opt_msg -- Parser.parse_method_with_name)
          >> (fn ((force, msg), (method_str, method)) => fn (ctxt : Proof.context) =>
                time_method default_logger (Option.getOpt (msg,method_str)) Position.none force (method ctxt))
      )
  in
    val _ = Theory.setup (Method.setup @{binding "time"} time_parser "")
  end

end;
