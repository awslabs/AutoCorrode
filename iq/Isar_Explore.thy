(* Original Copyright (c) 1986-2025,
            University of Cambridge,
            Technische Universitaet Muenchen,
            and contributors
   under the ISABELLE COPYRIGHT LICENSE

   Modifications Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *)

theory Isar_Explore
  imports Main
begin

(*
  The following is a near-copy of the `register` function in query_operation.ML.
  The main difference is that we pass on the exec_id and the instance name to the
  print function being registered.
*)

ML\<open>
fun register {name, pri} f =
  Command.print_function (name ^ "_query")
    (fn {args = instance :: args, exec_id, ...} =>
      SOME {delay = NONE, pri = pri, persistent = false, strict = false,
        print_fn = fn _ =>
              Thread_Attributes.uninterruptible
             (fn run => fn state =>
          let
            fun output_result s = Output.result [(Markup.instanceN, instance)] [s];
            val status = YXML.output_markup_only #> output_result;
            val writeln_result = Markup.markup Markup.writeln #> output_result
            val report_error = Markup.markup Markup.error #> output_result
            val report_exn = Runtime.exn_message #> report_error

            val _ = status Markup.running

            (* Small delay to ensure status is processed
               TODO: This should not be necessary...? *)
            val _ = OS.Process.sleep (Time.fromMilliseconds 100)
            fun main () =
              f {state = state, args = args, output_result = output_result,
                 writeln_result = writeln_result, instance=instance, exec_id=exec_id}
            val _ =
              (case Exn.capture_body (run main) of
                Exn.Res () => ()
              | Exn.Exn exn => report_exn exn)
            val _ = status Markup.finished
           in () end)}
    | _ => NONE);
\<close>

ML\<open>

(* Parse and run an Isar proof script on a proof state *)
fun isar_explore exec_id instance text state =
  let
    (*
       It appears that we have to use the provided execution ID to run the transition.
       This ID however seems stable across multiple overlays.

       In the rare case that the transition execution produces direct error output, we
       need to retain overlay specific position information _and_ avoid the output to be
       attributed to the parent command. We achieve this by using a dummy file name and
       encode the overlay instance ID in it.

       This is matched against in Extended_Query_Operation.scala.

       The only known case where this is needed is when transition execution forks off threads
       for the execution of `by ...` statements. We explicitly disable this one below with the
       thread-unsafe hack. With this, the dummy file assignment should not be necessary, but
       we leave it in just in case.
    *)
    val _ = instance (* suppress unused warning *)
    val pos = Position.none
    val thy = Toplevel.theory_of state
    (* Enable quick_and_dirty so that sorry is accepted in proof exploration *)
    val text' = "using [[quick_and_dirty]]\n" ^ text
    val transitions = Outer_Syntax.parse_text thy (fn () => thy) pos text'
      (* Without this, the execution fails with "Unregistered execution" *)
      |> List.map (Toplevel.exec_id exec_id)

    fun run_transition (tr, st) =
      let
         (* Disable highest level of parallel proof checking since this forks
            off threads for `by ...` statements which we have trouble capturing
            the output of (they capture their own exceptions and convert them
            directly into error_messages to Isabelle's output channel. *)
         val old_parallel_proofs = ! Multithreading.parallel_proofs
         val _ = Multithreading.parallel_proofs := Int.min(2, old_parallel_proofs)
         val st' = Toplevel.command_exception false tr st
         val _ = Multithreading.parallel_proofs := old_parallel_proofs
      in st' end
  in
    List.foldl (fn (tr, st) => run_transition (tr, st)) state transitions
  end;

(* Register `isar_explore` as a print function so it can be used as an overlay.
   This is the heart of enabling agents to try out alternative proofs without
   disrupting the users concurrent proof development. *)

(* Special handling for quickcheck - call it programmatically *)
fun run_quickcheck state =
  let
    val proof_state = Toplevel.proof_of state
    val ctxt = Proof.context_of proof_state
    val result = Quickcheck.quickcheck [] 1 proof_state
  in
    case result of
      NONE => "Quickcheck found no counterexample."
    | SOME (genuine, cex) =>
        let
          val formatted = Quickcheck.pretty_counterex ctxt false (SOME ((genuine, cex), []))
        in Pretty.string_of formatted end
  end
  handle ERROR msg => "Error: " ^ msg;

(* Get relevant facts using MePo relevance filter *)
fun run_print_context state =
  let
    val ctxt = Toplevel.context_of state

    (* Local facts (assumptions, etc.) *)
    val local_pretty = Proof_Context.pretty_local_facts true ctxt

    (* Try to get goal for MePo filtering *)
    val mepo_results =
      (case try Toplevel.proof_of state of
        SOME prf =>
          (case try Proof.goal prf of
            SOME {goal, ...} =>
              let
                val concl = Logic.strip_imp_concl (Thm.prop_of goal)
                val hyps = Logic.strip_imp_prems (Thm.prop_of goal)
                val facts = Sledgehammer_Fact.nearly_all_facts_of_context ctxt true
                  Sledgehammer_Fact.no_fact_override [] hyps concl
                val params = Sledgehammer_Commands.default_params \<^theory> []
                val relevant = Sledgehammer_MePo.mepo_suggested_facts ctxt params 20 NONE hyps concl facts
              in relevant end
            | NONE => [])
        | NONE => [])
      handle ERROR _ => []

    val mepo_pretty = if null mepo_results then []
      else [Pretty.big_list "Relevant theorems (MePo):"
        (map (fn ((name, _), _) => Pretty.str name) mepo_results)]

    val all_pretty = local_pretty @ mepo_pretty
    val result = if null all_pretty
      then "No facts in scope."
      else Pretty.string_of (Pretty.chunks all_pretty)
  in result end
  handle ERROR msg => "Error: " ^ msg;

(* Fetch definitions for a list of entity names (from PIDE markup) *)
fun get_defs state names =
  let
    val ctxt = Toplevel.context_of state

    (* Try to get definition for an entity name *)
    fun try_get_thms n =
      (SOME (Proof_Context.get_thms ctxt n)) handle ERROR _ => NONE

    fun get_def name =
      let val base = Long_Name.base_name name
      in
        (case try_get_thms (base ^ "_def") of
          SOME thms => SOME (name, thms)
        | NONE => (case try_get_thms (base ^ ".simps") of
            SOME thms => SOME (name, thms)
          | NONE => (case try_get_thms base of
              SOME thms => SOME (name, thms)
            | NONE => NONE)))
      end

    val defs = map_filter get_def names

    fun pretty_def (name, thms) = Pretty.block [
      Pretty.str (name ^ ":"),
      Pretty.brk 1,
      Pretty.chunks (map (Thm.pretty_thm ctxt) thms)
    ]
  in
    if null defs then "No additional context found."
    else Pretty.string_of (Pretty.big_list "Definitions:" (map pretty_def defs))
  end
  handle ERROR msg => "Error: " ^ msg;

(* Run simp with tracing, capturing trace output *)
fun run_simp_trace state method_name timeout_secs trace_depth =
  let
    val trace_output = Unsynchronized.ref ([] : string list)
    val old_tracing_fn = ! Private_Output.tracing_fn
    val _ = Private_Output.tracing_fn := (fn ss => trace_output := ss @ (! trace_output))

    val ctxt = Toplevel.context_of state
    val ctxt' = ctxt
      |> Config.put Raw_Simplifier.simp_trace true
      |> Config.put Raw_Simplifier.simp_trace_depth_limit trace_depth

    val prf = Toplevel.proof_of state
    val {goal, ...} = Proof.goal prf
    val goal_term = Thm.prop_of goal

    val result = Timeout.apply (Time.fromSeconds (Int.toLarge timeout_secs)) (fn () =>
      let
        val simplified = Simplifier.asm_full_rewrite ctxt' (Thm.cterm_of ctxt' goal_term)
        val result_term = Thm.rhs_of simplified
      in
        "SUCCEEDED:\n" ^ Syntax.string_of_term ctxt' (Thm.term_of result_term)
      end) ()
    handle Timeout.TIMEOUT _ => "TIMED_OUT: Method did not terminate within " ^ Int.toString timeout_secs ^ " seconds"
         | ERROR msg => "ERROR: " ^ msg

    val _ = Private_Output.tracing_fn := old_tracing_fn
    val trace = String.concatWith "\n" (rev (! trace_output))
  in
    "=== GOAL ===\n" ^ Syntax.string_of_term ctxt goal_term ^
    "\n\n=== RESULT ===\n" ^ result ^
    "\n\n=== TRACE ===\n" ^ (if trace = "" then "(no trace output)" else trace)
  end
  handle ERROR msg => "Error: " ^ msg;

val _ = register {name = "isar_explore", pri = Task_Queue.urgent_pri}
    (fn {state, args, writeln_result, instance, exec_id, ...} =>
      (case args of [isar_text] =>
        let
          val trimmed = Symbol.trim_blanks isar_text
          val result_text =
            if trimmed = "quickcheck" then
              run_quickcheck state
            else if trimmed = "print_context" then
              run_print_context state
            else if String.isPrefix "get_defs " trimmed then
              get_defs state (String.tokens (fn c => c = #" ") (String.extract (trimmed, 9, NONE)))
            else if String.isPrefix "simp_trace " trimmed then
              let val args = String.tokens (fn c => c = #" ") (String.extract (trimmed, 11, NONE))
                  val method = hd args handle Empty => "simp"
                  val timeout = the_default 5 (Int.fromString (nth args 1 handle Subscript => "5"))
                  val depth = the_default 10 (Int.fromString (nth args 2 handle Subscript => "10"))
              in run_simp_trace state method timeout depth end
            else
              let
                val st = isar_explore exec_id instance isar_text state
                val state_text = Pretty.string_of (Pretty.chunks (Toplevel.pretty_state st))
                val header =
                  if Toplevel.is_proof st then
                    let val {goal, ...} = Proof.goal (Toplevel.proof_of st)
                    in "PROOF_STATE " ^ Int.toString (Thm.nprems_of goal) end
                  else "PROOF_COMPLETE 0"
              in header ^ "\n" ^ state_text end
        in
          writeln_result result_text
        end
         | _ => raise (ERROR "Invalid number of arguments for isar_explore")))
\<close>

declare [[ML_write_global = true]]
ML_file\<open>../ir/ir.ML\<close>
ML_file\<open>../ir/tcp_handler.ML\<close>
ML_file\<open>../ir/ml_repl.ML\<close>
declare [[ML_write_global = false]]

end
