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
    val overlay_file = "overlay_instance(" ^ instance ^ ")"
    val pos = Position.none
    val thy = Toplevel.theory_of state
    val transitions = Outer_Syntax.parse_text thy (fn () => thy) pos text
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

val _ = register {name = "isar_explore", pri = Task_Queue.urgent_pri}
    (fn {state, args, writeln_result, instance, exec_id, ...} =>
      (case args of [isar_text] => isar_explore exec_id instance isar_text state
                                   |> (fn st => Pretty.string_of (Pretty.chunks (Toplevel.pretty_state st)))
                                   |> writeln_result
         | _ => raise (ERROR "Invalid number of arguments for isar_explore")))
\<close>

end
