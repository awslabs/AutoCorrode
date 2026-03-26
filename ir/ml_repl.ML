(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* ML REPL over TCP with PIDE-compatible message framing.

   Uses Message_Channel (the same component as isabelle_process.ML) to
   send output as length-prefixed, YXML-encoded messages — byte-identical
   to the PIDE protocol.  The only difference from a real PIDE session is
   the transport (TCP socket vs system channel) and the "done" message
   sent after each evaluation to signal completion.

   Output channels are wired exactly as in isabelle_process.ML via
   Unsynchronized.setmp on Private_Output.*_fn.

   Depends on: Tcp_Handler (tcp_handler.ML), Ir (ir.ML). *)

structure ML_Repl =
struct

(** Per-connection output routing **)

(* Routing table: maps connection group IDs to their message functions.
   Each TCP connection registers its group + Message_Channel.message here.
   Worker threads find their connection's channel by walking the group
   ancestry via Task_Queue.str_of_groups — the same technique previously
   used by is_server_context() for a single global. *)
val connection_messages :
    (int * (string -> Properties.T -> XML.body list -> unit)) list Synchronized.var =
  Synchronized.var "ML_Repl.connection_messages" [];

(* Find the message function for the current worker's connection.
   Walks the group chain: if any ancestor group has a registered entry
   in connection_messages, return its message function. *)
fun find_connection_message () =
  case Future.worker_group () of
    NONE => NONE
  | SOME group =>
      let
        val table = Synchronized.value connection_messages
        val gs = Task_Queue.str_of_groups group
        fun lookup [] = NONE
          | lookup ((gid, msg) :: rest) =
              if String.isSubstring (string_of_int gid) gs
              then SOME msg else lookup rest
      in lookup table end;

fun is_server_context () = is_some (find_connection_message ());


(** Lazy Private_Output wrapping **)

val wrapped : bool Synchronized.var = Synchronized.var "ML_Repl.wrapped" false;

fun install_wrappers () =
  Synchronized.change wrapped (fn already =>
    if already then true
    else
      let
        (* Build capture functions that delegate to the calling thread's
           connection message function via find_connection_message().
           These match isabelle_process.ML's message_context exactly. *)
        fun standard_message props name ss =
          if forall (fn s => s = "") ss then ()
          else
            case find_connection_message () of
              NONE => ()
            | SOME msg =>
                let val pos_props =
                      if exists Markup.position_property props then props
                      else props @ Position.properties_of (Position.thread_data ())
                in msg name pos_props [XML.blob ss] end;

        val serial_props = Markup.serial_properties o serial;

        fun cap_writeln ss =
          standard_message (serial_props ()) Markup.writelnN ss;
        fun cap_writeln_urgent ss =
          standard_message (serial_props () @ Markup.urgent_properties) Markup.writelnN ss;
        fun cap_state ss =
          standard_message (serial_props ()) Markup.stateN ss;
        fun cap_information ss =
          standard_message (serial_props ()) Markup.informationN ss;
        fun cap_tracing ss =
          standard_message (serial_props ()) Markup.tracingN ss;
        fun cap_warning ss =
          standard_message (serial_props ()) Markup.warningN ss;
        fun cap_legacy ss =
          standard_message (serial_props ()) Markup.legacyN ss;
        fun cap_error (i, ss) =
          standard_message (Markup.serial_properties i) Markup.errorN ss;
        fun cap_system ss =
          case find_connection_message () of
            NONE => ()
          | SOME msg => msg Markup.systemN [] [XML.blob ss];
        fun cap_status ss =
          standard_message [] Markup.statusN ss;
        fun cap_report ss =
          standard_message [] Markup.reportN ss;

        fun wrap cap (r : (string list -> unit) Unsynchronized.ref) =
          let val orig = !r
          in r := (fn ss => if is_server_context () then cap ss else orig ss) end;

        fun wrap_err cap (r : (serial * string list -> unit) Unsynchronized.ref) =
          let val orig = !r
          in r := (fn (i, ss) => if is_server_context () then cap (i, ss) else orig (i, ss)) end;
      in
        wrap cap_writeln Private_Output.writeln_fn;
        wrap cap_writeln_urgent Private_Output.writeln_urgent_fn;
        wrap cap_state Private_Output.state_fn;
        wrap cap_information Private_Output.information_fn;
        wrap cap_tracing Private_Output.tracing_fn;
        wrap cap_warning Private_Output.warning_fn;
        wrap cap_legacy Private_Output.legacy_fn;
        wrap cap_system Private_Output.system_message_fn;
        wrap cap_status Private_Output.status_fn;
        wrap cap_report Private_Output.report_fn;
        wrap_err cap_error Private_Output.error_message_fn;
        true
      end);


(** Server lifecycle **)

(* Priority for I/R futures: negative so that interactive jEdit work
   (which runs at pri >= 0) always takes precedence over REPL evaluation. *)
val ir_pri = ~1;

(* The top-level I/R group.  All connection groups are children of this.
   Stored in a Synchronized var so connection_serve can access it. *)
val ir_group_var : Future.group option Synchronized.var =
  Synchronized.var "ML_Repl.ir_group" NONE;


(** Per-connection handler **)

(* Evaluate a single ML command within a command sub-group.
   The sub-group is a child of conn_group, so worker threads spawned
   during eval will find the connection's message function via
   find_connection_message(). After eval, we join all pending tasks
   in the command group to ensure all output is flushed before "done". *)
fun eval_in_group conn_group message line =
  let
    val cmd_group = Future.new_group (SOME conn_group)

    val trimmed = #1 (Substring.splitr Char.isSpace (Substring.full line))
    val has_semi = Substring.isSuffix ";" trimmed

    val _ = if has_semi then ()
            else message Markup.errorN (Markup.serial_properties 0)
                   [XML.blob ["command must end with \";\""]]

    (* Auto-correct double backslashes in symbol escapes *)
    val line =
      if String.isSubstring ("\\\\" ^ "<") line
      then (message Markup.warningN (Markup.serial_properties 0)
              [XML.blob ["NOTE: double backslash auto-corrected in symbol escapes. Prefer ASCII symbols."]];
            let fun dedup [] = []
                  | dedup (#"\\" :: #"\\" :: #"<" :: cs) = #"\\" :: #"<" :: dedup cs
                  | dedup (c :: cs) = c :: dedup cs
            in String.implode (dedup (String.explode line)) end)
      else line

    fun do_eval () =
      if Substring.isEmpty trimmed orelse not has_semi
      then Exn.Res ()
      else Exn.capture (fn () =>
             ML_Compiler.eval (ML_Compiler.verbose true ML_Compiler.flags)
               Position.none (ML_Lex.tokenize line)) ()

    (* Fork eval into cmd_group so output routing works.
       Workers in cmd_group are descendants of conn_group, so
       find_connection_message() finds the right channel. *)
    val eval_future = (singleton o Future.forks)
      {name = "ir_eval", group = SOME cmd_group,
       deps = [], pri = ir_pri, interrupts = true}
      (fn () =>
        let val result = Print_Mode.with_modes [Print_Mode.PIDE] do_eval ()
        in case result of
              Exn.Res _ => ()
            | Exn.Exn exn =>
                message Markup.errorN (Markup.serial_properties 0)
                  [XML.blob [Runtime.exn_message exn]]
        end)

    (* Join the eval future. ML_Compiler.eval is synchronous and
       Toplevel.command_exception joins parallel proofs, so this
       suffices to ensure all output is flushed before "done". *)
    val _ = ignore (Future.join_result eval_future)
  in
    message "done" [] []
  end;

(* Per-connection handler registered as Tcp_Handler.connection_handler.
   Creates a persistent Message_Channel and group for the connection,
   registers in the routing table, runs a sequential read-eval loop,
   and cleans up on disconnect. *)
fun connection_serve in_stream out_stream =
  let
    val _ = install_wrappers ()
    val ir_group =
      case Synchronized.value ir_group_var of
        SOME g => g
      | NONE => error "ML_Repl.connection_serve: server not started"
    val conn_group = Future.new_group (SOME ir_group)
    val channel = Message_Channel.make out_stream
    val message = Message_Channel.message channel
    val gid = Task_Queue.group_id conn_group
    val _ = Synchronized.change connection_messages (cons (gid, message))
    fun loop () =
      case Byte_Message.read_line in_stream of
        NONE => ()
      | SOME line_bytes =>
          let val line = Bytes.content line_bytes
          in if line = "" then loop ()
             else (eval_in_group conn_group message line; loop ())
          end
  in
    loop ()
      handle OS.SysErr _ => ()
           | IO.Io _ => ();
    Synchronized.change connection_messages
      (filter (fn (g, _) => g <> gid));
    Message_Channel.shutdown channel
  end;


fun start port =
  if Tcp_Handler.is_running () then
    (Output.information ("IR_Repl: server already running");
     NONE)
  else
  let
    val (actual_port, _, accept_loop) = Tcp_Handler.start port
    val ir_group = Future.new_group NONE
    val _ = Synchronized.change ir_group_var (K (SOME ir_group))
    val _ = Synchronized.change Tcp_Handler.connection_handler
              (K (SOME connection_serve))
  in
    SOME (actual_port, (singleton o Future.forks)
      {name = "ml_repl_accept", group = SOME ir_group,
       deps = [], pri = ir_pri, interrupts = true}
      accept_loop)
  end;

fun stop () =
  (Tcp_Handler.stop ();
   Synchronized.change ir_group_var (K NONE);
   Synchronized.change connection_messages (K []));

end;

(* PIDE protocol command for starting I/R from jEdit *)

fun report_port port token =
  Output.protocol_message
    [Markup.function "IR_Repl.port",
     ("port", Value.print_int port),
     ("token", token),
     ("max_connections",
      Value.print_int (Synchronized.value Tcp_Handler.max_connections))] [];

val _ =
  Protocol_Command.define "IR_Repl.start"
    (fn args =>
      let
        val port =
          (case args of
            [] => 0
          | [p] => the_default 0 (Int.fromString p)
          | _ => error "IR_Repl.start: expected at most one argument (port)")
      in
        case ML_Repl.start port of
          SOME (actual_port, _) =>
            (case Tcp_Handler.token () of
              SOME pw => report_port actual_port pw
            | NONE => ();
             Output.writeln ("IR_Repl: started on port " ^ string_of_int actual_port))
        | NONE =>
            (case (Tcp_Handler.get_port (), Tcp_Handler.token ()) of
              (SOME p, SOME t) => report_port p t
            | (SOME p, NONE) => report_port p ""
            | _ => ();
             Output.writeln "IR_Repl: already running")
      end);

val _ =
  Protocol_Command.define "IR_Repl.stop"
    (fn _ =>
      (ML_Repl.stop ();
       Output.writeln "IR_Repl: stopped"));
