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

(** Server group tracking **)

val server_group_id : int Synchronized.var =
  Synchronized.var "ML_Repl.server_group_id" 0;

fun is_server_context () =
  let val gid = Synchronized.value server_group_id
  in if gid = 0 then false
     else case Future.worker_group () of
            NONE => false
          | SOME group =>
              String.isSubstring (string_of_int gid)
                (Task_Queue.str_of_groups group)
  end;


(** Lazy Private_Output wrapping **)

val wrapped : bool Synchronized.var = Synchronized.var "ML_Repl.wrapped" false;

(* The current message function, set per-connection in eval_handler.
   Between connections this is a no-op.  We use a Synchronized var so
   that worker threads spawned during eval (e.g. by Thy_Info.use_theories)
   can find the active message channel. *)
val current_message :
      (string -> Properties.T -> XML.body list -> unit) Synchronized.var =
  Synchronized.var "ML_Repl.current_message" (fn _ => fn _ => fn _ => ());

fun install_wrappers () =
  Synchronized.change wrapped (fn already =>
    if already then true
    else
      let
        (* Build capture functions that delegate to current_message.
           These match isabelle_process.ML's message_context exactly. *)
        fun standard_message props name ss =
          if forall (fn s => s = "") ss then ()
          else
            let
              val msg = Synchronized.value current_message
              val pos_props =
                if exists Markup.position_property props then props
                else props @ Position.properties_of (Position.thread_data ());
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
          let val msg = Synchronized.value current_message
          in msg Markup.systemN [] [XML.blob ss] end;
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


(** Eval handler **)

fun eval_handler line out_stream =
  let
    val _ = install_wrappers ()

    (* Create a Message_Channel for this evaluation.  This gives us
       PIDE-identical framing and a dedicated writer thread. *)
    val channel = Message_Channel.make out_stream
    val message = Message_Channel.message channel

    (* Install as the active message function for worker threads. *)
    val _ = Synchronized.change current_message (K message)

    val trimmed = #1 (Substring.splitr Char.isSpace (Substring.full line))
    val has_semi = Substring.isSuffix ";" trimmed

    val _ = if has_semi then ()
            else message Markup.errorN (Markup.serial_properties 0)
                   [XML.blob ["command must end with \";\""]];

    (* Debug: hexdump of input line to /tmp/ml_repl_hexdump.log *)
    (* val _ = let val f = TextIO.openAppend "/tmp/ml_repl_hexdump.log" *)
    (*             fun hex c = let val n = Char.ord c *)
    (*                         in (if n < 16 then "0" else "") ^ Int.fmt StringCvt.HEX n end *)
    (*             fun go i = *)
    (*               if i >= size line then () *)
    (*               else let val chunk = String.substring (line, i, Int.min (16, size line - i)) *)
    (*                        val hexs = String.concatWith " " (map hex (String.explode chunk)) *)
    (*                        val ascii = String.implode (map (fn c => if Char.ord c >= 32 andalso Char.ord c < 127 then c else #".") (String.explode chunk)) *)
    (*                    in TextIO.output (f, hexs ^ "  " ^ ascii ^ "\n"); go (i + 16) end *)
    (*         in TextIO.output (f, "ML_Repl hexdump (" ^ string_of_int (size line) ^ " bytes):\n"); *)
    (*            go 0; TextIO.closeOut f end *)

    (* Auto-correct double backslashes: replace \\\\ with \\ and warn *)
    val line =
      if String.isSubstring "\\\\" line
      then (message Markup.warningN (Markup.serial_properties 0)
              [XML.blob ["NOTE: double backslash auto-corrected. Prefer ASCII symbols."]];
            let fun dedup [] = []
                  | dedup (#"\\" :: #"\\" :: cs) = #"\\" :: dedup cs
                  | dedup (c :: cs) = c :: dedup cs
            in String.implode (dedup (String.explode line)) end)
      else line

    fun do_eval () =
      if Substring.isEmpty trimmed orelse not has_semi
      then Exn.Res ()
      else Exn.capture (fn () =>
             ML_Compiler.eval (ML_Compiler.verbose true ML_Compiler.flags)
               Position.none (ML_Lex.tokenize line)) ()

    val result =
      Print_Mode.with_modes [Print_Mode.PIDE] do_eval ()

    val _ = case result of
              Exn.Res _ => ()
            | Exn.Exn exn =>
                message Markup.errorN (Markup.serial_properties 0)
                  [XML.blob [Runtime.exn_message exn]]
  in
    (* Reset message function, then send "done" and shut down the channel. *)
    Synchronized.change current_message (K (fn _ => fn _ => fn _ => ()));
    message "done" [] [];
    Message_Channel.shutdown channel
  end;


(** Server lifecycle **)

(* Priority for I/R futures: negative so that interactive jEdit work
   (which runs at pri >= 0) always takes precedence over REPL evaluation. *)
val ir_pri = ~1;

fun start port =
  let
    val accept_loop = Tcp_Handler.start port
    val ir_group = Future.new_group NONE
    val _ = Synchronized.change server_group_id (K (Task_Queue.group_id ir_group))
    val _ = Synchronized.change Tcp_Handler.handler (K eval_handler)
  in
    (singleton o Future.forks)
      {name = "ml_repl_accept", group = SOME ir_group,
       deps = [], pri = ir_pri, interrupts = true}
      accept_loop
  end;

fun stop () =
  (Tcp_Handler.stop ();
   Synchronized.change server_group_id (K 0));

end;
