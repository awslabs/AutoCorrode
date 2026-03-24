(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Isabelle/REPL (I/R): interactive Isar REPL.

   Manages a set of named REPLs, each a list of Isar steps rooted in a
   theory.  Steps can be pushed, popped, edited, and replayed.  REPLs can
   fork from each other for sub-proof exploration and merge back.

   This file contains only the Isar REPL logic.  TCP serving and output
   capture are in tcp_handler.ML and ml_repl.ML respectively.

   See README.md for full documentation. *)

signature IR =
sig
  type config = {color: bool, show_ignored: bool, full_spans: bool,
                 show_theory_in_source: bool, auto_replay: bool}
  val config : (config -> config) -> unit
  val get_cfg : unit -> config

  val init : string -> string list -> unit
  val init_from_document : string -> string -> int -> unit
  val fork : string -> string -> int -> unit
  val step : string -> string -> unit
  val show : string -> unit
  val state : string -> int -> unit
  val text : string -> unit
  val edit : string -> int -> string -> unit
  val replay : string -> unit
  val truncate : string -> int -> unit
  val back : string -> unit
  val merge : string -> unit

  val remove : string -> unit
  val repls : unit -> unit
  val theories : unit -> unit
  val load_theory : string -> unit
  val source : string -> int -> int -> unit
  val source_map : string -> int -> int -> unit
  val sledgehammer : string -> int -> unit
  val sledgehammer_state : (Proof.state * int) option Synchronized.var
  val sledgehammer_result : string Synchronized.var
  val find_theorems : string -> int -> string -> unit
  val timeout : int -> unit
  val is_interactive_session : unit -> bool
  val help : unit -> unit
end;

(* Segment access via Thy_Info.get_theory_segments (requires record_theories=true) *)

structure Ir : IR =
struct

(** Configuration **)

type config = {color: bool, show_ignored: bool, full_spans: bool,
               show_theory_in_source: bool, auto_replay: bool};
val cfg : config Synchronized.var =
  Synchronized.var "Ir.cfg" {color = true, show_ignored = false, full_spans = false,
                                   show_theory_in_source = false, auto_replay = true};
fun config f = Synchronized.change cfg f;
fun get_cfg () = Synchronized.value cfg;

(** Step timeout (seconds, 0 = no limit) **)

val step_timeout : int Synchronized.var = Synchronized.var "Ir.timeout" 10;
fun timeout secs =
  (Synchronized.change step_timeout (K secs);
   TextIO.print ("Timeout set to " ^ (if secs = 0 then "unlimited" else string_of_int secs ^ "s") ^ "\n"));

(** Markup-based token rendering **)

fun flatten s = String.translate (fn #"\n" => " " | c => str c) s;

(* Produce marked-up text for a token.  With PIDE print mode active
   (set by ml_repl.ML in YXML mode), Markup.markups produces YXML;
   otherwise it returns plain text. *)
fun print_token keywords tok =
  Markup.markups (Token.markups keywords tok) (Token.unparse tok);

fun print_span keywords (Command_Span.Span (_, toks)) =
  flatten (implode (map (print_token keywords) toks));

fun span_text_full (Command_Span.Span (_, toks)) =
  flatten (implode (map Token.unparse toks));

(* Render a command span, optionally truncated. *)
fun render_span keywords full (Command_Span.Span (_, toks)) =
  if full then flatten (implode (map (print_token keywords) toks))
  else
    let fun go _ [] = ("", false)
          | go remaining (tok :: rest) =
              let val w = size (flatten (Token.unparse tok))
              in if w > remaining then ("", true)
                 else let val (s, trunc) = go (remaining - w) rest
                      in (flatten (print_token keywords tok) ^ s, trunc) end
              end
        val (text, truncated) = go 80 toks
    in if truncated then text ^ "..." else text end;

(* Render raw Isar text with markup (used by show). *)
fun render_isar_text thy text =
  let val kws = Thy_Header.get_keywords thy
      val toks = Token.tokenize kws {strict = false}
                   (Symbol_Pos.explode (text, Position.none))
  in flatten (implode (map (print_token kws) toks)) end;

fun is_ignored (Command_Span.Span (Command_Span.Ignored_Span, _)) = true
  | is_ignored _ = false;

(* Output function used by all Ir.* commands.  Uses writeln so that
   ml_repl.ML's output wrappers can capture it when running over TCP. *)
fun out s = writeln s;


(** Segments **)

fun find_source thy_name =
  Thy_Info.get_theory_segments thy_name
  handle ERROR msg =>
    error ("No recorded segments for " ^ quote thy_name ^
           ". Rebuild the session heap with: isabelle build -o record_theories=true -b <SESSION>");

fun source thy_name start stop =
  let val segs = find_source thy_name
      val thy = Thy_Info.get_theory thy_name
      val kws = Thy_Header.get_keywords thy
      val len = length segs
      val start' = if start < 0 then Int.max (0, len + start) else start
      val stop' = if stop < 0 then len + stop else stop
      val {show_ignored = incl, full_spans, show_theory_in_source, ...} = get_cfg ()
      val prefix = if show_theory_in_source then thy_name ^ ":" else ""
      fun pr _ [] = ()
        | pr i (({span, prev_state, ...} : Document_Output.segment) :: rest) =
            let val indent = StringCvt.padLeft #" " (2 * Toplevel.level prev_state) ""
            in (if i >= start' andalso i <= stop' then
               if is_ignored span then
                 (if incl then out (prefix ^ StringCvt.padLeft #" " 4 (string_of_int i) ^
                                    "  " ^ indent ^ span_text_full span) else ())
               else out (prefix ^ StringCvt.padLeft #" " 4 (string_of_int i) ^
                         "  " ^ indent ^ render_span kws full_spans span)
             else ();
             pr (i + 1) rest)
            end
  in pr 0 segs end;

(* Output segment index to source position mapping.
   Each non-ignored segment produces a fixed-width line:
     idx  keyword  line  offset  file
   Used by repl.py to build line-number navigation.
   start_line/stop_line filter by source line number (0 = from start, ~1 = to end). *)
fun source_map thy_name start_line stop_line =
  let val segs = find_source thy_name
      val {show_ignored = incl, ...} = get_cfg ()
      fun first_pos (Command_Span.Span (_, toks)) =
        case List.find (fn tok =>
          is_some (Position.line_of (Token.pos_of tok))) toks of
          SOME tok => Token.pos_of tok | NONE => Position.none
      fun first_keyword (Command_Span.Span (_, toks)) =
        case toks of
          (tok :: _) => Token.unparse tok
        | _ => ""
      (* Resolve ~N: find the max line number in all segments *)
      val max_line = fold (fn seg => fn acc =>
        let val ln = the_default 0 (Position.line_of (first_pos (#span (seg : Document_Output.segment))))
        in Int.max (acc, ln) end) segs 0
      val start' = if start_line < 0 then Int.max (0, max_line + 1 + start_line) else start_line
      val stop' = if stop_line < 0 then max_line + 1 + stop_line else stop_line
      val _ = out ("  idx  keyword                 line  offset  file")
      val _ = out ("-----  --------------------  ------  ------  " ^
                   "----------------------------------------")
      fun pr _ [] = ()
        | pr i (seg :: rest) =
            let val span = #span (seg : Document_Output.segment)
                val pos = first_pos span
                val ln = the_default 0 (Position.line_of pos)
                val ign = is_ignored span
            in (if ln >= start' andalso ln <= stop' then
                  (if not ign orelse incl then
                    out (StringCvt.padLeft #" " 5 (string_of_int i) ^ "  " ^
                         StringCvt.padRight #" " 20 (first_keyword span) ^ "  " ^
                         StringCvt.padLeft #" " 6 (string_of_int ln) ^ "  " ^
                         StringCvt.padLeft #" " 6 (string_of_int (the_default 0 (Position.offset_of pos))) ^ "  " ^
                         the_default "" (Position.file_of pos))
                  else ())
                else ());
               pr (i + 1) rest
            end
  in pr 0 segs end;


(** REPL core **)

datatype origin =
  From_Theory of string
| From_Segment of string * int
| From_REPL of string * int
| From_Document of string * int;

type repl_step = {
  text: string,
  pre_state: Toplevel.state,
  post_state: Toplevel.state,
  stale: bool
};

type repl = {
  origin: origin,
  base_state: Toplevel.state,
  steps: repl_step list
};

(* Sledgehammer bridge: structure-qualified vars survive heap save/load,
   unlike top-level val bindings. Used by ML_Compiler.eval in sledgehammer. *)
val sledgehammer_state : (Proof.state * int) option Synchronized.var =
  Synchronized.var "Ir.sledgehammer_state" NONE;
val sledgehammer_result : string Synchronized.var =
  Synchronized.var "Ir.sledgehammer_result" "";

val repl_tab : repl Symtab.table Synchronized.var
  = Synchronized.var "Ir.repls" Symtab.empty;

fun the_repl id =
  case Symtab.lookup (Synchronized.value repl_tab) id of
    SOME r => r
  | NONE => error ("No REPL " ^ quote id);

fun update_repl id r =
  Synchronized.change repl_tab (Symtab.update (id, r));

(* Execute Isar text against a state *)
fun exec_text text st =
  let val thy = Toplevel.theory_of st
      val transitions = Outer_Syntax.parse_text thy (fn () => thy) Position.none text
      fun run (tr, s) =
        let val old = !Multithreading.parallel_proofs
            val _ = Multithreading.parallel_proofs := Int.min (2, old)
            val s' = Toplevel.command_exception false tr s
            val _ = Multithreading.parallel_proofs := old
        in s' end
      val secs = Synchronized.value step_timeout
      fun go () = List.foldl (fn (tr, s) => run (tr, s)) st transitions
  in if secs > 0
     then Timeout.apply (Time.fromSeconds (Int.toLarge secs)) go ()
       handle Timeout.TIMEOUT _ =>
         error ("Step timed out after " ^ string_of_int secs ^ "s")
     else go ()
  end;

fun last_state ({steps, base_state, ...} : repl) =
  case rev steps of [] => base_state | ({post_state, ...} :: _) => post_state;

fun pretty_state st =
  Pretty.string_of (Pretty.chunks (Toplevel.pretty_state st));


(** Commands **)

(* Parse "TheoryName:IDX" or "TheoryName" *)
fun parse_spec spec =
  case String.fields (fn c => c = #":") spec of
    [thy, idx_str] =>
      (case Int.fromString idx_str of
        SOME idx => (thy, SOME idx)
      | NONE => error ("Bad index in " ^ quote spec))
  | [thy] => (thy, NONE)
  | _ => error ("Bad spec: " ^ quote spec);

(* Create a new REPL.  The theory must already be loaded — either present
   in the initial heap or previously loaded via Ir.load_theory. *)
fun init id specs =
  let val _ = if Symtab.defined (Synchronized.value repl_tab) id
              then error ("REPL " ^ quote id ^ " already exists")
              else ()
      val _ = if null specs then error "init requires at least one spec" else ()
      val parsed = map parse_spec specs
      val (origin, st) =
        case parsed of
          [(thy_name, SOME idx)] =>
            let val segs = find_source thy_name
                val seg = nth segs idx
                  handle General.Subscript =>
                    error ("Index " ^ string_of_int idx ^ " out of range")
            in (From_Segment (thy_name, idx), #state (seg : Document_Output.segment)) end
        | _ =>
            let val _ = if exists (fn (_, opt) => is_some opt) parsed
                        then error "Cannot mix theory and segment specs in multi-theory init"
                        else ()
                val thy_names = map #1 parsed
                val thys = map Thy_Info.get_theory thy_names
                val thy = Theory.begin_theory (id, Position.none) thys
            in (From_Theory (String.concatWith "+" thy_names),
                Toplevel.make_state (SOME thy)) end
      val r : repl = {origin = origin, base_state = st, steps = []}
  in update_repl id r;
     out ("Created REPL " ^ quote id)
  end;

fun init_from_document id node_name command_id =
  let
    val _ = if Symtab.defined (Synchronized.value repl_tab) id
            then error ("REPL " ^ quote id ^ " already exists") else ()
    val st = Document.state ()
    val exec =
      (case Exn.capture (Document.command_exec st node_name) command_id of
        Exn.Res (SOME e) => e
      | Exn.Res NONE =>
          error ("Command " ^ string_of_int command_id ^ " in " ^ quote node_name ^
                 " has not been executed yet")
      | Exn.Exn exn =>
          error ("Cannot access command " ^ string_of_int command_id ^ " in " ^
                 quote node_name ^ ": " ^ Runtime.exn_message exn))
    val (eval, _) = exec
    val _ = if not (Command.eval_finished eval) then
              error ("Command " ^ string_of_int command_id ^ " in " ^ quote node_name ^
                     " is still being evaluated")
            else ()
    val toplevel_st = Command.eval_result_state eval
    val r : repl = {origin = From_Document (node_name, command_id),
                    base_state = toplevel_st, steps = []}
  in update_repl id r;
     out ("Created REPL " ^ quote id ^ " from document " ^ quote node_name ^
          " command " ^ string_of_int command_id ^
          (if Toplevel.is_proof toplevel_st then " [proof]" else " [theory]"))
  end;

fun fork new_id parent_id state_idx =
  let val _ = if Symtab.defined (Synchronized.value repl_tab) new_id
              then error ("REPL " ^ quote new_id ^ " already exists")
              else ()
      val parent = the_repl parent_id
      val steps = #steps parent
      val n = length steps
      (* Use same indexing as state: 0=base, 1=after step 0, ... *)
      val i = if state_idx < 0 then n + 1 + state_idx else state_idx
      val st = if i = 0 then #base_state parent
               else if i >= 1 andalso i <= n then #post_state (nth steps (i - 1))
               else error ("State " ^ string_of_int state_idx ^ " out of range (0.." ^
                           string_of_int n ^ ")")
      val r : repl = {origin = From_REPL (parent_id, i), base_state = st, steps = []}
  in update_repl new_id r;
     out ("Forked REPL " ^ quote new_id ^ " from " ^ quote parent_id ^
          " at state " ^ string_of_int i)
  end;

fun step id text =
  let val r = the_repl id
      val pre = last_state r
      val post = exec_text text pre
      val s : repl_step = {text = text, pre_state = pre, post_state = post, stale = false}
      val r' : repl = {origin = #origin r, base_state = #base_state r,
                        steps = #steps r @ [s]}
  in update_repl id r';
     out (pretty_state post)
  end;

fun state id state_idx =
  let val r = the_repl id
      val steps = #steps r
      val n = length steps
      val i = if state_idx < 0 then n + 1 + state_idx else state_idx
      val st = if i = 0 then #base_state r
               else if i >= 1 andalso i <= n then #post_state (nth steps (i - 1))
               else error ("State " ^ string_of_int state_idx ^ " out of range (0.." ^
                           string_of_int n ^ ")")
  in out (pretty_state st) end;

fun show id =
  let val r = the_repl id
      val orig = case #origin r of
          From_Theory t => "theory " ^ t
        | From_Segment (t, i) => t ^ ":" ^ string_of_int i
        | From_REPL (p, i) => "REPL " ^ quote p ^ " state " ^ string_of_int i
        | From_Document (n, i) => "document " ^ quote n ^ " cmd " ^ string_of_int i
      val n = length (#steps r)
      val _ = out ("REPL " ^ quote id ^
                   " (" ^ string_of_int n ^ " steps, from " ^ orig ^ ")")
      val _ = out ("  base  level=" ^ string_of_int (Toplevel.level (#base_state r)))
      val thy = Toplevel.theory_of (#base_state r)
      fun pr _ [] = ()
        | pr i (({text, stale, pre_state, ...} : repl_step) :: rest) =
            let val stale_mark = if stale then " [stale]" else ""
                val lvl = Toplevel.level pre_state
                val indent = StringCvt.padLeft #" " (2 * lvl) ""
            in out ("  " ^ StringCvt.padLeft #" " 3 (string_of_int i) ^ "  " ^
                    indent ^ render_isar_text thy text ^ stale_mark);
               pr (i + 1) rest
            end
  in pr 0 (#steps r) end;

fun text id =
  let val r = the_repl id
      val t = map #text (#steps r)
  in out (String.concatWith "\n" t) end;

fun replay id =
  let val r = the_repl id
      fun go _ [] acc = rev acc
        | go prev_post (s :: rest) acc =
            if #stale (s : repl_step) then
              let val post = exec_text (#text s) prev_post
                  val s' : repl_step = {text = #text s, pre_state = prev_post,
                                         post_state = post, stale = false}
              in go post rest (s' :: acc) end
            else go (#post_state s) rest (s :: acc)
      val steps' = go (#base_state r) (#steps r) []
      val r' : repl = {origin = #origin r, base_state = #base_state r, steps = steps'}
  in update_repl id r';
     out ("Replayed " ^ string_of_int (length (filter #stale (#steps r))) ^ " stale steps")
  end;

fun edit id idx new_text =
  let val r = the_repl id
      val steps = #steps r
      val _ = if idx < 0 orelse idx >= length steps
              then error ("Step " ^ string_of_int idx ^ " out of range") else ()
      val pre = if idx = 0 then #base_state r
                else #post_state (nth steps (idx - 1))
      val post = exec_text new_text pre
      val edited : repl_step = {text = new_text, pre_state = pre, post_state = post, stale = false}
      val before_steps = List.take (steps, idx)
      val after_steps = List.drop (steps, idx + 1)
        |> map (fn s : repl_step => {text = #text s, pre_state = #pre_state s,
                                      post_state = #post_state s, stale = true})
      val r' : repl = {origin = #origin r, base_state = #base_state r,
                        steps = before_steps @ [edited] @ after_steps}
  in update_repl id r';
     out ("Edited step " ^ string_of_int idx ^ ", " ^
          string_of_int (length after_steps) ^ " subsequent steps marked stale");
     if #auto_replay (get_cfg ()) andalso not (null after_steps) then replay id else ()
  end;

fun truncate id raw_idx =
  let val r = the_repl id
      val steps = #steps r
      val n = length steps
      val idx = if raw_idx < 0 then n + raw_idx - 1 else raw_idx
      val _ = if idx < ~1 orelse idx >= n
              then error ("Step " ^ string_of_int raw_idx ^ " out of range ("
                          ^ string_of_int n ^ " steps)") else ()
      (* Remove sub-REPLs attached to dropped steps *)
      val dropped = length steps - idx - 1
      val _ = Synchronized.change repl_tab (fn tab =>
        Symtab.fold (fn (rid, r') =>
          case #origin (r' : repl) of
            From_REPL (pid, si) =>
              if pid = id andalso si > idx then Symtab.delete rid else I
          | _ => I) tab tab)
      val r' : repl = {origin = #origin r, base_state = #base_state r,
                        steps = if idx < 0 then [] else List.take (steps, idx + 1)}
  in update_repl id r';
     out ("Truncated to step " ^ string_of_int idx ^ ", dropped " ^
          string_of_int dropped ^ " steps")
  end;

fun back id = truncate id ~1;

fun merge id =
  let val r = the_repl id
      val (pid, pidx) =
        case #origin r of
          From_REPL (p, i) => (p, i)
        | _ => error ("REPL " ^ quote id ^ " is not a sub-REPL")
      val merged_text = String.concatWith "\n" (map #text (#steps r))
      val _ = Synchronized.change repl_tab (Symtab.delete_safe id)
      val target = pidx
  in if target < length (#steps (the_repl pid))
     then (edit pid target merged_text;
           out ("Merged " ^ quote id ^ " into " ^ quote pid ^
                " (replaced step " ^ string_of_int target ^ ")"))
     else (step pid merged_text;
           out ("Merged " ^ quote id ^ " into " ^ quote pid ^
                " (appended as new step)"))
  end;

fun remove id =
  let val _ = the_repl id (* check exists *)
      fun is_descendant rid =
        case #origin (the_repl rid) of
          From_REPL (pid, _) => pid = id orelse is_descendant pid
        | _ => false
      val all_ids = Symtab.keys (Synchronized.value repl_tab)
      val to_remove = id :: filter is_descendant all_ids
      val _ = List.app (fn rid =>
        Synchronized.change repl_tab (Symtab.delete_safe rid)) to_remove
  in out ("Removed " ^ commas (map quote to_remove)) end;

fun repls () =
  Symtab.fold (fn (id, r : repl) => fn () =>
    let val n = length (#steps r)
        val orig = case #origin r of
            From_Theory t => "theory " ^ t
          | From_Segment (t, i) => t ^ ":" ^ string_of_int i
          | From_REPL (p, i) => "REPL " ^ quote p ^ " state " ^ string_of_int i
          | From_Document (n, i) => "document " ^ quote n ^ " cmd " ^ string_of_int i
        val stale = length (filter #stale (#steps r))
        val desc = id ^ " (" ^ string_of_int n ^ " steps" ^
            (if stale > 0 then ", " ^ string_of_int stale ^ " stale" else "") ^
            ", from " ^ orig ^ ")"
    in out ("    " ^ desc)
    end) (Synchronized.value repl_tab) ();

(* Lists theories in the initial heap plus those loaded via load_theory. *)
fun theories () =
  List.app (fn s => out ("  " ^ s)) (Thy_Info.get_names ());

fun is_interactive_session () =
  ! Printer.show_markup_default;

(* Load a theory (and its transitive dependencies) by fully qualified name,
   e.g. "HOL-Library.Multiset".  After loading, the theory is available
   for Ir.init and appears in Ir.theories.
   Not available in interactive PIDE sessions (jEdit); use init_from_document instead. *)
fun load_theory name =
  if is_interactive_session () then
    error "load_theory is not available in interactive PIDE sessions. \
          \Open theories in Isabelle/jEdit and use init_from_document instead."
  else
  let val opts = Options.update "record_theories" "true" (Options.default ())
      val _ = Thy_Info.use_theories opts "" [(name, Position.none)]
  in out ("Loaded theory " ^ quote name) end;

(* Sledgehammer via compiler bridge *)

fun find_theorems id max_results query =
  let val st = last_state (the_repl id)
      val ctxt = Toplevel.context_of st
      val opt_goal = try (fn () => #goal (Proof.simple_goal (Toplevel.proof_of st))) ()
      val criteria = Find_Theorems.read_query Position.none query
      val limit = if max_results > 0 then SOME max_results else NONE
      val (opt_found, theorems) =
        Find_Theorems.find_theorems_cmd ctxt opt_goal limit false criteria
      val returned = length theorems
      val tally =
        (case opt_found of
           NONE => "displaying " ^ string_of_int returned ^ " theorem(s)"
         | SOME found =>
             "found " ^ string_of_int found ^ " theorem(s)" ^
             (if returned < found
              then " (" ^ string_of_int returned ^ " displayed)" else ""))
      val lines = map (fn t => Pretty.string_of (Find_Theorems.pretty_thm ctxt t)) theorems
  in out (tally ^ ":\n" ^ String.concatWith "\n" (rev lines)) end;

fun sledgehammer id timeout_secs =
  let val st = last_state (the_repl id)
      val prf = Toplevel.proof_of st
      val thy = Toplevel.theory_of st
      (* Sledgehammer structures are loaded by HOL/Sledgehammer.thy, which is
         not available at ir.ML compile time. We use ML_Compiler.eval to defer
         name resolution. Unlike the old approach, we pass arguments via
         Ir.sledgehammer_state/timeout which are structure-qualified and
         survive heap save/load (unlike top-level val bindings). *)
      val _ = Synchronized.change sledgehammer_state (K (SOME (prf, timeout_secs)))
      val code =
        "let " ^
        "val (prf, timeout) = the (Synchronized.value Ir.sledgehammer_state) " ^
        "val params = Sledgehammer_Commands.default_params " ^
        "  (Proof_Context.theory_of (Proof.context_of prf)) " ^
        "  [(\"timeout\", string_of_int timeout)] " ^
        "val (_, (_, msg)) = Sledgehammer.run_sledgehammer params " ^
        "  Sledgehammer_Prover.Normal NONE 1 " ^
        "  Sledgehammer_Fact.no_fact_override prf " ^
        "in Synchronized.change Ir.sledgehammer_result (K msg) end"
      val _ = Synchronized.change sledgehammer_result (K "")
      val _ =
        Context.setmp_generic_context (SOME (Context.Theory thy)) (fn () =>
          ML_Compiler.eval ML_Compiler.flags Position.none
            (ML_Lex.tokenize code)) ()
      val msg = Synchronized.value sledgehammer_result
      val _ = Synchronized.change sledgehammer_state (K NONE)
      val lines = String.fields (fn c => c = #"\n") msg
      val tries = filter (fn l => String.isSubstring "Try this" l) lines
  in if null tries then out msg
     else List.app out tries
  end;

fun help () = out
  "=== I/R API ===\n\
  \\n\
  \  All REPL operations take an explicit REPL id.\n\
  \\n\
  \  init id [specs]         create REPL from [\"Theory\"], [\"Theory:idx\"],\n\
  \                          or [\"T1\",\"T2\",...] (merges theories)\n\
  \  fork id new_id state_idx  fork sub-REPL from id at state (~1=latest)\n\
  \  step id \"isar text\"    append step to REPL\n\
  \  show id                describe REPL (origin, steps, staleness)\n\
  \  state id idx           show Toplevel.state (0=base, ~1=latest)\n\
  \  text id                print concatenated text of REPL\n\
  \  edit id idx \"text\"     edit step, replay if auto_replay=true\n\
  \  replay id              re-execute stale steps\n\
  \  truncate id idx        discard steps after idx (~N = revert last N)\n\
  \  back id                revert last step (synonym for truncate ~1)\n\
  \  merge id               inline sub-REPL into parent\n\
  \  sledgehammer id secs   run sledgehammer on proof state\n\
  \  find_theorems id n q   search theorems (n=max, 0=unlimited)\n\
  \  timeout secs           set step timeout (0=unlimited, default 5s)\n\
  \  remove id              remove REPL and its sub-REPLs\n\
  \  repls ()               list all REPLs\n\
  \  theories ()            list loaded theories\n\
  \  load_theory s          load theory by name\n\
  \  source thy s e         list command spans\n\
  \  source_map thy s e     segment-to-position map\n\
  \  config f               update config\n\
  \  help ()                this help\n\
  \\n\
  \=== Quick start ===\n\
  \\n\
  \  Ir.init \"R\" [\"Main\"];\n\
  \  Ir.step \"R\" \"lemma \\\"True\\\"\";\n\
  \  Ir.step \"R\" \"by simp\";\n\
  \  Ir.show \"R\";\n\
  \  Ir.state \"R\" ~1;\n\
  \\n\
  \=== Forking and merging ===\n\
  \\n\
  \  Ir.step \"R\" \"lemma \\\"P\\\"\";\n\
  \  Ir.step \"R\" \"sorry\";\n\
  \  Ir.fork \"R\" \"S\" 1;       (* fork from state before sorry *)\n\
  \  Ir.step \"S\" \"by auto\";\n\
  \  Ir.merge \"S\";             (* replace sorry with proof *)\n\
  \\n\
  \=== Editing ===\n\
  \\n\
  \  Ir.edit \"R\" 0 \"lemma \\\"Q\\\"\";  (* edit first step *)\n\
  \  Ir.truncate \"R\" 1;             (* keep only steps 0 and 1 *)\n\
  \\n\
  \=== Segments (record_theories) ===\n\
  \\n\
  \  Ir.source \"MySession.MyTheory\" 0 ~1;\n\
  \  Ir.init \"R\" [\"MySession.MyTheory:42\"];";

end;

val _ =
  let val names = Thy_Info.get_names ()
      val n = length names
      val has_segments = exists (fn n =>
        (ignore (Thy_Info.get_theory_segments n); true)
        handle ERROR _ => false) (List.take (names, Int.min (1, n)))
  in if has_segments
     then writeln ("Ir: source commands available (" ^
                   string_of_int n ^ " theories)")
     else writeln "Ir: source commands not available (no theories with recorded segments; rebuild with: isabelle build -o record_theories=true -b <SESSION>)"
  end;
