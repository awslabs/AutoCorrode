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

  val pin : string -> unit
  val unpin : string -> unit
  val rebase : string -> unit

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
  val timeout : string -> int -> unit
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

(** Default step timeout (seconds, 0 = no limit) **)

val default_timeout : int = 10;

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

datatype spec = LoadedTheory of string | PinnedRepl of string * int;

datatype origin =
  From_Theory of spec list
| From_Segment of string * int
| From_REPL of string * int
| From_Document of string * int;

type repl_step = {
  text: string,
  pre_state: Toplevel.state,
  post_state: Toplevel.state,
  stale: bool
};

type pin = {
  theory: theory,
  version: int,
  stale: bool
};

type repl = {
  origin: origin,
  base_state: Toplevel.state,
  steps: repl_step list,
  timeout: int,
  pin: pin option
};

(* Concurrency guard: repl_tab stores repl_entry values.  A slow mutation
   (step, edit, replay) atomically transitions Repl -> Claimed before
   running exec_text, then Claimed -> Repl with the result.  Any operation
   that calls the_repl/entry_repl on a Claimed entry fails immediately
   with "is busy", preventing concurrent mutations from racing.

   Claimed carries a snapshot taken atomically at claim time so that
   Ir.repls () can render busy entries with the same fields as live ones
   plus the operation in flight and elapsed time. *)
datatype claim_op = Op_Step | Op_Edit | Op_Replay | Op_Rebase | Op_Merge;

fun claim_op_str Op_Step   = "step"
  | claim_op_str Op_Edit   = "edit"
  | claim_op_str Op_Replay = "replay"
  | claim_op_str Op_Rebase = "rebase"
  | claim_op_str Op_Merge  = "merge";

type claim_info = {
  origin: origin,
  step_count: int,
  stale_count: int,
  operation: claim_op,
  claimed_at: Time.time
};

datatype repl_entry = Repl of repl | Claimed of claim_info;

fun entry_repl id (Repl r) = r
  | entry_repl id (Claimed _) = error ("REPL " ^ quote id ^ " is busy");

fun entry_origin (Repl r) = #origin r
  | entry_origin (Claimed ci) = #origin ci;

(* Sledgehammer bridge: structure-qualified vars survive heap save/load,
   unlike top-level val bindings. Used by ML_Compiler.eval in sledgehammer. *)
val sledgehammer_state : (Proof.state * int) option Synchronized.var =
  Synchronized.var "Ir.sledgehammer_state" NONE;
val sledgehammer_result : string Synchronized.var =
  Synchronized.var "Ir.sledgehammer_result" "";

val repl_tab : repl_entry Symtab.table Synchronized.var
  = Synchronized.var "Ir.repls" Symtab.empty;

fun get_repl_in tab id =
  case Symtab.lookup tab id of
    NONE => error ("No REPL " ^ quote id)
  | SOME e => entry_repl id e;

fun the_repl id = get_repl_in (Synchronized.value repl_tab) id;

fun descendants tab id =
  let fun is_desc rid =
        case Symtab.lookup tab rid of
          SOME entry => (case entry_origin entry of
            From_REPL (pid, _) => pid = id orelse is_desc pid
          | _ => false)
        | NONE => false
  in filter is_desc (Symtab.keys tab) end;

fun claim id op_kind =
  Synchronized.change_result repl_tab (fn tab =>
    let val r = get_repl_in tab id
        val ci : claim_info =
          {origin = #origin r,
           step_count = length (#steps r),
           stale_count = length (filter #stale (#steps r)),
           operation = op_kind,
           claimed_at = Time.now ()}
    in (r, Symtab.update (id, Claimed ci) tab) end);

fun mark_pin_stale (r : repl) : repl =
  case #pin r of
    SOME p => {origin = #origin r, base_state = #base_state r, steps = #steps r,
               timeout = #timeout r,
               pin = SOME {theory = #theory p, version = #version p, stale = true}}
  | NONE => r;

fun release id r =
  Synchronized.change repl_tab (Symtab.update (id, Repl (mark_pin_stale r)));

fun with_claim id op_kind (f : repl -> repl * 'a) : 'a =
  let val r = claim id op_kind
  in case Exn.capture f r of
       Exn.Res (r', result) => (release id r'; result)
     | Exn.Exn e => (release id r; Exn.reraise e)
  end;

fun with_repl id f =
  Synchronized.change_result repl_tab (fn tab => f (get_repl_in tab id) tab);

fun map_repl id (f : repl -> repl * 'a) : 'a =
  with_repl id (fn r => fn tab =>
    let val (r', result) = f r
    in (result, Symtab.update (id, Repl r') tab) end);

fun timeout id secs =
  (map_repl id (fn r =>
    ({origin = #origin r, base_state = #base_state r,
      steps = #steps r, timeout = secs, pin = #pin r}, ()));
   out ("Timeout for " ^ quote id ^ " set to " ^
        (if secs = 0 then "unlimited" else string_of_int secs ^ "s")));

(* Execute Isar text against a state *)
fun exec_text timeout_secs text st =
  let val thy = Toplevel.theory_of st
      val transitions = Outer_Syntax.parse_text thy (fn () => thy) Position.none text
      fun run (tr, s) =
        let val old = !Multithreading.parallel_proofs
            val _ = Multithreading.parallel_proofs := Int.min (2, old)
            val s' = Toplevel.command_exception false tr s
            val _ = Multithreading.parallel_proofs := old
        in s' end
      fun go () = List.foldl (fn (tr, s) => run (tr, s)) st transitions
  in if timeout_secs > 0
     then Timeout.apply (Time.fromSeconds (Int.toLarge timeout_secs)) go ()
       handle Timeout.TIMEOUT _ =>
         error ("Step timed out after " ^ string_of_int timeout_secs ^ "s")
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

(* The initial version 0 is a placeholder; resolve_spec looks up and
   returns the current pinned version regardless of the input version. *)
fun string_to_spec s =
  if String.isPrefix "pin@" s then PinnedRepl (String.extract (s, 4, NONE), 0)
  else LoadedTheory s;

(* Resolve a spec to a theory.  For PinnedRepl, the version in the argument
   is ignored; the current pinned version is looked up and returned. *)
fun resolve_spec tab (LoadedTheory s) = (Thy_Info.get_theory s, LoadedTheory s)
  | resolve_spec tab (PinnedRepl (name, _)) =
      case Symtab.lookup tab name of
        SOME (Repl r) =>
          (case #pin r of
             SOME p => if #stale p then error ("Pin " ^ quote name ^ " is stale")
                       else (#theory p, PinnedRepl (name, #version p))
           | NONE => error ("REPL " ^ quote name ^ " is not pinned"))
      | SOME (Claimed _) => error ("REPL " ^ quote name ^ " is busy")
      | NONE => error ("No REPL " ^ quote name);

fun has_pin_dep tab target_id =
  Symtab.exists (fn (_, entry) =>
    case entry_origin entry of
      From_Theory specs => exists (fn PinnedRepl (n, _) => n = target_id
                                    | _ => false) specs
    | _ => false) tab;

(* Create a new REPL.  Theory specs must already be loaded — either present
   in the initial heap or previously loaded via Ir.load_theory.
   Pin specs ("pin@NAME") reference a pinned REPL's theory snapshot. *)
fun init id specs =
  let val _ = if null specs then error "init requires at least one spec" else ()
      fun from_specs specs =
            let val tab = Synchronized.value repl_tab
                val resolved = map (resolve_spec tab o string_to_spec) specs
                val thys = map #1 resolved
                val spec_list = map #2 resolved
                val thy = Theory.begin_theory (id, Position.none) thys
            in (From_Theory spec_list, Toplevel.make_state (SOME thy)) end
      val parsed = map parse_spec specs
      val (origin, st) =
        case parsed of
          [(thy_name, SOME idx)] =>
            let val segs = find_source thy_name
                val seg = nth segs idx
                  handle General.Subscript =>
                    error ("Index " ^ string_of_int idx ^ " out of range")
            in (From_Segment (thy_name, idx),
                #state (seg : Document_Output.segment)) end
        | _ =>
            let val _ = if exists (fn (_, opt) => is_some opt) parsed
                        then error "Cannot mix theory and segment specs in multi-theory init"
                        else ()
            in from_specs (map #1 parsed) end
      val r : repl = {origin = origin, base_state = st, steps = [],
                      timeout = default_timeout, pin = NONE}
  in Synchronized.change_result repl_tab (fn tab =>
       if Symtab.defined tab id
       then error ("REPL " ^ quote id ^ " already exists")
       else ((), Symtab.update (id, Repl r) tab));
     out ("Created REPL " ^ quote id)
  end;

fun init_from_document id node_name command_id =
  let
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
                    base_state = toplevel_st, steps = [], timeout = default_timeout,
                    pin = NONE}
  in Synchronized.change_result repl_tab (fn tab =>
       if Symtab.defined tab id
       then error ("REPL " ^ quote id ^ " already exists")
       else ((), Symtab.update (id, Repl r) tab));
     out ("Created REPL " ^ quote id ^ " from document " ^ quote node_name ^
          " command " ^ string_of_int command_id ^
          (if Toplevel.is_proof toplevel_st then " [proof]" else " [theory]"))
  end;

fun fork parent_id new_id state_idx =
  (Synchronized.change repl_tab (fn tab =>
    let val _ = if Symtab.defined tab new_id
                then error ("REPL " ^ quote new_id ^ " already exists") else ()
        val parent = get_repl_in tab parent_id
        val steps = #steps parent
        val n = length steps
        val i = if state_idx < 0 then n + 1 + state_idx else state_idx
        val st = if i = 0 then #base_state parent
                 else if i >= 1 andalso i <= n then #post_state (nth steps (i - 1))
                 else error ("State " ^ string_of_int state_idx ^
                             " out of range (0.." ^ string_of_int n ^ ")")
        val r : repl = {origin = From_REPL (parent_id, i), base_state = st,
                        steps = [], timeout = #timeout parent, pin = NONE}
    in Symtab.update (new_id, Repl r) tab end);
   out ("Forked REPL " ^ quote new_id ^ " from " ^ quote parent_id ^
        " at state " ^ string_of_int state_idx));

fun step_repl timeout_secs text (r : repl) : repl =
  let val pre = last_state r
      val post = exec_text timeout_secs text pre
      val s : repl_step = {text = text, pre_state = pre, post_state = post, stale = false}
  in {origin = #origin r, base_state = #base_state r,
      steps = #steps r @ [s], timeout = #timeout r, pin = #pin r} end;

fun step id text =
  with_claim id Op_Step (fn r =>
    let val r' = step_repl (#timeout r) text r
    in (r', out (pretty_state (last_state r'))) end);

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

fun spec_str (LoadedTheory s) = s
  | spec_str (PinnedRepl (n, _)) = "pin@" ^ n;

fun origin_str orig = case orig of
    From_Theory specs => String.concatWith "+" (map spec_str specs)
  | From_Segment (t, i) => t ^ ":" ^ string_of_int i
  | From_REPL (p, i) => "REPL " ^ quote p ^ " state " ^ string_of_int i
  | From_Document (n, i) => "document " ^ quote n ^ " cmd " ^ string_of_int i;

fun pin_str NONE = ""
  | pin_str (SOME (p : pin)) =
      if #stale p then ", pinned [stale]" else ", pinned";

fun pin id =
  let val v = map_repl id (fn r =>
    let val st = last_state r
        val _ = if Toplevel.is_proof st
                then error ("Cannot pin " ^ quote id ^ ": REPL is in a proof state")
                else ()
        val thy = Toplevel.theory_of st
        val new_v = case #pin r of NONE => 1 | SOME p => #version p + 1
        val p : pin = {theory = thy, version = new_v, stale = false}
    in ({origin = #origin r, base_state = #base_state r, steps = #steps r,
         timeout = #timeout r, pin = SOME p}, new_v) end)
  in out ("Pinned " ^ quote id) end;

fun unpin id =
  (with_repl id (fn r => fn tab =>
    case #pin r of
      NONE => error ("REPL " ^ quote id ^ " is not pinned")
    | SOME _ =>
        if has_pin_dep tab id
        then error ("Cannot unpin " ^ quote id ^ ": other REPLs depend on it")
        else ((), Symtab.update (id, Repl {origin = #origin r, base_state = #base_state r,
               steps = #steps r, timeout = #timeout r, pin = NONE}) tab));
   out ("Unpinned " ^ quote id));

fun show id =
  let val r = the_repl id
      val orig = origin_str (#origin r)
      val n = length (#steps r)
      val tmo = if #timeout r = 0 then "unlimited"
                 else string_of_int (#timeout r) ^ "s"
      val _ = out ("REPL " ^ quote id ^
                   " (" ^ string_of_int n ^ " steps, from " ^ orig ^
                   ", timeout=" ^ tmo ^ pin_str (#pin r) ^ ")")
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

fun replay_repl (r : repl) : repl =
  let fun go _ [] acc = rev acc
        | go prev_post (s :: rest) acc =
            if #stale (s : repl_step) then
              let val post = exec_text (#timeout r) (#text s) prev_post
                  val s' : repl_step = {text = #text s, pre_state = prev_post,
                                         post_state = post, stale = false}
              in go post rest (s' :: acc) end
            else go (#post_state s) rest (s :: acc)
  in {origin = #origin r, base_state = #base_state r,
      steps = go (#base_state r) (#steps r) [],
      timeout = #timeout r, pin = #pin r} end;

fun replay id =
  with_claim id Op_Replay (fn r =>
    let val stale_count = length (filter #stale (#steps r))
        val r' = replay_repl r
    in (r', out ("Replayed " ^ string_of_int stale_count ^ " stale steps")) end);

fun mark_all_stale (steps : repl_step list) : repl_step list =
  map (fn s => {text = #text s, pre_state = #pre_state s,
                post_state = #post_state s, stale = true}) steps;

(* with_claim because Theory.begin_theory is expensive and must not hold
   the repl_tab lock.  Does NOT replay steps — leaves them stale for a
   subsequent Ir.replay call. *)
fun rebase id =
  with_claim id Op_Rebase (fn r =>
    case #origin r of
      From_Theory specs =>
        let val tab = Synchronized.value repl_tab
            (* Resolve all specs against current pin state *)
            val resolved = map (resolve_spec tab) specs
            val new_specs = map #2 resolved
        in if specs = new_specs
           then (r, out ("REPL " ^ quote id ^ " is already up to date"))
           else
             let val new_thy = Theory.begin_theory (id, Position.none) (map #1 resolved)
                 val new_base = Toplevel.make_state (SOME new_thy)
                 val n = length (#steps r)
                 val r' = {origin = From_Theory new_specs, base_state = new_base,
                           steps = mark_all_stale (#steps r),
                           timeout = #timeout r, pin = #pin r}
             in (r', out ("Rebased " ^ quote id ^ " (" ^
                          string_of_int n ^ " steps marked stale; use replay to re-execute)")) end
        end
    | orig => error ("REPL " ^ quote id ^ " (from " ^ origin_str orig ^
                     ") does not support rebase"));

fun edit_repl idx new_text (r : repl) : repl =
  let val steps = #steps r
      val _ = if idx < 0 orelse idx >= length steps
              then error ("Step " ^ string_of_int idx ^ " out of range") else ()
      val pre = if idx = 0 then #base_state r
                else #post_state (nth steps (idx - 1))
      val post = exec_text (#timeout r) new_text pre
      val edited : repl_step = {text = new_text, pre_state = pre, post_state = post, stale = false}
      val before_steps = List.take (steps, idx)
      val after_steps = List.drop (steps, idx + 1)
        |> map (fn s : repl_step => {text = #text s, pre_state = #pre_state s,
                                      post_state = #post_state s, stale = true})
      val r' : repl = {origin = #origin r, base_state = #base_state r,
                        steps = before_steps @ [edited] @ after_steps,
                        timeout = #timeout r, pin = #pin r}
  in if #auto_replay (get_cfg ()) andalso not (null after_steps)
     then replay_repl r' else r' end;

fun edit id idx new_text =
  with_claim id Op_Edit (fn r =>
    let val r' = edit_repl idx new_text r
        val after_count = length (#steps r) - idx - 1
    in (r', out ("Edited step " ^ string_of_int idx ^ ", " ^
                 string_of_int after_count ^ " subsequent steps marked stale")) end);

fun truncate id raw_idx =
  with_repl id (fn r => fn tab =>
    let val steps = #steps r
        val n = length steps
        val idx = if raw_idx < 0 then n + raw_idx - 1 else raw_idx
        val _ = if idx < ~1 orelse idx >= n
                then error ("Step " ^ string_of_int raw_idx ^ " out of range ("
                            ^ string_of_int n ^ " steps)") else ()
        val dropped = length steps - idx - 1
        val base_orphans = Symtab.fold (fn (rid, entry) =>
          case entry_origin entry of
            From_REPL (pid, si) =>
              if pid = id andalso si > idx then cons rid else I
          | _ => I) tab []
        val all_orphans =
          base_orphans @ flat (map (descendants tab) base_orphans)
        val _ = List.app (fn rid =>
          case Symtab.lookup tab rid of
            SOME (Claimed _) =>
              error ("Cannot truncate: sub-REPL " ^ quote rid ^ " is busy")
          | _ => ()) all_orphans
        val tab' = fold (fn rid => Symtab.delete_safe rid) all_orphans tab
        val r' : repl = mark_pin_stale {origin = #origin r, base_state = #base_state r,
                          steps = if idx < 0 then [] else List.take (steps, idx + 1),
                          timeout = #timeout r, pin = #pin r}
    in (out ("Truncated to step " ^ string_of_int idx ^ ", dropped " ^
             string_of_int dropped ^ " steps"),
        Symtab.update (id, Repl r') tab') end);

fun back id = truncate id ~1;

fun merge id =
  let val child = claim id Op_Merge
      val (pid, pidx) =
        case #origin child of
          From_REPL (p, i) => (p, i)
        | _ => (release id child;
                error ("REPL " ^ quote id ^ " is not a sub-REPL"))
      val merged_text = String.concatWith "\n" (map #text (#steps child))
  in
    case Exn.capture (with_claim pid Op_Merge) (fn parent =>
      let val r' =
            if pidx < length (#steps parent)
            then edit_repl pidx merged_text parent
            else step_repl (#timeout parent) merged_text parent
          val _ = Synchronized.change repl_tab (Symtab.delete id)
          val msg = if pidx < length (#steps parent)
                    then "replaced step " ^ string_of_int pidx
                    else "appended as new step"
      in (r', out ("Merged " ^ quote id ^ " into " ^ quote pid ^
                   " (" ^ msg ^ ")")) end) of
      Exn.Res x => x
    | Exn.Exn e => (release id child; Exn.reraise e)
  end;

fun remove id =
  let val removed =
    with_repl id (fn r => fn tab =>
      let val _ = case #pin r of
              SOME _ => if has_pin_dep tab id
                        then error ("Cannot remove " ^ quote id ^
                                    ": other REPLs depend on its pin")
                        else ()
            | NONE => ()
          val descs = descendants tab id
          val _ = List.app (fn rid =>
            case Symtab.lookup tab rid of
              SOME (Claimed _) =>
                error ("Cannot remove: sub-REPL " ^ quote rid ^ " is busy")
            | _ => ()) descs
          val to_remove = id :: descs
          val tab' = fold (fn rid => Symtab.delete_safe rid) to_remove tab
      in (to_remove, tab') end)
  in out ("Removed " ^ commas (map quote removed)) end;

fun repls () =
  let val tab = Synchronized.value repl_tab
      val now = Time.now ()
  in
    Symtab.fold (fn (id, entry) => fn () =>
      case entry of
        Claimed ci =>
          let val n = #step_count ci
              val stale = #stale_count ci
              val elapsed = Time.toReal (Time.- (now, #claimed_at ci))
              val desc = id ^ " (" ^ string_of_int n ^ " steps" ^
                  (if stale > 0 then ", " ^ string_of_int stale ^ " stale" else "") ^
                  ", from " ^ origin_str (#origin ci) ^
                  ", busy [" ^ claim_op_str (#operation ci) ^ "] " ^
                  Real.fmt (StringCvt.FIX (SOME 1)) elapsed ^ "s)"
          in out ("    " ^ desc) end
      | Repl r =>
        let val n = length (#steps r)
            val stale = length (filter #stale (#steps r))
            val desc = id ^ " (" ^ string_of_int n ^ " steps" ^
                (if stale > 0 then ", " ^ string_of_int stale ^ " stale" else "") ^
                ", from " ^ origin_str (#origin r) ^ pin_str (#pin r) ^ ")"
        in out ("    " ^ desc) end)
      tab ()
  end;

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
  \                          [\"pin@A\"], or [\"T1\",\"T2\",...] (merges)\n\
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
  \  pin id                 snapshot REPL theory state\n\
  \  unpin id               remove a REPL's pin\n\
  \  rebase id              update base to latest pins (marks steps stale)\n\
  \  sledgehammer id secs   run sledgehammer on proof state\n\
  \  find_theorems id n q   search theorems (n=max, 0=unlimited)\n\
  \  timeout id secs        set step timeout for REPL (0=unlimited, default 10s)\n\
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
  \=== Pinning and rebasing ===\n\
  \\n\
  \  Ir.pin \"R\";                        (* snapshot R's theory state *)\n\
  \  Ir.init \"S\" [\"pin@R\"];             (* new REPL from pinned state *)\n\
  \  Ir.step \"S\" \"lemma True by simp\";  (* work in S *)\n\
  \  (* ... edit R, then re-pin: *)\n\
  \  Ir.pin \"R\";\n\
  \  Ir.rebase \"S\";                     (* rebase S onto updated R *)\n\
  \  Ir.replay \"S\";                     (* re-execute stale steps *)\n\
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
