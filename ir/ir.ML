(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* REPL for exploring Isabelle theories via Isar text.
   Designed for use from the Poly/ML console after loading a heap. *)

signature IR =
sig
  type config = {color: bool, show_ignored: bool, full_spans: bool,
                 show_theory_in_source: bool, auto_replay: bool}
  val config : (config -> config) -> unit
  val get_cfg : unit -> config

  val init : string -> string list -> unit
  val fork : string -> int -> unit
  val focus : string -> unit
  val step : string -> unit
  val step_file : string -> unit
  val show : unit -> unit
  val state : int -> unit
  val text : unit -> unit
  val edit : int -> string -> unit
  val replay : unit -> unit
  val truncate : int -> unit
  val merge : unit -> unit

  val remove : string -> unit
  val repls : unit -> unit
  val theories : unit -> unit
  val source : string -> int -> int -> unit
  val sledgehammer : int -> unit
  val find_theorems : int -> string -> unit
  val timeout : int -> unit
  val help : unit -> unit
end;

(* Shared refs for sledgehammer compiler bridge -- must be in global namespace *)
val sh_state_ref = Unsynchronized.ref (Toplevel.make_state NONE);
val sh_timeout_ref = Unsynchronized.ref 30;
val sh_result_ref = Unsynchronized.ref "";

(* Probe for stored_segments -- may or may not exist in the loaded heap *)
val stored_segments_probe =
  Unsynchronized.ref (NONE : (string * Document_Output.segment list) list Synchronized.var option);
val _ = Exn.capture (fn () =>
  ML_Compiler.eval ML_Compiler.flags Position.none
    (ML_Lex.tokenize "stored_segments_probe := SOME stored_segments")) ();

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

val step_timeout : int Synchronized.var = Synchronized.var "Ir.timeout" 5;
fun timeout secs =
  (Synchronized.change step_timeout (K secs);
   TextIO.print ("Timeout set to " ^ (if secs = 0 then "unlimited" else string_of_int secs ^ "s") ^ "\n"));

(** Symbol translation **)

local
  fun parse_code s =
    StringCvt.scanString (Int.scan StringCvt.HEX)
      (if String.isPrefix "0x" s then String.extract (s, 2, NONE) else s);

  fun utf8_of_codepoint cp =
    if cp < 0x80 then chr cp
    else if cp < 0x800 then
      implode [chr (0xC0 + cp div 64), chr (0x80 + cp mod 64)]
    else if cp < 0x10000 then
      implode [chr (0xE0 + cp div 4096),
               chr (0x80 + (cp div 64) mod 64),
               chr (0x80 + cp mod 64)]
    else
      implode [chr (0xF0 + cp div 262144),
               chr (0x80 + (cp div 4096) mod 64),
               chr (0x80 + (cp div 64) mod 64),
               chr (0x80 + cp mod 64)];

  val symbol_table : string Symtab.table =
    let val path = Path.explode "$ISABELLE_HOME/etc/symbols"
        val lines = split_lines (File.read path)
        fun parse_line line =
          case String.tokens Char.isSpace line of
            (sym :: "code:" :: hex :: _) =>
              (case parse_code hex of
                SOME cp => SOME (sym, utf8_of_codepoint cp)
              | NONE => NONE)
          | _ => NONE
    in Symtab.make (map_filter parse_line lines) end;

  val unicode_to_symbol : string Symtab.table =
    Symtab.fold (fn (sym, utf) => Symtab.update (utf, sym)) symbol_table Symtab.empty;
in
  fun unicode_of_symbol sym =
    case Symtab.lookup symbol_table sym of SOME u => u | NONE => sym;

  fun to_unicode text =
    Symbol.explode text |> map unicode_of_symbol |> implode;

  fun from_unicode text =
    let fun convert [] = []
          | convert (c :: cs) =
              if Char.ord (String.sub (c, 0)) < 128 then c :: convert cs
              else
                let fun try_match n =
                      if n > 4 orelse n > length cs + 1 then NONE
                      else let val candidate = implode (List.take (c :: cs, n))
                           in case Symtab.lookup unicode_to_symbol candidate of
                                SOME sym => SOME (sym, List.drop (cs, n - 1))
                              | NONE => try_match (n + 1)
                           end
                in case try_match 1 of
                     SOME (sym, rest) => sym :: convert rest
                   | NONE => c :: convert cs
                end
    in implode (convert (map str (String.explode text))) end;
end;


(** ANSI highlighting **)

(** ANSI highlighting **)

local
  val reset = "\027[0m" val bold = "\027[1m"
  val red = "\027[31m" val green = "\027[32m"
  val yellow = "\027[33m" val blue = "\027[34m" val gray = "\027[90m"

  fun ansi_of tok =
    if Token.is_command tok then bold ^ blue
    else if Token.is_kind Token.Keyword tok then blue
    else if Token.is_kind Token.String tok then green
    else if Token.is_kind Token.Alt_String tok then green
    else if Token.is_kind Token.Cartouche tok then green
    else if Token.is_kind Token.Var tok then yellow
    else if Token.is_kind Token.Type_Var tok then yellow
    else if Token.is_kind Token.Type_Ident tok then yellow
    else if Token.is_comment tok then gray
    else if Token.is_error tok then red
    else ""

  fun colorize_token tok =
    let val text = Token.unparse tok
        val code = ansi_of tok
    in if code = "" then text else code ^ text ^ reset end

  fun flatten s = String.translate (fn #"\n" => " " | c => str c) s
in
  fun span_text_color (Command_Span.Span (_, toks)) =
    flatten (implode (map colorize_token toks));

  fun span_text_full (Command_Span.Span (_, toks)) =
    flatten (implode (map Token.unparse toks));

  fun fmt_span full (Command_Span.Span (_, toks)) =
    if full then
      let val use_color = #color (get_cfg ())
          val render = if use_color then colorize_token else Token.unparse
      in flatten (implode (map render toks)) end
    else
      let val use_color = #color (get_cfg ())
          val render = if use_color then colorize_token else Token.unparse
          fun go _ [] = ("", false)
            | go remaining (tok :: rest) =
                let val w = size (flatten (Token.unparse tok))
                in if w > remaining then ("", true)
                   else let val (s, trunc) = go (remaining - w) rest
                        in (flatten (render tok) ^ s, trunc) end
                end
          val (text, truncated) = go 80 toks
      in if truncated then text ^ reset ^ "..." else text end;
end;

fun is_ignored (Command_Span.Span (Command_Span.Ignored_Span, _)) = true
  | is_ignored _ = false;

fun out s = TextIO.print (to_unicode s ^ "\n");

(* Format a raw text string using the same config as spans *)
fun fmt_text text =
  let val thy = Theory.get_pure ()
      val kws = Thy_Header.get_keywords thy
      val toks = Token.tokenize kws {strict = false} (Symbol_Pos.explode (text, Position.none))
      val span = Command_Span.Span (Command_Span.Malformed_Span, toks)
  in fmt_span (#full_spans (get_cfg ())) span end;


(** Segments **)

fun find_source thy_name =
  case ! stored_segments_probe of
    NONE => error ("No stored segments available in this heap. " ^
                   "The 'source' command requires a heap built with segment storage.")
  | SOME sv =>
      (case List.find (fn (n, _) => n = thy_name) (Synchronized.value sv) of
         SOME (_, segs) => segs
       | NONE => error ("No stored segments for " ^ quote thy_name ^
                        ". Available: " ^ commas (map #1 (Synchronized.value sv))));

fun source thy_name start stop =
  let val segs = find_source thy_name
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
                                    "  " ^ indent ^ "\027[90m" ^ span_text_full span ^ "\027[0m") else ())
               else out (prefix ^ StringCvt.padLeft #" " 4 (string_of_int i) ^
                         "  " ^ indent ^ fmt_span full_spans span)
             else ();
             pr (i + 1) rest)
            end
  in pr 0 segs end;


(** REPL core **)

datatype origin =
  From_Theory of string
| From_Segment of string * int
| From_REPL of string * int;

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

val repl_tab : repl Symtab.table Synchronized.var
  = Synchronized.var "Ir.repls" Symtab.empty;

val current_repl : string Synchronized.var
  = Synchronized.var "Ir.current_repl" "";

fun the_repl id =
  case Symtab.lookup (Synchronized.value repl_tab) id of
    SOME r => r
  | NONE => error ("No REPL " ^ quote id);

fun the_current () =
  let val id = Synchronized.value current_repl
  in if id = "" then error "No current REPL" else (id, the_repl id) end;

fun update_repl id r =
  Synchronized.change repl_tab (Symtab.update (id, r));

(* Execute Isar text against a state *)
fun exec_text text st =
  let val text = from_unicode text
      val thy = Toplevel.theory_of st
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
     Synchronized.change current_repl (K id);
     out ("Created REPL " ^ quote id ^ ", set as current")
  end;

fun fork id state_idx =
  let val _ = if Symtab.defined (Synchronized.value repl_tab) id
              then error ("REPL " ^ quote id ^ " already exists")
              else ()
      val (pid, parent) = the_current ()
      val steps = #steps parent
      val n = length steps
      (* Use same indexing as state: 0=base, 1=after step 0, ... *)
      val i = if state_idx < 0 then n + 1 + state_idx else state_idx
      val st = if i = 0 then #base_state parent
               else if i >= 1 andalso i <= n then #post_state (nth steps (i - 1))
               else error ("State " ^ string_of_int state_idx ^ " out of range (0.." ^
                           string_of_int n ^ ")")
      val r : repl = {origin = From_REPL (pid, i), base_state = st, steps = []}
  in update_repl id r;
     Synchronized.change current_repl (K id);
     out ("Forked REPL " ^ quote id ^ " from " ^ quote pid ^
          " at state " ^ string_of_int i ^ ", set as current")
  end;

fun focus id =
  (ignore (the_repl id);
   Synchronized.change current_repl (K id);
   out ("Focused on REPL " ^ quote id));

fun step text =
  let val (id, r) = the_current ()
      val pre = last_state r
      val post = exec_text text pre
      val s : repl_step = {text = text, pre_state = pre, post_state = post, stale = false}
      val r' : repl = {origin = #origin r, base_state = #base_state r,
                        steps = #steps r @ [s]}
  in update_repl id r';
     out (pretty_state post)
  end;

fun step_file path = step (File.read (Path.explode path));

fun state state_idx =
  let val (_, r) = the_current ()
      val steps = #steps r
      val n = length steps
      (* state 0 = base, state 1 = after step 0, ..., state n = after step n-1 *)
      val i = if state_idx < 0 then n + 1 + state_idx else state_idx
      val st = if i = 0 then #base_state r
               else if i >= 1 andalso i <= n then #post_state (nth steps (i - 1))
               else error ("State " ^ string_of_int state_idx ^ " out of range (0.." ^
                           string_of_int n ^ ")")
  in out (pretty_state st) end;

fun show () =
  let val (id, r) = the_current ()
      val cur_id = Synchronized.value current_repl
      val orig = case #origin r of
          From_Theory t => "theory " ^ t
        | From_Segment (t, i) => t ^ ":" ^ string_of_int i
        | From_REPL (p, i) => "REPL " ^ quote p ^ " state " ^ string_of_int i
      val n = length (#steps r)
      val _ = out ("REPL " ^ quote id ^
                   (if id = cur_id then " \027[1m(current)\027[0m" else "") ^
                   " (" ^ string_of_int n ^ " steps, from " ^ orig ^ ")")
      val _ = out ("  base  level=" ^ string_of_int (Toplevel.level (#base_state r)))
      fun pr _ [] = ()
        | pr i (({text, stale, pre_state, ...} : repl_step) :: rest) =
            let val stale_mark = if stale then " \027[31m[stale]\027[0m" else ""
                val lvl = Toplevel.level pre_state
                val indent = StringCvt.padLeft #" " (2 * lvl) ""
            in out ("  " ^ StringCvt.padLeft #" " 3 (string_of_int i) ^ "  " ^
                    indent ^ fmt_text text ^ stale_mark);
               pr (i + 1) rest
            end
  in pr 0 (#steps r) end;

fun text () =
  let val (_, r) = the_current ()
      val t = map #text (#steps r)
  in out (String.concatWith "\n" t) end;

fun replay () =
  let val (id, r) = the_current ()
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

fun edit idx new_text =
  let val (id, r) = the_current ()
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
     if #auto_replay (get_cfg ()) andalso not (null after_steps) then replay () else ()
  end;

fun truncate idx =
  let val (id, r) = the_current ()
      val steps = #steps r
      val _ = if idx < 0 orelse idx >= length steps
              then error ("Step " ^ string_of_int idx ^ " out of range") else ()
      (* Remove sub-REPLs attached to dropped steps *)
      val dropped = length steps - idx - 1
      val _ = Synchronized.change repl_tab (fn tab =>
        Symtab.fold (fn (rid, r') =>
          case #origin (r' : repl) of
            From_REPL (pid, si) =>
              if pid = id andalso si > idx then Symtab.delete rid else I
          | _ => I) tab tab)
      val r' : repl = {origin = #origin r, base_state = #base_state r,
                        steps = List.take (steps, idx + 1)}
  in update_repl id r';
     out ("Truncated to step " ^ string_of_int idx ^ ", dropped " ^
          string_of_int dropped ^ " steps")
  end;

fun merge () =
  let val (id, r) = the_current ()
      val (pid, pidx) =
        case #origin r of
          From_REPL (p, i) => (p, i)
        | _ => error ("REPL " ^ quote id ^ " is not a sub-REPL")
      val merged_text = String.concatWith "\n" (map #text (#steps r))
      (* Switch to parent, edit the step at the fork point *)
      val _ = Synchronized.change repl_tab (Symtab.delete_safe id)
      val _ = Synchronized.change current_repl (K pid)
      (* pidx is state index; step pidx has pre_state = state pidx *)
      val target = pidx
  in if target < length (#steps (the_repl pid))
     then (edit target merged_text;
           out ("Merged " ^ quote id ^ " into " ^ quote pid ^
                " (replaced step " ^ string_of_int target ^ ")"))
     else (step merged_text;
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
      val _ = if member (op =) to_remove (Synchronized.value current_repl)
              then (Synchronized.change current_repl (K "");
                    out "Current REPL was removed. Use Ir.focus or Ir.init to select another.")
              else ()
  in out ("Removed " ^ commas (map quote to_remove)) end;

fun repls () =
  let val cur_id = Synchronized.value current_repl
  in Symtab.fold (fn (id, r : repl) => fn () =>
    let val n = length (#steps r)
        val is_cur = id = cur_id
        val orig = case #origin r of
            From_Theory t => "theory " ^ t
          | From_Segment (t, i) => t ^ ":" ^ string_of_int i
          | From_REPL (p, i) => "REPL " ^ quote p ^ " state " ^ string_of_int i
        val stale = length (filter #stale (#steps r))
        val desc = id ^ " (" ^ string_of_int n ^ " steps" ^
            (if stale > 0 then ", " ^ string_of_int stale ^ " stale" else "") ^
            ", from " ^ orig ^ ")"
    in out (if is_cur then "  \027[1m> " ^ desc ^ "\027[0m" else "    " ^ desc)
    end) (Synchronized.value repl_tab) ()
  end;

fun theories () =
  List.app (fn s => out ("  " ^ s)) (Thy_Info.get_names ());

(* Sledgehammer via compiler bridge *)

fun find_theorems max_results query =
  let val st = last_state (snd (the_current ()))
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

fun sledgehammer timeout_secs =
  let val st = last_state (snd (the_current ()))
      val _ = Toplevel.proof_of st
      val thy = Toplevel.theory_of st
      val _ = sh_state_ref := st
      val _ = sh_timeout_ref := timeout_secs
      val buf = Unsynchronized.ref ([] : string list)
      fun capture ss = buf := implode ss :: !buf
      val old_writeln = ! Private_Output.writeln_fn
      val old_warning = ! Private_Output.warning_fn
      val code =
        "val _ = sh_result_ref := (let " ^
        "val prf = Toplevel.proof_of (! sh_state_ref) " ^
        "val params = Sledgehammer_Commands.default_params " ^
        "  (Proof_Context.theory_of (Proof.context_of prf)) " ^
        "  [(\"timeout\", Int.toString (! sh_timeout_ref))] " ^
        "val (_, (_, msg)) = Sledgehammer.run_sledgehammer params " ^
        "  Sledgehammer_Prover.Normal NONE 1 " ^
        "  Sledgehammer_Fact.no_fact_override prf " ^
        "in msg end)"
      val _ = Private_Output.writeln_fn := capture
      val _ = Private_Output.warning_fn := (K ())
      val result = Exn.capture (fn () =>
        Context.setmp_generic_context (SOME (Context.Theory thy)) (fn () =>
          ML_Compiler.eval ML_Compiler.flags Position.none
            (ML_Lex.tokenize code)) ()) ()
      val _ = Private_Output.writeln_fn := old_writeln
      val _ = Private_Output.warning_fn := old_warning
      val _ = Exn.release result
      val all_text = rev (!buf) |> String.concatWith "\n"
      val lines = String.fields (fn c => c = #"\n") all_text
      val tries = filter (fn l => String.isSubstring "Try this" l) lines
  in if null tries then out all_text
     else List.app out tries
  end;

fun help () = out
  "=== I/R API ===\n\
  \\n\
  \  Sessions start in the context of a named theory -- do NOT issue\n\
  \  'theory' commands. Steps are Isar: lemma, definition, fun, by, etc.\n\
  \\n\
  \  init id [specs]    create REPL from [\"Theory\"], [\"Theory:idx\"],\n\
  \                     or [\"T1\",\"T2\",...] (merges theories)\n\
  \  fork id state_idx  fork sub-REPL from current at state (~1=latest)\n\
  \  focus id           switch current REPL\n\
  \  step \"isar text\"   append step to current REPL\n\
  \  step_file path     append step from file (supports unicode)\n\
  \  show ()            describe current REPL (origin, steps, staleness)\n\
  \  state idx          show Toplevel.state (0=base, 1=after step 0, ~1=latest)\n\
  \  text ()            print concatenated text of current REPL\n\
  \  edit idx \"text\"    edit step, replay if auto_replay=true\n\
  \  replay ()          re-execute stale steps\n\
  \  truncate idx       discard steps after idx\n\
  \  merge ()           inline current sub-REPL into parent\n\
  \  sledgehammer secs  run sledgehammer on current proof state\n\
  \  find_theorems n q  search theorems (n=max results, 0=unlimited)\n\
  \  timeout secs       set step timeout (0=unlimited, default 5s)\n\
  \  remove id          remove REPL and its sub-REPLs\n\
  \  repls ()           list all REPLs\n\
  \  theories ()   list loaded theories\n\
  \  source thy s e   list command spans (s e = range, ~N = from end)\n\
  \  config f           update config: color, show_ignored, full_spans,\n\
  \                     show_theory_in_source, auto_replay\n\
  \  help ()            this help\n\
  \\n\
  \=== Quick start ===\n\
  \\n\
  \  Ir.init \"R\" [\"MySession.MyTheory\"];\n\
  \  Ir.step \"lemma \\\"True\\\"\";\n\
  \  Ir.step \"by simp\";\n\
  \  Ir.show ();\n\
  \  Ir.state ~1;\n\
  \\n\
  \=== Forking and merging ===\n\
  \\n\
  \  Ir.step \"lemma \\\"P\\\"\";\n\
  \  Ir.step \"sorry\";\n\
  \  Ir.fork \"S\" 1;          (* fork from state before sorry *)\n\
  \  Ir.step \"by auto\";\n\
  \  Ir.merge ();             (* replace sorry with proof *)\n\
  \\n\
  \=== Editing ===\n\
  \\n\
  \  Ir.edit 0 \"lemma \\\"Q\\\"\";  (* edit first step, replays rest *)\n\
  \  Ir.truncate 1;             (* keep only steps 0 and 1 *)\n\
  \\n\
  \=== Segments (stored theories) ===\n\
  \\n\
  \  Ir.source \"MySession.MyTheory\" 0 ~1;  (* all *)\n\
  \  Ir.source \"MySession.MyTheory\" 0 10;  (* first 11 *)\n\
  \  Ir.init \"R\" [\"MySession.MyTheory:42\"];    (* from source 42 *)";

end;

val _ = writeln (case ! stored_segments_probe of
    NONE => "Ir: source commands not available (heap has no stored segments)"
  | SOME sv =>
      let val n = length (Synchronized.value sv)
      in if n = 0 then "Ir: source commands not available (no theories stored)"
         else "Ir: source commands available (" ^ string_of_int n ^ " theories)"
      end);
