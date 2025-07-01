(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature CRUSH_TACTICALS =
sig  
  (* Run a tactic if the goal satisfies a predicate. Fail if it does not *)
  val IF : (term -> bool) -> tactic -> tactic
  (* Run a goal-tactic if the goal satisfies a predicate. Fail if it does not *)
  val IF' : (term -> bool) -> (int -> tactic) -> (int -> tactic)
  (* Run a tactic if the goal satisfies a predicate. Do nothing if not *)
  val IF_OK : (term -> bool) -> tactic -> tactic
  (* Run a goal-tactic if the goal satisfies a predicate. Do nothing if not *)
  val IF_OK' : (term -> bool) -> (int -> tactic) -> (int -> tactic)
  (* Run tactic on current goal if _some_ goal passes filter *)
  val IF_ANY_GOAL' : (term -> bool) -> (int -> tactic) -> (int -> tactic)

  val IF_with_param' : (term -> 'a option) -> ('a -> int -> tactic) -> (int -> tactic)
 
  (* Log and report runtime of successful invocations of tactic *)
  val LOG : Proof.context -> bool -> string -> tactic -> tactic
  val LOG' : Proof.context -> bool -> string -> (int -> tactic) -> (int -> tactic)

  val DEBUG_BEFORE_AFTER : (thm -> thm -> unit) -> tactic -> tactic
  val DEBUG_BEFORE_AFTER' : (term -> term option -> unit) -> (int -> tactic) -> (int -> tactic)

  val LOG_pos : Proof.context -> Position.T -> bool -> string -> logger -> tactic -> tactic
  val LOG_pos' : Proof.context -> Position.T -> bool -> string -> logger -> (int -> tactic) -> (int -> tactic)

  (* Log and report runtime of successful and failed invocations of tactic *)
  val LOGFULL : Proof.context -> bool -> string -> tactic -> tactic
  val LOGFULL' : Proof.context -> bool -> string -> (int -> tactic) -> (int -> tactic)

  (* Evaluate a tactic only upon first call -- normally, this would need 'a lazy, but
     we can re-use the lambda for the goal number *)
  val LAZY' : (unit -> int -> tactic) -> int -> tactic

  (* Repeat a tactic until the total number of subgoals has been decreased. *)
  val DWELL : tactic -> tactic
  (* Repeat a tactic on a subgoal until the total number of subgoals has been decreased *)
  val DWELL' : (int -> tactic) -> (int -> tactic)

  (* Run two tactics and stop at point of divergence *)
  val DIVERGENCE : Proof.context -> tactic -> tactic -> tactic

  (* Tactic printing a string but doing nothing else *)
  val log_tac : string -> tactic

  (* all_tac, but allows to run an arbitrary function on the goal
     state, e.g. for printing *)
  val all_tac': (term -> unit) -> int -> tactic

  (* Guard method by goal predicate *)
  val guard_method : (Proof.context -> term -> bool) -> Method.method -> Method.method

  exception SMART of string
  val REPEAT_SMART: Proof.context -> logger -> bool -> (logger -> tactic) -> tactic
  val repeat_smart_method : logger -> bool -> Method.method -> Method.method

  (* Keep rotating subgoals until method succeeds *)
  val method_first: Method.method -> Method.method
  val method_first': (Proof.context -> Method.method) -> (Proof.context -> Method.method)

  val mepo_focused_tac: bool -> int -> Proof.context -> (int -> tactic) -> (int -> tactic)
  val mepo_focused_method: bool -> int -> Method.method -> Method.method
end;

structure Crush_Tacticals: CRUSH_TACTICALS =
struct

  fun IF' (guard : term -> bool) (t :int -> tactic) : int -> tactic =
    SUBGOAL (fn (goal, i) => if guard goal then t i else no_tac)

  fun IF_OK' (guard : term -> bool) (t :int -> tactic) : int -> tactic =
    SUBGOAL (fn (goal, i) => if guard goal then t i else all_tac)

  fun IF_with_param' (guard : term -> 'a option) (t: 'a -> int -> tactic) : int -> tactic =
    SUBGOAL (fn (goal, i) => case guard goal of NONE => no_tac | SOME x => t x i)

  fun IF_ANY_GOAL' (guard : term -> bool) (t :int -> tactic) : int -> tactic = fn i => 
    (fn thm => 
      if thm |> Thm.prems_of |> List.exists guard then
        t i thm
      else
        Seq.empty)

  fun LAZY' eval_tac = 
    let val lazy_tac = Lazy.lazy eval_tac in
      fn i => fn thm => Lazy.force lazy_tac i thm
    end

  fun IF (guard : term -> bool) (t : tactic) : tactic =
    IF' guard (K t) |> HEADGOAL

  fun IF_OK (guard : term -> bool) (t : tactic) : tactic =
    IF_OK' guard (K t) |> HEADGOAL

  val log_tac : string -> tactic = fn msg => fn st =>
    ((msg |> tracing); Seq.single st)

  val all_tac' : (term -> unit) -> int -> tactic = fn f =>
    SUBGOAL (fn (goal, _) => ((f goal); all_tac))

  fun DEBUG_BEFORE_AFTER (f: thm -> thm -> unit) (tac : tactic) st =
     Seq.map (fn st' => (f st st'; st')) (tac st)
  
  fun DEBUG_BEFORE_AFTER' (f: term -> term option -> unit) (tac: int -> tactic) (i: int) =
     DEBUG_BEFORE_AFTER (fn st => fn st' => let
       val goal_old = Thm.prem_of st i
       val goal_new = 
          if Thm.nprems_of st' < Thm.nprems_of st then NONE else
          SOME (Thm.prem_of st' i)
     in
       f goal_old goal_new
     end) (tac i)

  val time_to_str = fn t => (t |> #elapsed |> Time.fmt 6) ^ "s"

  fun LOG_pos (ctxt : Proof.context) (pos : Position.T) (enable : bool) 
    : string -> logger -> tactic -> tactic =
    let val log_goal = Config.get ctxt Crush_Config.log_goal in
    if not enable then K (K I) else fn msg => fn log => fn tac =>
      let val cb = fn (t : thm) => fn (t' : thm option) => fn (time : Timing.timing) => fn success => 
             if success then 
               [Pretty.mark_str (Markup.properties (Position.properties_of pos) Markup.position, msg), 
                 Pretty.brk 1, Pretty.str "success", Pretty.brk 1,
                 Pretty.enclose "(" ")" (time |> time_to_str |> Pretty.text)]
                @ (if log_goal then 
                    [Pretty.fbrk,
                      [Pretty.str "Before:", Pretty.brk 1, Thm.major_prem_of t |> Syntax.pretty_term ctxt] |> Pretty.item,
                     Pretty.fbrk,
                      [Pretty.str "After:", Pretty.brk 1] @
                       ([Thm.major_prem_of (Option.valOf t') |> Syntax.pretty_term ctxt]
                        handle THM _ => Pretty.text "Done") |> Pretty.item]
                   else [])                 
                 |> Pretty.text_fold |> log
             else ()
      in
         Crush_Time.time_seq cb tac
      end
    end

  val LOG = fn ctxt => fn enable => fn msg => LOG_pos ctxt Position.none enable msg default_logger

  fun LOGFULL (ctxt : Proof.context) (enable : bool) : string -> tactic -> tactic =
    if not enable then K I else fn msg => fn tac =>
      let val ptac_start : tactic = print_tac ctxt ("Evaluating " ^ msg ^ "...")
          val ptac_end : tactic = print_tac ctxt ("After evalution of " ^ msg)
          val cb = fn (_ : thm) => fn (_ : thm option) => fn (time : Timing.timing) => fn success => 
             if success then 
               (msg ^ " success (" ^ (time |> time_to_str) ^ ")" |> tracing)
             else
               (msg ^ " fail (" ^ (time |> time_to_str) ^ ")" |> tracing)
      in
         ptac_start THEN Crush_Time.time_seq cb tac THEN ptac_end
      end

  fun LOG_pos' (ctxt : Proof.context) (pos : Position.T) (enable : bool) : string -> logger -> (int -> tactic) -> (int -> tactic) =
     let val l = LOG_pos ctxt pos enable in fn msg => fn log => fn t => l msg log o t end

  val LOG' = fn ctxt => fn enable => fn msg => LOG_pos' ctxt Position.none enable msg default_logger

  fun LOGFULL' (ctxt : Proof.context) (enable : bool) : string -> (int -> tactic) -> (int -> tactic) =
     let val l = LOGFULL ctxt enable in fn msg => fn t => l msg o t end

  \<comment>\<open>Repeat a tactic until the total number of subgoals has been decreased.\<close>
  val DWELL : tactic -> tactic = fn t => fn st =>
      let val n = Thm.nprems_of st in
        REPEAT_DETERM1 (COND (has_fewer_prems n) no_tac t) st
      end

  \<comment>\<open>Repeat a tactic on a subgoal until the total number of subgoals has been decreased\<close>
  fun DWELL' (t : int -> tactic) = DWELL o t

  fun DIVERGENCE (ctxt : Proof.context) (tacA : tactic) (tacB: tactic) : tactic = fn st =>
     let val _ = "Evaluating tactic divergence..." |> Pretty.text |> Pretty.block |> Pretty.writeln
         fun core (base : int) (st : thm) : thm Seq.seq =
           let val opt_stA0 = SINGLE tacA st
               val opt_stB0 = SINGLE tacB st
           in
             case (opt_stA0, opt_stB0) of
                 (SOME stA0, SOME stB0) =>
                   if is_unifiable_pair ctxt (Thm.prop_of stA0) (Thm.prop_of stB0) then
                     let val _ = "Still equal after step " ^ (base |> Int.toString) |> tracing in
                     core (base + 1) stA0 end
                   else
                     let val _ = "Different goals emerging at step " ^ (base |> Int.toString) ^ ". " ^
                       "Showing last common state. Use `back` to see proof state when applying LHS, " ^
                       "and `back back` to see proof state when applying RHS." |>
                          Pretty.text |> Pretty.block |> Pretty.writeln
                     in
                     Seq.append (Seq.single st) (Seq.append (Seq.single stA0) (Seq.single stB0)) end
               | (NONE, NONE) => let val _ = "No difference" |> tracing in Seq.single st end
               | (SOME stA0, NONE) => let val _ = "LHS succeeds at step " ^ (base |> Int.toString) ^
                   ", but RHS fails. Showing last commong proof state. Use `back` to see proof state " ^
                   "when applying LHS." |>
                      Pretty.text |> Pretty.block |> Pretty.writeln 
                   in Seq.append (Seq.single st) (Seq.single stA0) end
               | (NONE, SOME stB0) => let val _ = "RHS succeeds at step " ^ (base |> Int.toString) ^
                   ", but LHS fails. Showing last commong proof state. Use `back` to see proof state " ^
                   "when applying RHS." |>
                      Pretty.text |> Pretty.block |> Pretty.writeln 
                   in Seq.append (Seq.single st) (Seq.single stB0) end
           end
     in
        core 0 st
     end

  fun guard_method (guard : Proof.context -> term -> bool) (m : Method.method) : Method.method =
     (fn thms => fn (ctxt, st) =>
        if Thm.nprems_of st = 0 orelse (guard ctxt (Thm.major_prem_of st)) then
          m thms (ctxt, st)
        else
          Seq.empty)

  fun intlist_to_string ls = "[" ^ (fold (fn i => fn s => s ^ " " ^ (i |> Int.toString)) ls "") ^ " ]"

  exception SMART of string
  fun REPEAT_SMART (ctxt : Proof.context) (log : logger) (aggressive : bool) (m : logger -> tactic) : tactic = let

     fun debug lvl = if lvl <= (Config.get ctxt Crush_Config.debug_level)  then tracing else K ()
     val m = if Config.get ctxt Crush_Config.do_big_steps then DWELL o m else m
     val gas = Config.get ctxt Crush_Config.gas

     fun error msg = msg |> tracing

     fun subgoals_have_changed st st' (i,j) =
       let val goal_i = List.nth (Thm.prems_of st, i-1)
           val goal_j = List.nth (Thm.prems_of st', j-1)
       in
         not (Envir.aeconv (goal_i, goal_j))
       end

    fun rotate_goal_adjust_indices i (st, is) =
      if i = 1 then (st, is) else
      let
        val _ = if Thm.nprems_of st < i then raise SMART ("Invalid goal number") else ()
        val st' = st |> Thm.permute_prems (i-1) 1 |> Thm.permute_prems 0 ~1
        fun adjust_idx j = if j < i then j + 1 else if j > i then j else 1
        val is' = List.map adjust_idx is
      in
        (st', is')
      end

    fun insert_goals_adjust_idxs inserted = List.map (fn j => j + inserted)

    fun list_contains_not [] _ = true
      | list_contains_not (x :: xs) x0 =
          if x = x0 then false else list_contains_not xs x0

     fun run_smart (_ : int) (st : thm) [] = (Seq.single (st, false) : (thm * bool) Seq.seq)
       | run_smart count st (i :: is) = if count >= gas then Seq.empty else Seq.make (fn _ =>
           let
             val log' = fn pp => 
               [Pretty.enclose "[" "]" [count |> Int.toString |> Pretty.str], Pretty.brk 1, pp]
               |> Pretty.block |> log
             val _ = "step: "     ^ (count |> Int.toString)                ^ ", " ^
                     "goal: "     ^ (i |> Int.toString)                    ^ ", " ^
                     "goals: "    ^ (st |> Thm.nprems_of |> Int.toString)  ^ ", " ^
                     "worklist: " ^ (intlist_to_string is) |> debug 0
             val (st, is) = rotate_goal_adjust_indices i (st, is)
             val (res, abort) = ((m log' st |> Seq.pull, false) handle SMART _ => (NONE, true))
           in if abort then (error ("inner tactic raised stop exception at step " ^ (Int.toString count));
                             SOME ((st, false), Seq.empty)) else
             case res of
               NONE => (* If it didn't work, we proceed with the rest of the goals *)
                 if aggressive then
                    Seq.pull (run_smart count st is)
                 else let
                   (* Check if the current goal contains a schematic *)
                   fun get_schematics t = Term.add_var_names t []
                   val prems = Thm.prems_of st
                   val cur_goal = hd prems
                   val cur_schematics = get_schematics cur_goal
                   in
                     if List.length cur_schematics = 0 then SOME ((st, false), Seq.empty)
                     else let
                       fun lists_intersect [] _ = false
                         | lists_intersect (x::xs) ys = (* improve perf? *)
                             exists (fn y => x=y) ys orelse lists_intersect xs ys
                       fun share_schematic i =
                          lists_intersect (i - 1 |> curry List.nth prems |> get_schematics) (cur_goal |> get_schematics)
                       val is' = List.filter share_schematic is
                       in
                         Seq.pull (run_smart count st is')
                       end
                    end
             | SOME (st', _) => let (* Success case *)
                 val nprems_old  = Thm.nprems_of st
                 val nprems_new  = Thm.nprems_of st'
                 val n_new_goals = nprems_new - nprems_old
                 val not_is_old = filter (list_contains_not is) (range_of_nats_base 2 (nprems_old-1))
                 val not_is_new = insert_goals_adjust_idxs n_new_goals not_is_old
                 val changed = (not_is_old, not_is_new) |> op ~~
                               |> List.filter (subgoals_have_changed st st') |> List.map snd

                 (* Add inserted subgoals to worklist *)
                 val is'  = insert_goals_adjust_idxs n_new_goals is
                 (* Add changed subgoals to worklist *)
                 val is'' = (range_of_nats_base 1 (n_new_goals+1)) @ changed @ is'

                 val _ = "Goals before: "     ^ (nprems_old |> Int.toString) |> debug 1
                 val _ = "Goals after: "      ^ (nprems_new |> Int.toString) |> debug 1
                 val _ = "Worklist: "         ^ (intlist_to_string is)       |> debug 1
                 val _ = "Worklist shifted: " ^ (intlist_to_string is')      |> debug 1
                 val _ = "New worklist: "     ^ (intlist_to_string is'')     |> debug 1
                 in
                   SOME ((st', true), run_smart (count+1) st' is'')
                 end
           end)
   in
     fn st => let
       val initial_worklist = range_of_nats_base 1 (Thm.nprems_of st)
       val results = run_smart 0 st initial_worklist
     in
       if Config.get ctxt Crush_Config.keep_history then
         let val results = Seq.list_of results
           val changes = results |> List.filter #2 in
         if List.length changes > 0 then
            results |> map #1 |> rev |> Seq.of_list
         else
            Seq.empty
         end
       else if Config.get ctxt Crush_Config.stepwise then
         results |> Seq.map #1
       else
         let val results = Seq.list_of results
           val changes = results |> List.filter #2 in
         if List.length changes > 0 then
            Seq.single (List.last results |> #1)
         else
            Seq.empty
         end
     end
   end

   fun repeat_smart_method (log : logger) (aggressive : bool) (m : Method.method) : Method.method =
      context_tactic_to_method' (fn thms => fn ctxt =>
        REPEAT_SMART ctxt log aggressive (K (method_to_tac' m thms ctxt)))

  fun method_first (m : Method.method) : Method.method = (fn thms => fn (ctxt, st) =>
    let fun try_with_rotated_subgoals i = fn (ctxt', st') =>
         let val s = m thms (ctxt', Thm.permute_prems 0 i st') in
           Seq.THEN (K s, ("Succeeded on subgoal " ^ (Int.toString i) |> tracing; Seq.succeed)) ()
         end
        val nprems = Thm.nprems_of st in
      if nprems > 0 then
        Seq.FIRST (map try_with_rotated_subgoals (range_of_nats nprems)) (ctxt, st)
      else
        m thms (ctxt, st)
    end)

  fun method_first' (m : Proof.context -> Method.method) : (Proof.context -> Method.method) = 
     m #> method_first

  val _ = Theory.setup (Method.setup @{binding "first"} (Scan.lift (Parser.parse_method >> method_first')) "")

  fun mepo_focused_tac_filter (max_facts: int) (ctxt: Proof.context) (t: int -> tactic) = 
    MePo_Prem.ignore_irrelevant_prems_tac ctxt max_facts
    THEN' (t THEN_ALL_NEW (
      MePo_Prem.unignore_tac ctxt))

  fun mepo_focused_tac_drop (max_facts: int) (ctxt: Proof.context) (t: int -> tactic) = 
    MePo_Prem.drop_irrelevant_prems_tac ctxt max_facts THEN' t

  fun mepo_focused_tac (drop: bool) = 
    if drop then mepo_focused_tac_drop else mepo_focused_tac_filter

  fun mepo_focused_method (drop: bool) (max_facts: int) (method: Method.method) =
    (fn ctxt => 
         method
      |> method_to_tac
      |> (fn t => t ctxt)
      |> K
      |> mepo_focused_tac drop max_facts ctxt
      |> (fn t => t 1)) |> context_tactic_to_method

  val _ = Theory.setup (Method.setup @{binding "focused"} (Scan.lift (
     (Scan.optional (Args.$$$ "drop" >> (K true)) false --
     Scan.optional  (Parse.nat >> SOME) NONE --
     Parser.parse_method) >> (fn ((drop,max_facts_opt),method) => fn (ctxt : Proof.context) =>
       let 
          val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
       in
         mepo_focused_method drop max_facts (method ctxt)
       end))) "")

end;

local
  val guard_parser : (Proof.context -> Method.method) context_parser = 
    Scan.lift ( (Parser.parse_term_filter -- Parser.parse_method) >> (
       fn (guard, method) => fn ctxt => 
           Crush_Tacticals.guard_method guard (method ctxt)))

  val _ = Theory.setup (Method.setup @{binding "guard"} guard_parser "")

  val _ = Theory.setup (Method.setup @{binding "repeat_smart"}
          (Scan.lift (Parser.parse_method >> (fn method => fn ctxt =>  
             Crush_Tacticals.repeat_smart_method default_logger true (method ctxt)))) "" )

  val _ = Theory.setup (Method.setup @{binding "repeat_smart_failfast"}
          (Scan.lift (Parser.parse_method >> (fn method => fn ctxt =>  
             Crush_Tacticals.repeat_smart_method default_logger false (method ctxt)))) "" )

  val _ = Theory.setup (Method.setup @{binding "divergence"}
          (Scan.lift (Parser.parse_method -- Parser.parse_method >> (fn (mA,mB) => fn ctxt =>  
             let val tA = method_to_tac (mA ctxt) ctxt
                 val tB = method_to_tac (mB ctxt) ctxt 
             in SIMPLE_METHOD (Crush_Tacticals.DIVERGENCE ctxt tA tB) end))) "")

  val _ = Theory.setup (Method.setup @{binding "log"}
          (Scan.lift ( Parse.string >> (fn txt => fn _ =>
             (fn _ => ("LOG: " ^ txt |> tracing; all_tac)) |> SUBGOAL |> SIMPLE_METHOD'))) "")

fun report_back () =
  Output.report [Markup.markup (Markup.bad ()) "Single-stepping"];

datatype StepType = 
    StepSingle  (* Run a single step *)
  | StepN of int (* Run n steps *)
  | StepUntilGoalPattern of Proof.context -> term -> bool (* Run until filter passes *)
  | StepUntilSchematicAppears of indexname (* Run until a named schematic appears *)
  | StepAll (* Run until finished *)

(* This is technically the same as backtracking, but conceptually different, so give
   it a different name. *)
val scan_step_args = 
  Scan.optional (
       (Parse.int >> StepN)
    || (Args.$$$ "*" |-- Scan.succeed StepAll) 
    || (Args.$$$ "to" |-- Args.$$$ "goal" |-- Args.$$$ "pattern" |--
          Parser.parse_goal_filter_pattern >> StepUntilGoalPattern)
    || (Args.$$$ "to" |-- Args.$$$ "premise" |-- Args.$$$ "pattern" |--
          Parser.parse_premise_filter_pattern >> StepUntilGoalPattern)
    || (Args.$$$ "to" |-- Args.$$$ "schematic" |-- (Parse.string -- (Scan.optional Parse.int 0))) >> StepUntilSchematicAppears
  ) StepSingle   

fun repeat_until_error (f : 'a -> 'a) = fn x =>
  repeat_until_error f (f x)
  handle ERROR _ => x

fun repeat_until_cond (cond : 'a -> bool) (f : 'a -> 'a) = fn x =>
  if cond x then
    x
  else
    repeat_until_cond cond f (f x)
  handle ERROR _ => x

fun step_proof (pf : Proof_Node.T) : Proof_Node.T =
  Proof_Node.back pf 
  handle ERROR _ => error "Tactic finished"

fun proof_node_back_iter (n : int) (pf: Proof_Node.T) : Proof_Node.T =
  case n of 
     0 => pf
   | n => proof_node_back_iter (n - 1) (step_proof pf)

val proof_node_to_context = Proof_Node.current #> Proof.goal #> #context
val proof_node_to_goal = Proof_Node.current #> Proof.goal #> #goal

fun goal_filter_to_proof_node_filter (f : Proof.context -> term -> bool) (pf : Proof_Node.T) : bool =
  let
    val goal = pf |> proof_node_to_goal
    val ctxt = pf |> proof_node_to_context
    val stop_condition = goal |> Thm.prems_of |> List.exists (f ctxt)
  in
    if stop_condition then
      (Pretty.text "Goal filter applies" |> Pretty.block |> Pretty.string_of |> Output.information; true)
    else
      false
  end

fun schematic_is_present (idx : indexname) = 
  (fn t => Term.is_Var t andalso (t |> Term.dest_Var |> fst) = idx) |> Term.exists_subterm 

fun proof_node_step (st : StepType) (pf : Proof_Node.T) : Proof_Node.T = 
  case st of
     StepSingle => step_proof pf
   | StepN n => proof_node_back_iter n pf
   | StepUntilGoalPattern cond => repeat_until_cond (goal_filter_to_proof_node_filter cond) step_proof pf
   | StepAll => repeat_until_error step_proof pf
   | StepUntilSchematicAppears v => 
       repeat_until_cond (goal_filter_to_proof_node_filter (K (schematic_is_present v))) step_proof pf

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>step\<close> "step through tactic"
    (scan_step_args >>
     (fn st => Toplevel.actual_proof (fn prf => (report_back (); proof_node_step st prf)) o
      Toplevel.skip_proof report_back));

in end