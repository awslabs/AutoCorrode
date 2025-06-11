(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature CRUSH_BASE =
sig
  type logger = Pretty.T -> unit
  val default_logger: logger

  \<comment>\<open>Convert a context-dependent tactic to a \<^verbatim>\<open>context_tactic\<close>.\<close>
  val context_tactic_to_context_tactic : (Proof.context -> tactic) -> context_tactic
  val context_tactic_to_context_tactic' : context_tactic -> (Proof.context -> tactic)
  \<comment>\<open>Convert a context-dependent tactic to a \<^verbatim>\<open>method\<close>.\<close>
  val context_tactic_to_method : (Proof.context -> tactic) -> Method.method
  val context_tactic_to_method' : (thm list -> Proof.context -> tactic) -> Method.method

  val context_transform_as_method : (Proof.context -> Proof.context) -> context_tactic

 \<comment>\<open>Convert a method to a tactic.
    WARNING: This ignores any change to the proof context that the method may have made,
             but which raw tactics don't support.\<close>
 val method_to_tac : Method.method -> Proof.context -> tactic
 val method_to_tac' : Method.method -> thm list -> Proof.context -> tactic

 (* lookup method by name *)
 val get_method : string -> Proof.context -> Method.method
 (* lookup method by name, return as tactic *)
 val get_method_as_tac: string -> Proof.context -> tactic

 (* strip away universal quantifiers at the meta level, replacing bound variables by
    free variables. *)
 val strip_meta_all : term -> term
 (* strip away meta quantification and premises *)
 val find_metaimp_conclusion : term -> term
 (* strip away meta and HOL quantifications and premises *)
 val find_conclusion : term -> term
 val find_conclusions : term -> term list

 (* checks whether the meta conclusion of the given term satisfies the given pattern;
  * pattern is expected to of type bool *)
 val metagoal_satisfies_pattern: string -> Proof.context -> term -> bool
 (* checks whether some pure premise of the given term satisfies the given pattern;
  * pattern must be of type bool *)
 val premise_satisfies_pattern: string -> Proof.context -> term -> bool

 (* Primitive term to string conversion -- omitting a lot of details *)
 val print_term : term -> string
 (* Some useful abbreviations *)
 val pwriteln : Pretty.T -> unit
 val pretty_term : Proof.context -> term -> Pretty.T
 val pretty_cterm : Proof.context -> cterm -> Pretty.T

 val is_unifiable_pair : Proof.context -> term -> term -> bool

 (* range_of_nats_base a n = [a,...,a+n-1] *)
 val range_of_nats_base : int -> int -> int list
 (* range_of_nats n = [0,...,n-1] *)
 val range_of_nats : int -> int list

 (* apply conversion under a Trueprop *)
 val prop_conv : conv -> conv
 (* try to apply conversion under Trueprop, otherwise apply conversion as-is *)
 val maybe_prop_conv : conv -> conv

 (* map HOL equalities to meta equalities; leave meta equalities unchanged *)
 val force_meta_eq : thm -> thm
 val force_meta_eqs : thm list -> thm list

 \<comment>\<open>Eta expand definitional theorem so there's no toplevel \<^verbatim>\<open>\<lambda>x. _\<close> on the RHS\<close>
 val eta_expand: thm -> thm 
 val eta_expands: thm list -> thm list  

 val intro_tac : thm list -> Proof.context -> int -> tactic
 val elim_tac : thm list -> Proof.context -> int -> tactic

 val safe_unfold_tac' : Proof.context -> thm list -> thm list -> int -> tactic
 val safe_simp_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic
 val safe_simp_no_asm_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic
 val safe_simp_no_asm_use_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic
 val safe_simp_no_asm_simp_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic

 val safe_unfold_tac : Proof.context -> thm list -> int -> tactic
 val safe_simp_only_tac : Proof.context -> thm list -> int -> tactic
 val safe_simp_no_asm_only_tac : Proof.context -> thm list -> int -> tactic
 val safe_simp_no_asm_use_only_tac : Proof.context -> thm list -> int -> tactic
 val safe_simp_no_asm_simp_only_tac : Proof.context -> thm list -> int -> tactic

 (* add simp trace *)
 val crush_simp_trace_setup : theory -> theory

 (* run a context-dependent conversion top down, but don't go past binders *)
 val stop_at_binder : (Proof.context -> conv) -> (Proof.context -> conv)
 (* run a context-dependent conversion top down, but don't go past quantifiers *)
 val stop_at_quantifier : (Proof.context -> conv) -> (Proof.context -> conv)

 (* like Conv.top_sweep_conv, but does not go inside binders *)
 val top_sweep_conv_no_bind : (Proof.context -> conv) -> (Proof.context -> conv)
 (* like Conv.top_sweep_conv, but does not go inside quantifiers *)
 val top_sweep_conv_no_quant : (Proof.context -> conv) -> (Proof.context -> conv)
 (* like Conv.top_sweep_conv, but provides base-conversion with the set of bound variables. *)
 val top_sweep_conv_with_info : (cterm list -> Proof.context -> conv) -> Proof.context -> conv

 (* converts a term filter to a conversion which fails or leave the term unchanged *)
 val filter_to_conv : (cterm -> bool) -> conv

 (* fails if the current context contains identical assumptions, no-op otherwise *)
 val fail_if_dup_assms_tac : Proof.context -> int -> tactic
 val remove_duplicate_tac : Proof.context -> int -> tactic

 (* thin_tac0 ctxt i removes first premise from i-th subgoal *)
 val thin_tac0 : Proof.context -> int -> tactic
 (* thin_tac_idx ctxt j i removes the j-th premise from the i-th subgoal *)
 val thin_tac_idx : Proof.context -> int -> int -> tactic
 (* like thin_tac_idx, but removing a list of premises; the premise indices
    must be in ascending order *)
 val thin_tac_idxs : Proof.context -> int list -> int -> tactic

 (* print_premise_tac j i prints the j-th premise of the i-th subgoal *)
 val print_premise_tac : Proof.context -> int -> int -> tactic

 (* solve goal by assumption *)
 val assm_tac : Proof.context -> int -> tactic

 val assert : bool -> unit
 val assert_not : bool -> unit
 val assert_eq : bool -> bool -> unit

 (* Checks if goal is a schematic equality which cannot be solved due to
    lack of parametricity in the schematic variable. If so, it fails; otherwise,
    it does nothing. *)
 val check_bad_schematic_equality_tac' : Proof.context -> bool -> int -> tactic
 (* Like check_bad_schematic_equality_tac', but checking all goals *)
 val check_bad_schematic_equality_tac : Proof.context -> bool -> tactic

 (* instantiate a schematic from a HOL or meta equality *)
 val instantiate_schematic_from_equality: Proof.context -> int -> tactic
 val instantiate_schematic_from_pure_equality: Proof.context -> int -> tactic
 val instantiate_schematic_from_hol_equality: Proof.context -> int -> tactic

end;

structure Crush_Base: CRUSH_BASE =
struct
  type logger = Pretty.T -> unit
  val default_logger : logger = Pretty.writeln

  exception ASSERT
  fun assert v = if v then () else raise ASSERT
  fun assert_not v = assert (not v)
  fun assert_eq v0 v1 = assert (v0 = v1)

  fun context_transform_as_method (t : Proof.context -> Proof.context) : context_tactic =
    fn (ctxt, thm) => (t ctxt, thm) |> Seq.single |> Seq.make_results

  fun simp_trace_apply ({unconditional=_, cterm, thm, rrule=_}) ctxt cont =
    if Config.get ctxt Crush_Config.crush_simp_trace_enable then (
     "Simplifier invoked on the following term" |> tracing;
     cterm |> Thm.term_of |> Syntax.pretty_term ctxt |> Pretty.writeln;
     "Theorem" |> tracing;
     thm |> Thm.prop_of |> Syntax.pretty_term ctxt |> Pretty.writeln;
     cont ctxt
    ) else cont ctxt

  val simp_trace_invoke = fn {depth=(_:int), cterm=(_:cterm)} => I
  fun simp_trace_simproc {name=(_:string), cterm=(_:cterm)} (ctxt : Proof.context) cont =
     cont ctxt

  val crush_simp_trace_setup =
    Raw_Simplifier.set_trace_ops {trace_rrule = simp_trace_apply, trace_invoke=simp_trace_invoke,
      trace_simproc=simp_trace_simproc}

  val assm_tac = fn ctxt =>
    eresolve_tac ctxt @{thms ASSUMPTION_D asm_rl}

  val print_premise_tac : Proof.context -> int -> int -> tactic = fn ctxt => fn j =>
    SUBGOAL (fn (goal, _) =>
       ((List.nth (Logic.strip_imp_prems goal, j) |> Syntax.pretty_term ctxt |> Pretty.writeln);
        all_tac))

  val thin_tac0 : Proof.context -> int -> tactic = fn ctxt =>
    DETERM o (eresolve_tac ctxt [thin_rl])

  val thin_tac_idx = fn ctxt => fn j =>
     if j = 0 then thin_tac0 ctxt else
     rotate_tac j THEN' thin_tac0 ctxt THEN' rotate_tac (~j)

  val thin_tac_idxs = fn ctxt => fn js =>
     EVERY' (List.map (thin_tac_idx ctxt) (rev js))

  fun context_tactic_to_context_tactic (t: Proof.context -> tactic) : context_tactic =
      fn (ctxt, thm) => (t ctxt thm |> Seq.make_results |> Seq.map_result (fn thm' => (ctxt, thm')))

  val context_tactic_to_context_tactic' : context_tactic -> Proof.context -> tactic = fn ct => fn ctxt =>
     Context_Tactic.NO_CONTEXT_TACTIC ctxt ct

  fun context_tactic_to_method (t : Proof.context -> tactic) : Method.method =
      t |> context_tactic_to_context_tactic |> K

  fun context_tactic_to_method' (t : thm list -> Proof.context -> tactic) : Method.method =
      fn ts => (fn ctxt => t ts ctxt) |> context_tactic_to_context_tactic

  fun method_to_tac (m : Method.method) : Proof.context -> tactic =
    context_tactic_to_context_tactic' (m [])

  fun method_to_tac' (m : Method.method) (ts : thm list) : Proof.context -> tactic =
    context_tactic_to_context_tactic' (m ts)

  fun get_method (m : string) : Proof.context -> Method.method =
    fn ctxt =>
    let val kwds = Thy_Header.get_keywords' ctxt
        val src = Token.explode0 kwds m in
      (Method.read ctxt src |> Method.evaluate) ctxt
    end

  fun get_method_as_tac (m : string) : Proof.context -> tactic =
    fn ctxt => method_to_tac (get_method m ctxt) ctxt

  fun strip_meta_all c =
    strip_meta_all (Logic.dest_all_global c |> snd)
    handle TERM _ => c

  fun find_metaimp_conclusion ((Const (@{const_name Pure.imp}, _)) $ _ $ c) = find_metaimp_conclusion c
    | find_metaimp_conclusion ((Const (@{const_name HOL.Trueprop}, _)) $ c) = c
    | find_metaimp_conclusion ((Const (@{const_name Pure.all}, _)) $ c) = find_metaimp_conclusion c
    | find_metaimp_conclusion (t as Abs (_, _, _)) = find_metaimp_conclusion (snd (Term.dest_abs_global t))
    | find_metaimp_conclusion c = c

  fun find_conclusion ((Const (@{const_name Pure.imp}, _)) $ _ $ c)    = find_conclusion c
    | find_conclusion ((Const (@{const_name HOL.Trueprop}, _)) $ c)    = find_conclusion c
    | find_conclusion ((Const (@{const_name Pure.all}, _)) $ c)        = find_conclusion c
    | find_conclusion ((Const (@{const_name HOL.All}, _)) $ c)         = find_conclusion c
    | find_conclusion ((Const (@{const_name HOL.implies}, _)) $ _ $ c) = find_conclusion c
    | find_conclusion (t as Abs (_, _, _)) = find_conclusion (snd (Term.dest_abs_global t))
    | find_conclusion c = c

  fun find_conclusions' done todo ((Const (@{const_name Pure.imp}, _)) $ _ $ c) = find_conclusions' done todo c
    | find_conclusions' done todo ((Const (@{const_name HOL.Trueprop}, _)) $ c)    = find_conclusions' done todo c
    | find_conclusions' done todo ((Const (@{const_name Pure.all}, _)) $ c)        = find_conclusions' done todo c
    | find_conclusions' done todo ((Const (@{const_name HOL.All}, _)) $ c)         = find_conclusions' done todo c
    | find_conclusions' done todo ((Const (@{const_name HOL.implies}, _)) $ _ $ c) = find_conclusions' done todo c
    | find_conclusions' done todo ((Const (@{const_name HOL.conj}, _)) $ a $ b) = find_conclusions' done (b :: todo) a
    | find_conclusions' done todo (t as Abs (_, _, _)) = find_conclusions' done todo (snd (Term.dest_abs_global t))
    | find_conclusions' done (t :: todo) c = find_conclusions' (c :: done) todo t
    | find_conclusions' done [] c = (c :: done)
  fun find_conclusions t = find_conclusions' [] [] t

  fun print_term (Const(str, _)) = "CONST " ^ str
    | print_term (Free(str,_)) = "FREE " ^ str
    | print_term (Var((name,nr),_)) = "INDEX(" ^ name ^ "," ^ (Int.toString nr)
    | print_term (Bound (i)) = "BOUND " ^ (Int.toString i)
    | print_term (Abs(str, _, term)) = "%" ^ str ^ " -> " ^ (print_term term)
    | print_term (t $ u) = "(" ^ (print_term t) ^ " $ " ^ (print_term u) ^ ")";

  val pwriteln = Pretty.writeln
  val pretty_term = Syntax.pretty_term
  fun pretty_cterm ctxt ctrm = pretty_term ctxt (Thm.term_of ctrm)
  val pretty_intset = Intset.dest #> List.map Int.toString #> Pretty.str_list "(" ")"

  (* Check if the goal is an equality of the form ?f {vars} = {expr}, where
     expr is not schematic but has universally quantfied variables which are
     not in {vars}. *)
  fun is_bad_schematic_equality (ctxt : Proof.context) (goal : term) : bool =
   let
     val (lhs, rhs) = HOLogic.dest_eq goal
     val (lhs_hd, rhs_hd) = (Term.head_of lhs, Term.head_of rhs)
     val lhs_bounds = Intset.make (Term.loose_bnos lhs)
     val rhs_bounds = Intset.make (Term.loose_bnos rhs)
     fun err (diff : Intset.T) =
       ([Pretty.str "Encountered unsolvable schematic, probably due to too late introduction of free variables",
         Pretty.brk 1, Syntax.pretty_term ctxt goal] |> Pretty.block |> Pretty.string_of |> Output.information;
        [Pretty.str "Missing parametrization for bound variable(s)",
         Pretty.brk 1, diff |> pretty_intset] |> Pretty.block |> Pretty.string_of |> Output.information)
   in
     if Term.is_Var lhs_hd andalso not (Term.is_schematic rhs) then
        let val diff = Intset.subtract lhs_bounds rhs_bounds in
        if Intset.size diff > 0 then
           (err diff; true)
        else
           false
        end
     else if Term.is_Var rhs_hd andalso not (Term.is_schematic lhs) then
        let val diff = Intset.subtract rhs_bounds lhs_bounds in
        if Intset.size diff > 0 then
          (err diff; true)
        else
           false
        end
     else
        false
   end

  val check_bad_schematic_equality_tac': Proof.context -> bool -> int -> tactic = 
    fn ctxt => fn fail_if_bad => fn i => fn thm =>
    let
      val goal =
          List.nth (Thm.prems_of thm, i-1)
       |> Logic.strip_assums_concl
       |> find_metaimp_conclusion
    in
      if is_bad_schematic_equality ctxt goal then
        if fail_if_bad then no_tac thm else all_tac thm
      else
        all_tac thm
    end
    handle Subscript => all_tac thm
     | Empty => all_tac thm
     | THM _ => all_tac thm
     | TERM _ => all_tac thm

  val check_bad_schematic_equality_tac : Proof.context -> bool -> tactic = 
    ALLGOALS oo check_bad_schematic_equality_tac'

  fun is_unifiable_pair ctx t0 t1 =
    let val matches = Unify.unifiers (Context.Proof ctx, Envir.empty 0, [(t0,t1)]) in
      Seq.pull matches |> Option.isSome
    end

  val range_of_nats_base =
    let fun core acc base n =
      if n <= 0 then rev acc else core (base :: acc) (base+1) (n-1)
    in core [] end

  val range_of_nats = range_of_nats_base 0

  \<comment>\<open>From \<^verbatim>\<open>smt_utils.ML\<close>: Apply conversion under a \<^term>\<open>Trueprop\<close>\<close>
  fun prop_conv cv ct =
    (case Thm.term_of ct of
      \<^Const_>\<open>Trueprop for _\<close> => Conv.arg_conv cv ct
    | _ => raise CTERM ("not a property", [ct]))

  fun maybe_prop_conv cv ct =
    (case Thm.term_of ct of
      \<^Const_>\<open>Trueprop for _\<close> => Conv.arg_conv cv ct
    | _ => cv ct)

  val intro_tac : thm list -> Proof.context -> int -> tactic = fn thms => fn ctxt =>
    CHANGED_PROP o REPEAT_ALL_NEW (match_tac ctxt thms)

  val elim_tac : thm list -> Proof.context -> int -> tactic = fn thms => fn ctxt =>
    CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt thms)

  fun reset_ctxt congs thms =
       clear_simpset
    #> (fn ctxt => ctxt addsimps thms)
    #> fold Raw_Simplifier.add_cong congs

  val safe_simp_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic = 
    fn ctxt => fn congs => fn thms => ctxt
      |> reset_ctxt congs thms 
      |> CHANGED_PROP oo safe_asm_full_simp_tac

  val safe_simp_no_asm_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic =
    fn ctxt => fn congs => fn thms => ctxt
      |> reset_ctxt congs thms 
      |> CHANGED_PROP oo safe_simp_tac

  val safe_simp_no_asm_use_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic = 
    fn ctxt => fn congs => fn thms => ctxt
      |> reset_ctxt congs thms 
      |> CHANGED_PROP oo safe_full_simp_tac

  val safe_simp_no_asm_simp_only_tac' : Proof.context -> thm list -> thm list -> int -> tactic = 
    fn ctxt => fn congs => fn thms => ctxt
      |> reset_ctxt congs thms 
      |> CHANGED_PROP oo safe_asm_simp_tac

  val safe_unfold_tac' : Proof.context -> thm list -> thm list -> int -> tactic = 
     fn ctxt => fn congs => fn ths =>
     CHANGED_PROP o (safe_simp_no_asm_use_only_tac' ctxt congs ths)

  val safe_simp_only_tac : Proof.context -> thm list -> int -> tactic = fn ctxt =>
    safe_simp_only_tac' ctxt []

  val safe_simp_no_asm_only_tac : Proof.context -> thm list -> int -> tactic = fn ctxt =>
    safe_simp_no_asm_only_tac' ctxt []

  val safe_simp_no_asm_use_only_tac : Proof.context -> thm list -> int -> tactic = fn ctxt =>
    safe_simp_no_asm_use_only_tac' ctxt []

  val safe_simp_no_asm_simp_only_tac : Proof.context -> thm list -> int -> tactic = fn ctxt =>
    safe_simp_no_asm_simp_only_tac' ctxt []

  val safe_unfold_tac : Proof.context -> thm list -> int -> tactic = fn ctxt =>
     safe_unfold_tac' ctxt []

  \<comment>\<open>Some variants of \<^verbatim>\<open>Conv.top_conv\<close>\<close>

  \<comment>\<open>Like \<^verbatim>\<open>Conv.top_sweep_conv\<close>, but provides base-conversion with the set of bound variables.\<close>
  fun top_sweep_conv_with_info (base_conv : cterm list -> Proof.context -> conv)
    (ctxt : Proof.context) (t : cterm) =
    let
    fun core (base_conv : cterm list -> Proof.context -> conv)
      (vs: cterm list) (ctxt : Proof.context) (t : cterm) =
      ((base_conv vs ctxt)
       else_conv (Conv.abs_conv (fn (v, ctxt') => fn t' => core base_conv (v :: vs) ctxt' t') ctxt)
       else_conv (Conv.comb_conv (core base_conv vs ctxt))
       else_conv Conv.all_conv) t
    in
      core base_conv [] ctxt t
    end

  (* Taken from smt_utils.ML *)
  fun under_quant_conv cv ctxt =
  let
    fun quant_conv inside ctxt cvs ct =
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>All\<close>, _) $ Abs _ =>
          Conv.binder_conv (under_conv cvs) ctxt
      | Const (\<^const_name>\<open>Ex\<close>, _) $ Abs _ =>
          Conv.binder_conv (under_conv cvs) ctxt
      | _ => if inside then cv (ctxt, cvs) else Conv.all_conv) ct
    and under_conv cvs (cv, ctxt) = quant_conv true ctxt (cv :: cvs)
  in quant_conv false ctxt [] end

  fun stop_at_binder(c : Proof.context -> conv) (ctxt : Proof.context) : conv =
     Conv.abs_conv (K Conv.all_conv) ctxt else_conv (c ctxt)
  fun stop_at_quantifier (c : Proof.context -> conv) (ctxt : Proof.context) : conv =
     under_quant_conv (K Conv.all_conv) ctxt else_conv (c ctxt)

  \<comment>\<open>Like \<^verbatim>\<open>Conv.top_sweep_conv\<close>, but does not go inside binders.\<close>
  fun top_sweep_conv_no_bind (c : Proof.context -> conv) : Proof.context -> conv =
    c |> stop_at_binder |> Conv.top_sweep_conv
  \<comment>\<open>Like  \<^verbatim>\<open>Conv.top_sweep_conv\<close>, but does not go inside quantifiers.\<close>
  fun top_sweep_conv_no_quant (c : Proof.context -> conv) : Proof.context -> conv =
    c |> stop_at_quantifier |> Conv.top_sweep_conv

  \<comment>\<open>Conversions operate on Pure/meta equalities. The following turns HOL equalities into
     meta equalities and leaves meta equalities as they are.\<close>
  fun force_meta_eq (t : thm): thm = t RS eq_reflection handle THM _ => t
  val force_meta_eqs : thm list -> thm list = List.map force_meta_eq

  fun eta_expand thm =
    let
      val num_abs = thm 
        |> Thm.prop_of 
        |> Logic.dest_equals 
        |> snd 
        |> Term.strip_abs 
        |> fst 
        |> length      
    in
      funpow num_abs (fn t => t RS @{thm meta_fun_cong}) thm
    end
  val eta_expands : thm list -> thm list = List.map eta_expand

  fun filter_to_conv (f : cterm -> bool) : conv = fn t =>
     if f t then Conv.all_conv t else Conv.no_conv t

  \<comment> \<open>fails if the current context contains identical assumptions, noop otherwise\<close>
  val fail_if_dup_assms_tac =
    let fun go xs i j l =
      if j >= l then
        all_tac
      else if i >= j then
        go xs 0 (1 + j) l
      else
      let
        val xi = nth xs i
        val xj = nth xs j
      in
        if Thm.prop_of xi = Thm.prop_of xj then
          no_tac
        else
          go xs (1 + i) j l
      end
    in
      Subgoal.FOCUS (fn {prems, ...} => go prems 0 0 (length prems))
    end

  val remove_dup_lemma = @{lemma \<open>P \<Longrightarrow> P \<Longrightarrow> R \<Longrightarrow> R\<close> by auto}
  fun remove_duplicate_tac (ctxt : Proof.context) (i : int) : tactic =
     ((Tactic.eresolve_tac ctxt [remove_dup_lemma] i) THEN (Tactic.assume_tac ctxt i))
     |> REPEAT

  \<comment>\<open>A plain \<^verbatim>\<open>simp\<close> will solve a goal like \<^verbatim>\<open>f x = f ?y\<close> by inferring \<^verbatim>\<open>?y \<leadsto> x\<close>, which
  oftentimes is not the right solution (in the context of other subgoals also referring to
  \<^verbatim>\<open>?y\<close>. On the other hand, safe variants of \<^verbatim>\<open>simp\<close> as used by \<^verbatim>\<open>clarsimp\<close>, do not seem to
  instantiate schematics at all, even in the special case where the goal is \<^verbatim>\<open>x = ?y\<close> where
  instantiation is safe.

  Here, we are writing a mini-tactic ourself which discharges goals of the form \<^verbatim>\<open>x = ?y\<close>,
  provided \<^verbatim>\<open>x\<close> does not contain \<^verbatim>\<open>?y\<close> as a subterm.\<close>

  fun check_schematic a_hd b b_hd =
    is_Var a_hd andalso (
      a_hd = b_hd orelse not (
        Term.exists_subterm (fn t => a_hd = t) b
      )
  )

  val instantiate_schematic_from_hol_equality: Proof.context -> int -> tactic =
    fn ctxt => SUBGOAL (fn (goal, i) =>
      let val goal = find_metaimp_conclusion goal
      val (lhs,rhs) = HOLogic.dest_eq goal
      val lhs_hd = lhs |> Term.strip_comb |> fst
      val rhs_hd = rhs |> Term.strip_comb |> fst
      in
        if check_schematic lhs_hd rhs rhs_hd orelse check_schematic rhs_hd lhs lhs_hd then
          resolve_tac ctxt @{thms HOL.refl} i
        else
          no_tac
      end handle TERM _ => no_tac)

  val instantiate_schematic_from_pure_equality: Proof.context -> int -> tactic =
    fn ctxt => SUBGOAL (fn (goal, i) =>
      let val goal = find_metaimp_conclusion goal
      val (lhs,rhs) = Logic.dest_equals goal
      val lhs_hd = lhs |> Term.strip_comb |> fst
      val rhs_hd = rhs |> Term.strip_comb |> fst

      in
        if check_schematic lhs_hd rhs rhs_hd orelse check_schematic rhs_hd lhs lhs_hd then
          resolve_tac ctxt @{thms Pure.reflexive} i
        else
          no_tac
      end handle TERM _ => no_tac)

  val instantiate_schematic_from_equality: Proof.context -> int -> tactic = fn ctxt =>
             instantiate_schematic_from_pure_equality ctxt
     ORELSE' instantiate_schematic_from_hol_equality ctxt

  fun metagoal_satisfies_pattern (pattern_str : string) (ctxt : Proof.context) (goal : term) = let
    val goal = goal |> find_metaimp_conclusion
    val pattern = pattern_str |> Proof_Context.read_term_pattern ctxt
    in is_unifiable_pair ctxt pattern goal end

  fun premise_satisfies_pattern (pattern_str : string) (ctxt : Proof.context) (goal : term) = let
    val prems = goal |> strip_meta_all |> Logic.strip_assums_hyp
    val pattern = "HOL.Trueprop (" ^ pattern_str ^ ")" |> Proof_Context.read_term_pattern ctxt
    in prems |> List.exists (is_unifiable_pair ctxt pattern) end

end;

(* Isar *)

local
  val _ = Theory.setup (Method.setup @{binding "refl_schematic"}
          (Scan.succeed (SIMPLE_METHOD' o Crush_Base.instantiate_schematic_from_equality)) "")

  val _ = Theory.setup (Method.setup @{binding "remove_duplicates"}
          (Scan.succeed (SIMPLE_METHOD' o Crush_Base.remove_duplicate_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "fail_if_dup_assms"}
          (Scan.succeed (SIMPLE_METHOD' o Crush_Base.fail_if_dup_assms_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "safe_no_asm_simp"}
          (Scan.succeed (SIMPLE_METHOD' o (CHANGED_PROP oo safe_asm_simp_tac))) "")

  val _ = Theory.setup (Attrib.setup @{binding "forget"}
                       (Thm.rule_attribute [] (K (K Drule.dummy_thm)) |> Scan.succeed) "")

  val _ = Theory.setup (Attrib.setup @{binding "meta_all_intro"}
                       (Thm.rule_attribute [] (K Thm.forall_intr_vars) |> Scan.succeed) "")

  val _ = Theory.setup (Attrib.setup @{binding "unabs_def"}
                       (Thm.rule_attribute [] (K Crush_Base.eta_expand) |> Scan.succeed) "")

  fun all_intro ctxt thm = 
     let val ctxt = Context.proof_of ctxt
         val thm' = Thm.forall_intr_vars thm
         val thm'' = Object_Logic.atomize ctxt (Thm.cprop_of thm')
     in
       Raw_Simplifier.rewrite_rule ctxt [thm''] thm'
     end

  val _ = Theory.setup (Attrib.setup @{binding "all_intro"}
                       (Thm.rule_attribute [] all_intro |> Scan.succeed) "")
in end
