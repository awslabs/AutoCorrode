(* Original Copyright (c) 1986-2023,
            University of Cambridge,
            Technische Universitaet Muenchen,
            and contributors
   under the ISABELLE COPYRIGHT LICENSE

   Modifications Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *)

(*
  MePo (Meng-Paulson) relevance filter — core ranking engine for premises.

  Standalone atop HOL. No tactics, no `IGNORE`, no Crush-specific dependencies.

  Ranks a subgoal's OWN PREMISES against its conclusion by iterative constant-
  overlap scoring (the same algorithm as Sledgehammer's `sledgehammer_mepo.ML`,
  adapted to work on premises rather than background lemmas).

  See mepo_prem.ML for the tactic layer that builds on this.
*)

signature MEPO_CORE =
sig

 (* --- Types --- *)

 (* Tuning parameters for the MePo relevance heuristic (thresholds, decay,
    weight multipliers).  NONE uses session-configurable defaults. *)
 type relevance_fudge

 (* Per-premise filter/transform applied before ranking.
    - NONE: exclude this premise from MePo ranking entirely.
    - SOME t': include it, extracting constants from t' (the original premise
      is retained in the output regardless).
    The default (`default_prem_prep`) drops ASSUMPTION-tagged premises. *)
 type prem_prep = term -> term option
 val default_prem_prep : prem_prep


 (* --- Ranking --- *)

 (* `relevant_prems_core' prem_prep ctxt max_facts fudge concl prems`

    The core premise ranker. Given a tagged premise list `prems : ('a * term)
    list` (tag * premise term) and a conclusion term, returns the premises MePo
    deems relevant, in RELEVANCE ORDER (most relevant first). The tag (typically
    an index, but opaque to the ranker) rides along untouched.

    Does NOT apply the nprems<=max_facts shortcut, does NOT re-sort by index —
    use this when you want the true priority ordering.

    `max_facts` caps acceptance (once reached, the filter stops accepting);
    premises below the decaying threshold are dropped from the output.
    `prem_prep` controls per-premise participation (see type above). *)
 val relevant_prems_core' : prem_prep -> Proof.context -> int ->
    relevance_fudge option -> term -> ('a * term) list -> ('a * term) list

 (* Like `relevant_prems_core'` with `default_prem_prep` (ASSUMPTION premises
    excluded from ranking). *)
 val relevant_prems_core : Proof.context -> int ->
    relevance_fudge option -> term -> ('a * term) list -> ('a * term) list

 (* `relevant_prems ctxt max_facts fudge subgoal_term`

    Goal-level entry point. Constifies bound params and frees (so MePo can
    count shared local variables), strips premises and conclusion, calls the
    core ranker, then RE-SORTS the result by original index.

    Short-circuits: if nprems <= max_facts, returns all premises (no ranking
    needed — they'd all be accepted anyway).

    Returns (nprems, relevant_premises_in_index_order). *)
 val relevant_prems : Proof.context -> int ->
    relevance_fudge option -> term -> int * ((int * term) list)

 (* Convenience: like `relevant_prems` but operates on the i-th subgoal of a
    goal thm directly, returning only the indices. *)
 val relevant_prems_in_goal : Proof.context -> int ->
    relevance_fudge option -> int -> thm -> int * (int list)

 (* `irrelevant_prems_in_goal ctxt max_facts fudge i thm`

    The COMPLEMENT of `relevant_prems_in_goal`: indices of premises that should
    be hidden or dropped. ASSUMPTION-tagged premises are force-kept (never
    appear in this list) via a separate pass, even if MePo did not rank them.

    Returns (nprems, irrelevant_indices_in_ascending_order). *)
 val irrelevant_prems_in_goal : Proof.context -> int ->
    relevance_fudge option -> int -> thm -> int * (int list)


 (* `rank_premises prem_prep ctxt fudge concl prems`

    Reorders ALL premises by MePo relevance — nothing is dropped by threshold.
    Premises excluded from ranking by `prem_prep` (returned NONE) are reported
    separately.

    Returns (ranked, excluded):
      ranked   — premises that participated in ranking, in RELEVANCE ORDER
                 (most relevant first). This is every premise for which
                 `prem_prep` returned SOME and MePo could extract constants.
      excluded — premises `prem_prep` dropped (returned NONE), in their
                 original order. *)
 val rank_premises : prem_prep -> Proof.context ->
    relevance_fudge option -> term -> ('a * term) list -> ('a * term) list * ('a * term) list


 (* --- Utilities --- *)

 (* `matching_prems ctxt thm pred i`: indices of premises in the i-th subgoal
    of `thm` whose term satisfies `pred`. *)
 val matching_prems : Proof.context -> thm -> (term -> bool) -> int -> int list

 (* 0-based enumeration of a list: [(0,x0),(1,x1),...]. *)
 val enumerate : 'a list -> (int * 'a) list

end;

structure MePo_Core: MEPO_CORE =
struct

  fun enumerate ls =
    let
      fun aux _ acc [] = List.rev acc
        | aux base acc (x :: xs) = aux (base + 1) ((base, x) :: acc) xs
    in
      aux 0 [] ls
    end

  fun matching_prems (_: Proof.context) (thm: thm) (prem_filter: term -> bool) i =
    let
      val subgoal = Thm.cprem_of thm i |> Thm.term_of
      val prems = Logic.strip_imp_prems subgoal
    in
      prems |> enumerate |> filter (snd #> prem_filter) |> map fst
    end


open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Prover

val trace = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_mepo_trace\<close> (K false)

val mepo_prem_config_threshold0 = Attrib.setup_config_real \<^binding>\<open>mepo_prem_threshold0\<close> (K 0.45)
val mepo_prem_config_threshold1 = Attrib.setup_config_real \<^binding>\<open>mepo_prem_threshold1\<close> (K 0.85)
val mepo_prem_config_local_const_multiplier = Attrib.setup_config_real \<^binding>\<open>mepo_prem_local_const_multipier\<close> (K 1.5)
val mepo_prem_config_bound_const_multiplier = Attrib.setup_config_real \<^binding>\<open>mepo_prem_bound_const_multipier\<close> (K 4.0)
val mepo_prem_config_free_const_multiplier = Attrib.setup_config_real \<^binding>\<open>mepo_prem_free_const_multipier\<close> (K 3.0)
val mepo_prem_config_threshold_divisor = Attrib.setup_config_real \<^binding>\<open>mepo_prem_threshold_divisor\<close> (K 1.5)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator
val pseudo_abs_name = sledgehammer_prefix ^ "abs"
val theory_const_suffix = Long_Name.separator ^ " 1"

type relevance_fudge =
  {fact_threshold0 : real,
   fact_threshold1 : real,
   local_const_multiplier : real,
   bound_const_multiplier : real,
   free_const_multiplier : real,
   worse_irrel_freq : real,
   higher_order_irrel_weight : real,
   abs_rel_weight : real,
   abs_irrel_weight : real,
   theory_const_rel_weight : real,
   theory_const_irrel_weight : real,
   chained_const_irrel_weight : real,
   max_imperfect : real,
   max_imperfect_exp : real,
   threshold_divisor : real,
   ridiculous_threshold : real}

(* FUDGE *)
fun default_relevance_fudge (ctxt : Proof.context) : relevance_fudge =
  {fact_threshold0 = Config.get ctxt mepo_prem_config_threshold0,
   fact_threshold1 = Config.get ctxt mepo_prem_config_threshold1,
   local_const_multiplier = Config.get ctxt mepo_prem_config_local_const_multiplier,
   bound_const_multiplier = Config.get ctxt mepo_prem_config_bound_const_multiplier,
   free_const_multiplier = Config.get ctxt mepo_prem_config_free_const_multiplier,
   worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   chained_const_irrel_weight = 0.25,
   max_imperfect = 11.5,
   max_imperfect_exp = 1.0,
   threshold_divisor =  Config.get ctxt mepo_prem_config_threshold_divisor,
   ridiculous_threshold = 0.1}

fun order_of_type (Type (\<^type_name>\<open>fun\<close>, [T1, T2])) =
    Int.max (order_of_type T1 + 1, order_of_type T2)
  | order_of_type (Type (_, Ts)) = fold (Integer.max o order_of_type) Ts 0
  | order_of_type _ = 0

(* An abstraction of Isabelle types and first-order terms *)
datatype pattern = PVar | PApp of string * pattern list
datatype ptype = PType of int * typ list

fun string_of_patternT (TVar _) = "_"
  | string_of_patternT (Type (s, ps)) = if null ps then s else s ^ string_of_patternsT ps
  | string_of_patternT (TFree (s, _)) = s
and string_of_patternsT ps = "(" ^ commas (map string_of_patternT ps) ^ ")"
fun string_of_ptype (PType (_, ps)) = string_of_patternsT ps

(*Is the second type an instance of the first one?*)
fun match_patternT (TVar _, _) = true
  | match_patternT (Type (s, ps), Type (t, qs)) = s = t andalso match_patternsT (ps, qs)
  | match_patternT (TFree (s, _), TFree (t, _)) = s = t
  | match_patternT (_, _) = false
and match_patternsT (_, []) = true
  | match_patternsT ([], _) = false
  | match_patternsT (p :: ps, q :: qs) = match_patternT (p, q) andalso match_patternsT (ps, qs)
fun match_ptype (PType (_, ps), PType (_, qs)) = match_patternsT (ps, qs)

(* Is there a unifiable constant? *)
fun pconst_mem f consts (s, ps) =
  exists (curry (match_ptype o f) ps) (map snd (filter (curry (op =) s o fst) consts))

fun pconst_hyper_mem f const_tab (s, ps) =
  exists (curry (match_ptype o f) ps) (these (Symtab.lookup const_tab s))

(* Pairs a constant with the list of its type instantiations. *)
fun ptype thy const x = (if const then these (try (Sign.const_typargs thy) x) else [])
fun rich_ptype thy const (s, T) = PType (order_of_type T, ptype thy const (s, T))
fun rich_pconst thy const (s, T) = (s, rich_ptype thy const (s, T))

fun string_of_hyper_pconst (s, ps) = s ^ "{" ^ commas (map string_of_ptype ps) ^ "}"

fun patternT_eq (TVar _, TVar _) = true
  | patternT_eq (Type (s, Ts), Type (t, Us)) = s = t andalso patternsT_eq (Ts, Us)
  | patternT_eq (TFree (s, _), TFree (t, _)) = (s = t)
  | patternT_eq _ = false
and patternsT_eq ([], []) = true
  | patternsT_eq ([], _) = false
  | patternsT_eq (_, []) = false
  | patternsT_eq (T :: Ts, U :: Us) = patternT_eq (T, U) andalso patternsT_eq (Ts, Us)

fun ptype_eq (PType (m, Ts), PType (n, Us)) = m = n andalso patternsT_eq (Ts, Us)

 (* Add a pconstant to the table, but a [] entry means a standard connective, which we ignore. *)
fun add_pconst_to_table (s, p) = Symtab.map_default (s, [p]) (insert ptype_eq p)

(* Set constants tend to pull in too many irrelevant facts. We limit the damage by treating them
   more or less as if they were built-in but add their axiomatization at the end. *)
val set_consts = [\<^const_name>\<open>Collect\<close>, \<^const_name>\<open>Set.member\<close>]

(* Test whether a premise is ASSUMPTION-tagged (under optional Trueprop). *)
local
  fun is_assumption t = (case t of
     \<^Const_>\<open>Trueprop for t1\<close> => is_assumption t1
   | \<^Const_>\<open>ASSUMPTION for _\<close> => true
   | _ => false)
in

type prem_prep = term -> term option

(* Default premise preparation: drop ASSUMPTION-tagged premises from ranking
   (they are force-kept separately in `irrelevant_prems_in_goal`), everything
   else ranks as itself. *)
val default_prem_prep : prem_prep =
  (fn t => if is_assumption t then NONE else SOME t)

(* Force-keep predicate for ASSUMPTION premises (used in
   `irrelevant_prems_in_goal` to ensure they are never dropped). *)
val is_assumption_prem : term -> bool = is_assumption

end

fun add_pconsts_in_term thy =
  let
    fun do_const const (x as (s, _)) ts =
      if member (op =) set_consts s then
        fold (do_term false) ts
      else
        (not (is_irrelevant_const s) ? add_pconst_to_table (rich_pconst thy const x))
        #> fold (do_term false) ts
    and do_term ext_arg t =
      (case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, T, t'), ts) =>
        ((null ts andalso not ext_arg)
         (* Since lambdas on the right-hand side of equalities are usually extensionalized later by
            "abs_extensionalize_term", we don't penalize them here. *)
         ? add_pconst_to_table (pseudo_abs_name, PType (order_of_type T + 1, [])))
        #> fold (do_term false) (t' :: ts)
      | (_, ts) => fold (do_term false) ts)
    and do_term_or_formula ext_arg T =
      if T = HOLogic.boolT then do_formula else do_term ext_arg
    and do_formula t =
      (case t of
        Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, t') => do_formula t'
      | \<^Const_>\<open>Pure.imp for t1 t2\<close> => do_formula t1 #> do_formula t2
      | Const (\<^const_name>\<open>Pure.eq\<close>, Type (_, [T, _])) $ t1 $ t2 =>
        do_term_or_formula false T t1 #> do_term_or_formula true T t2
      | \<^Const_>\<open>Trueprop for t1\<close> => do_formula t1
      | \<^Const_>\<open>False\<close> => I
      | \<^Const_>\<open>True\<close> => I
      | \<^Const_>\<open>Not for t1\<close> => do_formula t1
      | Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t') => do_formula t'
      | Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, t') => do_formula t'
      | \<^Const_>\<open>conj for t1 t2\<close> => do_formula t1 #> do_formula t2
      | \<^Const_>\<open>disj for t1 t2\<close> => do_formula t1 #> do_formula t2
      | \<^Const_>\<open>implies for t1 t2\<close> => do_formula t1 #> do_formula t2
      | Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [T, _])) $ t1 $ t2 =>
        do_term_or_formula false T t1 #> do_term_or_formula true T t2
      | Const (\<^const_name>\<open>If\<close>, Type (_, [_, Type (_, [T, _])])) $ t1 $ t2 $ t3 =>
        do_formula t1 #> fold (do_term_or_formula false T) [t2, t3]
      | Const (\<^const_name>\<open>Ex1\<close>, _) $ Abs (_, _, t') => do_formula t'
      | Const (\<^const_name>\<open>Ball\<close>, _) $ t1 $ Abs (_, _, t') =>
        do_formula (t1 $ Bound ~1) #> do_formula t'
      | Const (\<^const_name>\<open>Bex\<close>, _) $ t1 $ Abs (_, _, t') =>
        do_formula (t1 $ Bound ~1) #> do_formula t'
      | (t0 as Const (_, \<^typ>\<open>bool\<close>)) $ t1 =>
        do_term false t0 #> do_formula t1  (* theory constant *)
      | _ => do_term false t)
  in
    do_formula
  end

val bound_prefixN = "constified_bound_"
val free_prefixN = "constified_free_"

val is_bound_const = String.isPrefix bound_prefixN
val is_free_const = String.isPrefix free_prefixN

val wrap_bound_name = curry (op ^) bound_prefixN
val wrap_free_name = curry (op ^) free_prefixN

fun pconsts_in_fact thy t =
  Symtab.fold (fn (s, pss) => fold (cons o pair s) pss) (Symtab.empty |> add_pconsts_in_term thy t)
    []

(* `prem_prep` decides ranking participation and, when transforming, which term
   supplies the constants; the original `fact` is always retained for output. *)
fun pair_consts_fact' (prem_prep : prem_prep) thy term_of_fact fact =
  (case prem_prep (fact |> term_of_fact) of
    NONE => NONE
  | SOME t =>
    (case pconsts_in_fact thy t of
      [] => NONE
    | consts => SOME ((fact, consts), NONE)))

(* A two-dimensional symbol table counts frequencies of constants. It's keyed
   first by constant name and second by its list of type instantiations. For the
   latter, we need a linear ordering on "pattern list". *)

fun patternT_ord p =
  (case p of
    (Type (s, ps), Type (t, qs)) =>
    (case fast_string_ord (s, t) of
      EQUAL => dict_ord patternT_ord (ps, qs)
    | ord => ord)
  | (TVar _, TVar _) => EQUAL
  | (TVar _, _) => LESS
  | (Type _, TVar _) => GREATER
  | (Type _, TFree _) => LESS
  | (TFree (s, _), TFree (t, _)) => fast_string_ord (s, t)
  | (TFree _, _) => GREATER)

fun ptype_ord (PType (m, ps), PType (n, qs)) =
  (case dict_ord patternT_ord (ps, qs) of
    EQUAL => int_ord (m, n)
  | ord => ord)

structure PType_Tab = Table(type key = ptype val ord = ptype_ord)

fun count_fact_consts' thy term_of_fact =
  let
    fun do_const const (s, T) ts =
      (* Two-dimensional table update. Constant maps to types maps to count. *)
      PType_Tab.map_default (rich_ptype thy const (s, T), 0) (Integer.add 1)
      |> Symtab.map_default (s, PType_Tab.empty)
      #> fold do_term ts
    and do_term t =
      (case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, _, t'), ts) => fold do_term (t' :: ts)
      | (_, ts) => fold do_term ts)
  in do_term o term_of_fact end

fun pow_int _ 0 = 1.0
  | pow_int x 1 = x
  | pow_int x n = if n > 0 then x * pow_int x (n - 1) else pow_int x (n + 1) / x

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun pconst_freq match const_tab (c, ps) =
  PType_Tab.fold (fn (qs, m) => match (ps, qs) ? Integer.add m) (the (Symtab.lookup const_tab c)) 0

fun rel_weight_for _ freq = 1.0 + 2.0 / Math.ln (Real.fromInt freq + 1.0)

fun irrel_weight_for ({worse_irrel_freq, higher_order_irrel_weight, ...} : relevance_fudge) order
    freq =
  let val (k, x) = worse_irrel_freq |> `Real.ceil in
    (if freq < k then Math.ln (Real.fromInt (freq + 1)) / Math.ln x
     else rel_weight_for order freq / rel_weight_for order k)
    * pow_int higher_order_irrel_weight (order - 1)
  end

fun multiplier_of_const_name (_ : Proof.context) local_const_multiplier bound_const_multiplier free_const_multiplier s =
  if String.isSubstring "." s then 1.0
  else if is_bound_const s then bound_const_multiplier
  else if is_free_const s then free_const_multiplier
  else local_const_multiplier

fun generic_pconst_weight (ctxt : Proof.context) local_const_multiplier bound_const_multiplier free_const_multiplier abs_weight theory_const_weight chained_const_weight
    weight_for f const_tab chained_const_tab (c as (s, PType (m, _))) =
  if s = pseudo_abs_name then
    abs_weight
  else if String.isSuffix theory_const_suffix s then
    theory_const_weight
  else
    multiplier_of_const_name ctxt local_const_multiplier bound_const_multiplier free_const_multiplier s
    * weight_for m (pconst_freq (match_ptype o f) const_tab c)
    |> (if chained_const_weight < 1.0 andalso pconst_hyper_mem I chained_const_tab c then
          curry (op *) chained_const_weight
        else
          I)

fun rel_pconst_weight (ctxt : Proof.context) ({local_const_multiplier, bound_const_multiplier, free_const_multiplier, abs_rel_weight, theory_const_rel_weight,
    ...} : relevance_fudge) const_tab =
  generic_pconst_weight ctxt local_const_multiplier bound_const_multiplier free_const_multiplier abs_rel_weight theory_const_rel_weight 0.0
    rel_weight_for I const_tab Symtab.empty

fun irrel_pconst_weight (ctxt : Proof.context) (fudge as {local_const_multiplier, bound_const_multiplier, free_const_multiplier, abs_irrel_weight,
    theory_const_irrel_weight, chained_const_irrel_weight, ...}) const_tab chained_const_tab =
  generic_pconst_weight ctxt local_const_multiplier bound_const_multiplier free_const_multiplier abs_irrel_weight theory_const_irrel_weight
    chained_const_irrel_weight (irrel_weight_for fudge) swap const_tab chained_const_tab

fun is_odd_const_name s =
  s = pseudo_abs_name orelse String.isSuffix theory_const_suffix s

fun fact_weight' (ctxt : Proof.context) fudge const_tab rel_const_tab chained_const_tab
                fact_consts =
  (case fact_consts |> List.partition (pconst_hyper_mem I rel_const_tab)
                   ||> filter_out (pconst_hyper_mem swap rel_const_tab) of
    ([], _) => 0.0
  | (rel, irrel) =>
    if forall (forall (is_odd_const_name o fst)) [rel, irrel] then
      0.0
    else
      let
        val irrel = irrel |> filter_out (pconst_mem swap rel)
        val rel_weight = 0.0 |> fold (curry (op +) o rel_pconst_weight ctxt fudge const_tab) rel
        val irrel_weight =
          fold (curry (op +) o irrel_pconst_weight ctxt fudge const_tab chained_const_tab) irrel 0.0
        val res = rel_weight / (rel_weight + irrel_weight)
      in
        if Real.isFinite res then res else 0.0
      end)

fun take_most_relevant' ctxt max_facts remaining_max
    ({max_imperfect, max_imperfect_exp, ...} : relevance_fudge)
    fact_to_string candidates =
  let
    val max_imperfect =
      Real.ceil (Math.pow (max_imperfect,
        Math.pow (Real.fromInt remaining_max / Real.fromInt max_facts, max_imperfect_exp)))
    val (perfect, imperfect) = candidates
      |> sort (Real.compare o swap o apply2 snd)
      |> chop_prefix (fn (_, w) => w > 0.99999)
    val ((accepts, more_rejects), rejects) =
      chop max_imperfect imperfect |>> append perfect |>> chop remaining_max
  in
    trace_msg ctxt (fn () =>
      "Actually passed (" ^ string_of_int (length accepts) ^ " of " ^
      string_of_int (length candidates) ^ "): " ^
      (accepts
       |> map (fn (x, weight) => fact_to_string x ^ " [" ^ Real.toString weight ^ "]")
       |> commas));
    (accepts, more_rejects @ rejects)
  end

fun eq_prod eqx eqy ((x1, y1), (x2, y2)) = eqx (x1, x2) andalso eqy (y1, y2)

val really_hopeless_get_kicked_out_iter = 5 (* FUDGE *)

fun relevance_filter_generic (prem_prep : prem_prep) ctxt thres0 decay max_facts (term_of_fact: 'a -> term)
        (fudge as {threshold_divisor, ridiculous_threshold, ...}) (facts : 'a list) hyp_ts concl_t =
  let
    val thy = Proof_Context.theory_of ctxt
    val const_tab = fold (count_fact_consts' thy term_of_fact) facts Symtab.empty
    val add_pconsts = add_pconsts_in_term thy
    val chained_ts = facts |> List.map term_of_fact
    val chained_const_tab = Symtab.empty |> fold add_pconsts chained_ts
    val goal_const_tab =
      Symtab.empty
      |> fold add_pconsts hyp_ts
      |> add_pconsts concl_t

    fun iter' j remaining_max thres (fact_to_string : 'c -> string)
      (fact_to_consts : 'c -> (Symtab.key * ptype) list) rel_const_tab hopeless hopeful =
      let
        val hopeless =
          hopeless |> j = really_hopeless_get_kicked_out_iter ? filter_out (fn (_, w) => w < 0.001)
        fun relevant [] _ [] =
            (* Nothing has been added this iteration. *)
            if j = 0 andalso thres >= ridiculous_threshold then
              (* First iteration? Try again. *)
              iter' 0 max_facts (thres / threshold_divisor) fact_to_string fact_to_consts rel_const_tab hopeless hopeful
            else
              []
          | relevant candidates rejects [] =
            let
              val (accepts, more_rejects) =
                take_most_relevant' ctxt max_facts remaining_max fudge fact_to_string candidates
              val sps = maps (fact_to_consts o fst) accepts
              val rel_const_tab' =
                rel_const_tab |> fold add_pconst_to_table sps

              fun is_dirty (s, _) = Symtab.lookup rel_const_tab' s <> Symtab.lookup rel_const_tab s

              val (hopeful_rejects, hopeless_rejects) =
                 (rejects @ hopeless, ([], []))
                 |-> fold (fn (f, old_weight) =>
                   if exists is_dirty (fact_to_consts f) then apfst (cons (f, NONE))
                   else apsnd (cons (f, old_weight)))
                 |>> append (more_rejects
                             |> map (fn (f, old_weight) =>
                                        (f, if exists is_dirty (fact_to_consts f) then NONE
                                             else SOME old_weight)))
              val thres = 1.0 - (1.0 - thres) * Math.pow (decay, Real.fromInt (length accepts))
              val remaining_max = remaining_max - length accepts
            in
              trace_msg ctxt (fn () => "New or updated constants: " ^
                commas (rel_const_tab'
                  |> Symtab.dest
                  |> subtract (eq_prod (op =) (eq_list ptype_eq)) (Symtab.dest rel_const_tab)
                  |> map string_of_hyper_pconst));
              map fst accepts @
              (if remaining_max = 0 then
                 []
               else
                 iter' (j + 1) remaining_max thres fact_to_string fact_to_consts rel_const_tab' hopeless_rejects hopeful_rejects)
            end
          | relevant candidates rejects
              ((f, cached_weight) :: hopeful) =
            let
              val weight =
                (case cached_weight of
                  SOME w => w
                | NONE =>
                  fact_weight' ctxt fudge const_tab rel_const_tab chained_const_tab (fact_to_consts f))
            in
              if weight >= thres then
                relevant ((f, weight) :: candidates) rejects hopeful
              else
                relevant candidates ((f, weight) :: rejects) hopeful
            end
        in
          trace_msg ctxt (fn () =>
              "ITERATION " ^ string_of_int j ^ ": current threshold: " ^
              Real.toString thres ^ ", constants: " ^
              commas (rel_const_tab
                      |> Symtab.dest
                      |> filter (curry (op <>) [] o snd)
                      |> map string_of_hyper_pconst));
          relevant [] [] hopeful
        end
     val fact'_to_string = fst #> term_of_fact #> Syntax.pretty_term ctxt #> Pretty.string_of
     val fact'_to_consts = snd
  in
    facts
    |> map_filter (pair_consts_fact' prem_prep thy term_of_fact)
    |> iter' 0 max_facts thres0 fact'_to_string fact'_to_consts goal_const_tab []
    |> tap (fn accepts => trace_msg ctxt (fn () =>
      "Total relevant: " ^ string_of_int (length accepts)))
    |> List.map fst
  end

  fun relevance_filter' prem_prep ctxt thres0 decay max_facts fudge facts concl_t =
      relevance_filter_generic prem_prep ctxt thres0 decay max_facts snd fudge facts [] concl_t

  fun relevant_prems_core' prem_prep ctxt max_facts fudge concl_t facts =
  let
    val fudge = fudge |> the_default (default_relevance_fudge ctxt)
    val thres0 = #fact_threshold0 fudge
    val thres1 = #fact_threshold1 fudge
    val decay = Math.pow ((1.0 - thres1) / (1.0 - thres0), 1.0 / Real.fromInt (max_facts + 1))
  in
    trace_msg ctxt (fn () => "Considering " ^ string_of_int (length facts) ^ " facts");
    (if thres1 < 0.0 then
       facts
     else if thres0 > 1.0 orelse thres0 > thres1 orelse max_facts <= 0 then
       []
     else
       relevance_filter' prem_prep ctxt thres0 decay max_facts fudge facts concl_t)
  end

  (* Default (ASSUMPTION-dropping) premise preparation, matching prior behaviour. *)
  fun relevant_prems_core ctxt max_facts fudge concl_t facts =
    relevant_prems_core' default_prem_prep ctxt max_facts fudge concl_t facts

  (* Reorder ALL premises by relevance, nothing dropped by threshold.
     Premises excluded by `prem_prep` are singled out separately. *)
  fun rank_premises prem_prep ctxt fudge concl_t facts =
    let
      (* Tag each fact with a unique position so we can track identity without
         requiring equality on the caller's tag type. *)
      val indexed = enumerate facts  (* (pos, (tag, term)) *)
      val (candidates, excluded) =
        fold_rev (fn (pos, (tag, t)) => fn (cs, es) =>
          case prem_prep t of
            NONE => (cs, (tag, t) :: es)
          | SOME _ => ((pos, (tag, t)) :: cs, es))
        indexed ([], [])
      (* Call the core with max_facts = |candidates| so the threshold cap never
         truncates — every candidate that scores above any threshold round is
         accepted, giving us the full relevance ordering. The core sees
         (pos, (tag, term)) and uses `snd` for the term — but we need it to
         use `snd o snd`. We pass through relevant_prems_core' which uses
         `snd` as term_of_fact; so we adapt: candidates as (pos, term) for
         ranking, then re-attach the original (tag, term). *)
      val candidates_for_core = map (fn (pos, (_, t)) => (pos, t)) candidates
      val max_facts = length candidates_for_core
      val ranked_positions =
        relevant_prems_core' prem_prep ctxt max_facts fudge concl_t candidates_for_core
        |> map fst   (* the positions that were accepted, in relevance order *)
      (* Map positions back to original (tag, term) pairs. *)
      val pos_to_fact = AList.lookup (op =) (map (fn (pos, fact) => (pos, fact)) candidates)
      val ranked = map_filter pos_to_fact ranked_positions
      (* Candidates the core dropped below threshold: those positions not in ranked. *)
      val ranked_pos_set = ranked_positions
      fun was_ranked pos = member (op =) ranked_pos_set pos
      val unranked = map snd (filter (fn (pos, _) => not (was_ranked pos)) candidates)
    in
      (ranked @ unranked, excluded)
    end

  fun subst_abs_constify v b = subst_bound (v |> apfst wrap_bound_name |> Const, b);

  fun dest_abs_constify t =
  (case t of Abs (x, T, b) => subst_abs_constify (x, T) b
  | _ => raise TERM ("dest_abs_constify", [t]));

  fun dest_all_constify t =
  (case t of Const ("Pure.all", _) $ (u as Abs _) => dest_abs_constify u
  | _ => raise TERM ("dest_all_constify", [t]));

  (* Turn parameters into free variables *)
  fun dest_all_constify' g =
    g |> dest_all_constify |> dest_all_constify'
    handle TERM _ => g

  fun subst_Frees_constify tm =
      let
        fun subst (Free (x, T)) = Const (wrap_free_name x, T)
          | subst (Abs (a, T, t)) = Abs (a, T, subst t)
          | subst (t $ u) = subst t $ subst u
          | subst t = t;
      in subst tm end;

  fun relevant_prems ctxt max_facts fudge goal =
    let
      val goal = goal |> dest_all_constify' |> subst_Frees_constify
      (* Extract hypotheses *)
      val prems = Logic.strip_imp_prems goal
      val nprems = List.length prems
      val concl = Logic.strip_imp_concl goal
      val relevant = if nprems <= max_facts then (nprems, enumerate prems) else
         prems
      |> enumerate
      |> relevant_prems_core ctxt max_facts fudge concl
      |> sort (int_ord o apply2 fst)
      |> pair nprems
    in
      relevant
    end

  fun relevant_prems_in_goal ctxt max_facts fudge i thm =
    let
      val subgoal = Thm.cprem_of thm i |> Thm.term_of
    in
      relevant_prems ctxt max_facts fudge subgoal |> apsnd (List.map fst)
    end
    handle THM _ => (0, [])

  (* [a,a+1,...,b] without elements from `exclude`.
     `exclude` must be in ascending order. *)
  fun upto_without a b exclude =
    let fun aux (a : int) (b : int) acc [] = acc @ (a upto b)
      | aux (a : int) (b : int) acc (e :: es) = aux (e + 1) b (acc @ (a upto Int.min (e - 1, b))) es
    in
      aux a b [] exclude
    end

  fun sorted_union (a : int list) (b : int list) : int list = a @ b |> sort int_ord

  fun irrelevant_prems_in_goal ctxt max_facts fudge i thm =
    let
      val (nprems, relevant_prems_idxs) = relevant_prems_in_goal ctxt max_facts fudge i thm
      val force_relevant_idxs = matching_prems ctxt thm is_assumption_prem i
      val all_relevant_prems = sorted_union relevant_prems_idxs force_relevant_idxs
    in
      (nprems, upto_without 0 (nprems - 1) all_relevant_prems)
    end
    handle THM _ => (0, [])

end;
