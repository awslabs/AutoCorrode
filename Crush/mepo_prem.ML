(* Original Copyright (c) 1986-2023,
            University of Cambridge,
            Technische Universitaet Muenchen,
            and contributors
   under the ISABELLE COPYRIGHT LICENSE

   Modifications Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *)

(*

  The following is an adaptation of the Meng-Paulson filter
  (defined in HOL/Tools/Sledgehammer/sledgehammer_mepo.ML)
  to apply to the premises of a goal rather than the facts in
  the background theory.

  The goal is to speed-up `simp` calls in goals with a very large
  number of hypotheses.

*)

signature MEPO_PREM =
sig

 type relevance_fudge

 (* ignore_tac0 ctxt i wraps the first premise from i-th subgoal into IGNORE *)
 val ignore_tac0 : Proof.context -> int -> tactic
 (* ignore_tac_idx ctxt j i wraps the j-th premise from the i-th subgoal into IGNORE *)
 val ignore_tac_idx : Proof.context -> int -> int -> tactic
 (* like ignore_tac_idx, but wrapping a list of premises *)
 val ignore_tac_idxs : Proof.context -> int list -> int -> tactic
 (* reverse the action of ignore_tac_idxs_xxx *)
 val unignore_tac : Proof.context -> int -> tactic

 val matching_prems : Proof.context -> thm -> (term -> bool) -> int -> int list

 val relevant_prems_core : Proof.context -> int ->
    relevance_fudge option -> term -> (int * term) list -> (int * term) list

 val relevant_prems : Proof.context -> int ->
    relevance_fudge option -> term -> int * ((int * term) list)
 val relevant_prems_in_goal : Proof.context -> int ->
    relevance_fudge option -> int -> thm -> int * (int list)
 val irrelevant_prems_in_goal : Proof.context -> int ->
    relevance_fudge option -> int -> thm -> int * (int list)
 val ignore_irrelevant_prems_core_tac : Proof.context -> int ->
    relevance_fudge option -> int -> tactic

 val ignore_irrelevant_prems_tac : Proof.context -> int -> int -> tactic
 val drop_irrelevant_prems_tac : Proof.context -> int -> int -> tactic
 val reduced_clarsimp : Proof.context -> int -> bool -> int -> tactic
 val reduced_simp : Proof.context -> int -> bool -> int -> tactic
 val filtered_clarsimp : Proof.context -> int -> bool -> int -> tactic
 val filtered_simp : Proof.context -> int -> bool -> int -> tactic

end;

structure MePo_Prem: MEPO_PREM =
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

  val ignore_tac0 : Proof.context -> int -> tactic = fn ctxt =>
    DETERM o (eresolve_tac ctxt [@{thm IGNORE_imp_ignoreE}])

  val ignore_tac_idx = fn ctxt => fn j =>
     if j = 0 then ignore_tac0 ctxt else
     rotate_tac j THEN' ignore_tac0 ctxt THEN' rotate_tac (~j)

  val ignore_tac_idxs = fn ctxt => fn js =>
     EVERY' (List.map (fn j =>
        ignore_tac_idx ctxt j
        THEN' (TRY o (intro_tac @{thms IGNORE_imp_mergeI} ctxt))) (rev js))
     THEN' (TRY o (intro_tac @{thms IGNORE_imp_unwrapI} ctxt))

  val unignore_tac = fn ctxt =>
    TRY o (elim_tac @{thms IGNORE_splitE} ctxt)
    THEN' TRY o (elim_tac @{thms IGNORE_unwrapE} ctxt)


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

val ignore_consts = [\<^const_name>\<open>ASSUMPTION\<close>]

fun mepo_keep_premise_filter t = (case t of 
   \<^Const_>\<open>Trueprop for t1\<close> => mepo_keep_premise_filter t1
 | \<^Const_>\<open>ASSUMPTION for _\<close> => true
 | _ => false)

fun add_pconsts_in_term thy =
  let
    fun do_const const (x as (s, _)) ts =
      if member (op =) set_consts s then
        fold (do_term false) ts
      else if member (op =) ignore_consts s then
        I
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

fun pair_consts_fact' thy term_of_fact fact =
  if mepo_keep_premise_filter (fact |> term_of_fact) then NONE else
  (case fact |> term_of_fact |> pconsts_in_fact thy of
    [] => NONE
  | consts => SOME ((fact, consts), NONE))

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

(* A surprising number of theorems contain only a few significant constants. These include all
   induction rules and other general theorems. *)

(* "log" seems best in practice. A constant function of one ignores the constant
   frequencies. Rare constants give more points if they are relevant than less
   rare ones. *)
fun rel_weight_for _ freq = 1.0 + 2.0 / Math.ln (Real.fromInt freq + 1.0)

(* Irrelevant constants are treated differently. We associate lower penalties to
   very rare constants and very common ones -- the former because they can't
   lead to the inclusion of too many new facts, and the latter because they are
   so common as to be of little interest. *)
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

(* Computes a constant's weight, as determined by its frequency. *)
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

fun relevance_filter_generic ctxt thres0 decay max_facts (term_of_fact: 'a -> term)
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
    |> map_filter (pair_consts_fact' thy term_of_fact)
    |> iter' 0 max_facts thres0 fact'_to_string fact'_to_consts goal_const_tab []
    |> tap (fn accepts => trace_msg ctxt (fn () =>
      "Total relevant: " ^ string_of_int (length accepts)))
    |> List.map fst
  end

  fun relevance_filter' ctxt thres0 decay max_facts fudge facts concl_t =
      relevance_filter_generic ctxt thres0 decay max_facts snd fudge facts [] concl_t

  fun relevant_prems_core ctxt max_facts fudge concl_t facts =
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
       relevance_filter' ctxt thres0 decay max_facts fudge facts concl_t)
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
      val force_relevant_idxs = matching_prems ctxt thm mepo_keep_premise_filter i
      val all_relevant_prems = sorted_union relevant_prems_idxs force_relevant_idxs
    in
      (nprems, upto_without 0 (nprems - 1) all_relevant_prems)
    end
    handle THM _ => (0, [])

  fun ignore_irrelevant_prems_core_tac ctxt max_facts fudge i thm =
    let
      val (_, drop) = irrelevant_prems_in_goal ctxt max_facts fudge i thm
    in
      ignore_tac_idxs ctxt drop i thm
    end
    handle THM _ => all_tac thm

  fun drop_irrelevant_prems_core_tac ctxt max_facts fudge i thm =
    let
      val (_, drop) = irrelevant_prems_in_goal ctxt max_facts fudge i thm
    in
      thin_tac_idxs ctxt drop i thm
    end
    handle THM _ => all_tac thm

  fun ignore_irrelevant_prems_tac ctxt max_facts =
    ignore_irrelevant_prems_core_tac ctxt max_facts NONE

  fun drop_irrelevant_prems_tac ctxt max_facts =
    drop_irrelevant_prems_core_tac ctxt max_facts NONE

  fun reduced_clarsimp ctxt max_facts dry_run =
    drop_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else CHANGED_PROP o clarsimp_tac ctxt)

  fun reduced_simp ctxt max_facts dry_run =
    drop_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else CHANGED_PROP o simp_tac ctxt)

  fun filtered_clarsimp ctxt max_facts dry_run =
    ignore_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else
      CHANGED_PROP o clarsimp_tac ctxt
      THEN_ALL_NEW (unignore_tac ctxt)
    )

  fun filtered_simp ctxt max_facts dry_run =
    ignore_irrelevant_prems_tac ctxt max_facts
    THEN' (if dry_run then K all_tac else
      CHANGED_PROP o simp_tac ctxt
      THEN_ALL_NEW (unignore_tac ctxt)
    )

  val _ = Theory.setup (Method.setup @{binding "rclarsimp"}
    (Method.sections Clasimp.clasimp_modifiers |-- (Scan.lift (Scan.optional (Parse.nat >> SOME) NONE --
                 Scan.optional (Args.$$$ "dry_run" >> (K true)) false)) >>
      (fn (max_facts_opt, dry_run) => fn ctxt => SIMPLE_METHOD (
      let
        val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
      in
        reduced_clarsimp ctxt max_facts dry_run 1
      end
    ))) "Apply clarsimp after reducing premises via MePo filter (unsafe)")

  val _ = Theory.setup (Method.setup @{binding "fclarsimp"}
    (Method.sections Clasimp.clasimp_modifiers |-- (Scan.lift (Scan.optional (Parse.nat >> SOME) NONE --
                 Scan.optional (Args.$$$ "dry_run" >> (K true)) false)) >>
      (fn (max_facts_opt, dry_run) => fn ctxt => SIMPLE_METHOD (
      let
        val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
      in
        filtered_clarsimp ctxt max_facts dry_run 1
      end
    ))) "Apply clarsimp after ignoring premises via MePo filter (safe)")

  val _ = Theory.setup (Method.setup @{binding "mepo_focus"}
    ((Scan.lift (Scan.optional (Parse.nat >> SOME) NONE --
                 Scan.optional (Args.$$$ "drop" >> (K true)) false)) >>
      (fn (max_facts_opt, drop) => fn ctxt => SIMPLE_METHOD (
      let
        val max_facts = Option.getOpt (max_facts_opt, Config.get ctxt Crush_Config.relevance_filter_max_facts)
      in
        if drop then
          drop_irrelevant_prems_tac ctxt max_facts 1
        else
          ignore_irrelevant_prems_tac ctxt max_facts 1
      end
    ))) "Drop or ignore premises deemed irrelevant according to MePo relevance filter")

  val _ = Theory.setup (Method.setup @{binding "mepo_unfocus"}
     (Scan.succeed (fn ctxt => SIMPLE_METHOD (unignore_tac ctxt 1)))
     "Recover premises previously ignored via mepo_focus")

end;
