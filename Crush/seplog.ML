(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Various separation logic tactics *)

(* Picker theorem infrastructure: generation, caching, and lookup *)

structure ASepconj_Pick_Thms = Theory_Data
 (type T = int -> int -> thm option
  val empty = K (K NONE)
  fun merge (a,b) i j = (case a i j of SOME x => SOME x | _ => b i j))

structure ASepconj_Rotate_Thms = Theory_Data
 (type T = int -> thm option
  val empty = K NONE
  fun merge (a,b) n = (case a n of SOME x => SOME x | _ => b n))

(* Records the pre-generation limit so that the chunk size for
   pick composition can be derived automatically. *)
structure ASepconj_Pick_Cache_Limit = Theory_Data
 (type T = int
  val empty = 0
  fun merge (a, b) = Int.max (a, b))

local
  fun register_asepconj_pick_thm thm n i =
    ASepconj_Pick_Thms.map (fn m => fn n' => fn i' => if n' = n andalso i=i' then SOME thm else m n' i')

  fun register_asepconj_rotate_thm thm n =
    ASepconj_Rotate_Thms.map (fn m => fn n' => if n' = n then SOME thm else m n')

  fun gen_varname idx = "\<alpha>" ^ (Int.toString idx)
  fun gen_asepconj_iter_str (idx :: idxs) =
     fold (fn i => fn s =>  s ^ " \<star> " ^ (gen_varname i)) idxs (gen_varname idx)
   | gen_asepconj_iter_str _ = ""

  fun gen_asepconj_iter ctxt idxs_lhs idxs_rhs =
      (gen_asepconj_iter_str idxs_lhs ^ " = " ^ gen_asepconj_iter_str idxs_rhs)
    |> Syntax.read_prop ctxt

  fun int_range i =
    let fun core _    0 acc = acc
          | core base i acc = core (base + 1) (i - 1) (acc @ [base])
    in core 0 i [] end

  exception ASEPCONJ_PICK_GEN

  fun drop_ith 0 (_ :: xs) = xs
    | drop_ith i (x :: xs) = x :: (drop_ith (i-1) xs)
    | drop_ith _ _ = raise ASEPCONJ_PICK_GEN
  fun float_ith i xs = List.nth (xs,i) :: (drop_ith i xs)
  fun rotate_list [] = []
    | rotate_list (x :: xs) = xs @ [x]

  val swap_top_meta = @{thm asepconj_swap_top} RS eq_reflection
  val comm_meta_prf = @{thm asepconj_comm} RS eq_reflection
  val assoc_meta_prf = @{thm asepconj_assoc} RS eq_reflection

  (* Conversion that picks element i to the front via repeated swap_top.
     Falls back to comm for 2-element conjunctions where swap_top doesn't match. *)
  fun pick_swap_conv 0 : conv = Conv.all_conv
    | pick_swap_conv i =
        Conv.arg_conv (pick_swap_conv (i - 1))
        then_conv (Conv.rewr_conv swap_top_meta else_conv Conv.rewr_conv comm_meta_prf)

  (* Deep flatten: apply assoc at top, then recurse into the right subtree. *)
  fun deep_flatten_conv (ct : cterm) =
    ((Conv.rewr_conv assoc_meta_prf then_conv Conv.arg_conv deep_flatten_conv) ct
     handle CTERM _ => Conv.all_conv ct)

  (* Conversion that rotates by 1: comm + deep flatten. *)
  val rotate_conv : conv =
    Conv.rewr_conv comm_meta_prf then_conv deep_flatten_conv

  (* Rewrite the LHS of an object equality inside Trueprop. *)
  fun lhs_conv (c : conv) : conv =
    Conv.arg_conv (Conv.fun_conv (Conv.arg_conv c))

  fun prove_asepconj_pick_ith_from_n ctxt n i : thm =
    let
      val names = List.tabulate (n, gen_varname)
      val prop = gen_asepconj_iter ctxt (int_range n) (float_ith i (int_range n))
    in
      Goal.prove ctxt names [] prop
        (fn {context, ...} =>
          CONVERSION (lhs_conv (pick_swap_conv i)) 1
          THEN resolve_tac context [@{thm refl}] 1)
    end

  fun prove_asepconj_rotate_nfold ctxt n : thm =
    let
      val names = List.tabulate (n, gen_varname)
      val prop = gen_asepconj_iter ctxt (int_range n) (rotate_list (int_range n))
    in
      Goal.prove ctxt names [] prop
        (fn {context, ...} =>
          (if n <= 1 then all_tac
           else CONVERSION (lhs_conv rotate_conv) 1)
          THEN resolve_tac context [@{thm refl}] 1)
    end

  fun register_pick_thm i n thm ctxt = ctxt
     |> Local_Theory.note ((Binding.empty, @{attributes [asepconj_pick_thms]}), [thm]) |> snd
     |> (register_asepconj_pick_thm thm n i |> Local_Theory.background_theory)

  fun register_rotate_thm n thm ctxt = ctxt
     |> Local_Theory.note ((Binding.empty, @{attributes [asepconj_rotate_thms]}), [thm]) |> snd
     |> (register_asepconj_rotate_thm thm n |> Local_Theory.background_theory)

  fun prove_register_asepconj_pick_ith_from_n ctxt n i =
    register_pick_thm i n (prove_asepconj_pick_ith_from_n ctxt n i) ctxt

  fun prove_register_asepconj_rotate_nfold ctxt n =
    register_rotate_thm n (prove_asepconj_rotate_nfold ctxt n) ctxt

  fun prove_register_asepconj_pick_from_n n ctxt =
    let val idxs = if n = 1 then [0] else [n-2, n-1] in
    fold (fn i => fn c => prove_register_asepconj_pick_ith_from_n c n i) idxs ctxt end
in
  fun prove_register_asepconj_pick_upto n ctxt =
    fold (fn i => fn c => prove_register_asepconj_pick_from_n (i+1) c) (int_range n) ctxt
    |> Local_Theory.background_theory (ASepconj_Pick_Cache_Limit.put n)

  fun prove_register_asepconj_rotate_upto n ctxt =
    fold (fn i => fn c => prove_register_asepconj_rotate_nfold c (i+1)) (int_range n) ctxt

  (* Look up a cached picker theorem. For indices beyond the cache,
     use the chunked composition in asepconj_pick_conv instead. *)
  fun get_asepconj_pick_ith_from_n ctxt n i : thm =
    let val n = if i+1 < n then i+2 else i+1 in
    (case ASepconj_Pick_Thms.get (Proof_Context.theory_of ctxt) n i of
      NONE => error ("No cached picker theorem for ("
                     ^ Int.toString n ^ "," ^ Int.toString i ^ "). "
                     ^ "Use asepconj_pick_conv for indices beyond the pre-generation limit.")
     | SOME t => t) end

  fun get_asepconj_rotate ctxt n : thm =
    (case ASepconj_Rotate_Thms.get (Proof_Context.theory_of ctxt) n of
      NONE => error ("No cached rotation theorem for n="
                     ^ Int.toString n ^ ".")
     | SOME t => t)
end

(* Hoist-existential theorem infrastructure: generation, caching, and lookup.

   Two families of hoist theorems, analogous to the two picker families (last / non-last):

   "With-tail" hoist at position i (the \<Squnion> is not the last element):
     \<beta>0 \<star> ... \<star> \<beta>i-1 \<star> (\<Squnion>x. \<phi> x) \<star> \<psi> = (\<Squnion>x. \<beta>0 \<star> ... \<star> \<beta>i-1 \<star> \<phi> x \<star> \<psi>)

   "Tail" hoist at position i (the \<Squnion> is the last element):
     \<beta>0 \<star> ... \<star> \<beta>i-1 \<star> (\<Squnion>x. \<phi> x) = (\<Squnion>x. \<beta>0 \<star> ... \<star> \<beta>i-1 \<star> \<phi> x)

   Position 0 with-tail is just asepconj_Inf_distrib.
   Position 0 tail is just asepconj_Inf_distrib_right (on a 2-element conjunction).

   For the chunked composition beyond the cache limit, we need both families,
   just as the picker needs both pick(n, n-2) and pick(n, n-1). *)

structure ASepconj_Hoist_Thms = Theory_Data
 (type T = int -> thm option
  val empty = K NONE
  fun merge (a,b) i = (case a i of SOME x => SOME x | _ => b i))

structure ASepconj_Hoist_Tail_Thms = Theory_Data
 (type T = int -> thm option
  val empty = K NONE
  fun merge (a,b) i = (case a i of SOME x => SOME x | _ => b i))

structure ASepconj_Hoist_Cache_Limit = Theory_Data
 (type T = int
  val empty = 0
  fun merge (a, b) = Int.max (a, b))


local
  fun int_range' i =
    let fun core _    0 acc = acc
          | core base i acc = core (base + 1) (i - 1) (acc @ [base])
    in core 0 i [] end

  val distrib_meta = @{thm asepconj_Inf_distrib} RS eq_reflection
  val distrib_right_meta = @{thm asepconj_Inf_distrib_right} RS eq_reflection

  (* Conversion for proving with-tail hoist theorems:
     Descend i levels, apply distrib, bubble up with distrib_right. *)
  fun hoist_at_conv 0 : conv = Conv.rewr_conv distrib_meta
    | hoist_at_conv i =
        Conv.arg_conv (hoist_at_conv (i - 1))
        then_conv Conv.rewr_conv distrib_right_meta

  (* Conversion for proving tail hoist theorems:
     Descend i levels, apply distrib_right (last element), bubble up. *)
  fun hoist_tail_conv 0 : conv = Conv.rewr_conv distrib_right_meta
    | hoist_tail_conv i =
        Conv.arg_conv (hoist_tail_conv (i - 1))
        then_conv Conv.rewr_conv distrib_right_meta

  (* Rewrite the LHS of an object equality inside Trueprop. *)
  fun hoist_lhs_conv (c : conv) : conv =
    Conv.arg_conv (Conv.fun_conv (Conv.arg_conv c))

  fun gen_hoist_varname idx = "\<beta>" ^ (Int.toString idx)

  (* With-tail: \<beta>0 \<star> ... \<star> \<beta>i-1 \<star> (\<Squnion>x. \<phi> x) \<star> \<psi> = (\<Squnion>x. \<beta>0 \<star> ... \<star> \<beta>i-1 \<star> \<phi> x \<star> \<psi>) *)
  fun prove_asepconj_hoist_at ctxt i : thm =
    let
      val alpha_names = List.tabulate (i, gen_hoist_varname)
      val phi_name = "\<phi>"
      val psi_name = "\<psi>"
      val all_names = alpha_names @ [phi_name, psi_name]

      val alphas = String.concatWith " \<star> " (List.tabulate (i, gen_hoist_varname))
      val lhs_core = "(\<Squnion>x. " ^ phi_name ^ " x) \<star> " ^ psi_name
      val lhs = if i = 0 then lhs_core
                else alphas ^ " \<star> " ^ lhs_core
      val rhs_core = phi_name ^ " x \<star> " ^ psi_name
      val rhs_inner = if i = 0 then rhs_core
                      else alphas ^ " \<star> " ^ rhs_core
      val rhs = "(\<Squnion>x. " ^ rhs_inner ^ ")"
      val prop_str = lhs ^ " = " ^ rhs
      val prop = Syntax.read_prop ctxt prop_str
    in
      Goal.prove ctxt all_names [] prop
        (fn {context, ...} =>
          CONVERSION (hoist_lhs_conv (hoist_at_conv i)) 1
          THEN resolve_tac context [@{thm refl}] 1)
    end

  (* Tail: \<beta>0 \<star> ... \<star> \<beta>i \<star> (\<Squnion>x. \<phi> x) = (\<Squnion>x. \<beta>0 \<star> ... \<star> \<beta>i \<star> \<phi> x)
     Note: position here means the number of leading elements before the \<Squnion>.
     So tail hoist at position i has i+1 leading betas (\<beta>0..\<beta>i). *)
  fun prove_asepconj_hoist_tail ctxt i : thm =
    let
      val n = i + 1  (* number of leading elements *)
      val alpha_names = List.tabulate (n, gen_hoist_varname)
      val phi_name = "\<phi>"
      val all_names = alpha_names @ [phi_name]

      val alphas = String.concatWith " \<star> " (List.tabulate (n, gen_hoist_varname))
      val lhs = alphas ^ " \<star> (\<Squnion>x. " ^ phi_name ^ " x)"
      val rhs_inner = alphas ^ " \<star> " ^ phi_name ^ " x"
      val rhs = "(\<Squnion>x. " ^ rhs_inner ^ ")"
      val prop_str = lhs ^ " = " ^ rhs
      val prop = Syntax.read_prop ctxt prop_str
    in
      Goal.prove ctxt all_names [] prop
        (fn {context, ...} =>
          CONVERSION (hoist_lhs_conv (hoist_tail_conv i)) 1
          THEN resolve_tac context [@{thm refl}] 1)
    end

  fun register_hoist_thm i thm ctxt = ctxt
     |> (ASepconj_Hoist_Thms.map (fn m => fn i' =>
          if i' = i then SOME thm else m i') |> Local_Theory.background_theory)

  fun register_hoist_tail_thm i thm ctxt = ctxt
     |> (ASepconj_Hoist_Tail_Thms.map (fn m => fn i' =>
          if i' = i then SOME thm else m i') |> Local_Theory.background_theory)

  fun prove_register_asepconj_hoist_at ctxt i =
    register_hoist_thm i (prove_asepconj_hoist_at ctxt i) ctxt

  fun prove_register_asepconj_hoist_tail ctxt i =
    register_hoist_tail_thm i (prove_asepconj_hoist_tail ctxt i) ctxt
in
  fun prove_register_asepconj_hoist_upto n ctxt =
    ctxt
    |> fold (fn i => fn c => prove_register_asepconj_hoist_at c i) (int_range' n)
    |> fold (fn i => fn c => prove_register_asepconj_hoist_tail c i) (int_range' n)
    |> Local_Theory.background_theory (ASepconj_Hoist_Cache_Limit.put n)

  fun get_asepconj_hoist_at ctxt i : thm =
    (case ASepconj_Hoist_Thms.get (Proof_Context.theory_of ctxt) i of
      NONE => error ("No cached with-tail hoist theorem for position "
                     ^ Int.toString i ^ ".")
     | SOME t => t)

  fun get_asepconj_hoist_tail ctxt i : thm =
    (case ASepconj_Hoist_Tail_Thms.get (Proof_Context.theory_of ctxt) i of
      NONE => error ("No cached tail hoist theorem for position "
                     ^ Int.toString i ^ ".")
     | SOME t => t)
end

signature SEPARATION_LOGIC_TACTICS =
sig

  exception SeparationLogic of string

  \<comment> \<open>Boolean helpers to detect goals and terms of a particular shape.\<close>

  val is_entailment    : term -> bool
  val is_wp_entailment : term -> bool
  val is_wp_call       : term -> bool
  val is_ucincl        : term -> bool
  val is_points_to     : term -> bool
  val is_points_to_raw : term -> bool

  val find_wp_call_function : term -> string option

  (* Like is_ucincl, but also detects HOL conjunctions of ucincl conditions *)
  val is_ucincl'       : term -> bool

  \<comment> \<open>Helpers to destruct goals and terms of a particular shape.
     They all raise the \<^verbatim>\<open>SeparationLogic\<close> exception if the given term
     is not of the expected shape.\<close>

  \<comment>\<open>Destruct raw points_to relation, returning ref, share and global value.\<close>
  val dest_points_to_raw : term -> (term * term * term)
  \<comment>\<open>Destruct raw points_to relation, returning ref, share, global and local value.\<close>
  val dest_points_to : term -> (term * term * term * term)
  \<comment>\<open>Destructs iterated separating conjunction, returning multiset of assertions.\<close>
  val dest_asepconj_multi : term -> term
  \<comment>\<open>Destruct mapped multiset, returning mapping and indexing multiset.\<close>
  val dest_mapped_multiset : term -> (term * term)
  \<comment>\<open>Destruct iterated separating conjunction constructed from mapped multiset
     of assertions.\<close>
  val dest_asepconj_multi_mapped : term -> (term * term)

  val specialize_split_rule_to_wp_single: Proof.context -> thm -> thm
  val specialize_split_rule_to_wp: Proof.context -> thm list -> thm list
  val specialize_split_rule_to_wp_attribute : attribute

  \<comment> \<open>Basic transformation tactics for separating entailments\<close>

  \<comment> \<open>Rotate the components of separating conjunction appearing in a goal's assumptions\<close>
  val aentails_rotate_assms_tac : Proof.context -> int -> tactic
  \<comment> \<open>Rotate the components of separating conjunction appearing in a goal's conclusion\<close>
  val aentails_rotate_concls_tac : Proof.context -> int -> tactic

  \<comment> \<open>Move a spatial assumption in a separating conjunction on the left side of an entailment
      to the leftmost position.\<close>
  val aentails_pick_assms_tac : int -> Proof.context -> int -> tactic
  val aentails_pick_assms_tac_ext : int -> int -> Proof.context -> int -> tactic
  \<comment> \<open>Move a spatial assumption in a separating conjunction on the right side of an entailment
      to the leftmost position.\<close>
  val aentails_pick_concls_tac : int -> Proof.context -> int -> tactic
  val aentails_pick_concls_tac_ext : int -> int -> Proof.context -> int -> tactic

  \<comment> \<open>Normalize associativity of spatial assumptions / conclusions\<close>
  val aentails_normalize_assoc_assms_tac : Proof.context -> int -> tactic
  val aentails_normalize_assoc_concls_tac : Proof.context -> int -> tactic
  val aentails_normalize_assoc_tac : Proof.context -> int -> tactic

  val aentails_joinfirst_assms_tac : int -> Proof.context -> int -> tactic
  val aentails_joinfirst_concls_tac : int -> Proof.context -> int -> tactic

  val aentails_float_assms_tac : term list -> Proof.context -> int -> tactic
  val aentails_float_drule_assms_tac : thm -> Proof.context -> int -> tactic

  val aentails_drule_tac_single :  thm -> Proof.context -> int -> tactic
  val aentails_drule_tac : thm list -> Proof.context -> int -> tactic
  val aentails_cond_drule_tac : thm list -> Proof.context -> int -> tactic

  val aentails_float_assms_concls_tac : term list -> term list -> Proof.context -> int -> tactic
  val aentails_float_crule_tac : thm -> Proof.context -> int -> tactic

  val aentails_crule_tac_single :  thm -> Proof.context -> int -> tactic
  val aentails_crule_tac : thm list -> Proof.context -> int -> tactic
  val aentails_cond_crule_tac : thm list -> Proof.context -> int -> tactic

  val aentails_float_concls_tac : term list -> Proof.context -> int -> tactic
  val aentails_float_rule_concls_tac : thm -> Proof.context -> int -> tactic

  val aentails_rule_tac_single : thm -> Proof.context -> int -> tactic
  val aentails_rule_tac : thm list -> Proof.context -> int -> tactic
  val aentails_cond_rule_tac : thm list -> Proof.context -> int -> tactic

  \<comment> \<open>Moves pure assumptions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_pure_assms_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves pure conclusions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_pure_concls_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves pure assumptions in a separating entailment to the leftmost position(s);
      backtracking version floating one component at a time\<close>
  val aentails_float_pure_assms_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves pure conclusions in a separating entailment to the leftmost position(s);
      backtracking version floating one component at a time\<close>
  val aentails_float_pure_concls_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves pure assumptions and conclusions in a separating entailment to the left most position(s)\<close>
  val aentails_float_pure_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves typed points_to assumptions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_points_to_assms_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves typed points_to assumptions in a separating entailment to the leftmost position(s);
      backtracking version floating one component a time.\<close>
  val aentails_float_points_to_assms_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves raw points_to assumptions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_points_to_raw_assms_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves raw points_to assumptions in a separating entailment to the leftmost position(s);
      backtracking version floating one component a time.\<close>
  val aentails_float_points_to_raw_assms_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves typed points_to conclusions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_points_to_concls_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves typed points_to conclusions in a separating entailment to the leftmost position(s);
      backtracking version floating one component a time.\<close>
  val aentails_float_points_to_concls_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves raw points_to conclusions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_points_to_raw_concls_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves raw points_to conclusions in a separating entailment to the leftmost position(s);
      backtracking version floating one component a time.\<close>
  val aentails_float_points_to_raw_concls_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves iterated separating conjunction assumptions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_multi_assms_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves iterated separating conjunction conclusions in a separating entailment to the leftmost position(s)\<close>
  val aentails_float_multi_concls_tac : Proof.context -> int -> tactic
  \<comment> \<open>Moves iterated separating conjunction assumptions in a separating entailment to the leftmost position(s);
      backtracking version, moving one component a time.\<close>
  val aentails_float_multi_assms_tac' : Proof.context -> int -> tactic
  \<comment> \<open>Moves iterated separating conjunction conclusions in a separating entailment to the leftmost position(s);
      backtracking version, moving one component a time.\<close>
  val aentails_float_multi_concls_tac' : Proof.context -> int -> tactic

  val aentails_hoist_pure_assms_tac : Proof.context -> int -> tactic
  val aentails_hoist_pure_concls_tac : Proof.context -> int -> tactic
  \<comment>\<open>Hoist \<Squnion>(range ...) out of the LHS of an entailment, then intro \<^verbatim>\<open>aexists_entailsL\<close>.\<close>
  val aentails_hoist_existential_assms_tac : Proof.context -> int -> tactic
  val aentails_simp_core_intro_others_tac : Proof.context -> int -> tactic
  val aentails_simp_core_cancel_univ_prems : Proof.context -> int -> tactic

  val aentails_simp_core_tac : Proof.context -> int -> tactic

  \<comment> \<open>Cancellation tactics\<close>

  \<comment> \<open>Find a pair of separating assumption and conclusion passing the given filter function, and
      float them both to the top. This should be used in conjunction with the application of dedicated
      theorems handling the particular shape of assumption/conclusion -- see e.g. \<^verbatim>\<open>aentails_cancel_tac\<close>.\<close>
  val aentails_float_match : Proof.context -> (term -> term -> bool) -> int -> tactic
  \<comment> \<open>Find a pair of iterated separating conjunctions \<^verbatim>\<open>\<star>\<star>{# \<xi> . m #}\<close> and \<^verbatim>\<open>\<star>\<star>{# \<xi> . m' #}\<close>, and float
      them to the top.\<close>
  val aentails_float_matching_iterated_asepconj : Proof.context -> int -> tactic
  \<comment> \<open>Identifies pairs of \<^verbatim>\<open>points_to_raw\<close> relations with matching reference and share, and floats
      them to the top.\<close>
  val asepconj_match_float_points_to_raw_tac : Proof.context -> int -> tactic
  \<comment> \<open>Identifies pairs of \<^verbatim>\<open>points_to\<close> relations with matching reference and share, and floats
      them to the top.\<close>
  val asepconj_match_float_points_to_tac : Proof.context -> int -> tactic
  \<comment> \<open>Identifies unifiable pairs of separating assumptions and conclusions in a separating
      entailment, and cancels them.
      This is essentially \<^verbatim>\<open>float_match\<close> for \<^verbatim>\<open>is_unifiable_pair\<close>, plus a cancellation lemma.\<close>
  val aentails_cancel_core_tac : Proof.context -> int -> tactic
  \<comment> \<open>Identifies and cancels matching pairs of iterated separating conjunctions.\<close>
  val aentails_cancel_asepconj_multi: Proof.context -> int -> tactic
  \<comment> \<open>Identifies pairs of separating assumptions and conclusions which are both applications of the
      same partially injective function and where the jointly injective arguments are unifiable.
      If such pair exists, it's floated to the top and cancelled, leaving the caller with two goals.
      The tactic then needs to be paired with some goal-specific tactic for solving the split-off
      entailment.

      The first argument detects the head of the injective function to be considered.
      The second argument is the list of indices of the jointly injective arguments.

      An example says more than 1000 words: To cancel points_to relations with the same reference,
      but potentially different share and value, one would pass as the filter something that detects
      points_to, and [0] as the index list.\<close>
  val aentails_cancel_injective: (term -> bool) -> int list -> Proof.context -> int -> tactic

  val aentails_cancel_tac : Proof.context -> int -> tactic

  \<comment> \<open>Utility functions\<close>

  \<comment> \<open>Lookup a theorem by name\<close>
  val lookup_thm: Proof.context -> string -> thm

  \<comment> \<open>Finds \<^typ>\<open>'a\<close> in the type \<^typ>\<open>'a set\<close>, otherwise throws an exception\<close>
  val set_instantiation : Proof.context -> typ -> typ
  \<comment> \<open>Splits a term of the form \<^term>\<open>\<phi> \<star> \<psi>\<close> into its constituent subparts\<close>
  val split_asepconj : term -> term list
  \<comment> \<open>Makes a separating conjunction from a list of formulae\<close>
  val mk_asepconj : term list -> term

  \<comment> \<open>Filters out schematic variables ("metavariables") from the input list.\<close>
  val filter_metavariables : term list -> term list

  \<comment> \<open>Unification helpers\<close>

  \<comment> \<open>Returns the index of the first term appearing in the input term list that unifies with the
      given term.  Returns \<^verbatim>\<open>NONE\<close> if no such term exists.\<close>
  val find_unifiable_term : Proof.context -> term ->  term list -> int option
  \<comment> \<open>Given two lists of terms, find a pair of entries which unify and return their indices.
      Returns \<^verbatim>\<open>NONE\<close> if no such pair exists.\<close>
  val find_unifiable_term2 : Proof.context -> term list -> term list -> (int * int) option
  \<comment> \<open>Given a context and two terms, determines whether they are unifiable or not.\<close>
  val is_unifiable_pair : Proof.context -> term -> term -> bool

  \<comment> \<open>Given goal in the shape of a separating entailment, find pairs of assumption and assertion satisfying
      a given predicate. Returns the pair of indices on success, or \<^term>\<open>None\<close> otherwise.\<close>
  val find_match : term (* goal *) -> (term -> term -> bool) (* filter *) -> (int * int) option

  \<comment> \<open>Automatic / Assisted discharge of \<^verbatim>\<open>ucincl\<close> conditions.\<close>

  \<comment>\<open>Start a \<^verbatim>\<open>ucincl\<close>-proof for a contract with the provided name.\<close>
  val ucincl_contract_proof : string -> Proof.context -> Proof.state
  \<comment>\<open>Try to fully automatically conduct a \<^verbatim>\<open>ucincl\<close>-proof for a contract with the provided name.\<close>
  val ucincl_contract_auto : string -> Proof.context -> Proof.context
  \<comment>\<open>Start a \<^verbatim>\<open>ucincl\<close>-proof for an assertion-valued function with the provided name.\<close>
  val ucincl_assertion_proof : string -> Proof.context -> Proof.state
  \<comment>\<open>Try to fully automatically conduct a \<^verbatim>\<open>ucincl\<close>-proof for an assertion-valued function with the provided name.\<close>
  val ucincl_assertion_auto : string -> Proof.context -> Proof.context

  val ucincl_solve_tac : Proof.context -> int -> tactic
  val ucincl_discharge_tac : Proof.context -> (int -> tactic) -> (int -> tactic)
  val ucincl_discharge_tac' : (Proof.context -> int -> tactic) -> (Proof.context -> int -> tactic)
  val ucincl_must_discharge_tac : Proof.context -> (int -> tactic) -> (int -> tactic)
  val ucincl_must_discharge_tac' : (Proof.context -> int -> tactic) -> (Proof.context -> int -> tactic)

  val ucincl_discharge_method : Method.method -> Method.method

  \<comment> \<open>Solves the first goal if it is an equality between permuted separating conjunctions\<close>
  val asepconj_solve_eq_tac : Proof.context -> int -> tactic

  \<comment>\<open>More flexible but deprecated approach to permuting separting conjunctions:
     Build desired permutation equality by hand and pass it to the simplifier.
     This is very flexible and easy to use, but tends to generate a lot of flex-flex
     pairs, and moreover does not make use of the fact that we usually know exactly
     how separating conjunctions ought to be permuted.\<close>

  \<comment> \<open>Generic tactic for transforming the assumption of a separation logic entailment\<close>
  val aentails_transform_assms_tac : (term -> term) -> Proof.context -> int -> tactic
  \<comment> \<open>Generic tactic for transforming the conclusion of a separation logic entailment\<close>
  val aentails_transform_concls_tac : (term -> term) -> Proof.context -> int -> tactic

  \<comment> \<open>Generic tactic for transforming the assumption of a separation logic entailment;
      suitable for backtracking if permutation function returns more than one element.\<close>
  val aentails_transform_assms_tac' : (term -> term list) -> Proof.context -> int -> tactic
  \<comment> \<open>Generic tactic for transforming the conclusion of a separation logic entailment;
      suitable for backtracking if permutation function returns more than one element.\<close>
  val aentails_transform_concls_tac' : (term -> term list) -> Proof.context -> int -> tactic

  val matching_injective_assertion: Proof.context ->
      (term -> bool) -> int list -> term -> term -> bool
  val dest_assertion: (term -> bool) -> int list -> term -> term list option

  \<comment>\<open>Useful pre-baked permutations on separating conjunctions that can be used with
      \<^verbatim>\<open>aentails_transform_assms_tac\<close> and \<^verbatim>\<open>aentails_transform_concls_tac\<close>.\<close>
  structure Permutation :
  sig
    \<comment> \<open>Rotate a separating conjunction one place to the right\<close>
    val rotate : term -> term
    \<comment> \<open>Pick a formula from a separating conjunction (at an index) and move it to the leftmost
        position within the conjunction\<close>
    val pick   : int -> term -> term
    \<comment> \<open>Partition the components of a separating conjunction according to a filter function:
        Components returning \<^term>\<open>True\<close> are moved to the left, others to the right.\<close>
    val partition : (term -> bool) -> term -> term
    \<comment> \<open>Identify components in a separating conjunction matching filter function, and return
        the list of terms obtained by rotating exactly one-a-time to the left.\<close>
    val pickany : (term -> bool) -> term -> term list
    \<comment> \<open>Transform \<^verbatim>\<open>\<xi>\<^sub>1 \<star> \<xi>\<^sub>2 \<star> _ \<star> \<xi>\<^sub>n\<close> into \<^verbatim>\<open>(\<xi>\<^sub>1 \<star> _ \<xi>\<^sub>i) \<star> \<xi>\<^sub>i\<^sub>+\<^sub>1 \<star> _ \<star> \<xi>\<^sub>n\<close>\<close>
    val joinfirst : int -> term -> term
  end


  \<comment>\<open>Apply separate conversions to the premise and conclusion of a separating entailment\<close>
  val aentails_conv_core : conv -> conv -> conv

  \<comment>\<open>Apply separate conversions to the premise and conclusion of a separating entailment
     turned into a Pure proposition via \<^term>\<open>Trueprop\<close>\<close>
  val aentails_conv : conv -> conv -> conv

  \<comment>\<open>Apply separate conversions to the premise and conclusion of a separating entailment
     turned into a Pure proposition via \<^term>\<open>Trueprop\<close>. Strip pure universal quantification
     and premises first, if present.\<close>
  \<comment>\<open>Warning: The inner conversions don't take a context argument hence cannot know about
     bound variables. If you need to introduce/move bound variables, use \<^verbatim>\<open>aentails_conv''\<close>.\<close>
  val aentails_conv' : conv -> conv -> Proof.context -> conv

  val aentails_conv'' : (Proof.context -> conv) -> (Proof.context -> conv) -> Proof.context -> conv

  \<comment>\<open>Apply conversion to uRust argument in weakest precondition goal. Strip pure universal
     quantification and premises first, if present.\<close>
  val aentails_wp_conv' : conv -> Proof.context -> conv
  \<comment>\<open>Rewrite uRust expression in a WP goal according to a (pure or meta) equality\<close>
  val aentails_wp_rewrite_tac : thm -> Proof.context -> int -> tactic

  \<comment>\<open>Given a separating conjunction, return the generic rotation theorem
     that will apply to it.\<close>
  val get_rotate_thm : Proof.context -> cterm -> thm

  \<comment>\<open>A conversion for rotating separating conjunctions.\<close>
  val asepconj_rotate_conv : Proof.context -> conv

  \<comment>\<open>Conversions for rotating premises/conclusions of separating entailments\<close>
  val aentails_rotate_assms_conv : Proof.context -> conv
  val aentails_rotate_concls_conv : Proof.context -> conv

  \<comment>\<open>A conversion picking the i-th element from a separating conjunction of n elements.\<close>
  val asepconj_pick_conv : Proof.context -> int -> int -> conv
  \<comment>\<open>Conversions for picking the i-th element from the premises/conclusions of separating entailments.\<close>
  val aentails_pick_assm_conv : Proof.context -> int -> int -> conv
  val aentails_pick_concl_conv : Proof.context -> int -> int -> conv

  \<comment>\<open>A conversion for transforming \<^verbatim>\<open>\<xi>\<^sub>1 \<star> \<xi>\<^sub>2 \<star> _ \<star> \<xi>\<^sub>n\<close> into \<^verbatim>\<open>(\<xi>\<^sub>1 \<star> _ \<xi>\<^sub>i) \<star> \<xi>\<^sub>i\<^sub>+\<^sub>1 \<star> _ \<star> \<xi>\<^sub>n\<close>\<close>
  val asepconj_joinfirst_conv : Proof.context -> int -> int -> conv
  val aentails_joinfirst_assm_conv : Proof.context -> int -> int -> conv
  val aentails_joinfirst_concl_conv : Proof.context -> int -> int -> conv

  \<comment>\<open>Given a separating conjunction and a filter function on terms, return the list of
    0-based indices of those components which pass the filter.\<close>
  val asepconj_filter_idxs : term -> (term -> bool) -> int list

  \<comment>\<open>Conversions floating multiple components in a separating conjunction to the left.
     The index list provided here must be ascending and can be constructed via
     \<^verbatim>\<open>asepconj_filter_idxs\<close>, for example.\<close>
  val asepconj_pick_many_conv : Proof.context -> int -> int list -> conv
  val aentails_pick_many_assm_conv : Proof.context -> int -> int list -> conv
  val aentails_pick_many_concl_conv : Proof.context -> int -> int list -> conv

  val aentails_pick_many_assms_tac: int list -> Proof.context -> int -> tactic

  \<comment>\<open>Convenience wrappers inferring the number \<^verbatim>\<open>n\<close> of separating components.\<close>
  val asepconj_pick_conv' : Proof.context -> int -> conv
  val asepconj_pick_many_conv' : Proof.context -> int list -> conv
  val asepconj_joinfirst_conv' : Proof.context -> int -> conv
  val aentails_pick_assm_conv' : Proof.context -> int -> conv
  val aentails_pick_concl_conv' : Proof.context -> int -> conv
  val aentails_pick_many_assm_conv' : Proof.context -> int list -> conv
  val aentails_pick_many_concl_conv' : Proof.context -> int list -> conv
  val aentails_joinfirst_assm_conv' : Proof.context -> int -> conv
  val aentails_joinfirst_concl_conv' : Proof.context -> int -> conv

  \<comment>\<open>Apply separate conversions to the LHS and RHS of a separating conjunction\<close>
  val asepconj_conv' : conv -> conv -> conv
  \<comment>\<open>Apply a conversion to the RHS of a separating conjunction\<close>
  val asepconj_conv_right : conv -> conv
  \<comment>\<open>Apply a conversion to the LHS of a separating conjunction\<close>
  val asepconj_conv_left : conv -> conv

  \<comment>\<open>Hoist \<Squnion> at position i (with tail) out of a right-associated separating conjunction.
     Uses cached theorems for small i, chunked composition for large i.\<close>
  val asepconj_hoist_conv : Proof.context -> int -> conv
  \<comment>\<open>Hoist \<Squnion> at the last position i out of a right-associated separating conjunction.\<close>
  val asepconj_hoist_tail_conv : Proof.context -> int -> conv
  \<comment>\<open>Hoist all \<Squnion>(range ...) out of a right-associated separating conjunction.
     Dispatches between the pre-generated and 4-ary tree approaches based
     on the chain length.  The switchover threshold defaults to 300 and
     is configurable via \<^verbatim>\<open>crush_hoist_existential_tree_threshold\<close>.\<close>
  val asepconj_hoist_existential_conv : Proof.context -> conv
  \<comment>\<open>Pre-generated variant: walks the right spine and applies hoist at each
     \<Squnion> component. O(N) when all positions are within the cached range;
     O(N^2/L) otherwise, where L is the cache limit.\<close>
  val asepconj_hoist_existential_pregen_conv : Proof.context -> conv
  \<comment>\<open>Hoist all \<Squnion>(range ...) out of a right-associated separating conjunction,
     by rebalancing into a binary tree of depth O(log N), distributing bottom-up,
     and re-flattening. Asymptotically O(N log N) independent of the cache limit,
     but with higher constants than the pre-generated variant for small N.\<close>
  val asepconj_hoist_existential_tree_conv : Proof.context -> conv
  \<comment>\<open>Same as above, but using a 4-ary tree (depth O(log_4 N)).
     Fewer binder-descent levels during the merge phase, but up to 4
     distrib rewrites per node instead of 2.  Uses 4-ary distrib theorems
     (\<^verbatim>\<open>asepconj_Inf_distrib4_1\<close> through \<^verbatim>\<open>_4\<close>) plus 2/3-ary variants.\<close>
  val asepconj_hoist_existential_tree4_conv : Proof.context -> conv
  \<comment>\<open>Re-associate a right-associated \<star>-chain of \<^verbatim>\<open>n\<close> elements into a balanced binary tree.\<close>
  val asepconj_balance_conv : int -> conv

  \<comment>\<open>Conversion normalizing the bracketing of a separating conjunction to the right.\<close>
  val asepconj_assoc_normalize_conv : conv
  \<comment>\<open>Conversions normalizing the bracketing of premises/conclusions in a separating  entailment.\<close>
  val aentails_assoc_normalize_assms_conv : Proof.context -> conv
  val aentails_assoc_normalize_concls_conv : Proof.context -> conv
  val aentails_assoc_normalize_conv : Proof.context -> conv

  \<comment>\<open>Apply a conversion to every conclusion in an (n-fold) separating conjunction; if the term is not
     a separating conjunction, just apply the conversion.\<close>
  val asepconj_conv : conv -> conv

  \<comment>\<open>Apply separate conversions to pure and spatial premises and conclusions in the current goal.
     If the goal is not a separating entailment, \<^verbatim>\<open>concls\<close> is applied to the entire pure conclusion,
     and \<^verbatim>\<open>prems\<close> is only applied to the pure assumptions.\<close>
  val prems_concls_conv : (Proof.context -> conv) -> (Proof.context -> conv) -> (Proof.context -> conv)

  val simp_prems_conv : thm list -> Proof.context -> conv
  val simp_concls_conv : thm list -> Proof.context -> conv

  val aentails_simp_prems_conv : thm list -> Proof.context -> conv
  val aentails_simp_concls_conv : thm list -> Proof.context -> conv

  val simp_prems_tac : thm list -> Proof.context -> int -> tactic
  val simp_concls_tac : thm list -> Proof.context -> int -> tactic

  val aentails_simp_prems_tac : thm list -> Proof.context -> int -> tactic
  val aentails_simp_concls_tac : thm list -> Proof.context -> int -> tactic

  val unfold_prems_tac : thm list -> Proof.context -> int -> tactic

  val aentails_hoist_is_sat_tac: Proof.context -> int -> tactic

  val dest_spec_fun_full: term -> term * term
  val dest_spec_fun: term -> term
  val dest_spec_fun_str: term -> string

  val is_schematic_spec: thm -> bool

  val is_asepconj: term -> bool

  \<comment>\<open>SSA normalization for uRust expressions in WP goal\<close>
  val aentails_wp_ssa_normalize_tac : Proof.context -> int -> tactic
end

structure Separation_Logic_Tactics : SEPARATION_LOGIC_TACTICS =
struct

  fun specialize_split_rule_to_wp_single ctxt t =
     Rule_Insts.of_rule ctxt ([SOME "\<lambda>e. _ \<longlongrightarrow> \<W>\<P> _ e _ _ _"], []) [] t
     handle ERROR _ =>
       ([Pretty.str "Theorem ", Syntax.pretty_term ctxt (Thm.prop_of t),
        Pretty.str " not of the expected format. Ignoring."] |> Pretty.block |>
        Pretty.string_of |> Output.warning; t)

  fun specialize_split_rule_to_wp ctxt = List.map (specialize_split_rule_to_wp_single ctxt)

  val specialize_split_rule_to_wp_attribute =
     Thm.rule_attribute [] (fn context => specialize_split_rule_to_wp_single (Context.proof_of context))

  val aentails_prem_cong : thm = @{lemma \<open>\<phi> = \<phi>' \<Longrightarrow> \<phi> \<longlongrightarrow> \<xi> \<Longrightarrow> \<phi>' \<longlongrightarrow> \<xi>\<close> by simp}
  val aentails_concl_cong: thm = @{lemma \<open>\<phi> = \<phi>' \<Longrightarrow> \<xi> \<longlongrightarrow> \<phi> \<Longrightarrow> \<xi> \<longlongrightarrow> \<phi>'\<close> by simp}

  val aentails_drule_core : thm = @{lemma \<open>\<alpha> \<longlongrightarrow> \<beta> \<Longrightarrow> \<beta> \<star> \<gamma> \<longlongrightarrow> \<delta> \<Longrightarrow> \<alpha> \<star> \<gamma> \<longlongrightarrow> \<delta>\<close>
    by (blast intro: aentails_intro asepconj_mono2)}
  val aentails_drule_core0 : thm = @{lemma \<open>\<alpha> \<longlongrightarrow> \<beta> \<Longrightarrow> \<beta> \<longlongrightarrow> \<delta> \<Longrightarrow> \<alpha> \<longlongrightarrow> \<delta>\<close>
    by (blast intro: aentails_intro asepconj_mono2)}
  val aentails_rule_core : thm = @{lemma \<open>\<alpha> \<longlongrightarrow> \<beta> \<Longrightarrow> \<phi> \<longlongrightarrow> \<alpha> \<star> \<gamma> \<Longrightarrow> \<phi> \<longlongrightarrow> \<beta> \<star> \<gamma>\<close>
    by (blast intro: aentails_intro asepconj_mono2)}
  val aentails_rule_core0 : thm = @{lemma \<open>\<alpha> \<longlongrightarrow> \<beta> \<Longrightarrow> \<phi> \<longlongrightarrow> \<alpha> \<Longrightarrow> \<phi> \<longlongrightarrow> \<beta>\<close>
    by (blast intro: aentails_intro asepconj_mono2)}

  val aentails_crule_core : thm = @{thm asepconj_mono4}
  val aentails_crule_coreL : thm = @{thm asepconj_mono6}
  val aentails_crule_coreR : thm = @{thm asepconj_mono7}

  (* Some lemmas *)
  exception SeparationLogic of string

  \<comment> \<open>Some utility functions\<close>

  (* Search for list entry in the domain of the given partial map, and return the pair
     of its index and value under the map on success. Return NONE otherwise. *)
  fun find_idx pmap lst =
     (* Use a tail-recursive helper for this *)
     let fun core [] _ = NONE
           | core (x::xs) base =
               case pmap x of
                  SOME r => SOME (base, r)
                | NONE => core xs (base+1) in
     core lst 0
  end

  fun filter_to_pmap f =
     let fun bool_to_unit_option b = if b then SOME () else NONE
     in bool_to_unit_option o f end

  (* Search for pairs of list entries satisfying a given filter function *)
  fun find_pair pair_filter lst1 lst2 =
      let val opt_proj = Option.map (fn  (x,(y,_)) => (x,y)) in
      find_idx ( fn x =>
        find_idx (
          filter_to_pmap (pair_filter x)
        ) lst2
      ) lst1 |> opt_proj end

  fun bool_list_all (ls : bool list) : bool = fold (fn v => fn w => v andalso w) ls true

  fun zip [] [] = []
     | zip (x :: xs) (y :: ys) = (x,y) :: (zip xs ys)
     | zip _ _ = raise Subscript

  \<comment> \<open>Unification helpers\<close>

  fun is_unifiable_pair ctx t0 t1 =
    let val matches = Unify.unifiers (Context.Proof ctx, Envir.empty 0, [(t0,t1)]) in
      Seq.pull matches |> Option.isSome
    end

  fun find_unifiable_term ctx t =
     let val opt_proj = Option.map (fn (x,_) => x) in
       find_idx ((is_unifiable_pair ctx t) |> filter_to_pmap) #> opt_proj
     end

  fun find_unifiable_term2 ctx = find_pair (is_unifiable_pair ctx)

  \<comment> \<open>Destructing/Constructing separating conjunctions to/from lists of terms\<close>

  fun split_asepconj' ((Const (@{const_name asepconj}, _)) $ l $ r) =
     let val (lhs, _) = split_asepconj' l
         val (rhs, canonical) = split_asepconj' r
         val canonical = (length lhs = 1 andalso canonical)
      in
        (lhs @ rhs, canonical)
      end
    | split_asepconj' t = ([t], true)

  fun split_asepconj t = t |> split_asepconj' |> fst

  fun mk_asepconj []      =
        raise SeparationLogic("cannot make separating conjunction from an empty list of formulae")
    | mk_asepconj [x]     = x
    | mk_asepconj (x::xs) =
        case fastype_of x of
          Type (@{type_name set}, [a]) =>
            \<^Const>\<open>asepconj \<open>a\<close> for \<open>x\<close> \<open>mk_asepconj xs\<close>\<close>
        | _ => raise SeparationLogic("input term is not a set")

  fun set_instantiation _ (Type (@{type_name set}, [x])) = x
    | set_instantiation _ _ = raise SeparationLogic("type is not a set")

  \<comment> \<open>Destructing terms of various shapes\<close>

  fun dest_aentails ((Const (@{const_name aentails}, _)) $ P $ Q) = (P, Q)
    | dest_aentails t =
        raise SeparationLogic((t |> print_term) ^ "is not a separation logic entailment")

  fun dest_wp ((Const (@{const_name Weakest_Precondition.sepalg_class.wp}, _)) $ A0 $ A1 $ A2 $ A3 $ A4 ) = (A0, A1, A2, A3, A4)
    | dest_wp _ = raise SeparationLogic("not a WP' separation logic entailment")

  fun dest_urust_call ((Const (@{const_name Core_Expression.call}, _)) $ body ) = body
    | dest_urust_call _ = raise SeparationLogic("not a uRUst function call expression")

  fun dest_ucincl ((Const (@{const_name ucincl}, _)) $ P) = P
    | dest_ucincl _ = raise SeparationLogic("not ucincl proposition")

  fun dest_points_to_raw ((Const (@{const_name reference_defs.points_to_raw}, _))
                         $ _ $ r $ sh $ g) = (r,sh,g)
     | dest_points_to_raw _ = raise SeparationLogic "dest_points_to_raw"

  fun dest_points_to ((Const (@{const_name reference_defs.points_to}, _))
                         $ _ $ _ $ r $ sh $ g $ v) = (r,sh,g,v)
     | dest_points_to _ = raise SeparationLogic "dest_points_to_raw"

  fun dest_asepconj_multi ((Const (@{const_name "Assertion_Language.asepconj_multi"}, _)) $ t) = t
     | dest_asepconj_multi _ = raise SeparationLogic "dest_asepconj_multi"

  fun dest_asepconj ((Const (@{const_name "Assertion_Language.asepconj"}, _)) $ lhs $ rhs) = (lhs, rhs)
     | dest_asepconj _ = raise SeparationLogic "dest_asepconj"

  fun dest_mapped_multiset ((Const (@{const_name "Multiset.image_mset"}, _)) $ t0 $ t1) = (t0,t1)
     | dest_mapped_multiset _ = raise SeparationLogic "dest_mapped_multiset"

  fun dest_pure ((Const (@{const_name apure}, _)) $ t) = t
    | dest_pure _ = raise SeparationLogic "dest_pure"

  val dest_asepconj_multi_mapped = dest_asepconj_multi #> dest_mapped_multiset

  val unwrap_aentails    = find_metaimp_conclusion #> dest_aentails
  val unwrap_wp_aentails = unwrap_aentails #> snd #> dest_wp
  val unwrap_wp_call     = unwrap_wp_aentails #> #2 #> dest_urust_call
  val unwrap_ucincl      = find_metaimp_conclusion #> dest_ucincl

  fun dest_Const_or_Free (Const x) = x
    | dest_Const_or_Free (Free x) = x
    | dest_Const_or_Free t = raise TERM("dest_Const_or_Free", [t]);

  val find_wp_call_function = try (unwrap_wp_call #>
     Term.strip_comb #> fst #> dest_Const_or_Free #> fst #> Long_Name.base_name)

  \<comment> \<open>Detecting terms of various shapes\<close>

  fun succeeds f t = (let val _ = f t in true end handle SeparationLogic _ => false)

  val is_entailment     = succeeds unwrap_aentails
  val is_wp_entailment  = succeeds unwrap_wp_aentails
  val is_ucincl         = succeeds unwrap_ucincl
  val is_points_to      = succeeds dest_points_to
  val is_points_to_raw  = succeeds dest_points_to_raw
  val is_asepconj       = succeeds dest_asepconj
  val is_asepconj_multi = succeeds dest_asepconj_multi
  val is_pure           = succeeds dest_pure
  val is_wp_call        = succeeds unwrap_wp_call

  fun conjunction_of (filter : term -> bool) : term -> bool = find_conclusions #> List.all filter
  val is_ucincl' = conjunction_of is_ucincl

  fun asepconj_filter_idxs (t: term) (filter: term -> bool): int list =
      let val ts = split_asepconj t
          fun find_idxs acc _ [] = acc
            | find_idxs acc base (t::ts) =
                if filter t then
                   find_idxs (acc @ [base]) (base+1) ts
                else
                   find_idxs acc (base+1) ts
      in
        find_idxs [] 0 ts
      end

  \<comment> \<open>Transformations of separating conjunctions\<close>

   structure Permutation :
     sig
       val rotate    : term -> term
       val pick      : int -> term -> term
       val pickany   : (term -> bool) -> term -> term list
       val partition : (term -> bool) -> term -> term
       val joinfirst : int -> term -> term
     end =
   struct

     fun mk_permutation perm =
        split_asepconj #> perm #> mk_asepconj

     fun joinfirst (n : int) (goal : term) : term =
        let
          val cs = goal |> split_asepconj
          val first_n = List.take (cs,n)
          val remaining = List.drop (cs,n)
        in
          (mk_asepconj first_n) :: remaining |> mk_asepconj
        end

     val rotate =
       let
         fun go []      = []
           | go (x::xs) = xs @ [x]
       in
         go |> mk_permutation
       end

    fun pick index =
      let
        fun drop _ []      = raise SeparationLogic "pick"
          | drop 0 (_::xs) = xs
          | drop m (x::xs) = x::drop (m - 1) xs

        fun to_front idx lst =
          (nth lst idx) :: (drop idx lst)
      in
        to_front index |> mk_permutation
      end

    fun pickany filter t =
      List.map (fn i => pick i t) (asepconj_filter_idxs t filter)

    fun partition part =
      \<comment> \<open>Partitioning should fail if the terms are already partitioned\<close>
      \<comment> \<open>NB: One cannot use CHANGE at the top level of the partitioning tactic
          because some schematic variables may get renamed in which case the goal
          is seen as having 'changed' even if things are 'essentially' unchanged.\<close>
      let
        fun check_changed (new,old) =
          if new = old then raise SeparationLogic "check_changed" else new
      in
        `(List.partition part) #>> op @ #> check_changed |> mk_permutation
      end
   end

  \<comment> \<open>Solve equality goal for permutation of iterated separating conjunction.\<close>

  fun asepconj_solve_eq_tac ctxt i =
    if i = 1 then
      simp_tac ((ctxt |> clear_simpset) addsimps @{thms asepconj_AC}) i
    else
      all_tac


   \<comment> \<open>Automated/assisted discharge of \<^verbatim>\<open>ucincl\<close> conditions.\<close>
   exception LOOKUP of string

   fun lookup_thm_core ctxt thm_name =
     let val thm_opt = Facts.lookup (Context.Proof ctxt)
                                    (Proof_Context.facts_of ctxt)
                                    thm_name in
        case thm_opt of
            SOME thm => thm |> #thms |> List.hd
          | _ => raise LOOKUP thm_name
        end

   fun lookup_thm ctxt thm_name =
    let val thm_name_local = "local." ^ thm_name in
      lookup_thm_core ctxt thm_name_local
    end

   fun get_global_const_name ctxt name =
     name |> Syntax.read_term ctxt |> Term.head_of |> Term.dest_Const |> fst

   fun get_local_const_name _ name = "local." ^ name

   fun lookup_const_def ctxt cname =
     let val thm_name_local = cname |> get_local_const_name ctxt |> Thm.def_name in
       (thm_name_local, lookup_thm_core ctxt thm_name_local)
     end
     handle LOOKUP _ =>
     let val thm_name_global = cname |> get_global_const_name ctxt |> Thm.def_name in
       (thm_name_global, lookup_thm_core ctxt thm_name_global)
     end

  fun dest_spec_fun_full (Const (@{const_name HOL.Trueprop},_) $ (
        (Const (@{const_name "satisfies_function_contract"}, _) $ _ $ f $ g))) = (f,g)
    | dest_spec_fun_full t = raise TERM ("not a function contract goal", [t])

  fun dest_spec_fun t = t |> dest_spec_fun_full |> fst |> Term.head_of

  fun is_schematic_spec t =
   let val tm = t |> Thm.prop_of |> Logic.strip_assums_concl
       val (body, contract) = tm |> dest_spec_fun_full
       val body_schematics = Term.add_var_names body [] |> List.map fst
       val contract_schematics = Term.add_var_names contract [] |> List.map fst
   in
     List.exists (member (op =) body_schematics #> not) contract_schematics
   end

  val dest_spec_fun_str =
       Logic.strip_assums_concl
    #> dest_spec_fun
    #> Term.term_name
    #> Long_Name.base_name

  (* Takes a definitional thm `foo arg0 ... argN == lambda arg(N+1) .. argM. body` and turns it
     into the string `foo arg0 .. argM` *)
  fun get_generic_application_expression thm = let
     val lhs = thm |> Thm.cprop_of |> Thm.dest_equals_lhs |> Thm.term_of
     val rhs = thm |> Thm.cprop_of |> Thm.dest_equals_rhs |> Thm.term_of
     val drop_none = List.filter is_some #> List.map Option.valOf
     fun dest_Var_opt t = SOME (dest_Var t) handle TERM("dest_Var", _) => NONE
     val head = lhs |> Term.strip_comb |> fst |> Term.dest_Const |> fst |> Long_Name.base_name
     val lhs_args = lhs
                    |> Term.strip_comb
                    |> snd
                    |> List.map dest_Var_opt              (* Filter schematic arguments *)
                    |> drop_none
                    |> List.map (fst o fst)               (* Get schematic arguments as strings *)
     val rhs_args = rhs
                    |> Term.strip_abs_vars
                    |> List.map fst
                    |> List.map (fn s => s ^ "_l") (* The reason the arguments are on the RHS as a lambda,
                                                      -- rather than on the LHS as a parameter -- is typically
                                                      that they clash with existing global names.
                                                      Avoid this by adding some suffix. *)
     in
       fold (fn arg => fn str => str ^ " " ^ arg) (lhs_args @ rhs_args) head
     end

  fun ucincl_contract_proof contract_name ctxt = let
    val (contract_def, contract_thm) = contract_name |> lookup_const_def ctxt
    val app_exp = get_generic_application_expression contract_thm
    val prop_str_pre  = "ucincl (function_contract_pre (" ^ app_exp ^ "))"
    val prop_str_post = "ucincl (function_contract_post (" ^ app_exp ^ ") retval)"
    val prop_str_abort = "ucincl (function_contract_abort (" ^ app_exp ^ ") retval)"
    val thm_name = "ucincl_" ^ contract_name
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty,@{attributes [ucincl_intros]}), thms |> flat) |> snd
    val ucincl_pre_prop  = prop_str_pre  |> Syntax.read_prop ctxt
    val ucincl_post_prop = prop_str_post |> Syntax.read_prop ctxt
    val ucincl_abort_prop = prop_str_abort |> Syntax.read_prop ctxt
    val apply_text = (Seq.the_result "initial method") oo
                     ((fn t => (t, Position.no_range)) #> Proof.apply)
    val apply_method = K #> Method.Basic #> apply_text
    fun apply_txt ctxt =
        Input.string #> Method.read_closure_input ctxt #> fst #> apply_text
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name thm_name), []))
                      [[(ucincl_pre_prop, [])], [(ucincl_post_prop, [])], [(ucincl_abort_prop, [])]]
     |> apply_method (SIMPLE_METHOD all_tac)
     |> apply_txt ctxt ("unfold " ^ contract_def)
     |> apply_txt ctxt ("clarsimp?, ucincl_solve?")
     |> apply_method (METHOD (K (TRY (defer_tac 1))))
     |> apply_txt ctxt ("clarsimp?, ucincl_solve?")
     |> apply_txt ctxt ("clarsimp?, ucincl_solve?")
    end

  fun ucincl_assertion_proof assertion_name ctxt = let
    val (assertion_def, assertion_thm) = assertion_name |> lookup_const_def ctxt
    val app_exp = get_generic_application_expression assertion_thm
    val prop_str = "ucincl (" ^ app_exp ^ ")"
    val thm_name = "ucincl_" ^ assertion_name
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty,@{attributes [ucincl_intros]}), thms |> flat) |> snd
    val ucincl_prop  = prop_str  |> Syntax.read_prop ctxt
    val apply_text = (Seq.the_result "initial method") oo
                     ((fn t => (t, Position.no_range)) #> Proof.apply)
    val apply_method = K #> Method.Basic #> apply_text
    fun apply_txt ctxt =
        Input.string #> Method.read_closure_input ctxt #> fst #> apply_text
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name thm_name), []))
                      [[(ucincl_prop, [])]]
     |> apply_method (SIMPLE_METHOD all_tac)
     |> (let val txt = ("(ucincl_solve simp add: " ^ assertion_def ^ ")?")
             val _ = "APPLY: " ^ txt |> tracing
         in apply_txt ctxt txt end)
    end

  val ucincl_contract_auto  = (Proof.global_done_proof oo ucincl_contract_proof)
  val ucincl_assertion_auto = (Proof.global_done_proof oo ucincl_assertion_proof)

  val ucincl_solve_tac : Proof.context -> int -> tactic = fn ctxt =>
     let val ucincl_intro = intro_tac (Named_Theorems.get ctxt @{named_theorems ucincl_intros}) ctxt
         val ucincl_elim  = elim_tac  (Named_Theorems.get ctxt @{named_theorems ucincl_elims}) ctxt
         val ctxt' = ctxt addsimps @{thms Let_def}
         fun NOTE msg =  Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_ucincl) msg
                      #> Crush_Tacticals.LOG' ctxt (Config.get ctxt Crush_Config.log_ucincl) msg
     in Crush_Tacticals.IF' is_ucincl ( NOTE "ucincl_solve" (
       ( REPEAT_ALL_NEW (
                 NOTE "ucincl_solve_intro"      ucincl_intro
         ORELSE' NOTE "ucincl_solve_elim"       ucincl_elim
         ORELSE' NOTE "ucincl_solve_clarify"   (CHANGED_PROP o clarify_tac ctxt)
         ORELSE' NOTE "ucincl_solve_safe_simp" (CHANGED_PROP o safe_full_simp_tac ctxt')
         ORELSE' NOTE "ucincl_solve_safe"      (CHANGED_PROP o safe_steps_tac ctxt)
         ORELSE' ((print_tac ctxt
                  "Warning: ucincl_solve trying full-blown clarsimp -- should not be needed?" |> K)
           THEN' NOTE "ucincl_solve_clarsimp"  (CHANGED_PROP o clarsimp_tac ctxt'))
       ))))
     end

  val ucincl_discharge_tac : Proof.context -> (int -> tactic) -> (int -> tactic) = fn ctxt =>
    fn ct => ct THEN_ALL_NEW (TRY o (ucincl_solve_tac ctxt))

  val ucincl_discharge_tac' : (Proof.context -> int -> tactic) -> (Proof.context -> int -> tactic) =
    fn ct => fn ctxt => ct ctxt THEN_ALL_NEW (TRY o (ucincl_solve_tac ctxt))

  val ucincl_must_discharge_tac : Proof.context -> (int -> tactic) -> (int -> tactic) = fn ctxt =>
    fn ct => ct THEN_ALL_NEW (IF_OK' is_ucincl (SOLVED' (ucincl_solve_tac ctxt)))

  val ucincl_must_discharge_tac' : (Proof.context -> int -> tactic) -> (Proof.context -> int -> tactic) =
    fn ct => fn ctxt => ct ctxt THEN_ALL_NEW (IF_OK' is_ucincl (SOLVED' (ucincl_solve_tac ctxt)))

  val ucincl_discharge_method : Method.method -> Method.method = fn m => fn ts =>
    m ts |> context_tactic_to_context_tactic'
         |> (fn t => SELECT_GOAL o t)
         |> ucincl_discharge_tac'
         |> (fn t => HEADGOAL o t)
         |> context_tactic_to_context_tactic

  exception UCINCL_DISPATCH of string
  fun ucincl_dispatch f_assert f_contract binding ctxt = let
    (* We support two cases:
       - binding is an assertion-valued function
         In this case, we aim to prove that all assertions in its image are upwards closed
       - binding is a function contract valued function
         In this case, we aim to prove that all pre/post conditions are upwards closed *)
    val (_, binding_thm) = binding |> lookup_const_def ctxt
    val binding_lhs = binding_thm |> Thm.cprop_of |> Thm.dest_equals_lhs
    val binding_ty  = binding_lhs |> Thm.typ_of_cterm |> Term.body_type
    (* xxx Surely there's a better way to check the type... *)
    fun type_is_function_contract ty =
       let val tyname = ty |> Term.dest_Type |> fst
           val _ = "TYPE: " ^ tyname |> tracing in
        tyname = "Function_Contract.function_contract"
       end handle TYPE _ => ("Unexpected type" |> tracing;
                             ty |> Syntax.pretty_typ ctxt |> Pretty.writeln;
                             false)
    fun type_is_assertion ty =
       ((ty |> Term.dest_Type |> fst) = "Set.set")
       handle TYPE _ => false
    in
      if type_is_assertion binding_ty then
         ("dispatch to assertion" |> tracing;
         f_assert binding ctxt)
      else if type_is_function_contract binding_ty then
         ("dispatch to contract" |> tracing;
         f_contract binding ctxt)
      else
         raise UCINCL_DISPATCH ""
    end

  val ucincl_auto_single =
    ucincl_dispatch ucincl_assertion_auto ucincl_contract_auto

  val ucincl_proof =
    ucincl_dispatch ucincl_assertion_proof  ucincl_contract_proof

  val ucincl_auto = fold ucincl_auto_single

  val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "ucincl_proof"}
          "open a proof context for upward closure"
             (Parse.embedded >> ucincl_proof)

  val _ = Outer_Syntax.local_theory @{command_keyword "ucincl_auto"}
          "open a proof context for upward closure of a contract's pre/post condition"
             (Scan.repeat1 Parse.embedded >> ucincl_auto)

  \<comment>\<open>Instantiates and applied the theorem \<^term>\<open>thm\<close> with the transformation of \<^term>\<open>t\<close> under\<^term>\<open>pi\<close>.\<close>
  fun transform_and_apply_tac thm s ctxt =
    let
      val ty = fastype_of s
      val ins = set_instantiation ctxt ty
      val m = Thm.instantiate' [SOME (Thm.ctyp_of ctxt ins)] [SOME (Thm.cterm_of ctxt s)] thm
    in
      resolve_tac ctxt [m]
    end handle SeparationLogic _ => K no_tac

   fun aentails_transform_assms_tac pi = Subgoal.FOCUS (fn {context, concl, ...} =>
     let
       val (assms, _) = unwrap_aentails (Thm.term_of concl)
     in
        ((transform_and_apply_tac aentails_prem_cong (pi assms) context)
         THEN_ALL_NEW (asepconj_solve_eq_tac context)) 1
     end handle SeparationLogic _ => no_tac)

   fun aentails_transform_assms_tac' pis = Subgoal.FOCUS (fn {context, concl, ...} =>
     let
       val (assms, _) = unwrap_aentails (Thm.term_of concl)
       val perms = pis assms
       val APPEND_many = List.foldl Tactical.APPEND no_tac
       fun transform_to t = transform_and_apply_tac aentails_prem_cong t context 1
     in
        (APPEND_many (List.map transform_to perms )) THEN (asepconj_solve_eq_tac context 1)
     end handle SeparationLogic _ => no_tac)

   fun aentails_transform_concls_tac pi = Subgoal.FOCUS (fn {context, concl, ...} =>
     let val (_, concl) = unwrap_aentails (Thm.term_of concl) in
        ((transform_and_apply_tac aentails_concl_cong (pi concl) context)
         THEN_ALL_NEW (asepconj_solve_eq_tac context)) 1
     end handle SeparationLogic _ => no_tac)

   fun aentails_transform_concls_tac' pis = Subgoal.FOCUS (fn {context, concl, ...} =>
     let
       val (_, concls) = unwrap_aentails (Thm.term_of concl)
       val perms = pis concls
       val APPEND_many = List.foldl Tactical.APPEND no_tac
       fun transform_to t = transform_and_apply_tac aentails_concl_cong t context 1
     in
        (APPEND_many (List.map transform_to perms )) THEN (asepconj_solve_eq_tac context 1)
     end handle SeparationLogic _ => no_tac)

  \<comment>\<open>Given a separating conjunction, return the generic rotation theorem
     that will apply to it.\<close>
  \<comment>\<open>Helper constants for chunked pick/rotation composition.\<close>
  val asepconj_swap_top_meta = @{thm asepconj_swap_top} RS eq_reflection
  val asepconj_comm_meta = @{thm asepconj_comm} RS eq_reflection
  val asepconj_assoc_meta' = @{thm asepconj_assoc} RS eq_reflection

  \<comment>\<open>Derive the chunk size from the pre-generation limit stored in
     \<^verbatim>\<open>ASepconj_Pick_Cache_Limit\<close>. The cache covers non-last-element picks
     for indices 0..(limit - 2), so the chunk size is limit - 2.\<close>
  fun get_pick_chunk_size ctxt =
    ASepconj_Pick_Cache_Limit.get (Proof_Context.theory_of ctxt) - 2

  \<comment>\<open>Flatten a single left-nested blob at the top: \<^verbatim>\<open>(a \<star> b) \<star> rest \<leadsto> a \<star> b \<star> rest\<close>.\<close>
  fun asepconj_flatten_blob_conv ct =
    Conv.try_conv (Conv.rewr_conv asepconj_assoc_meta'
                   then_conv (Conv.arg_conv asepconj_flatten_blob_conv)) ct

  fun get_rotate_thm (ctxt : Proof.context) (ct : cterm) : thm =
    let val num = ct |> Thm.term_of |> split_asepconj |> length
    in
      get_asepconj_rotate ctxt num
    end

  \<comment>\<open>A conversion for rotating separating conjunctions.
     Uses cached rotation theorem if available, otherwise composes via comm + normalize.\<close>
  fun asepconj_rotate_conv ctxt : conv = fn ct =>
    let val num = ct |> Thm.term_of |> split_asepconj |> length in
      if num <= 1 then Conv.all_conv ct
      else
        (case ASepconj_Rotate_Thms.get (Proof_Context.theory_of ctxt) num of
          SOME thm => Conv.rewr_conv (thm RS eq_reflection) ct
        | NONE =>
            (Conv.rewr_conv asepconj_comm_meta
             then_conv asepconj_flatten_blob_conv) ct)
    end

  \<comment>\<open>Apply separate conversions to the premise and conclusion of a separating entailment\<close>
  fun aentails_conv_core (conv_lhs : conv) (conv_rhs: conv) : conv = (fn t =>
     case (Thm.term_of t) of
        (Const (@{const_name Assertion_Language.aentails}, _)) $ _ $ _ =>
            ((Conv.arg_conv conv_rhs) then_conv (Conv.fun_conv (Conv.arg_conv conv_lhs))) t
      | _ => Conv.no_conv t)

  \<comment>\<open>Apply separate conversions to the premise and conclusion of a separating entailment
     turned into a Pure proposition via \<^term>\<open>Trueprop\<close>\<close>
  fun aentails_conv (conv_lhs : conv) (conv_rhs: conv) : conv =
    aentails_conv_core conv_lhs conv_rhs |> prop_conv

  \<comment>\<open>Apply separate conversions to the premise and conclusion of a separating entailment
     turned into a Pure proposition via \<^term>\<open>Trueprop\<close>. Strip pure universal quantification
     and premises first, if present.\<close>
  fun aentails_conv' (conv_lhs : conv) (conv_rhs: conv) : Proof.context -> conv =
     (Conv.params_conv ~1 (fn _ => (Conv.concl_conv ~1 (aentails_conv (conv_lhs) (conv_rhs)))))

  fun aentails_conv'' (conv_lhs : Proof.context -> conv) (conv_rhs: Proof.context -> conv) : Proof.context -> conv =
     (Conv.params_conv ~1 (fn ctxt => (Conv.concl_conv ~1 (aentails_conv (conv_lhs ctxt) (conv_rhs ctxt)))))

  fun wp_conv (urust_conv : conv) : conv = (fn t =>
    case (Thm.term_of t) of
      (Const (@{const_name Weakest_Precondition.wp}, _)) $ _ $ _ $ _ $ _ $ _ =>
         Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg_conv urust_conv))) t
     | _ => Conv.no_conv t)

  fun aentails_wp_conv' (conv_urust : conv) : Proof.context -> conv =
    aentails_conv' Conv.all_conv (wp_conv conv_urust)

  fun aentails_wp_rewrite_tac (thm_eq : thm) (ctxt : Proof.context) : int -> tactic =
      CONVERSION (aentails_wp_conv' (Conv.rewr_conv (force_meta_eq thm_eq)) ctxt)

  \<comment>\<open>Conversions for rotating premises/conclusions of separating entailments\<close>
  fun aentails_rotate_assms_conv ctxt : conv = aentails_conv' (asepconj_rotate_conv ctxt) Conv.all_conv ctxt
  fun aentails_rotate_concls_conv ctxt : conv = aentails_conv' Conv.all_conv (asepconj_rotate_conv ctxt) ctxt

  (* rotating a separating conjunction *)
  val aentails_rotate_assms_tac  = fn ctxt => (CONVERSION (aentails_rotate_assms_conv  ctxt))
  val aentails_rotate_concls_tac = fn ctxt => (CONVERSION (aentails_rotate_concls_conv ctxt))


  \<comment>\<open>Split a separating conjunctions into its components\<close>
  fun split_asepconj ((Const (@{const_name Assertion_Language.sepalg_class.asepconj}, _)) $ l $ r) =
        split_asepconj l @ split_asepconj r
    | split_asepconj t = [t]

  \<comment>\<open>Given a separating conjunction and a filter function on terms, return the list of
    0-based indices of those components which pass the filter.\<close>
  fun asepconj_filter_idxs (t: term) (filter: term -> bool): int list =
      let val ts = split_asepconj t
          fun find_idxs acc _ [] = acc
            | find_idxs acc base (t::ts) =
                if filter t then
                   find_idxs (acc @ [base]) (base+1) ts
                else
                   find_idxs acc (base+1) ts
      in
        find_idxs [] 0 ts
      end

  \<comment>\<open>A conversion picking the i-th element from a separating conjunction of n elements.
     For i within the cached range, uses cached picker theorems directly.
     For larger i, composes picks in chunks:
       1. Group first chunk_size elements into a blob (1 cached pick + 1 comm)
       2. Recursively pick (i - chunk_size) from the tail
       3. Swap the result past the blob
       4. Re-normalize
     This gives ceil(i / chunk_size) cached pick operations, where chunk_size
     is derived from the pre-generation limit in \<^verbatim>\<open>Assertion_Language.thy\<close>.\<close>
  fun asepconj_pick_conv ctxt n i: conv =
    let val chunk = get_pick_chunk_size ctxt in
    if i <= chunk then
      let val pick_thm = get_asepconj_pick_ith_from_n ctxt n i
      in Conv.rewr_conv (pick_thm RS eq_reflection) end
    else
      let
        \<comment>\<open>Inline joinfirst(chunk): pick the tail-blob to front, then comm.\<close>
        val joinfirst_pick_thm =
          get_asepconj_pick_ith_from_n ctxt (chunk + 1) chunk
        val joinfirst_conv =
          Conv.rewr_conv (joinfirst_pick_thm RS eq_reflection)
          then_conv Conv.rewr_conv asepconj_comm_meta
      in
        joinfirst_conv
        then_conv
        Conv.arg_conv (asepconj_pick_conv ctxt (n - chunk) (i - chunk))
        then_conv
        Conv.rewr_conv asepconj_swap_top_meta
        then_conv
        Conv.arg_conv asepconj_flatten_blob_conv
      end
    end
  \<comment>\<open>Convenience wrapper inferring the number \<^verbatim>\<open>n\<close> of separating components.\<close>
  fun asepconj_pick_conv' ctxt i: conv = (fn ct =>
    let val n = ct |> Thm.term_of |> split_asepconj |> length in
    asepconj_pick_conv ctxt n i ct end)

  \<comment>\<open>Conversions for picking the i-th element from the premises/conclusions of separating entailments.\<close>
  fun aentails_pick_assm_conv ctxt n i: conv = aentails_conv' (asepconj_pick_conv ctxt n i) Conv.all_conv ctxt
  fun aentails_pick_assm_conv' ctxt i: conv = aentails_conv' (asepconj_pick_conv' ctxt i) Conv.all_conv ctxt
  fun aentails_pick_concl_conv ctxt n i : conv = aentails_conv' Conv.all_conv (asepconj_pick_conv ctxt n i) ctxt
  fun aentails_pick_concl_conv' ctxt i : conv = aentails_conv' Conv.all_conv (asepconj_pick_conv' ctxt i) ctxt

  \<comment>\<open>Conversions floating multiple components in a separating conjunction to the left.
     The index list provided here must be ascending and can be constructed via
     \<^verbatim>\<open>asepconj_filter_idxs\<close>, for example.\<close>
  fun asepconj_pick_many_conv ctxt n is: conv =
    let fun pick_conv i = asepconj_pick_conv ctxt n i
        fun inc_ith_by_i_core acc _ [] = acc
          | inc_ith_by_i_core acc base (x :: xs) =
               inc_ith_by_i_core (acc @ [x + base]) (base + 1) xs
    in
      (inc_ith_by_i_core [] 0 (List.rev is)) |> List.map pick_conv |> Conv.every_conv
    end
  \<comment>\<open>Convenience wrapper inferring the number \<^verbatim>\<open>n\<close> of separating components.\<close>
  fun asepconj_pick_many_conv' ctxt is: conv = (fn ct =>
    let val n = ct |> Thm.term_of |> split_asepconj |> length in
    asepconj_pick_many_conv ctxt n is ct end)

  fun aentails_pick_many_assm_conv ctxt n is: conv = aentails_conv' (asepconj_pick_many_conv ctxt n is) Conv.all_conv ctxt
  fun aentails_pick_many_assm_conv' ctxt is: conv = aentails_conv' (asepconj_pick_many_conv' ctxt is) Conv.all_conv ctxt
  fun aentails_pick_many_concl_conv ctxt n is: conv = aentails_conv' Conv.all_conv (asepconj_pick_many_conv ctxt n is) ctxt
  fun aentails_pick_many_concl_conv' ctxt is: conv = aentails_conv' Conv.all_conv (asepconj_pick_many_conv' ctxt is) ctxt

  \<comment>\<open>A conversion for transforming \<^verbatim>\<open>\<xi>\<^sub>1 \<star> \<xi>\<^sub>2 \<star> _ \<star> \<xi>\<^sub>n\<close> into \<^verbatim>\<open>(\<xi>\<^sub>1 \<star> _ \<xi>\<^sub>i) \<star> \<xi>\<^sub>i\<^sub>+\<^sub>1 \<star> _ \<star> \<xi>\<^sub>n\<close>\<close>
  fun asepconj_joinfirst_conv ctxt n i: conv =
    if i = n then Conv.all_conv else
    (asepconj_pick_conv ctxt (i+1) i) then_conv (Conv.rewr_conv (@{thm asepconj_comm} RS eq_reflection))
  \<comment>\<open>Convenience wrapper inferring the number \<^verbatim>\<open>n\<close> of separating components.\<close>
  fun asepconj_joinfirst_conv' ctxt i: conv = fn ct =>
    let val n = ct |> Thm.term_of |> split_asepconj |> length in
    asepconj_joinfirst_conv ctxt n i ct end

  fun aentails_joinfirst_assm_conv ctxt n i: conv = aentails_conv' (asepconj_joinfirst_conv ctxt n i) Conv.all_conv ctxt
  fun aentails_joinfirst_concl_conv ctxt n i : conv = aentails_conv' Conv.all_conv (asepconj_joinfirst_conv ctxt n i) ctxt
  fun aentails_joinfirst_assm_conv' ctxt i: conv = aentails_conv' (asepconj_joinfirst_conv' ctxt i) Conv.all_conv ctxt
  fun aentails_joinfirst_concl_conv' ctxt i : conv = aentails_conv' Conv.all_conv (asepconj_joinfirst_conv' ctxt i) ctxt

  \<comment>\<open>Apply separate conversions to the LHS and RHS of a separating conjunction\<close>
  fun asepconj_conv' (c_left : conv) (c_right : conv) : conv =
     Conv.combination_conv (Conv.arg_conv c_left) c_right
  \<comment>\<open>Apply a conversion to the RHS of a separating conjunction\<close>
  fun asepconj_conv_right (c : conv) : conv = asepconj_conv' Conv.all_conv c
  \<comment>\<open>Apply a conversion to the LHS of a separating conjunction\<close>
  fun asepconj_conv_left (c : conv) : conv = asepconj_conv' c Conv.all_conv

  \<comment>\<open>Apply a conversion to every conclusion in an (n-fold) separating conjunction; if the term is not
     a separating conjunction, just apply the conversion.\<close>
  fun asepconj_conv (c : conv) (t : cterm) : thm =
     case (Thm.term_of t) of
        (Const (@{const_name Assertion_Language.sepalg_class.asepconj}, _)) $ _ $ _ =>
            Conv.binop_conv (Conv.try_conv (asepconj_conv c)) t
      | _ => c t

  (* floating a single formula to the front of a separating conjunction *)

  fun aentails_pick_assms_tac i  = fn ctxt => (CONVERSION (aentails_pick_assm_conv'  ctxt i))
  fun aentails_pick_concls_tac i = fn ctxt => (CONVERSION (aentails_pick_concl_conv' ctxt i))
  fun aentails_pick_assms_tac_ext n i  = fn ctxt => (CONVERSION (aentails_pick_assm_conv  ctxt n i))
  fun aentails_pick_concls_tac_ext n i = fn ctxt => (CONVERSION (aentails_pick_concl_conv ctxt n i))

  fun aentails_joinfirst_assms_tac i  = fn ctxt => (CONVERSION (aentails_joinfirst_assm_conv'  ctxt i))
  fun aentails_joinfirst_concls_tac i = fn ctxt => (CONVERSION (aentails_joinfirst_concl_conv' ctxt i))

  val asepconj_assoc_meta = @{thm asepconj_assoc} RS eq_reflection

  \<comment>\<open>Conversion hoisting \<Squnion> at a given position out of a right-associated separating conjunction.
     For positions within the cached range, uses cached hoist theorems directly.
     For larger positions, uses chunked composition analogous to asepconj_pick_conv:
       1. Group first chunk_size elements into a blob (1 cached hoist at position chunk_size - 1 for the blob tail)
       ... (fallback: compose hoist_at_conv on the fly)

     asepconj_hoist_conv ctxt i:  applies a with-tail hoist at position i.
     asepconj_hoist_tail_conv ctxt i:  applies a tail hoist at position i.
     asepconj_hoist_existential_pregen_conv ctxt: walks the right spine, hoists all \<Squnion>(range ...).\<close>

  local
    fun repeat_arg_conv 0 c = c
      | repeat_arg_conv n c = Conv.arg_conv (repeat_arg_conv (n - 1) c)
  in
    \<comment>\<open>With-tail hoist at position i: hoists \<Squnion> that is not the last element.
       For i within the cache, uses a single rewr_conv.
       For i beyond the cache, uses chunked composition:
         1. Descend chunk levels via repeated arg_conv
         2. Recursively hoist at position (i - chunk)
         3. Apply cached tail hoist at position (chunk - 1) to bubble \<Squnion> past the prefix\<close>
    fun asepconj_hoist_conv ctxt i : conv =
      let val limit = ASepconj_Hoist_Cache_Limit.get (Proof_Context.theory_of ctxt) in
        if i < limit then
          Conv.rewr_conv (get_asepconj_hoist_at ctxt i RS eq_reflection)
        else
          let val chunk = limit in
            repeat_arg_conv chunk (asepconj_hoist_conv ctxt (i - chunk))
            then_conv Conv.rewr_conv (get_asepconj_hoist_tail ctxt (chunk - 1) RS eq_reflection)
          end
      end

    \<comment>\<open>Tail hoist at position i: hoists \<Squnion> that is the last element.
       For i within the cache, uses a single rewr_conv.
       For i beyond the cache, uses chunked composition:
         1. Descend chunk levels via repeated arg_conv
         2. Recursively tail-hoist at position (i - chunk)
         3. Apply cached tail hoist at position (chunk - 1) to bubble \<Squnion> past the prefix\<close>
    fun asepconj_hoist_tail_conv ctxt i : conv =
      let val limit = ASepconj_Hoist_Cache_Limit.get (Proof_Context.theory_of ctxt) in
        if i < limit then
          Conv.rewr_conv (get_asepconj_hoist_tail ctxt i RS eq_reflection)
        else
          let val chunk = limit in
            repeat_arg_conv chunk (asepconj_hoist_tail_conv ctxt (i - chunk))
            then_conv Conv.rewr_conv (get_asepconj_hoist_tail ctxt (chunk - 1) RS eq_reflection)
          end
      end
  end

  local
    (* Descend into the body of \<Squnion>x. ..., i.e., Sup (image (\<lambda>x. body) \<top>) *)
    fun SUP_body_conv (conv : Proof.context -> conv) ctxt : conv =
      Conv.arg_conv (Conv.fun_conv (Conv.arg_conv
        (Conv.abs_conv (fn (_, ctxt') => conv ctxt') ctxt)))
  in
    (*  Hoist all \<Squnion>(range ...) out of a right-associated \<star>-chain.

        Algorithm:
          1. Scan the chain to find positions of all \<Squnion>(range ...) components.
          2. Hoist from rightmost to leftmost:
             - Use asepconj_hoist_tail_conv if it's the last element
             - Use asepconj_hoist_conv otherwise
             Each hoist wraps the result in \<Squnion>x., so subsequent hoists
             descend through accumulated binders first.

        Each hoist uses a single cached theorem (O(1)), and the binder
        descent is O(1) per level. Total: O(N) scan + O(K) hoists. *)
    fun asepconj_hoist_existential_pregen_conv (ctxt: Proof.context) : conv = fn ct =>
      let
        val components = split_asepconj (Thm.term_of ct)
        val n = length components

        (* Count nested \<Squnion>(range ...) layers at a term.
           \<Squnion>(range R)       = Sup(image R \<top>)                         has depth 1.
           \<Squnion>x y. R x y  = Sup(image (\<lambda>x. Sup(image (\<lambda>y. R x y) \<top>)) \<top>)  has depth 2. *)
        fun sup_depth (Const (@{const_name Sup}, _) $
              (Const (@{const_name image}, _) $ f $ Const (@{const_name top}, _))) =
              1 + (case f of Abs (_, _, body) => sup_depth body | _ => 0)
          | sup_depth _ = 0

        (* Build position list with repetitions for nested Sups, reversed so rightmost first *)
        val sup_positions =
          components |> map_index I
          |> map_filter (fn (i, t) =>
               let val d = sup_depth t
               in if d > 0 then SOME (List.tabulate (d, K i)) else NONE end)
          |> List.concat

        (* Apply a single hoist at position i, choosing tail vs with-tail *)
        fun hoist1 ctxt i : conv =
          if i = n - 1 then
            (* Last element: use tail hoist. Position i means i leading elements. *)
            asepconj_hoist_tail_conv ctxt (i - 1)
          else
            asepconj_hoist_conv ctxt i

        (* Hoist all positions, leftmost first. After each hoist,
           descend into the \<Squnion>x. body for the next one. *)
        fun hoist_all [] _ ct = Conv.all_conv ct
          | hoist_all [i] ctxt ct = hoist1 ctxt i ct
          | hoist_all (i :: is) ctxt ct =
              let val thm1 = hoist1 ctxt i ct
              in Thm.transitive thm1
                   (SUP_body_conv (fn ctxt' => hoist_all is ctxt') ctxt (Thm.rhs_of thm1))
              end
      in
        if null sup_positions then raise CTERM ("asepconj_hoist_existential_pregen_conv: no change", [ct])
        else hoist_all sup_positions ctxt ct
      end
  end

  \<comment>\<open>Alternative bulk hoist using a balanced binary tree.

     Rather than hoisting one \<Squnion> at a time past a right-associated prefix
     (which requires chunked composition for positions beyond the cache),
     this re-associates the chain into a balanced binary tree, distributes
     \<Squnion> bottom-up with \<^verbatim>\<open>asepconj_Inf_distrib\<close>/\<^verbatim>\<open>asepconj_Inf_distrib_right\<close>,
     and finally re-flattens. Each internal node performs a constant number of
     rewrites, so the total cost is O(N log N) and is independent of the
     cache limit used for \<^verbatim>\<open>asepconj_hoist_existential_pregen_conv\<close>.

     In practice, the binary tree version is asymptotically better but has
     higher constants; it only starts to win for large N once the
     pre-generated cache is small relative to the chain length.\<close>
  local
    val tree_assoc_meta = @{thm asepconj_assoc} RS eq_reflection
    val tree_assoc_sym_meta = @{thm asepconj_assoc[symmetric]} RS eq_reflection
    val tree_distrib_l_meta = @{thm asepconj_Inf_distrib} RS eq_reflection
    val tree_distrib_r_meta = @{thm asepconj_Inf_distrib_right} RS eq_reflection

    fun tree_count_asepconj (Const (@{const_name asepconj}, _) $ _ $ r) =
          1 + tree_count_asepconj r
      | tree_count_asepconj _ = 1

    (* a \<star> (b \<star> c) -> (a \<star> b) \<star> c *)
    val tree_group_left_once : conv = Conv.rewr_conv tree_assoc_sym_meta

    (* Group the first k+1 elements into a blob:
       a0 \<star> (a1 \<star> (... \<star> (a_k \<star> rest))) -> (a0 \<star> a1 \<star> ... \<star> a_k) \<star> rest.
       The resulting left blob is itself right-associated, so no renormalization
       is needed before recursing. *)
    fun tree_group_left 0 : conv = Conv.all_conv
      | tree_group_left k =
          Conv.arg_conv (tree_group_left (k - 1)) then_conv tree_group_left_once

    (* Recursively balance a right-associated chain of n elements into a
       balanced binary tree of depth O(log N). *)
    fun tree_balance_conv 1 : conv = Conv.all_conv
      | tree_balance_conv 2 = Conv.all_conv
      | tree_balance_conv n =
          let
            val left_size = n div 2
            val right_size = n - left_size
          in
            tree_group_left (left_size - 1)
            then_conv Conv.combination_conv
              (Conv.arg_conv (tree_balance_conv left_size))
              (tree_balance_conv right_size)
          end

    (* Descend into the body of \<Squnion>x. ..., i.e., Sup (image (\<lambda>x. body) \<top>). *)
    fun tree_SUP_body_conv (conv : Proof.context -> conv) ctxt : conv =
      Conv.arg_conv (Conv.fun_conv (Conv.arg_conv
        (Conv.abs_conv (fn (_, ctxt') => conv ctxt') ctxt)))

    (* Merge (\<Squnion>^k A) \<star> (\<Squnion>^l B) into \<Squnion>^(k+l). A \<star> B
       by repeatedly applying distrib at the top and descending into
       the new binder.  O(k+l) rewrites per call. *)
    fun tree_merge_existentials ctxt : conv =
      Conv.try_conv (
        Conv.rewrs_conv [tree_distrib_l_meta, tree_distrib_r_meta]
        then_conv tree_SUP_body_conv tree_merge_existentials ctxt)

    (* Bottom-up hoist on a balanced tree. At each \<star> node:
         1. Recursively hoist in both subtrees.
         2. Merge the resulting existentials at this node. *)
    fun tree_hoist_conv ctxt : conv = fn ct =>
      (case Thm.term_of ct of
        Const (@{const_name asepconj}, _) $ _ $ _ =>
          (Conv.combination_conv
            (Conv.arg_conv (tree_hoist_conv ctxt))
            (tree_hoist_conv ctxt)
          then_conv tree_merge_existentials ctxt) ct
      | _ => Conv.all_conv ct)

    (* Right-normalize a tree-shaped \<star> by repeated assoc at the top,
       then recursing into the right subtree. *)
    fun tree_reflatten_asepconj (ct : cterm) : thm =
      ((Conv.repeat_conv (Conv.rewr_conv tree_assoc_meta)
        then_conv Conv.try_conv (Conv.arg_conv tree_reflatten_asepconj)) ct)

    (* Descend through nested \<Squnion>x. binders, then flatten the \<star>-body. *)
    fun tree_reflatten_conv ctxt : conv = fn ct =>
      (case Thm.term_of ct of
        Const (@{const_name Sup}, _) $ _ =>
          Conv.arg_conv (Conv.fun_conv (Conv.arg_conv
            (Conv.abs_conv (fn (_, ctxt') => tree_reflatten_conv ctxt') ctxt))) ct
      | Const (@{const_name asepconj}, _) $ _ $ _ =>
          tree_reflatten_asepconj ct
      | _ => Conv.all_conv ct)
  in
    fun asepconj_balance_conv n : conv = tree_balance_conv n

    fun asepconj_hoist_existential_tree_conv (ctxt : Proof.context) : conv = fn ct =>
      let val n = tree_count_asepconj (Thm.term_of ct) in
        if n <= 1 then
          raise CTERM ("asepconj_hoist_existential_tree_conv: nothing to hoist", [ct])
        else
          (tree_balance_conv n
           then_conv tree_hoist_conv ctxt
           then_conv tree_reflatten_conv ctxt) ct
      end
  end

  \<comment>\<open>4-ary tree variant of the existential hoist.  Same algorithm as the
     binary tree version, but each internal node has up to 4 children.
     This reduces the tree depth from O(log_2 N) to O(log_4 N), halving
     the number of \<^verbatim>\<open>abs_conv\<close> binder-descent levels at the cost of up
     to 3 distrib rewrites per merge (instead of 1).\<close>
  local
    val t4_assoc_meta = @{thm asepconj_assoc} RS eq_reflection
    val t4_assoc_sym_meta = @{thm asepconj_assoc[symmetric]} RS eq_reflection

    val t4_distrib_1 = @{thm asepconj_Inf_distrib4_1} RS eq_reflection
    val t4_distrib_2 = @{thm asepconj_Inf_distrib4_2} RS eq_reflection
    val t4_distrib_3 = @{thm asepconj_Inf_distrib4_3} RS eq_reflection
    val t4_distrib_4 = @{thm asepconj_Inf_distrib4_4} RS eq_reflection

    val t3_distrib_1 = @{thm asepconj_Inf_distrib3_1} RS eq_reflection
    val t3_distrib_2 = @{thm asepconj_Inf_distrib3_2} RS eq_reflection
    val t3_distrib_3 = @{thm asepconj_Inf_distrib3_3} RS eq_reflection

    val t2_distrib_1 = @{thm asepconj_Inf_distrib} RS eq_reflection
    val t2_distrib_2 = @{thm asepconj_Inf_distrib_right} RS eq_reflection

    fun t4_count (Const (@{const_name asepconj}, _) $ _ $ r) = 1 + t4_count r
      | t4_count _ = 1

    val t4_group_once : conv = Conv.rewr_conv t4_assoc_sym_meta
    fun t4_group 0 : conv = Conv.all_conv
      | t4_group k = Conv.arg_conv (t4_group (k - 1)) then_conv t4_group_once

    (* Right-normalize a left-associated blob. *)
    fun t4_renorm (ct : cterm) : thm =
      ((Conv.repeat_conv (Conv.rewr_conv t4_assoc_meta)
        then_conv Conv.try_conv (Conv.arg_conv t4_renorm)) ct)

    (* Balance into a 4-ary tree.  For n <= 4 elements, leave as-is
       (right-associated chain is already a single node).  Otherwise,
       split into 4 roughly equal parts and recurse. *)
    fun t4_balance 1 : conv = Conv.all_conv
      | t4_balance n =
          if n <= 4 then Conv.all_conv
          else
            let
              val q = n div 4
              val r = n mod 4
              (* Sizes: first r parts get q+1, remaining get q *)
              val s0 = q + (if r > 0 then 1 else 0)
              val s1 = q + (if r > 1 then 1 else 0)
              val s2 = q + (if r > 2 then 1 else 0)
              val s3 = n - s0 - s1 - s2
            in
              (* Split at s0: (part0) ⋆ rest *)
              t4_group (s0 - 1)
              then_conv Conv.combination_conv
                (Conv.arg_conv (t4_renorm then_conv t4_balance s0))
                (* Split rest at s1: (part1) ⋆ rest' *)
                (t4_group (s1 - 1)
                 then_conv Conv.combination_conv
                   (Conv.arg_conv (t4_renorm then_conv t4_balance s1))
                   (* Split rest' at s2: (part2) ⋆ part3 *)
                   (t4_group (s2 - 1)
                    then_conv Conv.combination_conv
                      (Conv.arg_conv (t4_renorm then_conv t4_balance s2))
                      (t4_balance s3)))
            end

    fun t4_SUP_body (cv : Proof.context -> conv) ctxt : conv =
      Conv.arg_conv (Conv.fun_conv (Conv.arg_conv
        (Conv.abs_conv (fn (_, ctxt') => cv ctxt') ctxt)))

    fun t4_merge ctxt : conv =
      Conv.try_conv (
        (Conv.rewrs_conv [t4_distrib_1, t4_distrib_2, t4_distrib_3, t4_distrib_4]
         else_conv Conv.rewrs_conv [t3_distrib_1, t3_distrib_2, t3_distrib_3]
         else_conv Conv.rewrs_conv [t2_distrib_1, t2_distrib_2])
        then_conv t4_SUP_body t4_merge ctxt)

     \<comment>\<open>Apply a conversion to every conclusion in a right-associated separating conjunction.
        If the term is not a separating conjunction, do nothing. Does not recurse. \<close>
     fun asepconj_conv0 (max : int) (c : conv) (t : cterm) : thm =
        (case (Thm.term_of t) of
            (Const (@{const_name Assertion_Language.sepalg_class.asepconj}, _)) $ _ $ _ =>
               if max > 1 then
                 (Conv.combination_conv (Conv.arg_conv c) (asepconj_conv0 (max - 1) c)) t
               else
                 c t
         | _ => Conv.all_conv t)

    fun t4_hoist ctxt = fn ct => (asepconj_conv0 4 (t4_hoist ctxt) then_conv (t4_merge ctxt)) ct

    fun t4_reflatten_asepconj (ct : cterm) : thm =
      ((Conv.repeat_conv (Conv.rewr_conv t4_assoc_meta)
        then_conv Conv.try_conv (Conv.arg_conv t4_reflatten_asepconj)) ct)

    fun t4_reflatten ctxt : conv = fn ct =>
      (case Thm.term_of ct of
        Const (@{const_name Sup}, _) $ _ =>
          Conv.arg_conv (Conv.fun_conv (Conv.arg_conv
            (Conv.abs_conv (fn (_, ctxt') => t4_reflatten ctxt') ctxt))) ct
      | Const (@{const_name asepconj}, _) $ _ $ _ =>
          t4_reflatten_asepconj ct
      | _ => Conv.all_conv ct)
  in
    fun asepconj_hoist_existential_tree4_conv (ctxt : Proof.context) : conv = fn ct =>
      let val n = t4_count (Thm.term_of ct) in
        if n <= 1 then
          raise CTERM ("asepconj_hoist_existential_tree4_conv: nothing to hoist", [ct])
        else
          (t4_balance n
           then_conv t4_hoist ctxt
           then_conv t4_reflatten ctxt) ct
      end
  end

  fun asepconj_hoist_existential_conv (ctxt : Proof.context) : conv = fn ct =>
    let
      val n = ct |> Thm.term_of |> split_asepconj |> length
      val threshold = Config.get ctxt Crush_Config.hoist_existential_tree_threshold
    in
      if n <= threshold
      then asepconj_hoist_existential_pregen_conv ctxt ct
      else asepconj_hoist_existential_tree4_conv ctxt ct
    end

  \<comment>\<open>Conversion normalizing the bracketing of a separating conjunction to the right.\<close>
  fun asepconj_assoc_normalize_conv (ct : cterm) =
    let val (_, canonical) = ct |> Thm.term_of |> split_asepconj' in
      if canonical then Conv.all_conv ct else
                  ((Conv.repeat_conv (Conv.rewr_conv asepconj_assoc_meta))
        then_conv (Conv.try_conv (asepconj_conv_right asepconj_assoc_normalize_conv)))
    ct
    end

  \<comment>\<open>Conversions normalizing the bracketing of premises/conclusions in a separating  entailment.\<close>
  fun aentails_assoc_normalize_assms_conv ctxt : conv =
     aentails_conv' asepconj_assoc_normalize_conv Conv.all_conv ctxt
  fun aentails_assoc_normalize_concls_conv ctxt : conv =
     aentails_conv' Conv.all_conv asepconj_assoc_normalize_conv ctxt
  fun aentails_assoc_normalize_conv ctxt : conv =
     aentails_conv' asepconj_assoc_normalize_conv asepconj_assoc_normalize_conv ctxt

  val aentails_normalize_assoc_assms_tac = fn ctxt => (CONVERSION (aentails_assoc_normalize_assms_conv ctxt))
  val aentails_normalize_assoc_concls_tac = fn ctxt => (CONVERSION (aentails_assoc_normalize_concls_conv ctxt))
  val aentails_normalize_assoc_tac = fn ctxt => (CONVERSION (aentails_assoc_normalize_conv ctxt))

  fun aentails_pick_many_assms_tac is  = fn ctxt => (CONVERSION (aentails_pick_many_assm_conv'  ctxt is))
  fun aentails_pick_many_concls_tac is = fn ctxt => (CONVERSION (aentails_pick_many_concl_conv' ctxt is))

  val APPEND_many = List.foldl Tactical.APPEND no_tac

  fun filter_idxs filter lst = let
    fun filter_idxs_core acc _ [] = acc
      | filter_idxs_core acc base (t::ts) =
                if filter t then
                   filter_idxs_core (acc @ [base]) (base+1) ts
                else
                   filter_idxs_core acc (base+1) ts
    in
      filter_idxs_core [] 0 lst
    end

  fun is_initial_range _ [] = true
    | is_initial_range base (x :: xs) = if base = x then is_initial_range (base+1) xs else false

  fun aentails_pick_concls_tac' filter (ctxt: Proof.context) (i: int) (st: thm) =
    let val (_, concls) = unwrap_aentails (Thm.cprem_of st i |> Thm.term_of)
        val (comps, canonical) = split_asepconj' concls
        val idxs = comps |> filter_idxs filter
        val core = List.map (fn idx => aentails_pick_concls_tac idx ctxt i) idxs |> APPEND_many
    in
      (if canonical then
        core
       else
        aentails_normalize_assoc_concls_tac ctxt i THEN core
      ) st
    end
    handle THM _ => Seq.empty | SeparationLogic _ => Seq.empty

  fun aentails_pick_concls_tac'' filter (ctxt: Proof.context) (i: int) (st: thm) =
    let val (_, concls) = unwrap_aentails (Thm.cprem_of st i |> Thm.term_of)
        val (comps, canonical) = split_asepconj' concls
        val idxs = comps |> filter_idxs filter
    in
      (if is_initial_range 0 idxs then K no_tac else
         if not canonical then
            (aentails_normalize_assoc_concls_tac ctxt
             THEN' aentails_pick_many_concls_tac idxs ctxt)
         else
             aentails_pick_many_concls_tac idxs ctxt)
      i st
    end
    handle THM _ => Seq.empty | SeparationLogic _ => Seq.empty

  fun aentails_pick_assms_tac' filter (ctxt: Proof.context) (i: int) (st: thm) =
    let val (assms, _) = unwrap_aentails (Thm.cprem_of st i |> Thm.term_of)
        val (comps, canonical) = split_asepconj' assms
        val idxs = comps |> filter_idxs filter
        val core = List.map (fn idx => aentails_pick_assms_tac idx ctxt i) idxs |> APPEND_many
    in
      (if canonical then
        core
       else
        aentails_normalize_assoc_assms_tac ctxt i THEN core
      ) st
    end
    handle THM _ => Seq.empty | SeparationLogic _ => Seq.empty

  fun aentails_pick_assms_tac'' filter (ctxt: Proof.context) (i: int) (st: thm) =
    let val (assms, _) = unwrap_aentails (Thm.cprem_of st i |> Thm.term_of)
        val (comps, canonical) = split_asepconj' assms
        val idxs = comps |> filter_idxs filter
    in
      (if is_initial_range 0 idxs then K no_tac else
         if not canonical then
            (aentails_normalize_assoc_assms_tac ctxt
             THEN' aentails_pick_many_assms_tac idxs ctxt)
         else
             aentails_pick_many_assms_tac idxs ctxt)
      i st
    end
    handle THM _ => Seq.empty | SeparationLogic _ => Seq.empty

  (* floating pure assumptions to the front of a separating conjunction *)
  val aentails_float_pure_assms_tac  = aentails_pick_assms_tac''  is_pure
  val aentails_float_pure_concls_tac = aentails_pick_concls_tac'' is_pure
  val aentails_float_pure_assms_tac'  = aentails_pick_assms_tac'  is_pure
  val aentails_float_pure_concls_tac' = aentails_pick_concls_tac' is_pure

  (* floating typed points_to relations to the front of a separating conjunction *)

  val aentails_float_points_to_assms_tac      = aentails_pick_assms_tac''  is_points_to
  val aentails_float_points_to_raw_assms_tac  = aentails_pick_assms_tac''  is_points_to_raw
  val aentails_float_points_to_assms_tac'      = aentails_pick_assms_tac'  is_points_to
  val aentails_float_points_to_raw_assms_tac'  = aentails_pick_assms_tac'  is_points_to_raw
  val aentails_float_points_to_concls_tac     = aentails_pick_concls_tac'' is_points_to
  val aentails_float_points_to_raw_concls_tac = aentails_pick_concls_tac'' is_points_to_raw
  val aentails_float_points_to_concls_tac'     = aentails_pick_concls_tac' is_points_to
  val aentails_float_points_to_raw_concls_tac' = aentails_pick_concls_tac' is_points_to_raw

  val aentails_float_multi_assms_tac  = aentails_pick_assms_tac''  is_asepconj_multi
  val aentails_float_multi_concls_tac = aentails_pick_concls_tac'' is_asepconj_multi

  val aentails_float_multi_assms_tac'  = aentails_pick_assms_tac'  is_asepconj_multi
  val aentails_float_multi_concls_tac' = aentails_pick_concls_tac' is_asepconj_multi

  (* Given a separating entailment theorem, try to find its spatial assumptions within the current
     subgoal's spatial premises, and float them to the left.

     This tactic does only unify assumptions one by one -- there's no guarantee that the resulting
     combination will actually match the given theorem, but there's some change at least.
     Backtracking will then go through the different options. *)
  fun extract_spatial_assms (thm : thm) : term list =
       thm |> Thm.prop_of |> find_metaimp_conclusion |> dest_aentails |> fst |> split_asepconj

  fun aentails_float_assms_tac (sp_assms: term list) (ctxt : Proof.context) (i : int) =
     let
       val num_assms = List.length sp_assms
       fun filter arg t = is_unifiable_pair ctxt arg t
       fun float_matching_assms (arg : term) : tactic =
          aentails_pick_assms_tac' (filter arg) ctxt i
     in
       (List.foldl Tactical.THEN all_tac (List.map float_matching_assms sp_assms))
       THEN (aentails_joinfirst_assms_tac num_assms ctxt i)
     end
     handle SeparationLogic _ => no_tac

  val aentails_float_drule_assms_tac = extract_spatial_assms #> aentails_float_assms_tac

  fun extract_spatial_concls (thm : thm) : term list =
       thm |> Thm.prop_of |> find_metaimp_conclusion |> dest_aentails |> snd |> split_asepconj

  fun aentails_float_concls_tac (sp_concls: term list) (ctxt : Proof.context) (i : int) =
     let
       val num_concls = List.length sp_concls
       fun float_matching_concls (arg : term) : tactic =
          aentails_pick_concls_tac' (is_unifiable_pair ctxt arg) ctxt i
     in
       (List.foldl Tactical.THEN all_tac (List.map float_matching_concls sp_concls))
       THEN (aentails_joinfirst_concls_tac num_concls ctxt i)
     end
     handle SeparationLogic _ => no_tac

  val aentails_float_rule_concls_tac = extract_spatial_concls #> aentails_float_concls_tac

  fun aentails_float_assms_concls_tac (sp_assms : term list) (sp_concls: term list) (ctxt : Proof.context) =
           aentails_float_concls_tac sp_concls ctxt
     THEN' aentails_float_assms_tac sp_assms ctxt

  fun dest_aentails_cond_rule ((Const (@{const_name aentails_conditional_rule}, _)) $ P $ C $ Q) = (P, Q, C)
    | dest_aentails_cond_rule t = raise SeparationLogic((t |> print_term) ^ "is not a conditional entailment rule")

  fun dest_aentails_cond_drule ((Const (@{const_name aentails_conditional_drule}, _)) $ P $ C $ Q) = (P, Q, C)
    | dest_aentails_cond_drule t = raise SeparationLogic((t |> print_term) ^ "is not a conditional entailment drule")

  fun dest_aentails_cond_crule ((Const (@{const_name aentails_conditional_crule}, _)) $ P $ C0 $ C1 $ Q) = (P, Q, C0, C1)
    | dest_aentails_cond_crule t = raise SeparationLogic((t |> print_term) ^ "is not a conditional entailment crule")

  fun dest_aentails_cond_crule_strong ((Const (@{const_name aentails_conditional_crule_strong}, _)) $ P $ C0 $ C1 $ Q) = (P, Q, C0, C1)
    | dest_aentails_cond_crule_strong t = raise SeparationLogic((t |> print_term) ^ "is not a conditional entailment strong crule")

  fun extract_spatial_assms_concls_from_cond_rule (thm : thm) =
    let
      val (_, b, C) = thm |> Thm.prop_of |> find_metaimp_conclusion |> dest_aentails_cond_rule
    in
      (C |> split_asepconj, b |> split_asepconj)
    end

  fun extract_spatial_assms_concls_from_cond_drule (thm : thm) =
    let
      val (a, _, C) = thm |> Thm.prop_of |> find_metaimp_conclusion |> dest_aentails_cond_drule
    in
      (a |> split_asepconj, C |> split_asepconj)
    end

  fun extract_spatial_assms_concls_from_cond_crule (thm : thm) =
    let
      val t = thm |> Thm.prop_of |> find_metaimp_conclusion
      val (a, b, _, _) = t |> dest_aentails_cond_crule handle SeparationLogic _ =>
                         t |> dest_aentails_cond_crule_strong
    in
      (a |> split_asepconj, b |> split_asepconj)
    end

  fun aentails_float_cond_rule_tac (thm : thm) =
    let
      val (sp_assms, sp_concls) = extract_spatial_assms_concls_from_cond_rule thm
    in
      aentails_float_assms_concls_tac sp_assms sp_concls
    end

  fun aentails_float_cond_drule_tac (thm : thm) =
    let
      val (sp_assms, sp_concls) = extract_spatial_assms_concls_from_cond_drule thm
    in
      aentails_float_assms_concls_tac sp_assms sp_concls
    end

  fun aentails_float_cond_crule_tac (thm : thm) =
    let
      val (sp_assms, sp_concls) = extract_spatial_assms_concls_from_cond_crule thm
    in
      aentails_float_assms_concls_tac sp_assms sp_concls
    end

  infix 1 THEN_LAST
  fun (tac1 THEN_LAST tac2) i st =
    st |> (tac1 i THEN (fn st' =>
      st' |> tac2 (i + Thm.nprems_of st' - Thm.nprems_of st)));

  fun aentails_drule_tac_single (thm : thm) (ctxt : Proof.context) =
     ((aentails_float_drule_assms_tac thm ctxt)
     THEN' (
         resolve_tac ctxt [aentails_drule_core OF [thm],
                             aentails_drule_core0 OF [thm]] handle THM _ => K no_tac
     ))
     THEN_LAST (TRY o (aentails_normalize_assoc_assms_tac ctxt))

  fun make_rules_from_thm (thm : thm) =
     (List.mapPartial (fn t => SOME (t OF [thm]) handle THM _ => NONE)
        @{thms aentails_conditional_rules
               aentails_conditional_drules
               aentails_conditional_crules
               aentails_conditional_crules_strong})

  fun aentails_rule_single float_tac (thm : thm) (ctxt : Proof.context) =
    float_tac thm ctxt THEN' (resolve_tac ctxt (make_rules_from_thm thm))
    THEN_LAST (TRY o (aentails_normalize_assoc_concls_tac ctxt))

  val aentails_cond_drule_tac_single =
    aentails_rule_single aentails_float_cond_drule_tac

  val aentails_cond_crule_tac_single =
    aentails_rule_single aentails_float_cond_crule_tac

  fun aentails_rule_tac_single (thm : thm) (ctxt : Proof.context) =
    ((aentails_float_rule_concls_tac thm ctxt)
     THEN' (
         resolve_tac ctxt [aentails_rule_core OF [thm],
                            aentails_rule_core0 OF [thm]] handle THM _ => K no_tac
     ))
     THEN_LAST (TRY o (aentails_normalize_assoc_concls_tac ctxt))

  val aentails_cond_rule_tac_single =
    aentails_rule_single aentails_float_cond_rule_tac

  fun aentails_float_crule_tac (thm : thm) (ctxt : Proof.context) =
           aentails_float_rule_concls_tac thm ctxt
     THEN' aentails_float_drule_assms_tac thm ctxt

  fun aentails_crule_tac_single (thm : thm) (ctxt : Proof.context) =
    (aentails_float_crule_tac thm ctxt
     THEN' (
         resolve_tac ctxt [aentails_crule_core OF [thm],
                           aentails_crule_coreL OF [thm],
                           aentails_crule_coreR OF [thm], thm]
            handle THM _ => K no_tac
     ))
     THEN_LAST (TRY o (aentails_normalize_assoc_concls_tac ctxt))

  fun aentails_drule_tac (thms : thm list) (ctxt : Proof.context) =
    thms |> List.map (fn t => aentails_drule_tac_single t ctxt) |> FIRST'

  fun aentails_crule_tac (thms : thm list) (ctxt : Proof.context) =
    thms |> List.map (fn t => aentails_crule_tac_single t ctxt) |> FIRST'

  fun aentails_rule_tac (thms : thm list) (ctxt : Proof.context) =
    thms |> List.map (fn t => aentails_rule_tac_single t ctxt) |> FIRST'

  fun aentails_cond_drule_tac (thms : thm list) (ctxt : Proof.context) =
    thms |> List.map (fn t => aentails_cond_drule_tac_single t ctxt) |> FIRST'

  fun aentails_cond_rule_tac (thms : thm list) (ctxt : Proof.context) =
    thms |> List.map (fn t => aentails_cond_rule_tac_single t ctxt) |> FIRST'

  fun aentails_cond_crule_tac (thms : thm list) (ctxt : Proof.context) =
    thms |> List.map (fn t => aentails_cond_crule_tac_single t ctxt) |> FIRST'

  \<comment>\<open>Identity & Float separating assumptions and conclusions which 'match' with
    respect to a generic filter function.\<close>

  fun find_match goal filter =
    let
      val (P,Q) = unwrap_aentails goal
      val Ps = split_asepconj P
      val Qs = split_asepconj Q
    in
      find_pair filter Ps Qs
    end handle SeparationLogic _ => NONE

   \<comment> \<open>NB: We don't use \<^verbatim>\<open>Subgoal.FOCUS\<close> here because it seems to freeze schematic variables by
       converting them into Skolem variables, making unification fail in cases where it requires
       instantiation of schematics.  The downside is that we have to 'unwrap' the goal ourselves,
       while \<^verbatim>\<open>Subgoal.FOCUS\<close> provides direct access to the conclusion.\<close>
   fun aentails_float_match ctxt filter =
      SUBGOAL (fn (goal, i) =>
                 case find_match goal filter of
                    NONE => no_tac
                  | SOME (k,j) =>
                          (aentails_pick_assms_tac  k ctxt i)
                     THEN (aentails_pick_concls_tac j ctxt i))

   \<comment> \<open>The general cancellation tactic for components of separating conjunctions does only cancel
      pairs which are unifiable. Sometimes, however, a more aggressive cancellation is necessary:
      For example, if a separating entailment contains a pair of points-to assertions on either side
      of the entailment, where moreover the address terms are unifiable, then the entailment can
      only hold if the pointed-to values are equal. Thus, the matching assertions should be
      cancelled and an  equality goal should be generated.\<close>
  fun dest_assertion match_head arglist term =
      let val (head,args) = Term.strip_comb term in
      if match_head head then
         SOME (List.map (curry List.nth args) arglist)
      else
         NONE
      end
      handle Subscript => ("FAIL Subscript!" |> tracing; NONE)
      handle TERM _ => ("FAIL TERM!" |> tracing; NONE)

  fun matching_injective_assertion ctxt const_name arglist t1 t2 =
     let val u = is_unifiable_pair in
     case (dest_assertion const_name arglist t1, dest_assertion const_name arglist t2) of
       (SOME t1_args, SOME t2_args) =>
              zip t1_args t2_args
           |> List.map (u ctxt |> uncurry)
           |> bool_list_all
      | _ => false end
     handle Subscript => ("FAIL Subscript!" |> tracing; false)

  fun matching_iterated_asepconjs ctxt t1 t2 =
     let val (t1,_) = dest_asepconj_multi_mapped t1
         val (t2,_) = dest_asepconj_multi_mapped t2 in
       is_unifiable_pair ctxt t1 t2
     end
     handle SeparationLogic _ => false

   fun aentails_float_matching_iterated_asepconj ctxt i =
     aentails_float_match ctxt (matching_iterated_asepconjs ctxt) i

   fun aentails_cancel_asepconj_multi ctxt i =
     aentails_float_matching_iterated_asepconj ctxt i
     THEN ((resolve_tac ctxt [@{thm aentails_cancel_multi}] i)
           ORELSE (resolve_tac ctxt [@{thm aentails_cancel_multi_0L}] i)
           ORELSE (resolve_tac ctxt [@{thm aentails_cancel_multi_0R}] i)
           ORELSE all_tac)

   fun aentails_cancel_injective match_head arglist ctxt i =
     aentails_float_match ctxt (matching_injective_assertion ctxt match_head arglist) i
     THEN ((resolve_tac ctxt [@{thm asepconj_mono4}] i)
           ORELSE (resolve_tac ctxt [@{thm asepconj_mono6}] i)
           ORELSE (resolve_tac ctxt [@{thm asepconj_mono7}] i)
           ORELSE all_tac)

  val solves_reference_axioms : Proof.context -> int -> tactic =
    fn ctxt => resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems reference_axioms})

  val aentails_split_top_points_to_assm_tac : Proof.context -> int -> tactic = fn ctxt =>
           (intro_tac @{thms reference.aentails_split_single_points_to_assm} ctxt
           THEN_ALL_NEW (TRY o SOLVED' (solves_reference_axioms ctxt)))
    ORELSE' (intro_tac @{thms reference.aentails_split_top_points_to_assm} ctxt
             THEN_ALL_NEW ((solves_reference_axioms ctxt |> SOLVED')
                           ORELSE' (aentails_rotate_assms_tac ctxt)))

  val aentails_split_points_to_assms_tac : Proof.context -> int -> tactic = fn ctxt => fn i =>
     REPEAT_DETERM1 ((aentails_float_points_to_assms_tac' ctxt i)
                     THEN (aentails_split_top_points_to_assm_tac ctxt i))

  val asepconj_match_float_points_to_raw_tac : Proof.context -> int -> tactic =
   let fun is_points_to_raw (Const (@{const_name reference_defs.points_to_raw}, _)) = true
         | is_points_to_raw _ = false in
        aentails_cancel_injective is_points_to_raw [1, 2]
     end

  val aentails_cancel_points_to_raw_tac : Proof.context -> int -> tactic = fn ctxt =>
          asepconj_match_float_points_to_raw_tac ctxt
    THEN' (intro_tac @{thms reference.points_to_raw_aentails} ctxt
           THEN_ALL_NEW
           (TRY o (solves_reference_axioms ctxt |> SOLVED')))

  val asepconj_match_float_points_to_tac : Proof.context -> int -> tactic =
     let fun is_points_to (Const (@{const_name reference_defs.points_to}, _)) = true
        | is_points_to _ = false in
        aentails_cancel_injective is_points_to [1, 2]
     end

  val aentails_cancel_points_to_tac : Proof.context -> int -> tactic = fn ctxt =>
          asepconj_match_float_points_to_tac ctxt
    THEN' (intro_tac @{thms reference.points_to_aentails}  ctxt
           THEN_ALL_NEW
           (TRY o (solves_reference_axioms ctxt |> SOLVED')))

  val aentails_cancel_points_to_raw_with_typed_tac : Proof.context -> int -> tactic = fn ctxt => let
    fun NOTE msg =  Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_aentails_cancel) msg
                  #> Crush_Tacticals.LOG' ctxt (Config.get ctxt Crush_Config.log_aentails_cancel) msg in
          NOTE "aentails_cancel_raw_with_typed_float_concls" (aentails_float_points_to_concls_tac' ctxt)
    THEN' NOTE "aentails_cancel_raw_with_typed_float_assms" (aentails_float_points_to_raw_assms_tac' ctxt)
    THEN' (resolve_tac ctxt @{thms reference.aentails_cancel_points_to_raw_with_typed
                                   reference.aentails_cancel_points_to_raw_with_typed_0LR
                                   reference.aentails_cancel_points_to_raw_with_typed_0L
                                   reference.aentails_cancel_points_to_raw_with_typed_0R})
    THEN' (TRY o (solves_reference_axioms ctxt |> SOLVED'))
    THEN' (SOLVED' (resolve_tac ctxt @{thms refl} ORELSE'
             NOTE "aentails_cancel_raw_with_typed_simpA" (CHANGED o asm_simp_tac ctxt)))
    THEN' (TRY o (resolve_tac ctxt @{thms refl} ORELSE'
             NOTE "aentails_cancel_raw_with_typed_simpB" (CHANGED o asm_simp_tac ctxt)))
    end

  val aentails_float_pure_tac : Proof.context -> int -> tactic = fn ctxt =>
     let val float_concls = aentails_float_pure_concls_tac ctxt
         val float_assms  = aentails_float_pure_assms_tac ctxt
     in
       fn i => [float_concls i, float_assms i] |> map TRY |> EVERY |> CHANGED
     end

  val aentails_simp_core_intro_others_tac : Proof.context -> int -> tactic = fn ctxt =>
    intro_tac @{thms aforall_entailsL aforall_entailsR aexists_entailsL
      aentails_refl all_aentails_true aentails_top_R aentails_top_R'
      bot_aentails_all awand_adjointI aentails_intI aentails_true} ctxt

  val aentails_simp_core_cancel_univ_prems : Proof.context -> int -> tactic = fn ctxt =>
    ucincl_must_discharge_tac ctxt (intro_tac @{thms aentails_top_L aentails_top_L'} ctxt)

  val aentails_simp_core_simps_tac : Proof.context -> int -> tactic = fn ctxt =>
     let val asepconj_simps = Named_Theorems.get ctxt @{named_theorems crush_asepconj_simp} in
       safe_simp_no_asm_simp_only_tac ctxt asepconj_simps
     end

  val aentails_simp_core_split_tac : Proof.context -> int -> tactic = fn ctxt =>
     if Config.get ctxt Crush_Config.enable_branch_split then
       intro_tac @{thms aentails_disj_L0} ctxt
     else
       K no_tac

  val aentails_hoist_pure_assms_tac : Proof.context -> int -> tactic = fn ctxt =>
            (* float all pure assumptions *)
            TRY o aentails_float_pure_assms_tac ctxt
            (* consolidate them into one pure assumption *)
      THEN' TRY o (intro_tac @{thms aentails_asepconjL_pureI aentails_asepconjL_pure2I} ctxt)
            (* hoist it out, generating single ucincl condition *)
      THEN' (intro_tac @{thms apure_entailsL0} ctxt
              ORELSE' (ucincl_must_discharge_tac ctxt (intro_tac @{thms apure_entailsL} ctxt))
              ORELSE' (intro_tac @{thms apure_entailsL'} ctxt))
            (* split the newly introduced pure premise *)
      THEN' TRY o (elim_tac @{thms HOL.conjE} ctxt)

  val aentails_hoist_pure_concls_tac : Proof.context -> int -> tactic = fn ctxt =>
    ucincl_discharge_tac ctxt (
            (* float all pure conclusion *)
            TRY o aentails_float_pure_concls_tac ctxt
            (* hoist them out *)
      THEN' intro_tac @{thms apure_entailsR} ctxt
    )

  val aentails_hoist_existential_assms_tac : Proof.context -> int -> tactic = fn ctxt =>
    CHANGED o (
      CONVERSION (aentails_conv'' (Conv.changed_conv o asepconj_hoist_existential_conv) (K Conv.all_conv) ctxt)
      THEN' REPEAT_ALL_NEW (resolve_tac ctxt @{thms aexists_entailsL})
    )

  (* TODO: This is out of sync with the _method_ `aentails_simp_core` *)
  val aentails_simp_core_tac : Proof.context -> int -> tactic = fn ctxt => let
     fun NOTE msg =  Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_aentails_core) msg
                  #> Crush_Tacticals.LOG' ctxt (Config.get ctxt Crush_Config.log_aentails_core) msg in
    ucincl_discharge_tac ctxt (
            NOTE "aentails_core_hoist_pure_assms" (aentails_hoist_pure_assms_tac ctxt)
    ORELSE' NOTE "aentails_core_hoist_pure_concls" (aentails_hoist_pure_concls_tac ctxt)
    ORELSE' NOTE "aentails_core_intro_others" (aentails_simp_core_intro_others_tac ctxt)
    ORELSE' NOTE "aentails_core_cancel_univ_prems" (aentails_simp_core_cancel_univ_prems ctxt)
    ORELSE' NOTE "aentails_core_hoist_existential_assms" (aentails_hoist_existential_assms_tac ctxt)
    ORELSE' NOTE "aentails_core_simps" (aentails_simp_core_simps_tac ctxt)
    ORELSE' NOTE "aentails_core_split" (aentails_simp_core_split_tac ctxt)) end

  val aentails_cancel_multi_tac : Proof.context -> int -> tactic = fn ctxt =>
           aentails_float_multi_assms_tac ctxt
     THEN' (intro_tac @{thms aentails_cancel_multi_0R'} ctxt)

   fun is_cancellable_pair (ctxt : Proof.context) =
      let val allow_pure = Config.get ctxt Crush_Config.cancel_pure in
      fn (t0 : term) => fn (t1 : term) =>
        if (not allow_pure) andalso (is_pure t0 orelse is_pure t1) then
          false
        else
          is_unifiable_pair ctxt t0 t1
      end

   fun aentails_cancel_core_tac ctxt =
     (Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_aentails_cancel) "aentails_cancel_tac_unify_and_float"
                  (aentails_float_match ctxt (is_cancellable_pair ctxt)))
           THEN' (resolve_tac ctxt @{thms aentails_refl asepconj_mono asepconj_mono5 aentails_cancel_r})

  val aentails_cancel_legacy_points_to : Proof.context -> int -> tactic = fn ctxt =>
     if not (Config.get ctxt Crush_Config.enable_legacy_points_to_tactics) then
       K no_tac
     else
     let
     fun NOTE msg =  Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_aentails_cancel) msg
                  #> Crush_Tacticals.LOG' ctxt (Config.get ctxt Crush_Config.log_aentails_cancel) msg in
              NOTE "aentails_cancel_tac_points_to" (aentails_cancel_points_to_tac ctxt)
      ORELSE' NOTE "aentails_cancel_tac_points_to_raw" (aentails_cancel_points_to_raw_tac ctxt)
      ORELSE' NOTE "aentails_cancel_tac_raw_with_typed" (aentails_cancel_points_to_raw_with_typed_tac ctxt)
      ORELSE' NOTE "aentails_cancel_tac_split_points_to" (aentails_split_points_to_assms_tac ctxt)
     end

  val aentails_cancel_tac : Proof.context -> int -> tactic = fn ctxt => let
     fun NOTE msg =  Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_aentails_cancel) msg
                  #> Crush_Tacticals.LOG' ctxt (Config.get ctxt Crush_Config.log_aentails_cancel) msg in
            NOTE "aentails_cancel_tac_core" (aentails_cancel_core_tac ctxt)
    ORELSE' NOTE "aentails_cancel_tac_multi" (aentails_cancel_multi_tac ctxt)
    ORELSE' NOTE "aentails_cancel_legacy_points_to" (aentails_cancel_legacy_points_to ctxt)
    end

  val filter_metavariables = List.filter (fn x =>
    case x of Var _ => false | _ => true)

  \<comment>\<open>Apply separate conversions to pure and spatial premises and conclusions in the current goal.
     If the goal is not a separating entailment, \<^verbatim>\<open>concls\<close> is applied to the entire pure conclusion,
     and \<^verbatim>\<open>prems\<close> is only applied to the pure assumptions.\<close>
  fun aentails_prems_concls_conv (prems : Proof.context -> conv) (concls : Proof.context -> conv)
    (ctxt : Proof.context) : conv =
    let
      val prems'  = prems  #> asepconj_conv
      val concls' = concls #> asepconj_conv
    in
      Conv.params_conv ~1 (fn ctxt =>
        (Conv.concl_conv ~1 (aentails_conv (prems' ctxt) (concls' ctxt)))) ctxt
    end

  fun prems_concls_conv (prems : Proof.context -> conv) (concls : Proof.context -> conv)
    (ctxt : Proof.context) : conv =
      Conv.params_conv ~1 (fn ctxt =>
                   Conv.prems_conv ~1 (prems ctxt |> Conv.try_conv)
        then_conv (Conv.concl_conv ~1 (concls ctxt |> Conv.try_conv))) ctxt

  fun simp_prems_conv (thms : thm list) : Proof.context -> conv =
     (prems_concls_conv (thms |> force_meta_eqs |> Conv.rewrs_conv |> maybe_prop_conv |> K) (K Conv.all_conv))
     #> Conv.changed_conv
  fun simp_concls_conv (thms : thm list) : Proof.context -> conv =
     (prems_concls_conv (K Conv.all_conv) (thms |> force_meta_eqs |> Conv.rewrs_conv |> maybe_prop_conv |> K))
     #> Conv.changed_conv

  fun aentails_simp_prems_conv (thms : thm list) : Proof.context -> conv =
     (aentails_prems_concls_conv (thms |> force_meta_eqs |> eta_expands |> Conv.rewrs_conv |> maybe_prop_conv |> K) (K Conv.all_conv))
     #> Conv.changed_conv
  fun aentails_simp_concls_conv (thms : thm list) : Proof.context -> conv =
     (aentails_prems_concls_conv (K Conv.all_conv) (thms |> force_meta_eqs |> eta_expands |> Conv.rewrs_conv |> maybe_prop_conv |> K))
     #> Conv.changed_conv

  fun simp_prems_tac (thms : thm list) (ctxt : Proof.context) : int -> tactic =
     CONVERSION (simp_prems_conv thms ctxt)
  fun simp_concls_tac (thms : thm list) (ctxt : Proof.context) : int -> tactic =
     CONVERSION (simp_concls_conv thms ctxt)

  fun aentails_simp_prems_tac (thms : thm list) (ctxt : Proof.context) : int -> tactic =
     CONVERSION (aentails_simp_prems_conv thms ctxt)
  fun aentails_simp_concls_tac (thms : thm list) (ctxt : Proof.context) : int -> tactic =
     CONVERSION (aentails_simp_concls_conv thms ctxt)

  val unfold_prems_tac : thm list -> Proof.context -> int -> tactic =  fn thms => fn ctxt =>
    let val TIME = Crush_Time.TIME' ctxt (Config.get ctxt Crush_Config.time_unfold_prems) in
    CHANGED_PROP o (
             TRY o TIME "unfold_prems_sat_unfold"    (Crush_Unfold.sat_unfold_tac thms ctxt)
       (* This seems redundant given the saturating unfold...?
       THEN' TRY o TIME "unfold_prems_simp_prems"    (simp_prems_tac thms ctxt) *)
       THEN' TRY o TIME "unfold_prems_simp_aentails" (aentails_simp_prems_tac thms ctxt))
    end

  val aentails_hoist_is_sat_tac: Proof.context -> int -> tactic = fn ctxt =>
    eresolve_tac ctxt @{thms apure_entailsR0_revE}

  fun aentails_wp_ssa_normalize_tac (ctxt : Proof.context) : int -> tactic =
    let
      val micro_rust_simps = Named_Theorems.get ctxt @{named_theorems "micro_rust_simps"}
      val micro_rust_ssa = Named_Theorems.get ctxt @{named_theorems "micro_rust_ssa"}
    in
      CONVERSION (
     Conv.bottom_conv (K (Conv.try_conv (
                  (Conv.rewr_conv @{thm MICRO_RUST_SSA_CONTROL_def[symmetric]})
        then_conv (Conv.try_conv (Conv.rewrs_conv (micro_rust_ssa |> force_meta_eqs)))
     ))) ctxt
     then_conv Conv.bottom_conv (K (
         Conv.try_conv (Conv.rewr_conv @{thm MICRO_RUST_SSA_CONTROL_def}))) ctxt)
      THEN' (TRY o safe_simp_only_tac ctxt micro_rust_simps)
    end

end;

(* Isar extensions *)
local
  val unfold_prems_parser : Method.method context_parser = Attrib.thms >> (fn thms =>
    context_tactic_to_method (fn ctxt => Separation_Logic_Tactics.unfold_prems_tac thms ctxt 1))

  val unfold_concls_parser : Method.method context_parser = Attrib.thms >> (fn thms =>
    context_tactic_to_method (fn ctxt =>
      CHANGED (TRY (Separation_Logic_Tactics.simp_concls_tac thms ctxt 1)
          THEN TRY (Separation_Logic_Tactics.aentails_simp_concls_tac thms ctxt 1))))

  val _ = Theory.setup (Method.setup @{binding "unfold_prems"} (unfold_prems_parser >> K) "")
  val _ = Theory.setup (Method.setup @{binding "unfold_concls"} (unfold_concls_parser >> K) "")

  val _ = Theory.setup (Method.setup @{binding "asepconj_rotate_assms"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_rotate_assms_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_rotate_concls"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_rotate_concls_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_normalize_assoc_concls"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_normalize_assoc_concls_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_normalize_assoc_assms"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_normalize_assoc_assms_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_normalize_assoc"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_normalize_assoc_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_drule"}
             (Attrib.thms >> (fn thms => fn _ => (context_tactic_to_method (fn ctxt =>
                (Separation_Logic_Tactics.aentails_drule_tac thms ctxt 1))))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_cond_drule"}
             (Attrib.thms >> (fn thms => fn _ => (context_tactic_to_method (fn ctxt =>
                (Separation_Logic_Tactics.aentails_cond_drule_tac thms ctxt 1))))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_crule"}
             (Attrib.thms >> (fn thms => fn _ => (context_tactic_to_method (fn ctxt =>
                (Separation_Logic_Tactics.aentails_crule_tac thms ctxt 1))))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_cond_crule"}
             (Attrib.thms >> (fn thms => fn _ => (context_tactic_to_method (fn ctxt =>
                (Separation_Logic_Tactics.aentails_cond_crule_tac thms ctxt 1))))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_rule"}
          (Attrib.thms >> (fn thms => fn _ => (context_tactic_to_method (fn ctxt =>
             (Separation_Logic_Tactics.aentails_rule_tac thms ctxt 1))))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_cond_rule"}
          (Attrib.thms >> (fn thms => fn _ => (context_tactic_to_method (fn ctxt =>
             (Separation_Logic_Tactics.aentails_cond_rule_tac thms ctxt 1))))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_hoist_pure_assms"}
          (Scan.succeed (SIMPLE_METHOD' o (Separation_Logic_Tactics.aentails_hoist_pure_assms_tac))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_hoist_existential"}
          (Scan.succeed (SIMPLE_METHOD' o (Separation_Logic_Tactics.aentails_hoist_existential_assms_tac)))
          "hoist existentials out of the LHS of a separating entailment")

  val _ = Theory.setup (Method.setup @{binding "aentails_pick_concl"}
          (Scan.lift Parse.nat >> (SIMPLE_METHOD' oo (Separation_Logic_Tactics.aentails_pick_concls_tac))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_pick_assm"}
          (Scan.lift Parse.nat >> (SIMPLE_METHOD' oo (Separation_Logic_Tactics.aentails_pick_assms_tac))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_pick_concl_ext"}
          (Scan.lift Parse.nat -- Scan.lift Parse.nat >>
            (SIMPLE_METHOD' oo (fn (n,i) => Separation_Logic_Tactics.aentails_pick_concls_tac_ext n i))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_pick_assm_ext"}
          (Scan.lift Parse.nat -- Scan.lift Parse.nat >>
            (SIMPLE_METHOD' oo (fn (n,i) => Separation_Logic_Tactics.aentails_pick_assms_tac_ext n i))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_joinfirst_concl"}
          (Scan.lift Parse.nat >>
              (SIMPLE_METHOD' oo (Separation_Logic_Tactics.aentails_joinfirst_concls_tac))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_joinfirst_assm"}
          (Scan.lift Parse.nat >>
              (SIMPLE_METHOD' oo (Separation_Logic_Tactics.aentails_joinfirst_assms_tac))) "")

  val _ = Theory.setup (Method.setup @{binding "ucincl_solve"}
          (Method.sections (Simplifier.simp_modifiers @ Splitter.split_modifiers)
                |-- Scan.succeed (fn ctxt => SIMPLE_METHOD' (REPEAT_DETERM1 o (Separation_Logic_Tactics.ucincl_solve_tac ctxt)))) "")

  val _ = Theory.setup (Method.setup @{binding "ucincl_discharge"}
          (Method.sections Simplifier.simp_modifiers |-- Scan.lift (Parser.parse_method >> (fn m => fn (ctxt : Proof.context) =>
             Separation_Logic_Tactics.ucincl_discharge_method (m ctxt)))) "")

  val _ = Theory.setup (Method.setup @{binding "aentails_hoist_is_sat"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_hoist_is_sat_tac)) "")

  val _ = Theory.setup (Method.setup @{binding "micro_rust_ssa_wp_normalize"}
          (Scan.succeed (SIMPLE_METHOD' o Separation_Logic_Tactics.aentails_wp_ssa_normalize_tac)) "")

  val _ = Theory.setup (Attrib.setup @{binding "wp_split"}
                       (Separation_Logic_Tactics.specialize_split_rule_to_wp_attribute |> Scan.succeed) "")

in end
