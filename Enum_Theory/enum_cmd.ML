(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Enum command: typedef-based construction with all theorems proven *)

signature ENUM_CMD =
sig
  val enum_trace_config: bool Config.T
  val enum_sync_prove_config: bool Config.T
  val enum_eq_simproc: simproc
  val enum_cmd: (binding * (binding * string list) list) -> local_theory -> local_theory
end

structure Enum_Cmd : ENUM_CMD =
struct

open Ctr_Sugar_Util

val enum_trace_config = Attrib.setup_config_bool (Binding.name "enum_trace") (fn _ => false)
val enum_sync_prove_config = Attrib.setup_config_bool (Binding.name "enum_sync_prove") (fn _ => true)


fun timer ctx timer msg = (if Config.get ctx enum_trace_config
  then tracing (msg ^ ": " ^ Timing.message (Timing.result timer))
  else (); Timing.start ())

fun time_tactic msg ctx tac =
  if Config.get ctx enum_trace_config then
    fn th =>
      let
        val start = Timing.start ()
        val res = tac th |> Seq.list_of |> Seq.of_list
        val tim = Timing.result start
        val _ = tracing (msg ^ ": " ^ Timing.message tim)
      in
        res
      end
  else tac

fun trace_prove ctxt xs asms prop tac = 
  if Config.get ctxt enum_sync_prove_config then
    Goal.prove ctxt xs asms prop tac
  else
    Goal.prove_sorry ctxt xs asms prop tac

fun par_do_the_works works =
    works
  |> chop_groups 10
  |> Par_List.map (map (fn f => f ()))
  |> List.concat

fun do_the_works ctxt works =
  if Config.get ctxt enum_sync_prove_config then
    (* if we do synchronous proving, at least we can use parallelism to speed up the proofs *)
    par_do_the_works works
  else
    (* if we do asynchronous proving, then we just don't bother doing optimization *)
    map (fn f => f ()) works

(* Build sum type from a list of types*)
fun mk_sum_type [] = raise ERROR "Empty enum"
  | mk_sum_type [ty] = ty
  | mk_sum_type (ty :: tys) =
    @{Type \<open>sum ty \<open>mk_sum_type tys\<close>\<close>}

(* Build injection term: inject the nth element into a sum type *)
(* Special case: if there's only one constructor, no injection needed *)
fun mk_inj_term 0 term @{Type \<open>sum a b\<close>} = @{Const\<open>Inl a b for term\<close>}
  | mk_inj_term 0 term _ = term  (* Single constructor, no sum type needed *)
  | mk_inj_term n term @{Type \<open>sum a rest\<close>} = @{Const\<open>Inr rest a for \<open>mk_inj_term (n - 1) term rest\<close>\<close>}
  | mk_inj_term _ _ _ = raise ERROR "mk_inj_term: malformed sum type"

fun find_inner_most_arg (_ $ x) = find_inner_most_arg x
  | find_inner_most_arg t = t

fun get_type_thm_local ctxt typ thm_suffix =
  let
    fun type_name_of (Type (name, _)) = Long_Name.base_name name
      | type_name_of _ = ""

    val typ_name = type_name_of typ
  in
    if typ_name = "" then raise ERROR "thm is not found!"
    else
      let
        val thm_name = typ_name ^ "." ^ thm_suffix
      in
        Proof_Context.get_thm ctxt thm_name
      end
  end


fun has_type_thm_local ctxt typ thm_suffix =
  (get_type_thm_local ctxt typ thm_suffix; true)
  handle ERROR _ => false

fun has_is_enum_thm ctxt typ = has_type_thm_local ctxt typ "is_enum"

fun get_ctor_def ctxt typ ctor =
  let
    val name = dest_Const_name ctor
    val basename = Long_Name.base_name name
  in
    get_type_thm_local ctxt typ (basename ^ "_def")
  end

fun same_ctor af bf =
  let
    val aname = dest_Const_name af
    val bname = dest_Const_name bf
  in
    aname = bname
  end

fun only_simpset context thms =
  context |> Simplifier.clear_simpset |> Simplifier.add_simps thms

fun enum_eq_proc ctxt ct =
  let
    val orig_t = Thm.term_of ct
  in
    case orig_t of
      @{Const_\<open>HOL.eq T for a b\<close>} => if has_is_enum_thm ctxt T
      then
        let
          val (af, _) = strip_comb a
          val (bf, _) = strip_comb b
        in
          (if not (same_ctor af bf) then
            let
              val Abs_inject = get_type_thm_local ctxt T "Abs_inject"
              val adef = get_ctor_def ctxt T af
              val bdef = get_ctor_def ctxt T bf
              val goal = orig_t |> HOLogic.mk_not |> HOLogic.mk_Trueprop
              val thm = trace_prove ctxt [] [] goal (fn {context, ...} =>
                simp_tac (only_simpset context ([Abs_inject, adef, bdef] @ @{thms sum.distinct sum.inject simp_thms UNIV_I lessThan_iff triv_forall_equality})) 1)
            in
              SOME (thm RS @{thm Eq_FalseI})
            end
          else NONE)
          handle ERROR _ => NONE |  TERM _ => NONE
        end
      else NONE
    | _ => NONE
  end

val enum_eq_simproc = @{simproc_setup\<open>enum_eq (\<open>x = y\<close>) = \<open>K enum_eq_proc\<close>\<close>}

fun add_and_prove_is_enum typ_name lthy =
  let
    val is_enum_prop = HOLogic.mk_Trueprop @{term True}
    val is_enum_thm = trace_prove lthy [] [] is_enum_prop
      (fn {context, ...} => rtac context @{thm TrueI} 1)

    val is_simpl_binding = Binding.qualify true typ_name (Binding.name "is_enum")
    val (_, lthy') = lthy
      |> Local_Theory.note ((is_simpl_binding, []), [is_enum_thm]) 
  in
    lthy'
  end

fun mk_case_certificate ctxt raw_thms =
  let
    val thms as thm1 :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Thm.unvarify_global (Proof_Context.theory_of ctxt)
      |> Conjunction.elim_balanced (length raw_thms)
      |> map Simpdata.mk_meta_eq
      |> map Drule.zero_var_indexes
    val params = Term.add_free_names (Thm.prop_of thm1) []
    val rhs = thm1
      |> Thm.prop_of |> Logic.dest_equals |> fst |> Term.strip_comb
      ||> fst o split_last |> list_comb
    val lhs = Free (singleton (Name.variant_list params) "case", Term.fastype_of rhs)
    val assum = Thm.cterm_of ctxt (Logic.mk_equals (lhs, rhs))
  in
    thms
    |> Conjunction.intr_balanced
    |> rewrite_rule ctxt [Thm.symmetric (Thm.assume assum)]
    |> Thm.implies_intr assum
    |> Thm.generalize (Names.empty, Names.make_set params) 0
    |> Axclass.unoverload ctxt
    |> Thm.varifyT_global
  end

fun mk_equal_eqns typ constr_terms constr_arg_typs inject_simps thy =
  let
    val ctxt = Proof_Context.init_global thy
    val equal_const = Const (@{const_name HOL.equal}, typ --> typ --> HOLogic.boolT)

    fun mk_applied_pair ctxt0 ((ci, argi), (cj, argj)) =
      let
        val (xs, ctxt1) = mk_Frees "x" argi ctxt0
        val (ys, _) = mk_Frees "y" argj ctxt1
        val lhs = list_comb (ci, xs)
        val rhs = list_comb (cj, ys)
        val eq_tm = equal_const $ lhs $ rhs
        val is_same = (ci aconv cj)
        val goal_body =
          if is_same andalso null argi
          then HOLogic.mk_eq (eq_tm, @{term True})
          else if is_same
          then HOLogic.mk_eq (eq_tm,
            foldr1 HOLogic.mk_conj (map2 (fn x => fn y => HOLogic.mk_eq (x, y)) xs ys))
          else HOLogic.mk_eq (eq_tm, @{term False})
        val goal = fold_rev Logic.all (xs @ ys) (HOLogic.mk_Trueprop goal_body)
      in
        (goal, is_same andalso null argi)
      end

    val indexed = constr_terms ~~ constr_arg_typs
    val pairs = map_product pair indexed indexed
    val goals_with_refl = map (mk_applied_pair ctxt) pairs
    val simp_thms = @{thms equal_eq} @ inject_simps
    val eqns = map (fn (goal, _) =>
      Goal.prove_sorry_global thy [] [] goal (fn {context, ...} =>
        simp_tac (Simplifier.add_simps simp_thms context) 1)
      |> Simpdata.mk_eq) goals_with_refl
    val refl_eqn = fst (the (find_first (fn (_, (_, is_nullary_refl)) => is_nullary_refl)
      (eqns ~~ goals_with_refl)))
      handle Option => hd eqns
  in
    (refl_eqn, eqns)
  end

fun add_equal_instance typ constr_terms constr_arg_typs case_eq_thms inject_simps thy =
  let
    val tyco = dest_Type_name typ
    fun add_eq_def lthy_inst =
      let
        fun mk_side const_name =
          Const (const_name, typ --> typ --> HOLogic.boolT) $ Free ("x", typ) $ Free ("y", typ)
        val spec =
          HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_side @{const_name HOL.equal}, mk_side @{const_name HOL.eq}))
          |> Syntax.check_term lthy_inst
        val ((_, (_, raw_def)), lthy_inst') =
          Specification.definition NONE [] [] (Binding.empty_atts, spec) lthy_inst
        val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy_inst')
        val def = singleton (Proof_Context.export lthy_inst' thy_ctxt) raw_def
      in
        (def, lthy_inst')
      end
    fun eq_tac ctxt thms =
      Class.intro_classes_tac ctxt [] THEN ALLGOALS (Proof_Context.fact_tac ctxt thms)
  in
    thy
    |> Class.instantiation ([tyco], [], @{sort equal})
    |> add_eq_def
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) eq_tac o single
    |> snd
    |> Code.declare_datatype_global
         (map (fn c => (dest_Const_name c, fastype_of c)) constr_terms)
    |> (fn thy' =>
         let
           val ctxt = Proof_Context.init_global thy'
           val case_thms = map Thm.varifyT_global case_eq_thms
           val (refl_eqn, eq_eqns) =
             mk_equal_eqns typ constr_terms constr_arg_typs inject_simps thy'
         in thy'
           |> Code.declare_default_eqns_global
                ((refl_eqn, false) :: map (rpair true) (rev eq_eqns))
           |> Code.declare_default_eqns_global (map (rpair true) (rev case_thms))
           |> Code.declare_case_global (mk_case_certificate ctxt case_thms)
         end)
  end

fun prove_complex_induct lthy2 vars ind_prop Abs_induct constrs_with_typs constr_defs =
trace_prove lthy2 vars [] ind_prop
      (fn {context, ...} =>
        let
          val n = length constrs_with_typs
        in EVERY [
            resolve_tac context [Abs_induct] 1,
            rewrite_goal_tac context constr_defs 1,
            (* For singleton enums, no sum type case splitting needed *)
            if n = 1 then ALLGOALS (clarsimp_tac context)
            else
              REPEAT (Subgoal.FOCUS (fn {context, concl, ...} =>
                let val concl = Thm.term_of concl
                    val var = find_inner_most_arg concl
                    val cvar = Thm.cterm_of context var
                    val bconcl = concl |> HOLogic.dest_Trueprop |> Thm.cterm_of context
                    val instan = infer_instantiate' context [SOME cvar, SOME bconcl] @{thm sum.exhaust}
                in rtac context instan 1
                end) context 1 THEN
                ALLGOALS (clarsimp_tac context))
          ]
        end)

(* prove exhaust using induction principle *)
fun solve_exhaust_tac context x_ind goal induct_thm = 
  let
    val x = Thm.cterm_of context x_ind
    val g = lambda x_ind (Induct.atomize_term context goal)
    val induct = infer_instantiate' context [SOME (Thm.cterm_of context g), SOME x] induct_thm
  in
    EVERY [
      Induct.atomize_tac context 1,
      rtac context induct 1,
      ALLGOALS (Induct.rulify_tac context),
      ALLGOALS (fn i => Subgoal.FOCUS (fn {context, prems, ...} =>
        resolve_tac context [nth prems (i - 1)] 1 THEN
        simp_tac (context |> Simplifier.clear_simpset) 1) context i)
    ]
  end

fun add_and_prove_exhaust lthy typ_name vars x_ind goal induct_thm constr_names =
  let
    val exhaust_thm = trace_prove lthy vars [] goal
        (fn {context, ...} => solve_exhaust_tac context x_ind goal induct_thm)
    val exhaust_binding = Binding.qualify true typ_name (Binding.name "exhaust")
    val case_names_att = Attrib.internal \<^here> (fn _ => Rule_Cases.case_names constr_names)
  in
    (exhaust_thm, lthy |> Local_Theory.note ((exhaust_binding, case_names_att :: @{attributes [cases type]}), [exhaust_thm]) |> snd)
  end

fun solve_split_tac context x_varc case_eq_thms exhaust_thm =
  let
    fun solve_tac context i =
      Object_Logic.rulify_tac context i THEN
            asm_full_simp_tac (only_simpset context case_eq_thms) i
  in
    EVERY [
      rtac context @{thm HOL.iffI} 1,
      REPEAT (rtac context @{thm conjI} 1 THEN
        solve_tac context 1) |> time_tactic "split repeat" context,
      solve_tac context 1,

      REPEAT (etac context @{thm conjE} 1),
      Object_Logic.rulify_tac context 1,
      rtac context (Thm.instantiate' [] [SOME x_varc] exhaust_thm) 1,
      ALLGOALS (fn i => Subgoal.FOCUS
        (fn {context, prems, ...} =>
          let
            val eq = List.last prems
            val i' = i - 1
            val case_eq = nth case_eq_thms i'
          in
            asm_full_simp_tac (only_simpset context [eq, case_eq]) 1 THEN
            rtac context (nth prems i') 1 THEN
            rtac context eq 1
          end)
        context i) |> time_tactic "split to simp" context
    ]
  end

fun solve_split_asm_tac context split_thm =
  simp_tac (only_simpset context (split_thm :: @{thms de_Morgan_disj de_Morgan_conj disj_not1 not_ex simp_thms})) 1 |> time_tactic "split asm" context

fun enum_cmd_complex (typ_binding, constrs) lthy =
  let
    val _ = if null constrs then error "Empty enum not allowed" else ()
    val time = timer lthy
    val timer = time (Timing.start ())
    val typ_name = Binding.name_of typ_binding

    (* Parse constructor argument types *)
    val constrs_with_typs : (binding * typ list) list =
      map (fn (c, typ_strs) => (c, Syntax.read_typs lthy typ_strs)) constrs

    (* Build representation type as sum of products *)
    val prod_typs = map (HOLogic.mk_tupleT o snd) constrs_with_typs
    val rep_typ = mk_sum_type prod_typs
    val timer = time (timer "Setup")

    (* Step 1: Define the type using typedef *)
    val typedef_set = HOLogic.mk_UNIV rep_typ

    (* Create qualified bindings for Abs, Rep, and type_definition *)
    val typedef_bindings = SOME {
      Abs_name = Binding.qualify true typ_name (Binding.name "Abs"),
      Rep_name = Binding.qualify true typ_name (Binding.name "Rep"),
      type_definition_name = Binding.qualify true typ_name (Binding.name "type_definition")
    }

    val ((_, (typ_info, typedef_info)), lthy1) = lthy
      |> Typedef.add_typedef {overloaded = false}
           (typ_binding, [], NoSyn) typedef_set typedef_bindings
           (fn ctxt => resolve_tac ctxt @{thms UNIV_witness} 1)
      ||> add_and_prove_is_enum typ_name

    val { abs_type = typ, Abs_name, Rep_name, ...} = typ_info
    val abs_const = Const (Abs_name, rep_typ --> typ)
    val rep_const = Const (Rep_name, typ --> rep_typ)

    (* Get typedef theorems *)
    val { Abs_induct,
          Abs_inverse,
          Abs_inject,
           ...} = typedef_info
    val timer = time (timer "Typedef")

    (* Step 2: Define constructors *)
    fun define_constructor (idx, (c_binding, arg_typs)) lthy =
      let
        (* Build constructor body: \<lambda>x1 ... xn. Abs (Inl/Inr (x1, ..., xn)) *)
        val (var_terms, lthy1) = mk_Frees "x" arg_typs lthy
        val tuple = HOLogic.mk_tuple var_terms
        val injected = mk_inj_term idx tuple rep_typ
        val abs_applied = abs_const $ injected
        (* Use absfree to properly abstract over Free variables *)
        val constr_tm = fold_rev lambda var_terms abs_applied

        (* Qualify constructor name *)
        val qual_c_binding = Binding.qualify false typ_name c_binding
        val def_binding = Binding.qualify true typ_name (Binding.suffix_name "_def" c_binding)

        val (_, lthy') = lthy1
          |> Local_Theory.define ((qual_c_binding, NoSyn),
                                  ((def_binding, []), constr_tm))
      in
        (qual_c_binding, lthy')
      end

    val (constr_qbindings, lthy2) = lthy1
      |> snd o Local_Theory.begin_nested
      |> fold_map define_constructor (map_index I constrs_with_typs)
      ||> Local_Theory.end_nested
    val constr_terms = map (fn (c, args) =>
      Const (Local_Theory.full_name lthy2 c, args ---> typ))
      (constr_qbindings ~~ map snd constrs_with_typs)
    val constr_defs = map (get_type_thm_local lthy2 typ o Binding.name_of o Binding.suffix_name "_def") constr_qbindings
    val timer = time (timer "Constructor Definitions")

    (* Step 3: Prove induction principle *)
    (* \<lbrakk> ?P C1; ?P C2; ... \<rbrakk> \<Longrightarrow> ?P ?x *)
    val ((P_ind, x_ind), _) =
      lthy2
      |> mk_Frees "P" [typ --> HOLogic.boolT]
      ||>> mk_Frees "x" [typ]
      |>> map_prod the_single the_single

    fun mk_ind_prem c_const arg_typs =
      let
        val vars = map_index (fn (i, ty) => Var (("x" ^ Int.toString (i + 1), 0), ty)) arg_typs
        val c_applied = list_comb (c_const, vars)
        val body = P_ind $ c_applied
        val body_prop = HOLogic.mk_Trueprop body
      in
        fold_rev Logic.all vars body_prop
      end

    val ind_prems_prop = map2 mk_ind_prem constr_terms (map snd constrs_with_typs)
    val ind_concl = P_ind $ x_ind
    val ind_prop = Logic.list_implies (ind_prems_prop, HOLogic.mk_Trueprop ind_concl)

    val vars = Variable.add_free_names lthy2 ind_prop []
    val induct_thm = prove_complex_induct lthy2 vars ind_prop Abs_induct constrs_with_typs constr_defs

    (* Add the induction theorem to the context with qualified name and induct_type attribute *)
    val induct_binding = Binding.qualify true typ_name (Binding.name "induct")
    val constr_names = map (Binding.name_of o fst) constrs_with_typs
    val case_names_att = Attrib.internal \<^here> (fn _ => Rule_Cases.case_names constr_names)
    val (_, lthy3) = lthy2
      |> Local_Theory.note ((induct_binding, case_names_att :: @{attributes [induct type]}), [induct_thm])
    val timer = time (timer "Induction Principle")

    (* Step 4: Define case combinator *)
    (* case_<typ> : (arg_typs1 -> 'a) -> ... -> (arg_typsN -> 'a) -> <typ> -> 'a *)
    val (Ta, lthy4) = map_prod the_single I (mk_TFrees 1 lthy3)

    (* Create function types for each case *)
    fun mk_case_arg_type arg_typs = arg_typs ---> Ta

    val case_arg_typs = map (mk_case_arg_type o snd) constrs_with_typs
    val case_typ = case_arg_typs ---> typ --> Ta

    (* Create case function variables *)
    val (case_funs, lthy5) = mk_Frees "f" case_arg_typs lthy4

    (* Build case body: match on constructor and apply corresponding function *)
    (* For each constructor C x1 ... xn, we want: if input = C x1 ... xn then f x1 ... xn *)
    fun mk_case_branch arg_typs f =
      let
        val (args, _) = mk_Frees "x" arg_typs lthy5
      in
        HOLogic.tupled_lambda (HOLogic.mk_tuple args) (list_comb (f, args))
      end

    val branches = map2 mk_case_branch (map snd constrs_with_typs) case_funs

    (* Use Abs_induct and constructor definitions to build the case function *)
    (* case f1 f2 ... x = case (Rep x) of Inl a => f1 a | Inr (Inl b) => f2 b | ... *)
    val case_body_var = rep_const $ x_ind

    fun mk_case_of_sum [] _ _ = raise ERROR "mk_case_of_sum: empty list"
      | mk_case_of_sum [rhs] var _ = rhs $ var
      | mk_case_of_sum (rhs :: rest) sum_var ctx =
        let
          val @{Type \<open>sum a b\<close>} = fastype_of sum_var
          val (right_var, ctx') = yield_singleton (mk_Frees "b") b ctx
          val right_body = mk_case_of_sum rest right_var ctx'
          val right_branch = lambda right_var right_body
        in
          @{Const \<open>case_sum a Ta b for rhs right_branch sum_var\<close>}
        end

    val case_body = mk_case_of_sum branches case_body_var lthy5
    val case_tm = fold_rev lambda case_funs (lambda x_ind case_body)

    (* Define the case combinator *)
    val case_binding = Binding.qualify true typ_name (Binding.name "case")
    val case_def_binding = Binding.qualify true typ_name (Binding.name "case_def")

    val ((case_const, (_, case_def)), lthy6) = lthy5
      |> Local_Theory.define ((case_binding, NoSyn),
                              ((case_def_binding, []), case_tm))
    val phi = Local_Theory.target_morphism lthy6
    val case_const = Morphism.term phi case_const
    val case_const = Const (dest_Const_name case_const, case_typ)
    val case_def = Morphism.thm phi case_def

    (* Register with Case_Translation for pattern matching *)
    val lthy7 = lthy6
      |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
           (fn _ => Case_Translation.register case_const constr_terms)
    val timer = time (timer "Case expression")

    (* Step 5: Prove case equality theorems *)
    (* For each constructor Ci: case f1 ... fn (Ci x1 ... xk) = fi x1 ... xk *)
    fun mk_case_eq_thm (idx, (c_term, arg_typs)) =
      let
        (* Create fresh variables for constructor arguments *)
        val arg_vars = mk_Frees "x" arg_typs lthy7 |> fst
        val c_applied = list_comb (c_term, arg_vars)

        (* Create fresh variables for case functions *)
        val case_fun_vars = mk_Frees "f" case_arg_typs lthy7 |> fst

        (* LHS: case f1 ... fn (Ci x1 ... xk) *)
        val lhs = list_comb (case_const, case_fun_vars @ [c_applied])

        (* RHS: fi x1 ... xk *)
        val fi = nth case_fun_vars idx
        val rhs = list_comb (fi, arg_vars)

        val eq = HOLogic.mk_eq (lhs, rhs)

        val goal = fold_rev Logic.all (arg_vars @ case_fun_vars) (HOLogic.mk_Trueprop eq)

        (* Prove it using case_def and constructor definitions *)
        (* TODO: This proof needs proper tactics to handle tuple destructuring *)
        val thm = trace_prove lthy7 [] [] goal
          (fn {context, ...} =>
            rewrite_goal_tac context [case_def] 1 THEN
            clarsimp_tac (Simplifier.add_simps (Abs_inverse :: case_def :: constr_defs) context) 1)
      in
        thm
      end

    val case_eq_thms = map_index mk_case_eq_thm (constr_terms ~~ map snd constrs_with_typs)

    (* Store case theorems as ENUM.cases with simp attribute *)
    val cases_binding = Binding.qualify true typ_name (Binding.name "cases")
    val ((_, _), lthy8) = lthy7
      |> Local_Theory.note ((cases_binding, @{attributes [simp]}), case_eq_thms)
    val timer = time (timer "Case Equalities")

    (* Step 6: Prove exhaustiveness theorem *)
    val P = lthy8 |> Variable.variant_fixes ["P"] |> fst |> the_single |> (fn P => Free (P, HOLogic.boolT)) |> HOLogic.mk_Trueprop

    fun exhaust_case ctor argTs =
      let
        val vars = mk_Frees "x" argTs lthy8 |> fst
        val apped = list_comb (ctor, vars)
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (x_ind, apped))
      in
        fold_rev Logic.all vars (Logic.mk_implies (eq, P))
      end

    val premises = map2 exhaust_case constr_terms (map snd constrs_with_typs)
    val goal = Logic.list_implies (premises, P)
    val vars = Variable.add_free_names lthy8 goal []
    val constr_names = map (Binding.name_of o fst) constrs_with_typs
    val (exhaust_thm, lthy9) = add_and_prove_exhaust lthy8 typ_name vars x_ind goal induct_thm constr_names
    val _ = time (timer "Case Split")

    (* Step 7: Prove split theorems *)
    (* The split theorem allows case expressions to be split into individual cases *)
    (* P (case x of C1 x1..xk => f1 x1..xk | ... | Cn => fn) = ((x = C1 x1..xk --> P (f1 x1..xk)) & ... & (x = Cn --> P fn)) *)

    val P_var = lthy9 |> yield_singleton (mk_Frees "P") (Ta --> HOLogic.boolT) |> fst

    (* Build LHS: P (case f1 ... fn x) *)
    val case_expr = list_comb (case_const, case_funs @ [x_ind])
    val lhs = P_var $ case_expr

    (* Build RHS: (ALL x1..xk. x = C1 x1..xk --> P (f1 x1..xk)) & ... *)
    fun mk_split_clause ((ctor, branch), arg_typs) =
      let
        val arg_vars = mk_Frees "a" arg_typs lthy9 |> fst
        val ctor_applied = list_comb (ctor, arg_vars)
        val branch_applied = list_comb (branch, arg_vars)
        val eq = HOLogic.mk_eq (x_ind, ctor_applied)
        val consequent = P_var $ branch_applied
        val body = HOLogic.mk_imp (eq, consequent)
      in
        fold_rev (fn v => fn b => HOLogic.mk_all (fst (dest_Free v), fastype_of v, abstract_over (v, b))) arg_vars body
      end

    val rhs_clauses = map mk_split_clause ((constr_terms ~~ case_funs) ~~ map snd constrs_with_typs)
    val rhs = foldr1 HOLogic.mk_conj rhs_clauses

    val split_prop = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
    val split_vars = Variable.add_free_names lthy9 split_prop []

    val x_varc = Thm.cterm_of lthy9 x_ind
    val split_thm = trace_prove lthy9 split_vars [] split_prop
      (fn {context, ...} =>
        solve_split_tac context x_varc case_eq_thms exhaust_thm)

    fun mk_split_clause' ((ctor, branch), arg_typs) =
      let
        val arg_vars = mk_Frees "a" arg_typs lthy9 |> fst
        val ctor_applied = list_comb (ctor, arg_vars)
        val branch_applied = list_comb (branch, arg_vars)
        val eq = HOLogic.mk_eq (x_ind, ctor_applied)
        val consequent = P_var $ branch_applied |> HOLogic.mk_not
        val body = HOLogic.mk_conj (eq, consequent)
      in
        fold_rev (fn v => fn b => HOLogic.mk_exists (fst (dest_Free v), fastype_of v, abstract_over (v, b))) arg_vars body
      end

    val rhs_clauses' = map mk_split_clause' ((constr_terms ~~ case_funs) ~~ map snd constrs_with_typs)
    val rhs' = foldr1 HOLogic.mk_disj rhs_clauses' |> HOLogic.mk_not
    val split_asm_prop = HOLogic.mk_eq (lhs, rhs') |> HOLogic.mk_Trueprop
    val split_asm_thm = trace_prove lthy9 split_vars [] split_asm_prop
      (fn {context, ...} => solve_split_asm_tac context split_thm)

    val split_binding = Binding.qualify true typ_name (Binding.name "split")
    val split_asm_binding = Binding.qualify true typ_name (Binding.name "split_asm")
    val splits_binding = Binding.qualify true typ_name (Binding.name "splits")
    val lthy10 = lthy9
      |> Local_Theory.note ((split_binding, []), [split_thm])
      |> snd
      |> Local_Theory.note ((split_asm_binding, []), [split_asm_thm])
      |> snd
      |> Local_Theory.note ((splits_binding, []), [split_thm, split_asm_thm])
      |> snd
    val _ = timer "Split Theorem"

    val lthy11 = lthy10
      |> Local_Theory.background_theory
           (add_equal_instance typ constr_terms (map snd constrs_with_typs)
              case_eq_thms
              (Abs_inject :: constr_defs))

  in
    lthy11
  end

(* Simplified enum command using natural number representation *)
fun enum_cmd_simpl (typ_binding, constrs : binding list) lthy =
  let
    val _ = if null constrs then error "Empty enum not allowed" else ()
    val time = timer lthy
    val timer = time (Timing.start ())
    val typ_name = Binding.name_of typ_binding
    val n = length constrs

    (* Step 1: Define the type using typedef over {..<n} *)
    val n_term = HOLogic.mk_nat n
    val typedef_set = @{Const\<open>lessThan HOLogic.natT for n_term\<close>}
    val timer = time (timer "Setup")

    val typedef_bindings = SOME {
      Abs_name = Binding.qualify true typ_name (Binding.name "Abs"),
      Rep_name = Binding.qualify true typ_name (Binding.name "Rep"),
      type_definition_name = Binding.qualify true typ_name (Binding.name "type_definition")
    }

    val ((_, (typ_info, typedef_info)), lthy1) = lthy
      |> Typedef.add_typedef {overloaded = false}
           (typ_binding, [], NoSyn) typedef_set typedef_bindings
           (fn ctxt => auto_tac ctxt)

    val { abs_type = typ, Abs_name, ...} = typ_info
    val abs_const = Const (Abs_name, HOLogic.natT --> typ)

    val {  Abs_induct, Abs_inject, ...} = typedef_info
    val timer = time (timer "Typedef")

    (* Step 2: Define constructors - each is just Abs i *)
    fun define_constructor c_binding (n, lthy) =
      let
        val constr_tm = abs_const $ n

        val qual_c_binding = Binding.qualify false typ_name c_binding
        val def_binding = Binding.qualify true typ_name (Binding.suffix_name "_def" c_binding)

        val ((trm, (_, def_thm)), lthy') = lthy
          |> Local_Theory.define ((qual_c_binding, NoSyn),
                                  ((def_binding, []), constr_tm))
        val phi = Local_Theory.target_morphism lthy'
        val trm = Morphism.term phi trm
        val def_thm = Morphism.thm phi def_thm
      in
        ((trm, def_thm), (HOLogic.mk_Suc n, lthy'))
      end

    val ((constr_terms, constr_defs), lthy2) = lthy1
      |> snd o Local_Theory.begin_nested
      |> pair HOLogic.zero
      |> fold_map define_constructor constrs
      ||> Local_Theory.end_nested o snd
      |>> split_list
    val timer = time (timer "Constructor Definitions")

    (* Step 3: Prove induction principle *)
    val ((P_ind, _), (x_ind, _)) =
      lthy2
      |> mk_Frees' "P" [typ --> HOLogic.boolT]
      |>> map_prod the_single the_single
      ||>> (mk_Frees' "x" [typ]
           #>> map_prod the_single the_single)
      |> fst

    val ind_prems = map (fn c => HOLogic.mk_Trueprop (P_ind $ c)) constr_terms
    val ind_concl = HOLogic.mk_Trueprop (P_ind $ x_ind)
    val ind_prop = Logic.list_implies (ind_prems, ind_concl)

    val vars = Variable.add_free_names lthy2 ind_prop []
    val induct_thm = trace_prove lthy2 vars [] ind_prop
      (fn {context, ...} =>
        EVERY [
          resolve_tac context [Abs_induct] 1 |> time_tactic "resolve" lthy2,
          rewrite_goal_tac context constr_defs 1 |> time_tactic "rewrite" lthy2,
          clarsimp_tac context 1 |> time_tactic "clarsimp" lthy2,
          (* Split on disjunctions from set membership *)
          REPEAT (etac context @{thm less_SucE} 1 THEN etac context @{thm HOL.ssubst} 2 THEN assume_tac context 2)
            |> time_tactic "repeat" lthy2, 
          TRY (simp_tac context 1) |> time_tactic "finale" lthy2
        ])
    val induct_binding = Binding.qualify true typ_name (Binding.name "induct")
    val constr_names = map Binding.name_of constrs
    val case_names_att = Attrib.internal \<^here> (fn _ => Rule_Cases.case_names constr_names)
    val (_, lthy3) = lthy2
      |> Local_Theory.note ((induct_binding, case_names_att :: @{attributes [induct type]}), [induct_thm])
    val timer = time (timer "Induction Principle")

    (* Step 4: Define case combinator *)
    (* case : 'a -> ... -> 'a -> typ -> 'a *)
    val (Ta, lthy4) = map_prod the_single I (mk_TFrees 1 lthy3)
    val case_arg_typs = replicate n Ta
    val case_typ = case_arg_typs ---> typ --> Ta

    val (case_branches, lthy5) = mk_Frees "f" case_arg_typs lthy4
    val prodTa = HOLogic.mk_prodT (typ, Ta)
    fun mk_case_list [] = @{Const\<open>Nil prodTa\<close>}
      | mk_case_list ((c, f) :: cfs) = @{Const\<open>Cons prodTa for \<open>HOLogic.mk_prod (c, f)\<close> \<open>mk_case_list cfs\<close>\<close>}

    (* the_map_of [(C1, f0), ..., (Cn, fn)] x *)
    val case_body = @{Const\<open>the_map_of typ Ta for \<open>mk_case_list (constr_terms ~~ case_branches)\<close> x_ind\<close>}
    val case_tm = fold_rev lambda case_branches (lambda x_ind case_body)

    val case_binding = Binding.qualify true typ_name (Binding.name "case")
    val case_def_binding = Binding.qualify true typ_name (Binding.name "case_def")

    val ((case_const, (_, case_def)), lthy6) = lthy5
      |> Local_Theory.define ((case_binding, NoSyn),
                              ((case_def_binding, []), case_tm))
    val phi = Local_Theory.target_morphism lthy6
    val case_const = Morphism.term phi case_const
    val case_const = Const (dest_Const_name case_const, case_typ)
    val case_def = Morphism.thm phi case_def

    (* Register with Case_Translation *)
    val lthy7 = lthy6
      |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
           (fn _ => Case_Translation.register case_const constr_terms)
    val timer = time (timer "Case expression")

    (* Step 5: Prove distinct theorems *)
    fun mk_distinct_thm idx =
      if idx = 0 then []
      else let
        val lower = 0 upto idx - 1
        val t = nth constr_terms idx
        val tdef = nth constr_defs idx
        fun pf j =
          let
            val t' = nth constr_terms j
            val neq = HOLogic.mk_eq (t, t') |> HOLogic.mk_not |> HOLogic.mk_Trueprop
            val t'def = nth constr_defs j
          in
            fn () => trace_prove lthy7 [] [] neq
              (fn {context, ...} => simp_tac (only_simpset context [Abs_inject, tdef, t'def, @{thm lessThan_iff}]) 1)
          end
      in
        map pf lower
      end
    val distinct_thms = maps mk_distinct_thm (1 upto n - 1) |> do_the_works lthy7
    val cases_binding = Binding.qualify true typ_name (Binding.name "distinct")
    val ((_, _), lthy8) = lthy7
      |> Local_Theory.note ((cases_binding, @{attributes [simp]}), distinct_thms)
    val timer = time (timer "Distinct")

    (* Step 6: Prove case equality theorems *)
    val case_eq_simp_thms = @{thms the_map_of_Cons_eq the_map_of_Cons_neq simp_thms} @ case_def :: distinct_thms
    fun mk_case_eq_thm (idx, c_term) =
      let
        val lhs = list_comb (case_const, case_branches @ [c_term])
        val fi = nth case_branches idx
        val eq = HOLogic.mk_eq (lhs, fi)
        val goal = fold_rev Logic.all case_branches (HOLogic.mk_Trueprop eq)
        val vars = Variable.add_free_names lthy8 goal []
      in
        fn () => trace_prove lthy8 vars [] goal
          (fn {context, ...} =>
            simp_tac (only_simpset context case_eq_simp_thms) 1 |> time_tactic "case simp" lthy8)
      end

    val case_eq_thms = 0 upto n - 1 ~~ constr_terms |> map mk_case_eq_thm |> do_the_works lthy8

    val cases_binding = Binding.qualify true typ_name (Binding.name "cases")
    val ((_, _), lthy9) = lthy8
      |> Local_Theory.note ((cases_binding, @{attributes [simp]}), case_eq_thms)
    val timer = time (timer "Case Equalities")

    (* Step 7: Prove exhaustiveness theorem *)
    val P = lthy9 |> Variable.variant_fixes ["P"] |> fst |> the_single |> (fn P => Free (P, HOLogic.boolT)) |> HOLogic.mk_Trueprop
    fun exhaust_case ctor =
      let
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (x_ind, ctor))
      in
        Logic.mk_implies (eq, P)
      end
    val premises = map exhaust_case constr_terms
    val goal = Logic.list_implies (premises, P)
    val vars = Variable.add_free_names lthy9 goal []
    val constr_names = map Binding.name_of constrs
    val (exhaust_thm, lthy10) = add_and_prove_exhaust lthy9 typ_name vars x_ind goal induct_thm constr_names
    val timer = time (timer "Exhaustiveness")

    (* Step 8: Prove split theorems *)
    (* P (case x of C1 => f1 | ... | Cn => fn) = ((x = C1 --> P f1) & ... & (x = Cn --> P fn)) *)

    val P_var = lthy10 |> yield_singleton (mk_Frees "P") (Ta --> HOLogic.boolT) |> fst

    val case_expr = list_comb (case_const, case_branches @ [x_ind])
    val lhs = P_var $ case_expr

    fun mk_split_clause (ctor, branch) =
      let
        val eq = HOLogic.mk_eq (x_ind, ctor)
        val consequent = P_var $ branch
      in
        HOLogic.mk_imp (eq, consequent)
      end

    val rhs_clauses = map mk_split_clause (constr_terms ~~ case_branches)
    val rhs = foldr1 HOLogic.mk_conj rhs_clauses

    val split_prop = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
    val split_vars = Variable.add_free_names lthy10 split_prop []

    val x_varc = Thm.cterm_of lthy10 x_ind
    val split_thm = trace_prove lthy10 split_vars [] split_prop
      (fn {context, ...} =>
        solve_split_tac context x_varc case_eq_thms exhaust_thm)

    fun mk_split_clause' (ctor, branch) =
      let
        val eq = HOLogic.mk_eq (x_ind, ctor)
        val consequent = P_var $ branch |> HOLogic.mk_not
      in
        HOLogic.mk_conj (eq, consequent)
      end

    val rhs_clauses' = map mk_split_clause' (constr_terms ~~ case_branches)
    val rhs' = foldr1 HOLogic.mk_disj rhs_clauses' |> HOLogic.mk_not
    val split_asm_prop = HOLogic.mk_eq (lhs, rhs') |> HOLogic.mk_Trueprop
    val split_asm_thm = trace_prove lthy10 split_vars [] split_asm_prop
      (fn {context, ...} => solve_split_asm_tac context split_thm)

    val split_binding = Binding.qualify true typ_name (Binding.name "split")
    val split_asm_binding = Binding.qualify true typ_name (Binding.name "split_asm")
    val splits_binding = Binding.qualify true typ_name (Binding.name "splits")
    val lthy11 = lthy10
      |> Local_Theory.note ((split_binding, []), [split_thm])
      |> snd
      |> Local_Theory.note ((split_asm_binding, []), [split_asm_thm])
      |> snd
      |> Local_Theory.note ((splits_binding, []), [split_thm, split_asm_thm])
      |> snd
    val _ = timer "Split Theorem"

    val lthy12 = lthy11
      |> add_and_prove_is_enum typ_name
      |> Local_Theory.background_theory
           (add_equal_instance typ constr_terms (replicate n [])
              case_eq_thms [])

  in
    lthy12
  end

fun enum_cmd (typ_binding, constrs) lthy =
  let
    val time = timer lthy
    val timer = time (Timing.start ())
    
    val lthy' = if List.all (null o snd) constrs
      then enum_cmd_simpl (typ_binding, map fst constrs) lthy
      else enum_cmd_complex (typ_binding, constrs) lthy

    val _ = timer "Enum Complete"
  in
    lthy'
  end
end

(* Register the command *)
val _ =
  Outer_Syntax.local_theory @{command_keyword enum} "define enumeration type with proven theorems"
    (Parse.binding --
      (Parse.$$$ "=" |-- Parse.enum1 "|" (Parse.binding -- Scan.repeat Parse.typ))
     >> Enum_Cmd.enum_cmd)