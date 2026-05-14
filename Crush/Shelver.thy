theory Shelver
  imports Main
  keywords "schematic_have" :: prf_goal % "proof"
    and "schematic_show" :: prf_goal % "proof"
    and "show_goal" :: prf_goal % "proof"
    and "unshelve" :: prf_goal % "proof"
    and "setup_shelving" :: prf_block % "proof"
    and "begin_proof" :: prf_goal % "proof"
begin

text \<open>
  Proof shelving infrastructure for Isabelle/Isar.

  This theory provides a mechanism for deferring proof obligations to the end
  of a proof, similar to Rocq's @{text shelve}/@{text unshelve} tactics.

  The main user-facing commands are:
    \<^item> @{command setup_shelving} — opens a proof block with shelving infrastructure.
    \<^item> @{command begin_proof} — enters the main proof body (apply-style).
    \<^item> The @{text shelve} method — defers the current subgoal as a shelved obligation.
    \<^item> @{command unshelve} — after the main proof, presents all shelved obligations
      as concrete structured subgoals with a clickable proof skeleton.

  Additional utility commands:
    \<^item> @{command schematic_have}/@{command schematic_show} — like @{command have}/@{command show}
      but allow schematic variables in the goal statement.
    \<^item> @{command show_goal} — shows the first pending subgoal with all schematic
      instantiations applied.

  Internally, shelved goals are accumulated in a right-nested chain using
  @{text OPAQUE_SHELVE} and @{text SHELVE_CONJ}, both opaque to the simplifier.
  At @{command unshelve} time, the trailing schematic is instantiated to @{term True}
  and the chain is decomposed into individual subgoals.
\<close>

text \<open>Schematic variants of @{command have}/@{command show} that allow unbound
  schematic variables in goal statements. Implemented by setting
  @{ML Proof_Context.mode_schematic} before delegating to the standard commands.\<close>
ML \<open>
fun set_schematic_mode state =
  Proof.map_context (Proof_Context.set_mode Proof_Context.mode_schematic) state;
\<close>

ML \<open>
structure Shelve_Data = Proof_Data
(
  type T = term list option
  fun init _ = NONE
);
\<close>

ML \<open>
local

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes
    >> (fn ((shows, (strict, assumes)), fixes) => (strict, fixes, assumes, shows));

val _ =
  Outer_Syntax.command @{command_keyword "schematic_have"} "schematic local goal"
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int =>
        set_schematic_mode #> Proof.have_cmd a NONE (K I) b c d int #> #2)));

val _ =
  Outer_Syntax.command @{command_keyword "schematic_show"} "schematic local goal, to refine pending subgoals"
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int =>
        set_schematic_mode #> Proof.show_cmd a NONE (K I) b c d int #> #2)));

fun show_goal_cmd int state =
  let
    val {goal, ...} = Proof.raw_goal state;
    val subgoal = Thm.prems_of goal |> hd;
    val shows = [(Binding.empty_atts, [(subgoal, [])])];
  in
    state
    |> set_schematic_mode
    |> Proof.show true NONE (K I) [] [] shows int
    |> #2
  end;

(* this is useful if you don't want to spell out the precise next goal, and just transition to
the proof state where you now have to prove that goal *)
val _ =
  Outer_Syntax.command @{command_keyword "show_goal"}
    "show the first pending subgoal (with instantiations applied)"
    (Scan.succeed (Toplevel.proof' show_goal_cmd));
in end
\<close>


text \<open>Shelving definitions and lemmas. @{text OPAQUE_SHELVE} wraps the accumulated
  shelved conjunction; @{text SHELVE_CONJ} is a private conjunction that the simplifier
  cannot decompose (protected by congruence rules).\<close>

definition OPAQUE_SHELVE :: \<open>bool \<Rightarrow> bool\<close> where
  \<open>OPAQUE_SHELVE p \<equiv> p\<close>

definition SHELVE_CONJ :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>SHELVE_CONJ p q \<equiv> p \<and> q\<close>

lemma OPAQUE_SHELVE_cong[cong]: \<open>OPAQUE_SHELVE p = OPAQUE_SHELVE p\<close> by simp
lemma SHELVE_CONJ_cong[cong]: \<open>SHELVE_CONJ p q = SHELVE_CONJ p q\<close> by simp

text \<open>Print translation: @{text "OPAQUE_SHELVE ..."} displays as @{text SHELVED}
  regardless of the accumulated conjunction inside.\<close>


syntax "_SHELVED" :: \<open>bool\<close> (\<open>SHELVED\<close>)

typed_print_translation \<open>
  [(@{const_syntax OPAQUE_SHELVE}, fn _ => fn _ => fn _ =>
    Syntax.const @{syntax_const "_SHELVED"})]
\<close>

text \<open>Infrastructure lemmas for the shelving mechanism.\<close>

lemma cut_shelve:
  assumes \<open>OPAQUE_SHELVE shelve \<Longrightarrow> P\<close>
      and \<open>shelve\<close>
  shows \<open>P\<close>
  using assms unfolding OPAQUE_SHELVE_def by force

text\<open>Used to instantiate the shelf with the current goal. The instantiation will keep open a
remaining shelf so multiple subgoals can be shelved.\<close>
lemma FROM_SHELVE:
  assumes \<open>OPAQUE_SHELVE (SHELVE_CONJ P shelve)\<close>
  shows \<open>P\<close>
  using assms unfolding OPAQUE_SHELVE_def SHELVE_CONJ_def by simp

text\<open>Introduction rule used when proving the shelved subgoals\<close>
lemma SHELVE_CONJ_I:
  assumes \<open>P\<close> \<open>Q\<close>
  shows \<open>SHELVE_CONJ P Q\<close>
  using assms unfolding SHELVE_CONJ_def by simp

text\<open>When the shelve has been used (at least) once, we cannot directly use @{thm FROM_SHELVE}
to instantiate the remaining shelved goals. Instead, we use this rule to float the tail to the
top.\<close>
lemma SHELVE_ROTATE:
  assumes \<open>OPAQUE_SHELVE (SHELVE_CONJ P shelve)\<close>
      and \<open>OPAQUE_SHELVE shelve \<Longrightarrow> Q\<close>
    shows \<open>Q\<close>
  using assms unfolding OPAQUE_SHELVE_def SHELVE_CONJ_def by simp

text\<open>We add private copies of quantification, so we can ensure existing quantifications are not 
messed with\<close>
definition SHELVE_ALL :: \<open>('p \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>S\<forall>\<close> 10) where
  \<open>SHELVE_ALL \<equiv> All\<close>
lemma SHELVE_ALL_I:
  assumes \<open>\<And> x. P x\<close>
  shows \<open>S\<forall>x. P x\<close>
  using assms by (auto simp add: SHELVE_ALL_def)
lemma SHELVE_ALL_spec:
  assumes \<open>SHELVE_ALL P\<close>
  shows \<open>P x\<close>
  using assms by (auto simp add: SHELVE_ALL_def)

text\<open>Similarly for implication\<close>
definition SHELVE_IMP :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>SHELVE_IMP P Q \<equiv> P \<longrightarrow> Q\<close>
lemma SHELVE_IMP_I:
  assumes \<open>P \<Longrightarrow> Q\<close>
  shows \<open>SHELVE_IMP P Q\<close>
  using assms by (simp add: SHELVE_IMP_def)
lemma SHELVE_IMP_rev_mp:
  assumes \<open>P\<close>
      and \<open>SHELVE_IMP P Q\<close>
    shows \<open>Q\<close>
  using assms by (simp add: SHELVE_IMP_def)

text \<open>The @{text shelve} method: defers the current subgoal by consing it onto the
  shelved conjunction chain via @{thm FROM_SHELVE}. Uses @{thm SHELVE_ROTATE} to
  skip past already-shelved obligations.\<close>

ML_file "shelver.ML"

method_setup shelve =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Shelver.shelve_tac ctxt))\<close>
  \<open>shelve the current goal for later proof\<close>
text \<open>Commands: @{command unshelve}, @{command setup_shelving}, @{command begin_proof}.\<close>

ML \<open>
local

(* instantiate the last schematic with just @{term True} *)
fun instantiate_shelve_tail ctxt goal =
  let
    val subgoal = Thm.prems_of goal |> hd;
    val body = HOLogic.dest_Trueprop (Logic.strip_assums_concl subgoal);
    val conjuncts = Shelver.decompose_shelve_conj body;
    val (_, tail) = split_last conjuncts;
  in
    case tail of
      Var v => Thm.instantiate (TVars.empty,
        Vars.make [(v, Thm.cterm_of ctxt @{term True})]) goal
    | _ => raise TERM ("instantiate_shelve_tail: expected trailing schematic", [tail])
  end;

fun first_and keyword f items =
  map_index (fn (i, x) =>
    (if i = 0 then keyword else "    and") ^ " " ^ f x) items;

(* produces a suggested proof skeleton for proving state, if any open subgoals remain *)
fun unshelve_skeleton_post state =
  let
    val ctxt = Proof.context_of state

    fun subgoal_skeleton sg =
      let
        val params = Logic.strip_params sg;
        val param_frees = rev (map Free params);
        fun subst t = fold (fn f => fn t => Term.subst_bound (f, t)) param_frees t;

        val fixes = first_and "  fix"
          (fn (x, T) => x ^ " :: \<open>" ^ Syntax.string_of_typ ctxt T ^ "\<close>") params;

        val assums = Logic.strip_assums_hyp sg;
        val assums' = map subst assums;
        val assumes = first_and "  assume"
          (fn p => "\<open>" ^ Syntax.string_of_term ctxt (HOLogic.dest_Trueprop p) ^ "\<close>") assums';

        val concl = Logic.strip_assums_concl sg;
        val concl' = subst concl;
        val concl_str = Syntax.string_of_term ctxt (HOLogic.dest_Trueprop concl');

      in cat_lines (fixes @ assumes @ ["  show \<open>" ^ concl_str ^ "\<close>", "    sorry"]) end;

    val {goal, ...} = Proof.raw_goal state;
    val subgoals = Thm.prems_of goal;
  in
    if null subgoals then NONE
    else SOME (String.concatWith "\nnext\n" (map subgoal_skeleton subgoals))
  end;

(* in state mode, instantiate the shelved tail with True *)
fun close_shelve_tail state =
  state
  |> Proof.enter_backward
  |> Proof.refine_primitive (fn ctxt => instantiate_shelve_tail ctxt)
  |> Proof.enter_forward;

fun unfold_prems_tac ctxt =
  (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms SHELVE_ALL_I}))
  THEN' (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms SHELVE_IMP_I}));

(* Take apart the conjunction of (folded) implications/quantifications into regular goals *)
fun decompose_shelved_goals int state =
  let
    val {goal, ...} = Proof.raw_goal state;
    val subgoal = Thm.prems_of goal |> hd;
    val body = HOLogic.dest_Trueprop (Logic.strip_assums_concl subgoal);
    val goal_prop = HOLogic.mk_Trueprop body;
    val shows = [(Binding.empty_atts, [(goal_prop, [])])];
    val decompose_method = Method.Basic (fn ctxt => SIMPLE_METHOD (
      ALLGOALS (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms SHELVE_CONJ_I}))
      THEN ALLGOALS (TRY o resolve_tac ctxt @{thms TrueI})
      THEN ALLGOALS (unfold_prems_tac ctxt)));
  in
    state
    |> set_schematic_mode
    |> Proof.show true NONE (K I) [] [] shows int
    |> #2
    |> Proof.proof (SOME (decompose_method, Position.no_range))
    |> Seq.the_result ""
  end;

(* In a proof state, output a clickable proof skeleton to show the remaining goals *)
fun emit_unshelve_skeleton state =
  let val _ =
    case unshelve_skeleton_post state of
      NONE => Output.information "No shelved goals: complete proof with qed"
    | SOME s => Output.information
        ("Suggested proof skeleton:\n" ^ Active.sendback_markup_command s)
  in state end;

(* Unshelve: close the shelved tail, decompose the shelved goals, then output a clickable proof
skeleton for proving those goals *)
fun unshelve_cmd int state =
  state
  |> close_shelve_tail
  |> decompose_shelved_goals int
  |> emit_unshelve_skeleton;

val _ =
  Outer_Syntax.command @{command_keyword "unshelve"}
    "show shelved goals with concrete proof skeleton"
    (Scan.succeed (Toplevel.proof' unshelve_cmd));

(* Note: uses Logic.strip_params instead of Term.strip_all_vars.
The former does HHF normalization, and so can spot meta quantification deeper in the
goal. *)
fun has_meta_params st =
  not (null (Logic.strip_params (Thm.prems_of st |> hd)))
  handle List.Empty => false;

val shelving_skeleton =
  "  begin_proof\n" ^
  "    sorry\n" ^
  "  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>\n" ^
  "  qed\n" ^
  "qed";

fun suggest_subgoal_for ctxt st =
  let
    val subgoal = Thm.prems_of st |> hd;
    val param_names = Logic.strip_params subgoal
      |> Syntax_Trans.variant_bounds ctxt subgoal
      |> map #1;
    val for_clause = String.concatWith " " param_names;
  in
    "apply (rule asm_rl) \<comment>\<open>May be necessary to force HHF, moving meta-quantification to the front\<close>\n" ^
    "subgoal for " ^ for_clause ^ "\n" ^
    "setup_shelving\n" ^
    shelving_skeleton ^ "\n" ^
    "done"
  end;

(* Store the current premises as an assumption under name prems_binding.
Also stores them in Shelve_Data, so these premises will not be folded into 
shelved goals as hypotheses. *)
fun store_known_premises prems_binding state =
  case prems_binding of
    NONE => state
  | SOME prem_name =>
    let
      val {goal, ...} = Proof.raw_goal state;
      val subgoal = Thm.prems_of goal |> hd;
      val ctxt = Proof.context_of state;
      val prems = Logic.strip_imp_prems subgoal;
      val non_shelve_prems = filter_out Shelver.is_shelve_prem prems;
      val non_shelve_cprems = map (Thm.cterm_of ctxt) non_shelve_prems;
      val _ = (if null non_shelve_prems then
        Output.warning "Did not bind any premises to a name, no premises found?"
      else ())
    in
      state
      |> Proof.map_context (fn ctxt' =>
          let
            val (prem_thms, ctxt'') =
              Assumption.add_assumes non_shelve_cprems ctxt';
          in
            ctxt''
            |> Shelve_Data.put (SOME non_shelve_prems)
            |> Proof_Context.note_thmss ""
                [((Binding.name prem_name, []), [(prem_thms, [])])]
            |> snd
          end)
    end;

(* Applies @{thm cut_shelve}, and makes you \<^verbatim>\<open>show\<close> both premises. Also suggests
a clickable proof skeleton. *)
fun setup_shelving_core state =
  let
    val {goal = st, ...} = Proof.raw_goal state;

    fun setup_tactic ctxt =
      if has_meta_params st then
        let
          val suggestion = suggest_subgoal_for ctxt st;
          val id_props = Position.properties_of (Position.thread_data ());
          val _ = Output.warning
            ("Warning: Shelving under bound variables makes proofs less legible.\n" ^ 
             "You might want to turn your meta bound variables into skolem variables with:\n" ^
              Active.sendback_markup_properties id_props suggestion);
        in
          Goal.norm_hhf_tac ctxt
          THEN' Shelver.fold_prems_tac ctxt
          THEN' resolve_tac ctxt @{thms cut_shelve}
          THEN' unfold_prems_tac ctxt
        end
      else
        resolve_tac ctxt @{thms cut_shelve};

    val setup_method = Method.Basic (fn ctxt =>
      SIMPLE_METHOD (setup_tactic ctxt 1)
    );

    val _ = Output.information
      ("Proof skeleton:\n" ^ Active.sendback_markup_command shelving_skeleton);
  in
    state
    |> Proof.proof (SOME (setup_method, Position.no_range))
    |> Seq.the_result ""
  end;

fun shelving_proof_cmd prems_binding _ state =
  state
  |> setup_shelving_core
  |> store_known_premises prems_binding;

val _ =
  Outer_Syntax.command @{command_keyword "setup_shelving"}
    "open proof with shelving infrastructure"
    (Scan.optional (Parse.$$$ "premises" |-- Parse.name >> SOME) NONE
      >> (fn prems => Toplevel.proof' (shelving_proof_cmd prems)));

fun enter_proof_cmd int state =
  let
    val {goal, ...} = Proof.raw_goal state;
    val subgoal = Thm.prems_of goal |> hd;
    val shows = [(Binding.empty_atts, [(subgoal, [])])];
  in
    state
    |> set_schematic_mode
    |> Proof.show true NONE (K I) [] [] shows int
    |> #2
  end;

val _ =
  Outer_Syntax.command @{command_keyword "begin_proof"}
    "enter the main proof body after setup_shelving"
    (Scan.succeed (Toplevel.proof' enter_proof_cmd));

in end
\<close>


text \<open>Examples demonstrating the shelving mechanism.\<close>

experiment
  assumes PIGSFLY : False
begin

lemma SORRY:
  shows \<open>P\<close>
  using PIGSFLY by simp

method_setup admit =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (resolve_tac ctxt @{thms SORRY}))\<close>


text \<open>Schematic variable witness discovery via unification.\<close>
lemma
  assumes "P a" "Q a"
  shows "\<exists>x. P x \<and> Q x"
proof (intro exI conjI)
  schematic_show "P ?y"
    by (fact assms(1))
  schematic_show "Q ?y"
    by (fact assms(2))
qed

text \<open>Manual shelving with explicit @{text OPAQUE_SHELVE} management.\<close>
lemma exist_even_div_4:
  shows \<open>\<exists> n :: nat. even n \<and> n mod 4 = 0 \<and> n mod 7 = 0\<close>
proof (rule cut_shelve)
  schematic_show \<open>OPAQUE_SHELVE ?shelve \<Longrightarrow> (\<exists>n. even n \<and> n mod 4 = 0 \<and> n mod 7 = 0)\<close>
    apply (rule exI[of _ 2], simp, intro conjI)
     apply shelve
    apply shelve
    done
  unshelve
    show \<open>2 mod 4 = 0\<close>
      by admit
  next
    show \<open>2 mod 7 = 0\<close> 
      by admit
  qed
qed

text \<open>Using @{command setup_shelving} to hide the shelving boilerplate.\<close>
lemma exist_even_div_4_shorter:
  shows \<open>\<exists> n :: nat. even n \<and> n mod 4 = 0 \<and> n mod 7 = 0 \<and> n mod 13 = 0\<close>
proof -
  have fact1: \<open>2 mod 4 = 0\<close>
    by admit
  have fact2: \<open>2 mod 7 = 0\<close>
    by admit
  show ?thesis
  setup_shelving
    begin_proof
      apply (rule exI[of _ 2])
      apply (simp only: even_numeral simp_thms, intro conjI)
      apply shelve
      apply shelve
      apply shelve
      done
    unshelve
      from fact1 show \<open>2 mod 4 = 0\<close> by simp
    next
      from fact2 show \<open>2 mod 7 = 0\<close> by simp
    next
      show \<open>2 mod 13 = 0\<close> by admit
    qed
  qed
qed

text \<open>Empty shelving: no obligations deferred.\<close>
lemma exist_even_div_4_shorter_empty:
  shows \<open>\<exists> n :: nat. even n \<and> n mod 4 = 0 \<and> n mod 7 = 0\<close>
setup_shelving
  begin_proof
    by admit
  unshelve
  qed
qed

text \<open>Shelving when the target contains meta-implications\<close>
lemma test_impl_conj:
  shows \<open>D \<Longrightarrow> A \<longrightarrow> (E \<longrightarrow> B) \<and> (F \<longrightarrow> C)\<close>
setup_shelving premises prems
  begin_proof
    apply (intro conjI impI)
    using exist_even_div_4_shorter_empty
    apply shelve
    apply shelve
    done
  unshelve
    assume \<open>A\<close>
      and \<open>E\<close>
      and \<open>\<exists>n. even n \<and> n mod 4 = 0 \<and> n mod 7 = 0\<close>
    show \<open>B\<close>
      by admit
  next
    assume \<open>A\<close>
      and \<open>F\<close>
    show \<open>C\<close>
      by admit
  qed
qed

lemma test_impl_conj2:
  shows \<open>H \<Longrightarrow> (E \<longrightarrow> B) \<and> (F \<longrightarrow> (\<forall> y :: bool. D y \<longrightarrow> C y))\<close>
setup_shelving premises prems
  begin_proof
    apply (intro conjI strip)
     apply shelve
    apply shelve
    done
  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
    assume \<open>E\<close>
    show \<open>B\<close>
      by admit
  next
    fix y :: \<open>bool\<close>
    assume \<open>F\<close>
    show \<open>C y\<close>
      by admit
  qed
qed

text\<open>now lets try quantified variables\<close>
lemma test_impl_quant:
  shows \<open>E \<Longrightarrow> (\<forall> x :: nat. C x \<longrightarrow> D x)\<close>
setup_shelving premises prems
  begin_proof
    apply (intro strip)
    apply shelve
    done
  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
    fix x :: \<open>nat\<close>
    assume \<open>C x\<close>
    show \<open>D x\<close>
      by admit
  qed
qed

lemma test_quant_binder_names:
  shows \<open>(\<forall> y. P y) \<and> (\<forall> x. P x)\<close>
setup_shelving
  begin_proof
    apply (intro conjI strip)
     apply shelve
    apply shelve
    done
  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
    \<comment>\<open>Quirk: names are lost in this case because of eta-reduction\<close>
    fix x :: \<open>'a\<close>
    show \<open>P x\<close>
      by admit
  next
    fix x :: \<open>'a\<close>
    show \<open>P x\<close>
      by admit
  qed
qed

lemma test_multi_quant:
  shows \<open>\<forall> x y. C x \<longrightarrow> D y \<longrightarrow> E x y\<close>
setup_shelving
  begin_proof
    apply (intro strip)
    apply shelve
    done
  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
    fix x :: \<open>'a\<close>
      and y :: \<open>'b\<close>
    assume \<open>C x\<close>
      and \<open>D y\<close>
    show \<open>E x y\<close>
      by admit
  qed
qed

lemma test_multi_quant_imp_keep_structure:
  shows \<open>\<forall> x y. C x y \<longrightarrow> (\<forall> z. D z \<longrightarrow> E x y z)\<close>
setup_shelving
  begin_proof
    apply (intro allI)
    apply (intro impI)
    apply shelve
    done
  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
    fix x :: \<open>'a\<close>
      and y :: \<open>'b\<close>
    assume \<open>C x y\<close>
    show \<open>\<forall>z. D z \<longrightarrow> E x y z\<close>
      by admit
  qed
qed

lemma test_known_multi_quant:
  shows \<open>\<And> x. P x \<Longrightarrow> (\<forall> y z. C x \<longrightarrow> D y \<longrightarrow> E x y) \<and> (\<forall> nameless. F nameless) \<and> (\<forall> name. True \<longrightarrow> F name)\<close>
  apply (rule asm_rl)
  subgoal for x
  setup_shelving premises prems
    begin_proof
      apply (intro strip conjI)
       apply shelve
       apply shelve
      apply shelve
      done
    unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
      fix y :: \<open>'b\<close>
        and z :: \<open>'c\<close>
      assume \<open>C x\<close>
        and \<open>D y\<close>
      show \<open>E x y\<close>
        by admit
    next
      fix x :: \<open>'d\<close>
      show \<open>F x\<close>
        by admit
    next
      fix name :: \<open>'d\<close>
      show \<open>F name\<close>
        by admit
    qed
  qed
  done

lemma test_meta_quant_not_in_head_ignore:
  shows \<open>P \<Longrightarrow> (\<And> x. G x \<Longrightarrow> H x)\<close>
\<comment> \<open>Intentionally shows a warning\<close>
setup_shelving
  begin_proof
    apply shelve
    done
  unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
    fix x :: \<open>'a\<close>
    assume \<open>P\<close>
      and \<open>G x\<close>
    show \<open>H x\<close>
      by admit
  qed
qed

lemma test_meta_quant_not_in_head_follow:
  shows \<open>P \<Longrightarrow> (\<And> x. G x \<Longrightarrow> H x)\<close>
  apply (rule asm_rl) \<comment>\<open>May be necessary to force HHF, moving meta-quantification to the front\<close>
  subgoal for x
  setup_shelving premises prems
    begin_proof
      apply shelve
      done
    unshelve \<comment> \<open>Navigate here for a suggested proof script to resolve shelved obligations\<close>
      from prems show \<open>H x\<close>
        by admit
    qed
  qed
  done

end

end
