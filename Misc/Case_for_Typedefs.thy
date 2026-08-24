(*<*)
theory Case_for_Typedefs
  imports
    Word_Lib.Typedef_Morphisms
    Num_Case_Expression
  keywords "setup_case_for_typedef" :: thy_decl and "variants_thm" and "distinct_thm"
begin
(*>*)

definition find_index_offset :: \<open>'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat\<close> where
  \<open>find_index_offset vs offset v \<equiv> (fst \<circ> the) (List.find (\<lambda> (_, r). r = v) (indexed_from offset vs))\<close>

lemma find_index_offset_fst[simp]:
  shows \<open>find_index_offset (a # vs) n a = n\<close>
  by (simp add: find_index_offset_def)

lemma find_index_offset_not_fst:
  assumes \<open>a \<noteq> b\<close>
      and \<open>b \<in> set vs\<close>
  shows \<open>find_index_offset (a # vs) n b = find_index_offset vs (Suc n) b\<close>
  using assms
proof (induction vs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons c vs)
  then show ?case
    by (simp add: find_index_offset_def)
qed

lemma in_set_indexed_from_in_set:
  assumes \<open>v \<in> set (indexed_from n vs)\<close>
  shows \<open>snd v \<in> set vs\<close>
  using assms
  by (metis list.map(2) map_snd_indexed_from not_Cons_self remdups.simps(2) remdups_map_remdups)

lemma find_index_offset_eqs:
  assumes \<open>distinct vs\<close>
  shows \<open>list_all (\<lambda> (i, v). find_index_offset vs n v = i) (indexed_from n vs)\<close>
  using assms
proof (induction vs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a vs)
  moreover from calculation have 
    \<open>list_all (\<lambda>(i, v). find_index_offset vs (Suc n) v = i) (indexed_from (Suc n) vs)\<close>
    by simp
  with \<open>distinct (a # vs)\<close> show ?case
    apply simp
    apply (erule list.pred_mono_strong)
    by (force intro!: find_index_offset_not_fst dest!: in_set_indexed_from_in_set
        split: prod.splits)
qed

lemma find_index_offset_eqs_nth:
  assumes \<open>distinct vs\<close>
      and \<open>k < length vs\<close>
    shows \<open>find_index_offset vs n (vs ! k) = n + k\<close>
proof -
  note find_index_offset_eqs[OF assms(1), simplified list_all_length length_indexed_from, where n=n,
      THEN spec, THEN mp, OF assms(2)]
  with assms(2) show ?thesis
    by (simp add: nth_indexed_from_eq)
qed

definition find_index :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat\<close> where
  \<open>find_index vs v \<equiv> find_index_offset vs 0 v\<close>

lemma find_index_eqs:
  assumes \<open>distinct vs\<close>
  shows \<open>list_all (\<lambda> (i, v). find_index vs v = i) (indexed_from 0 vs)\<close>
  using find_index_offset_eqs[OF assms]
  by (simp add: find_index_def)


ML \<open>
signature CASE_FOR_TYPEDEF =
sig
  (* \<^verbatim>\<open>verbose\<close> controls whether a summary of the generated items is written out;
     a command that composes this setup into a larger one reports for itself instead. *)
  type config = { verbose: bool }
  val default_config: config

  (* The items generated for a type with the given name and number of constructors,
     one line each, for reporting. *)
  val generated_summary: string -> int -> string list

  (* What the setup generated, for a caller composing it into a larger command: the
     \<^verbatim>\<open>case_TYPE\<close> constant plus the rewrite chain that reduces it on a concrete variant
     (\<^verbatim>\<open>case_def\<close>, then \<^verbatim>\<open>match_def\<close>, then one of \<^verbatim>\<open>indices\<close>) --- the same chain the registered
     simproc applies. Handing these back avoids resolving them by name, which does not work
     from a context whose naming differs from the declaration's. *)
  type case_result = { case_const: term, case_def: thm, match_def: thm, index_def: thm, indices: thm list }

  (* setup_case_for_typedef config type_name variants_thm distinct_thm *)
  val setup_case_for_typedef: config -> string -> thm -> thm -> local_theory ->
    case_result * local_theory
end

structure Case_For_Typedef : CASE_FOR_TYPEDEF =
struct

type config = { verbose: bool }
val default_config = { verbose = true }

type case_result = { case_const: term, case_def: thm, match_def: thm, index_def: thm, indices: thm list }

(* Naming conventions for generated constants and facts *)
fun index_name type_name = type_name ^ "_index"
fun indices_concrete_name type_name = type_name ^ "_indices_concrete"
fun match_name type_name = "match_" ^ type_name
fun match_def_name type_name = "match_" ^ type_name ^ "_def"
fun case_const_name type_name = "case_" ^ type_name
fun case_def_name type_name = "case_" ^ type_name ^ "_def"
fun simproc_name type_name = type_name ^ "_case_simproc"

fun generated_summary type_name n =
  ["definition  " ^ index_name type_name,
   "fact        " ^ indices_concrete_name type_name ^ " (" ^ string_of_int n ^ " thms)",
   "definition  " ^ match_name type_name,
   "definition  " ^ case_const_name type_name,
   "simproc     " ^ simproc_name type_name ^ " [active]"]

(* Convert a theorem to HOL equality if it is a meta-equality *)
fun to_hol_eq thm = thm RS @{thm meta_eq_to_obj_eq} handle THM _ => thm

(* Extract (variant_list_const, constructors, element_type) from a variants theorem
   of the form "variant_list = [C1, C2, ..., Cn]" *)
fun dest_variants_thm thm =
  let
    val (lhs, rhs) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
        handle TERM _ => Thm.prop_of thm |> Logic.dest_equals
    val elemT = case fastype_of rhs of
        Type (\<^type_name>\<open>list\<close>, [T]) => T
      | T => error ("setup_case_for_typedef: variants theorem RHS is not a list type: " ^
            @{make_string} T)
    val ctrs = HOLogic.dest_list rhs
  in (lhs, ctrs, elemT) end

(* Define a constant in fully-applied form: name args = rhs.
   Returns the constant, its definitional theorem, and the updated context. *)
fun define_applied lthy name_str args rhs =
  let
    val binding = Binding.name name_str
    val fun_type = fold_rev (fn a => fn T => fastype_of a --> T) args (fastype_of rhs)
    val lhs = list_comb (Free (name_str, fun_type), args)
    val spec = Logic.mk_equals (lhs, rhs)
    val ((_, (_, def_thm)), lthy') = Specification.definition {verbose = false}
      (SOME (binding, NONE, NoSyn)) [] []
      ((Binding.name (name_str ^ "_def"), []), spec) lthy
    val full_name = Local_Theory.full_name lthy' binding
    val const = Const (full_name, fun_type)
    (* Transport the definitional theorem to the target, so that its LHS mentions the
       constant under the name it actually has there. Without this it still refers to the
       pre-export Free, and callers outside this function cannot rewrite with it. *)
    val def_thm = Morphism.thm (Local_Theory.target_morphism lthy') def_thm
  in (const, def_thm, lthy') end

(* Step 1: Define TYPE_index x = find_index variant_list x *)
fun define_index lthy type_name elemT variant_list_term =
  let val x_free = Free ("x", elemT)
      val rhs = \<^Const>\<open>find_index elemT\<close> $ variant_list_term $ x_free
  in define_applied lthy (index_name type_name) [x_free] rhs end

(* Simp rules for reducing find_index_eqs into concrete index equalities *)
fun indices_simp_rules variants_hol index_def =
  @{thms indexed_from_simps}
  @ [variants_hol RS @{thm HOL.arg_cong[where f=\<open>indexed_from 0\<close>]}]
  @ @{thms nth_Cons_numeral diff_numeral_Suc pred_numeral_simps
        One_nat_def[symmetric] diff_zero}
  @ @{thms Num.BitM.simps nth_Cons_0 nth_Cons_Suc list_all_Cons_iff prod.simps
        Suc_numeral Suc_1 add_One}
  @ @{thms Num.inc.simps list_all_Nil_iff simp_thms atomize_conj[symmetric]}
  @ [Thm.symmetric index_def]

(* Prove TYPE_index Ci = i for each constructor, returned as a thm list *)
fun generate_indices lthy distinct_thm variants_hol index_def =
  Proof_Context.get_thm lthy "find_index_eqs"
  |> (fn th => th OF [distinct_thm])
  |> Simplifier.simplify (lthy |> Simplifier.clear_simpset
       |> Simplifier.add_simps (indices_simp_rules variants_hol index_def))
  |> Conjunction.elim_conjunctions

(* Step 2: Prove TYPE_indices_concrete and register as a fact *)
fun register_indices lthy type_name distinct_thm variants_thm index_def =
  let
    val variants_hol = to_hol_eq variants_thm
    val indices_thms = generate_indices lthy distinct_thm variants_hol index_def
    val ((_, indices_thms), lthy') = Local_Theory.note
      ((Binding.name (indices_concrete_name type_name), []), indices_thms) lthy
  in (indices_thms, lthy') end

(* Step 3: Define match_TYPE vs x = vs ! TYPE_index x *)
fun define_match lthy type_name elemT index_const =
  let
    val aT = TFree ("'a", \<^sort>\<open>type\<close>)
    val vs_free = Free ("vs", Type (\<^type_name>\<open>list\<close>, [aT]))
    val mx_free = Free ("x", elemT)
    val rhs = \<^Const>\<open>nth aT\<close> $ vs_free $ (index_const $ mx_free)
  in define_applied lthy (match_name type_name) [vs_free, mx_free] rhs end

(* Step 4: Define case_TYPE e0...en x = match_TYPE [e0,...,en] x *)
fun define_case lthy type_name elemT n match_const =
  let
    val aT = TFree ("'a", \<^sort>\<open>type\<close>)
    val vars = List.tabulate (n, fn i => Free ("e" ^ string_of_int i, aT))
    val cx_free = Free ("x", elemT)
    val listT = Type (\<^type_name>\<open>list\<close>, [aT])
    val consT = aT --> listT --> listT
    fun mk_list [] = Const (\<^const_name>\<open>Nil\<close>, listT)
      | mk_list (h :: tl) = Const (\<^const_name>\<open>Cons\<close>, consT) $ h $ mk_list tl
    val rhs = match_const $ mk_list vars $ cx_free
  in define_applied lthy (case_const_name type_name) (vars @ [cx_free]) rhs end

(* Step 5: Register with Case_Translation *)
fun register_case_translation lthy case_const ctrs =
  Local_Theory.declaration {syntax = false, pervasive = true, pos = \<^here>}
    (K (Case_Translation.register case_const ctrs)) lthy

(* Build a simproc spec that reduces case_TYPE ... Ci to [arms] ! i.
   Uses Conv.rewr_conv for each step — no recursive simplifier calls.
   Theorems are looked up by name at invocation time because the simproc is
   defined inside a local_theory where constants appear as Free; after export
   they become Const, so closed-over theorems from definition time would fail
   to match via Conv.rewr_conv. *)
fun mk_case_simproc elemT type_name case_qualified_name n =
  let
    (* Pattern for the simplifier's term net: case_TYPE ?e0 ... ?e(n-1) ?x *)
    val bT = TVar (("'b", 0), \<^sort>\<open>type\<close>)
    val pat_vars = List.tabulate (n, fn i => Var (("e", i), bT))
    val pat_x = Var (("x", 0), elemT)
    val pat_case_type = funpow n (fn T => bT --> T) (elemT --> bT)
    val lhs_pattern = list_comb (Const (case_qualified_name, pat_case_type), pat_vars @ [pat_x])

    (* Fact names for dynamic lookup *)
    val the_case_def_name = case_def_name type_name
    val the_match_def_name = match_def_name type_name
    val the_indices_name = indices_concrete_name type_name
  in
    {passive = false, name = Binding.name (simproc_name type_name),
     kind = Simplifier.Simproc,
     lhss = [lhs_pattern],
     proc = fn _ => fn ctxt => fn ct =>
       let
         (* Guard: only fire when the last argument (the scrutinee) is a
            concrete constructor constant of the right type *)
         val args = snd (strip_comb (Thm.term_of ct))
         val x = List.last args
       in
         (case x of
           Const (_, T) =>
             if T = elemT then
               let
                 val c_def = Proof_Context.get_thm ctxt the_case_def_name
                 val m_def = Proof_Context.get_thm ctxt the_match_def_name
                 val idx_thms = Proof_Context.get_thms ctxt the_indices_name
                 val idx_meta = map (fn th => th RS @{thm eq_reflection}) idx_thms
               in
                 (* Rewrite chain:
                    case_TYPE e0...en Ci
                    --> match_TYPE [e0,...,en] Ci     (by case_def)
                    --> [e0,...,en] ! TYPE_index Ci   (by match_def)
                    --> [e0,...,en] ! k               (by indices_concrete) *)
                 SOME ((Conv.rewr_conv c_def
                   then_conv Conv.rewr_conv m_def
                   then_conv Conv.arg_conv (Conv.rewrs_conv idx_meta)) ct)
               end
             else NONE
         | _ => NONE)
         handle CTERM _ => NONE
       end,
     identifier = []} : (term, Morphism.morphism -> Proof.context -> cterm -> thm option, thm list) Simplifier.simproc_spec
  end

(* Step 6: Register active simproc *)
fun register_simproc lthy elemT type_name case_const n =
  let val case_qualified_name = fst (dest_Const case_const)
      val simproc_spec = mk_case_simproc elemT type_name case_qualified_name n
      val (_, lthy') = Simplifier.define_simproc simproc_spec lthy
  in lthy' end

(* Main implementation of setup_case_for_typedef *)
fun setup_case_for_typedef ({ verbose }: config) type_name variants_thm distinct_thm lthy =
  let
    val (variant_list_term, ctrs, elemT) = dest_variants_thm variants_thm
    val n = length ctrs

    (* define TYPE_index : type => nat *)
    val (index_const, index_def, lthy) =
      define_index lthy type_name elemT variant_list_term
    (* prove TYPE_concrete_indices: - TYPE_index <inhabitants> = <num> *)
    val (indices_thms, lthy) =
      register_indices lthy type_name distinct_thm variants_thm index_def
    (* define match_TYPE : 'a list \<Rightarrow> TYPE \<Rightarrow> 'a *)
    val (match_const, match_def, lthy) =
      define_match lthy type_name elemT index_const
    (* define case_TYPE : ('a =>)^{length TYPE} => TYPE \<Rightarrow> 'a *)
    val (case_const, case_def, lthy) =
      define_case lthy type_name elemT n match_const
    (* register case_TYPE so that it works with [case _ of] syntax *)
    val lthy = register_case_translation lthy case_const ctrs
    (* register the simproc for reducing [case <inhabitant> of _ \<Rightarrow> ]*)
    val lthy = register_simproc lthy elemT type_name case_const n

    val _ = if not verbose then () else
      writeln ("setup_case_for_typedef " ^ type_name ^ " (" ^ string_of_int n ^ " constructors):\n" ^
        cat_lines (map (prefix "  ") (generated_summary type_name n)))
  in ({ case_const = case_const, case_def = case_def, match_def = match_def,
        indices = indices_thms, index_def = index_def }, lthy) end

end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>setup_case_for_typedef\<close>
    "register case combinator for a typedef-style type with enumerated constructors"
    (Parse.name --
      (Parse.$$$ "variants_thm" |-- Parse.$$$ ":" |-- Parse.thm) --
      (Parse.$$$ "distinct_thm" |-- Parse.$$$ ":" |-- Parse.thm) >>
      (fn ((type_name, variants_ref), distinct_ref) => fn lthy =>
        snd (Case_For_Typedef.setup_case_for_typedef Case_For_Typedef.default_config type_name
          (hd (Attrib.eval_thms lthy [variants_ref]))
          (hd (Attrib.eval_thms lthy [distinct_ref])) lthy)))
\<close>



subsection\<open>Theory\<close>
text\<open>The following lemmas develop the \<^term>\<open>find_index\<close> theory a bit further. It culminates
with a lemma equating the (unfolded) \<^verbatim>\<open>case\<close> term to \<^term>\<open>ncase_selector\<close>, so we can go between
the two styles of case analysis.\<close>

lemma find_index_offset_bounded_if_in_list:
  assumes \<open>r \<in> set rs\<close>
  shows \<open>find_index_offset rs n r < length rs + n\<close>
  using assms
proof (induction rs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a rs n)
  from Cons(1)[of \<open>Suc n\<close>] Cons(2) show ?case
    by (cases \<open>r = a\<close>, auto simp add: find_index_offset_not_fst)
qed

corollary find_index_bounded_if_in_list:
  assumes \<open>r \<in> set rs\<close>
  shows \<open>find_index rs r < length rs\<close>
  using find_index_offset_bounded_if_in_list[of r rs 0] assms
  by (simp add: find_index_def)

lemma find_index_offset_Suc:
  assumes \<open>r \<in> set rs\<close>
  shows \<open>find_index_offset rs (Suc n) r = Suc (find_index_offset rs n r)\<close>
  using assms
proof (induction rs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
    by (cases \<open>a = r\<close>, auto simp add: find_index_offset_not_fst)
qed

lemma lookup_at_find_index:
  assumes \<open>r \<in> set rs\<close>
  shows \<open>rs ! find_index rs r = r\<close>
  using assms
proof (induction rs arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
    by (cases \<open>a = r\<close>, auto simp add: find_index_def find_index_offset_not_fst find_index_offset_Suc)
qed

lemma lookup_find_index_into_ncase:
  assumes \<open>length vs = length all_cases\<close>
      and \<open>r \<in> set all_cases\<close>
      and \<open>distinct all_cases\<close>
    shows \<open>vs ! find_index all_cases r = ncase_selector (zip (List.map Some all_cases) vs) r\<close>
proof -
  have \<open>find_index all_cases r < length all_cases\<close>
    using find_index_bounded_if_in_list[OF assms(2)] by simp
  with assms have \<open>List.find (\<lambda>(ma, b). case ma of None \<Rightarrow> True | Some a \<Rightarrow> a = r) (zip (list.map Some all_cases) vs)
                  = Some (Some r, vs ! find_index all_cases r)\<close>
    apply (simp add: find_Some_iff)
    apply (rule exI[of _ \<open>find_index all_cases r\<close>])
    using assms(2)
    apply (clarsimp simp add: lookup_at_find_index)
    using assms(3)
    by (metis basic_trans_rules(19) find_index_def find_index_offset_eqs_nth less_irrefl_nat semiring_norm(50))
  then show ?thesis
    by (simp add: ncase_selector_def ncase_selector_raw_def)
qed


experiment
begin
subsection\<open>Tests\<close>

definition cool_numbers_ids :: \<open>nat list\<close> where
  \<open>cool_numbers_ids \<equiv> [
    1337,
    42,
    72,
    0xdeadbeef,
    0xcafe,
    10006660001
  ]\<close>

theorem all_cool_number_ids_distinct:
  shows \<open>distinct cool_numbers_ids\<close>
by (simp add: cool_numbers_ids_def)

typedef cool_number = \<open>set cool_numbers_ids\<close>
  by (auto simp add: cool_numbers_ids_def)
setup_lifting type_definition_cool_number

lift_definition cool_1337 :: \<open>cool_number\<close> is \<open>1337\<close> by (simp add: cool_numbers_ids_def)
lift_definition cool_42 :: \<open>cool_number\<close> is \<open>42\<close> by (simp add: cool_numbers_ids_def)
lift_definition cool_72 :: \<open>cool_number\<close> is \<open>72\<close> by (simp add: cool_numbers_ids_def)
lift_definition cool_deadbeef :: \<open>cool_number\<close> is \<open>0xdeadbeef\<close> by (simp add: cool_numbers_ids_def)
lift_definition cool_cafe :: \<open>cool_number\<close> is \<open>0xcafe\<close> by (simp add: cool_numbers_ids_def)
lift_definition cool_devil_prime :: \<open>cool_number\<close> is \<open>10006660001\<close> by (simp add: cool_numbers_ids_def)

definition all_cool_numbers :: \<open>cool_number list\<close> where
  \<open>all_cool_numbers \<equiv> [cool_1337, cool_42, cool_72, cool_deadbeef, cool_cafe, cool_devil_prime]\<close>

lemma all_cool_numbers_alt:
  shows \<open>all_cool_numbers = List.map Abs_cool_number cool_numbers_ids\<close>
  by (simp add: all_cool_numbers_def cool_numbers_ids_def cool_1337_def
        cool_42_def cool_72_def cool_deadbeef_def cool_cafe_def cool_devil_prime_def)

lemma cool_numbers_total:
  shows \<open>x \<in> set all_cool_numbers\<close>
  apply (rule type_definition.Abs_cases[OF type_definition_cool_number, of x])
  by (force simp add: all_cool_numbers_alt)

lemma all_system_register_ids_distinct:
  shows \<open>distinct all_cool_numbers\<close>
  unfolding all_cool_numbers_alt
  apply (subst distinct_map; simp add: all_cool_number_ids_distinct inj_on_def)
  by (metis (no_types, lifting) type_definition.Abs_eqD type_definition_cool_number)

setup_case_for_typedef "cool_number"
  variants_thm: all_cool_numbers_def
  distinct_thm: all_system_register_ids_distinct

definition is_cool_number_odd :: \<open>cool_number \<Rightarrow> bool\<close> where
  \<open>is_cool_number_odd x \<equiv>
    case x of
      cool_72 \<Rightarrow> True
    | cool_1337 \<Rightarrow> True
    | cool_deadbeef \<Rightarrow> True
    | cool_devil_prime \<Rightarrow> True
    | _ \<Rightarrow> False\<close>

lemma test_cool_proof:
  shows \<open>is_cool_number_odd cool_72\<close> \<open>\<not> is_cool_number_odd cool_42\<close> \<open>is_cool_number_odd cool_deadbeef\<close>
  by (simp_all add: is_cool_number_odd_def)

lemma test_no_early_reduce_variable:
  assumes \<open>(case x of cool_42 \<Rightarrow> False | cool_cafe \<Rightarrow> False | _ \<Rightarrow> True)\<close>
  shows \<open>is_cool_number_odd x\<close>
  apply (simp add: is_cool_number_odd_def)
  by (rule assms)

lemma test_no_early_reduce_non_constant:
  assumes \<open>(case x of cool_42 \<Rightarrow> False | cool_cafe \<Rightarrow> False | _ \<Rightarrow> True)\<close>
  shows \<open>is_cool_number_odd x\<close>
  apply (simp add: is_cool_number_odd_def)
  by (rule assms)

definition \<open>constant_unknown_number \<equiv> cool_cafe\<close>

lemma test_no_early_reduce:
  shows \<open>\<not> is_cool_number_odd constant_unknown_number\<close>
  apply (simp add: is_cool_number_odd_def)
  by (simp add: constant_unknown_number_def)


subsection\<open>Demo how the index itself (for which simplification rules are generated) can be lifted
to a simproc to reduce equalities on concrete variants\<close>
lemma match_cool_number_dist:
  shows \<open>match_cool_number (List.map f all_cool_numbers) n = f n\<close>
  using cool_numbers_total[of n]
  by (auto simp add: all_cool_numbers_def match_cool_number_def cool_number_indices_concrete)

lemma variant_equality_to_index_equality:
  fixes x y :: cool_number
  shows \<open>(x = y) = (cool_number_index x = cool_number_index y)\<close>
proof (rule, goal_cases)
  case 1
  then show ?case by simp
next
  case 2
  note match_cool_number_dist[of \<open>\<lambda> n. n\<close> x, simplified match_cool_number_def 2, simplified match_cool_number_def[symmetric] match_cool_number_dist]
  then show ?case by simp
qed

\<comment>\<open>With this theorem, we can already prove (in)equalities like this quickly with manual simp rules\<close>
lemma test_variant_equality:
  shows \<open>cool_42 \<noteq> cool_cafe\<close>
  by (simp add: cool_number_indices_concrete variant_equality_to_index_equality)

\<comment>\<open>But we can do a bit better, and setup a simproc to do this automatically\<close>
ML\<open>
  fun cool_number_eq_conv (_: Proof.context) : conv =
    (* Simplify equality with variant_equality_to_index_equality *)
    Conv.rewr_conv @{thm variant_equality_to_index_equality[THEN eq_reflection]}
    (* Simplify under LHS and RHS of equality separately *)
    then_conv (@{thms cool_number_indices_concrete[THEN eq_reflection]} |> Conv.rewrs_conv |> Conv.binop_conv)

  fun cool_number_eq_simproc (ctxt: Proof.context) (ct: cterm) =
    SOME (cool_number_eq_conv ctxt ct) handle CTERM _ => NONE
\<close>

simproc_setup cool_number_eq
  ("(x :: cool_number) = (y :: cool_number)")
  = \<open>K cool_number_eq_simproc\<close>

lemma test_variant_equality_simproc:
  shows \<open>cool_72 \<noteq> cool_devil_prime\<close>
  by simp


text\<open>Now, demonstrate @{thm lookup_find_index_into_ncase}\<close>
lemma match_cool_number_into_ncase:
  assumes \<open>length vs = length all_cool_numbers\<close>
  shows \<open>match_cool_number vs r = ncase_selector (zip (List.map Some all_cool_numbers) vs) r\<close>
  using lookup_find_index_into_ncase[OF assms(1) cool_numbers_total all_system_register_ids_distinct]
  by (simp add: match_cool_number_def cool_number_index_def)

lemma turn_case_into_ncase: 
  shows \<open>is_cool_number_odd r = (
        ncase r of cool_1337 \<Rightarrow> True | cool_42 \<Rightarrow> False | cool_72 \<Rightarrow> True | cool_deadbeef \<Rightarrow> True
                   | cool_cafe \<Rightarrow> False | cool_devil_prime \<Rightarrow> True)\<close>
  by (simp add: is_cool_number_odd_def case_cool_number_def
      match_cool_number_into_ncase all_cool_numbers_def)

end

(*<*)
end
(*>*)