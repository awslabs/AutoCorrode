(*<*)
theory Remove_Enum_Discriminate_Elims
  imports
    Main
begin
(*>*)

text\<open>By default, a new isabelle \<^verbatim>\<open>datatype\<close> with \<^verbatim>\<open>n\<close> constructors will generate \<^verbatim>\<open>n \<times> (n - 1)\<close> 
elimination rules of the form \<^term>\<open>ConstructorI = ConstructorJ \<Longrightarrow> R\<close> with \<^term>\<open>i \<noteq> j\<close>. This
quadratic scaling leads to performance issues in Isabelle2025, which has been reported on the
mailing list \<^url>\<open>https://isabelle.zulipchat.com/#narrow/channel/247541-Mirror.3A-Isabelle-Users-Mailing-List/topic/.5Bisabelle.5D.20Merging.20elimination.20rules.20of.20Claset.20is.20slow.20-.20.2E.2E.2E/near/525149986\<close>

Moreover, the rules are are superfluous in some sense, since \<^verbatim>\<open>simp\<close> will also prove such goals
without the elimination rule, by simplifying \<^term>\<open>(ConstructorI = ConstructorJ) = False\<close>.

There is currently no native way to disable the generation of these elimination rules.
As a temporary stopgap, this file adds a new \<^verbatim>\<open>datatype\<close> plugin, which removes the elimination
rules from a newly generated \<^verbatim>\<open>datatype\<close> directly after they have been generated.\<close>

ML\<open>
  \<comment> \<open>Given a generic context, get the list of safe elimination rules\<close>
  fun safe_elims_of ctxt =
    let
      fun is_safe_elim (_, {kind, ...}) =
        Bires.kind_safe kind andalso Bires.kind_is_elim kind;
    in
      Classical.dest_decls (Context.proof_of ctxt) is_safe_elim
      |> List.map #1
    end;

  \<comment> \<open>Some wrappers for use with \<^verbatim>\<open>@{theory}\<close> and \<^verbatim>\<open>@{context}\<close>}\<close>
  val safe_elims_of_thy = Context.Theory #> safe_elims_of;
  val safe_elims_of_ctx = Context.Proof #> safe_elims_of;

  \<comment> \<open>Delete the given rule from the safe elimination rules of a generic context\<close>
  fun delete_safe_elim_from_thy rule =
    Thm.apply_attribute Classical.rule_del rule #> snd;

  \<comment> \<open>Delete the given list of rules from the safe elimination rules of a generic context\<close>
  val delete_safe_elims_from_thy =
    fold delete_safe_elim_from_thy;

  fun delete_last_n_elims_from_thy num thy =
    let
      val safe_elims = safe_elims_of thy;
      val trunc = List.take (safe_elims, num);
      \<comment> \<open>To log what is deleted, uncomment the following:\<close> (*
      val _ = (warning o Pretty.string_of o Pretty.big_list "deleting:")
          (List.map (Thm.pretty_thm @{context}) trunc); *)
    in
      delete_safe_elims_from_thy trunc thy
    end;

  fun count_safe_elims_ctx thy = List.length (safe_elims_of_ctx thy);
  fun count_safe_elims_thy thy = List.length (safe_elims_of_thy thy);

  fun assert cond msg =
    if not cond then
      raise Fail ("Assertion failed: " ^ msg)
    else
      ()
\<close>

text\<open>We can now easily query the number of safe elimination rules: \<^verbatim>\<open>283\<close> in Isabelle2025\<close>
ML\<open>
  val safe_elim_rules_at_start = @{context} |> count_safe_elims_ctx;
\<close>

experiment
begin
  datatype testenum =
      Foo
    | Bar
    | Boo

  text\<open>After adding a 3-constructor datatype, \<^verbatim>\<open>3 \<times> 2 = 6\<close> elimination rules get added\<close>
  ML\<open>
    assert (safe_elim_rules_at_start + 6 = (@{context} |> count_safe_elims_ctx)) "New elim rules not added?";
  \<close>
end

text\<open>After exiting the experiment, those rules are removed again.\<close>
ML\<open>
  assert (safe_elim_rules_at_start = (@{context} |> count_safe_elims_ctx)) "New elim rules not removed?";
\<close>

text\<open>We only want to stop elimination rules being generated for new \<^verbatim>\<open>datatype\<close>s, so we store the
existing \<^verbatim>\<open>datatype\<close>s at this point and build helper functions to only take actions for new ones.\<close>
ML\<open>
  \<comment> \<open>List of existing \<^verbatim>\<open>datatype\<close>s -- internally, these are 'constructor sugars' of type
      \<^verbatim>\<open>Ctr_Sugar.ctr_sugar\<close>.\<close>
  val existing_ctr_sugars = Ctr_Sugar.ctr_sugars_of @{context};

  \<comment> \<open>Equality on the \<^verbatim>\<open>Ctr_Sugar.ctr_sugar\<close> type, by comparing type names.\<close>
  fun ctr_eq (ctr1 : Ctr_Sugar.ctr_sugar, ctr2 : Ctr_Sugar.ctr_sugar) =
    Term.eq_Type_name (#T ctr1, #T ctr2)

  \<comment> \<open>Is the given \<^verbatim>\<open>ctr\<close> in the \<^verbatim>\<open>existing_ctr_sugars\<close> list?\<close>
  fun is_existing_ctr ctr = member ctr_eq existing_ctr_sugars ctr;

  \<comment> \<open>Run a function \<^verbatim>\<open>f\<close> only for new constructors \<^verbatim>\<open>ctr\<close>\<close>
  fun only_for_new_ctr (f : Ctr_Sugar.ctr_sugar -> 'a -> 'a) ctr =
    if is_existing_ctr ctr then I else f ctr
\<close>

ML\<open>
  \<comment> \<open>Given a datatype, delete the last \<^verbatim>\<open>n \<times> (n - 1)\<close> elimination rules, where \<^verbatim>\<open>n\<close> is the number
      of constructors of the datatype. Must be run directly after generation of the datatype,
      since then these elimination rules will then precisely be the rules of the form
      \<^term>\<open>ConstructorI = ConstructorJ \<Longrightarrow> R\<close> that we wish to remove.
      TODO: This is not very robust, can we do better?\<close>
  fun delete_discriminate_elims (ctr : Ctr_Sugar.ctr_sugar) =
    let
      val num_ctrs = List.length (#ctrs ctr)
    in
      delete_last_n_elims_from_thy (num_ctrs * (num_ctrs - 1))
    end;

  \<comment> \<open>Helper function to turn a function of type \<^verbatim>\<open>Context.generic \<rightarrow> Context.generic\<close> into a
      function of type \<^verbatim>\<open>local_theory \<rightarrow> local_theory\<close>.\<close>
  fun declare_local_theory (f : Context.generic -> Context.generic)  =
    Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (K f);
\<close>

text\<open>Now we have all the ingredients to register a plugin which removes the elimination rules
from newly generated datatypes.\<close>
setup\<open>
  let
    val delete_elims_plugin = Plugin_Name.declare_setup \<^binding>\<open>delete_elims\<close>
  in
    Ctr_Sugar.ctr_sugar_interpretation delete_elims_plugin (
      delete_discriminate_elims #> declare_local_theory |> only_for_new_ctr
    )
  end
\<close>

text\<open>No elimination rules have been deleted now that the plugin is active\<close>
ML\<open>
  assert (safe_elim_rules_at_start = (@{context} |> count_safe_elims_ctx)) "Elim rules were removed unexpectedly?";
\<close>

datatype testenum =
    Foo
  | Bar
  | Boo
  | Zar

text\<open>After adding a new datatype, the number of elimination rules is unchanged\<close>
ML\<open>
  assert (safe_elim_rules_at_start = (@{context} |> count_safe_elims_ctx)) "Elim rules were added unexpectedly?";
\<close>

experiment
begin
  datatype testenum =
      Foo
    | Bar
    | Boo
    | Zar

  text\<open>This also works inside a \<^verbatim>\<open>experiment\<close>/\<^verbatim>\<open>context\<close> block\<close>
  ML\<open>
    assert (safe_elim_rules_at_start = (@{context} |> count_safe_elims_ctx)) "Elim rules were added unexpectedly?";
  \<close>
end

text\<open>The removal does not persist after exiting the \<^verbatim>\<open>experiment\<close>, just like the addition.\<close>
ML\<open>
  assert (safe_elim_rules_at_start = (@{context} |> count_safe_elims_ctx)) "Elim rules were removed unexpectedly?";
\<close>

(*<*)
end
(*>*)
