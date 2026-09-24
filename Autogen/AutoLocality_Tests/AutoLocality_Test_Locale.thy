(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Locale
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Locale-defined operations and attributes, and their interpretations\<close>

text\<open>An operation or attribute may be defined inside a locale, so that its definition mentions a
locale parameter. @{verbatim \<open>locality_lemma\<close>} must then handle two coordinate systems that ordinary
records never exercise:

  \<^enum> The cancellation simproc's picker runs over the bare constant with the locale parameter applied
    explicitly (@{term \<open>bigval bump R\<close>}), so the footprint-database entry must use bare-relative
    argument indices, not the abbreviation-relative ones visible in the locale.

  \<^enum> The simproc's match pattern must schematise the leading locale-parameter positions; otherwise it
    bakes in the locale's fixed parameter and never matches an interpreted instance.

Two further usage points are pinned here:

  \<^item> Register a locale constant from a @{command context} re-entry, not from inside the defining
    @{command locale} body: the auto-derivation's core proof only closes once the definitions are
    fully established.

  \<^item> The cancellable inner operation (@{term \<open>setc\<close>}) is defined at the top level, on the bare record.
    Only the parameter-using constants (@{term \<open>bigval\<close>}, @{term \<open>bumpval\<close>}) live in the locale - which
    is the representative shape, and side-steps the fact that a parameter-free constant defined
    inside a locale is not found by the picker once the locale is left.\<close>

datatype_record loc =
  oa :: nat
  ob :: nat
  oc :: nat

locality_init for loc

\<comment>\<open>A top-level, parameter-free operation on a disjoint field - the thing we cancel against.\<close>
definition setc :: \<open>nat \<Rightarrow> loc \<Rightarrow> loc\<close> where
  \<open>setc k \<equiv> update_oc (\<lambda>_. k)\<close>
locality_lemma for loc: \<open>setc\<close> footprint [oc] .

locale scaler =
  fixes bump :: \<open>nat \<Rightarrow> nat\<close>
begin

\<comment>\<open>An attribute whose definition mentions the locale parameter @{term \<open>bump\<close>}.\<close>
definition bigval :: \<open>loc \<Rightarrow> bool\<close> where
  \<open>bigval R \<equiv> bump (oa R) > 10\<close>
definition bigval_at :: \<open>nat \<Rightarrow> loc \<Rightarrow> bool\<close> where
  \<open>bigval_at n R \<equiv> bump (oa R) > n\<close>
\<comment>\<open>An operation whose body mentions the locale parameter.\<close>
definition bumpval :: \<open>loc \<Rightarrow> loc\<close> where
  \<open>bumpval R \<equiv> update_oa bump R\<close>

end

text\<open>Register from a @{command context} re-entry, with the SHORT names: a short name re-parses to the
bare constant with the locale parameter applied, whereas the qualified name would leave the
parameter unapplied and mis-register the argument indices.\<close>

context scaler begin
locality_lemma for loc: \<open>bigval\<close> footprint [oa] .
locality_lemma for loc: \<open>bigval_at\<close> footprint [oa] .
locality_lemma for loc: \<open>bumpval\<close> footprint [oa] .
end

context scaler begin

ML\<open>
structure AutoLocality_Test_Locale_Dispatch_Before =
struct

val head_name = "AutoLocality_Test_Locale.scaler.bigval"
val ctxt = \<^context>
val inventory_entries =
  LocalityDispatcherInventory.get (Context.Proof ctxt)
  |> LocalityDispatchKeyTable.dest
  |> map (fn (key, entry : locality_dispatcher_inventory_entry) =>
       (key, #alias entry))
  |> filter (fn (key, _) => #head_name key = head_name)
val (dispatch_key, alias) =
  (case inventory_entries of
     [(key, alias)] => (key, alias)
   | _ => error "Expected one source locale dispatcher inventory entry")
val trigger = locality_dispatch_trigger ctxt dispatch_key
val raw_dispatchers =
  Raw_Simplifier.simpset_of ctxt
  |> Raw_Simplifier.dest_ss
  |> #simprocs
  |> filter (fn (_, lhss) =>
       case lhss of
         [lhs] => Term.aconv (lhs, trigger)
       | _ => false)
val name =
  (case raw_dispatchers of
     [(name, _)] => name
   | _ => error "Expected one source locale raw dispatcher")
val checked_alias =
  #1 (Simplifier.check_simproc ctxt (alias, Position.none))
val _ = AutoLocality_Assert.run_suite "Locale/source-local-dispatch"
  [ ("source locale has one inventory identity",
       fn () => AutoLocality_Assert.check "one source inventory identity"
         (length inventory_entries = 1)),
    ("source locale inventory alias resolves",
       fn () => AutoLocality_Assert.check "source named dispatcher"
         (checked_alias = alias)),
    ("source locale has one raw dispatcher",
       fn () => AutoLocality_Assert.check "one source raw dispatcher"
         (length raw_dispatchers = 1)) ]

end
\<close>

end

ML\<open>
  val leaked_inventory =
    LocalityDispatcherInventory.get (Context.Proof \<^context>)
    |> LocalityDispatchKeyTable.dest
    |> filter (fn (key, _) =>
         #head_name key =
           AutoLocality_Test_Locale_Dispatch_Before.head_name)
  val _ = AutoLocality_Assert.run_suite
    "Locale/no-background-leak"
    [ ("locale dispatcher remains local before interpretation",
         fn () => AutoLocality_Assert.check "no top-level dispatcher"
           (null leaked_inventory)) ]
\<close>

subsection\<open>Cancellation inside the locale\<close>

context scaler begin

text\<open>A footprint-disjoint operation under the parameter-using attribute cancels by plain
@{term \<open>simp\<close>}.\<close>
lemma \<open>bigval (setc c X) = bigval X\<close> by simp
lemma explicit_cancellation_uses_relative_index:
  shows \<open>bigval (setc c X) = bigval X\<close>
  by (rule [[locality_autocancellation setc bigval 0]])
lemma explicit_cancellation_uses_nonzero_relative_index:
  shows \<open>bigval_at n (setc c X) = bigval_at n X\<close>
  by (rule [[locality_autocancellation setc bigval_at 1]])
lemma \<open>bigval (setc c (bumpval X)) = bigval (bumpval X)\<close> by simp
\<comment>\<open>The parameter-using operation's own disjointness lemma holds.\<close>
lemma \<open>ob (bumpval X) = ob X\<close> by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Locale.loc"
  val attr = "scaler.bigval"
  val _ = AutoLocality_Assert.run_suite "Locale/local-context-simproc"
    [ ("generic locale parameter cancels",
         fn () => AutoLocality_Assert.assert_simproc_cancels_to ctxt rec_name attr
                    "scaler.bigval bump (setc c X)" "scaler.bigval bump X"),
      ("generic locale parameter declines a shared footprint",
         fn () => AutoLocality_Assert.assert_simproc_declines ctxt rec_name attr
                    "scaler.bigval bump (bumpval X)") ]
\<close>

end

subsection\<open>Transport through @{command interpretation}\<close>

text\<open>Interpreting the locale instantiates the parameter with a concrete function. Because the
simproc pattern schematises the leading parameter position, the very same cancellation simproc fires
on the interpreted constants @{verbatim \<open>sc.bigval\<close>}, @{verbatim \<open>sc.bumpval\<close>}.\<close>

interpretation sc: scaler \<open>\<lambda>n. n + 1\<close> .

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Locale.loc"
  val raw_interpreted_pattern = \<^term>\<open>scaler.bigval (\<lambda>n. n + 1)\<close>
  val interpreted_pattern = \<^term>\<open>scaler.bigval Suc\<close>
  val raw_interpreted_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute" raw_interpreted_pattern
  val interpreted_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute" interpreted_pattern
  val direct_result =
    Option.map (fn entry =>
      locality_cancellation_simproc_for_entry rec_name entry ctxt
        (Thm.cterm_of ctxt \<^term>\<open>scaler.bigval Suc (setc c X)\<close>))
      interpreted_entry
  val _ = AutoLocality_Assert.run_suite "Locale/interpreted-registration"
    [ ("raw interpreted entry exists",
         fn () => AutoLocality_Assert.check "raw interpreted entry exists"
           (Option.isSome raw_interpreted_entry)),
      ("typed interpreted entry exists",
         fn () => AutoLocality_Assert.check "typed interpreted entry exists"
           (Option.isSome interpreted_entry)),
      ("interpreted entry cancels directly",
         fn () => AutoLocality_Assert.check "interpreted entry cancels directly"
           (case direct_result of SOME (SOME _) => true | _ => false)) ]
\<close>

lemma \<open>sc.bigval (setc c X) = sc.bigval X\<close> by simp
lemma \<open>sc.bigval (setc c (sc.bumpval X)) = sc.bigval (sc.bumpval X)\<close> by simp

text\<open>A second, independent interpretation works the same way.\<close>
interpretation sc2: scaler \<open>\<lambda>n. n * 2\<close> .

lemma \<open>sc2.bigval (setc c X) = sc2.bigval X\<close> by simp
lemma interpreted_simp_only_reactivation:
  shows \<open>sc.bigval (setc c X) = sc.bigval X \<and>
    sc2.bigval (setc c X) = sc2.bigval X\<close>
  by (simp only: [[locality_cancel]])

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Locale.loc"
  val attr = "scaler.bigval"
  val first_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>scaler.bigval Suc\<close>
  val second_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>scaler.bigval (\<lambda>n. n * 2)\<close>
  val interpreted_family_entries =
    get_record_locality_entries rec_name ctxt
    |> filter (fn entry =>
         locality_entry_kind entry = Locality_Attribute
         andalso #const_name entry =
           AutoLocality_Test_Locale_Dispatch_Before.head_name)
  val inventory_entries =
    LocalityDispatcherInventory.get (Context.Proof ctxt)
    |> LocalityDispatchKeyTable.dest
    |> map (fn (key, entry : locality_dispatcher_inventory_entry) =>
         (key, #alias entry))
    |> filter (fn (key, _) =>
         #head_name key =
           AutoLocality_Test_Locale_Dispatch_Before.head_name)
  val inventory_stable =
    (case inventory_entries of
       [(key, alias)] =>
         locality_dispatch_key_eq
           (key, AutoLocality_Test_Locale_Dispatch_Before.dispatch_key)
         andalso
           #1 (Simplifier.check_simproc
             ctxt (alias, Position.none)) = alias
     | _ => false)
  val raw_family_dispatchers =
    Raw_Simplifier.simpset_of ctxt
    |> Raw_Simplifier.dest_ss
    |> #simprocs
    |> filter (fn (name, _) =>
         name = AutoLocality_Test_Locale_Dispatch_Before.name)
  val public_fact_base =
    register_locality_attr_cancellation_thm_name
      rec_name "bigval" 0
  val public_fact_names =
    Global_Theory.facts_of (Proof_Context.theory_of ctxt)
    |> Facts.dest_static true []
    |> map #1
  fun interpreted_public_fact_exists interpretation =
    exists (fn name =>
      Long_Name.base_name name = public_fact_base
      andalso member (op =) (Long_Name.explode name) interpretation)
      public_fact_names
  val _ = AutoLocality_Assert.run_suite "Locale/common-origin-dispatch"
    [ ("interpretations retain distinct semantic entries",
         fn () => AutoLocality_Assert.check "distinct interpreted entries"
           (case (first_entry, second_entry) of
              (SOME first, SOME second) =>
                length interpreted_family_entries = 2
                andalso not (locality_operational_key_eq
                  (#key first, #key second))
            | _ => false)),
      ("first interpretation still cancels",
         fn () => AutoLocality_Assert.assert_simproc_cancels_to
           ctxt rec_name attr
           "scaler.bigval Suc (setc c X)"
           "scaler.bigval Suc X"),
      ("second interpretation still cancels",
         fn () => AutoLocality_Assert.assert_simproc_cancels_to
           ctxt rec_name attr
           "scaler.bigval (\<lambda>n. n * 2) (setc c X)"
           "scaler.bigval (\<lambda>n. n * 2) X"),
      ("interpretations retain their public facts",
         fn () => AutoLocality_Assert.check "interpreted public facts"
           (interpreted_public_fact_exists "sc"
            andalso interpreted_public_fact_exists "sc2")),
      ("interpretations retain one family inventory",
         fn () => AutoLocality_Assert.check "stable interpreted inventory"
           inventory_stable),
      ("common-origin interpretations share one raw dispatcher",
         fn () => AutoLocality_Assert.check "one interpreted raw dispatcher"
           (length raw_family_dispatchers = 1)) ]
\<close>

lemma repeated_cleared_reactivation_cancels:
  shows \<open>sc.bigval (setc c X) = sc.bigval X \<and>
    sc2.bigval (setc c X) = sc2.bigval X\<close>
  by (simp only: [[locality_cancel]] [[locality_cancel]])

subsection\<open>Maximal dispatcher rank shadows lower registrations\<close>

definition rank_shadow_attr :: \<open>nat \<Rightarrow> loc \<Rightarrow> bool\<close> where
  \<open>rank_shadow_attr n R \<equiv> oa R > n\<close>

locality_lemma for loc: \<open>rank_shadow_attr\<close> footprint [oa] .

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Locale.loc"
  val lower_entry =
    (case select_locality_entry_for_pattern ctxt rec_name "attribute"
            \<^term>\<open>rank_shadow_attr\<close> of
       SOME entry => entry
     | NONE => error "Missing lower-ranked shadow registration")
  val operation_entry =
    (case select_locality_entry_for_pattern ctxt rec_name "operation"
            \<^term>\<open>setc\<close> of
       SOME entry => entry
     | NONE => error "Missing shadowing operation registration")
  val dispatch_key = locality_dispatch_key_of_entry ctxt lower_entry
  val higher_entry =
    make_locality_entry rec_name Locality_Attribute
      (#const_name lower_entry)
      \<^term>\<open>rank_shadow_attr (0 :: nat)\<close>
      [false] ["oc"] 1 0 false [] [] NONE
  val _ =
    if locality_dispatch_key_eq
         (dispatch_key, locality_dispatch_key_of_entry ctxt higher_entry)
    then ()
    else error "Shadow registrations do not share a dispatch family"
  val shadow_context =
    Context.Proof ctxt
    |> RecordLocalityData.map (insert_locality_entry higher_entry)
    |> LocalitySecondaryIndex.map
         (insert_locality_secondary_key_with_dispatch
           (SOME dispatch_key) higher_entry)
  val shadow_ctxt = Context.proof_of shadow_context
  val redex =
    Thm.cterm_of shadow_ctxt
      \<^term>\<open>rank_shadow_attr (0 :: nat) (setc c X)\<close>
  val actual = Thm.term_of redex
  val ranked_key_sets =
    locality_dispatch_ranked_key_queries_with
      locality_no_count shadow_ctxt dispatch_key actual
    |> map (fn (query : locality_ranked_key_query) =>
         #retrieve query ()
         |> locality_equality_valid_keys_with
              locality_no_count shadow_ctxt (#actual query))
    |> filter_out LocalityOperationalKeyTable.is_empty

  fun singleton_key_is entry keys =
    (case LocalityOperationalKeyTable.keys keys of
       [key] => locality_operational_key_eq (key, #key entry)
     | _ => false)

  val maximal_is_higher =
    (case ranked_key_sets of
       keys :: _ => singleton_key_is higher_entry keys
     | [] => false)
  val lower_is_strictly_later =
    (case ranked_key_sets of
       _ :: lower_sets =>
         exists (fn keys =>
           LocalityOperationalKeyTable.defined keys (#key lower_entry))
           lower_sets
     | [] => false)
  val higher_result =
    locality_cancellation_for_entry
      rec_name higher_entry shadow_ctxt redex
  val lower_result =
    locality_cancellation_for_entry
      rec_name lower_entry shadow_ctxt redex
  val dispatcher_result =
    locality_cancellation_simproc_for_dispatch
      dispatch_key shadow_ctxt redex
  val _ = AutoLocality_Assert.run_suite "Locale/maximal-rank-shadowing"
    [ ("longer exact registration is the maximal nonempty rank",
         fn () => AutoLocality_Assert.check "maximal shadow rank"
           (maximal_is_higher andalso lower_is_strictly_later)),
      ("higher footprint blocks while lower footprint permits cancellation",
         fn () => AutoLocality_Assert.check "shadow footprint split"
           (not (disjoint_footprint
              (#footprint higher_entry) (#footprint operation_entry))
            andalso
            disjoint_footprint
              (#footprint lower_entry) (#footprint operation_entry))),
      ("higher registration declines before using its empty payload",
         fn () => AutoLocality_Assert.check "higher rank declines"
           (null (#core_thms higher_entry)
            andalso null (#disjoint_thms higher_entry)
            andalso not (Option.isSome (#local_thm higher_entry))
            andalso
            (case higher_result of NONE => true | SOME _ => false))),
      ("lower registration would cancel the same redex",
         fn () => AutoLocality_Assert.check "lower rank cancels"
           (case lower_result of SOME _ => true | NONE => false)),
      ("generic dispatcher does not fall through below maximal rank",
         fn () => AutoLocality_Assert.check "maximal rank is terminal"
           (case dispatcher_result of NONE => true | SOME _ => false)) ]
\<close>

subsection\<open>Generated theorem-note lifecycle\<close>

named_theorems autolocality_explicit_operation_note_oracle
named_theorems autolocality_explicit_attribute_note_oracle

definition note_default_op :: \<open>loc \<Rightarrow> loc\<close> where
  \<open>note_default_op R \<equiv> update_oa Suc R\<close>

definition note_explicit_op :: \<open>loc \<Rightarrow> loc\<close> where
  \<open>note_explicit_op R \<equiv> update_ob Suc R\<close>

definition note_default_attr :: \<open>loc \<Rightarrow> bool\<close> where
  \<open>note_default_attr R \<equiv> oa R = ob R\<close>

definition note_explicit_attr :: \<open>loc \<Rightarrow> bool\<close> where
  \<open>note_explicit_attr R \<equiv> oa R \<le> ob R\<close>

locality_lemma for loc:
  \<open>note_default_op\<close> footprint [oa, ob] .
locality_lemma for loc:
  \<open>note_default_attr\<close> footprint [oa, ob] .
locality_lemma for loc [autolocality_explicit_operation_note_oracle]:
  \<open>note_explicit_op\<close> footprint [oa, ob] .
locality_lemma for loc [autolocality_explicit_attribute_note_oracle]:
  \<open>note_explicit_attr\<close> footprint [oa, ob] .

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Locale.loc"

  fun operation_note_names pattern =
    let
      val public_id = locality_public_id ctxt pattern
    in
      [register_locality_op_commutativity_thm_name
         rec_name public_id,
       register_locality_op_disjointness_thm_name
         rec_name public_id]
    end

  fun attribute_note_name pattern =
    register_locality_attr_cancellation_thm_name
      rec_name (locality_public_id ctxt pattern) 0

  fun public_facts names =
    maps (Proof_Context.get_thms ctxt) names

  fun named_collection name =
    Named_Theorems.get ctxt
      (Named_Theorems.check ctxt (name, Position.none))

  fun matching_facts collection public =
    filter (fn observed => Thm.eq_thm_prop (public, observed))
      collection

  fun exact_public_activation collection public =
    (case matching_facts collection public of
       [observed] =>
         Thm.has_name_hint public
         andalso Thm.has_name_hint observed
         andalso Thm.get_name_hint public = Thm.get_name_hint observed
     | _ => false)

  fun exact_anonymous_activation collection public =
    (case matching_facts collection public of
       [observed] =>
         Thm.has_name_hint public
         andalso not (Thm.has_name_hint observed)
     | _ => false)

  val default_operation_public =
    operation_note_names \<^term>\<open>note_default_op\<close>
    |> public_facts
  val default_attribute_public =
    [attribute_note_name \<^term>\<open>note_default_attr\<close>]
    |> public_facts
  val explicit_operation_public =
    operation_note_names \<^term>\<open>note_explicit_op\<close>
    |> public_facts
  val explicit_attribute_public =
    [attribute_note_name \<^term>\<open>note_explicit_attr\<close>]
    |> public_facts
  val default_observations =
    named_collection (default_named_theorems_for_record rec_name)
  val explicit_operation_observations =
    named_collection "autolocality_explicit_operation_note_oracle"
  val explicit_attribute_observations =
    named_collection "autolocality_explicit_attribute_note_oracle"

  val _ = AutoLocality_Assert.run_suite "Locale/theorem-note-lifecycle"
    [ ("default operation activates on exactly two public notes",
         fn () => AutoLocality_Assert.check
           "default operation public-note activations"
           (length default_operation_public = 2
            andalso forall
              (exact_public_activation default_observations)
              default_operation_public)),
      ("default attribute activates on exactly one public note",
         fn () => AutoLocality_Assert.check
           "default attribute public-note activation"
           (length default_attribute_public = 1
            andalso forall
              (exact_public_activation default_observations)
              default_attribute_public)),
      ("explicit operation keeps two anonymous attribute activations",
         fn () => AutoLocality_Assert.check
           "explicit operation public-plus-anonymous notes"
           (length explicit_operation_public = 2
            andalso length explicit_operation_observations = 2
            andalso forall
              (exact_anonymous_activation
                explicit_operation_observations)
              explicit_operation_public)),
      ("explicit attribute keeps one anonymous attribute activation",
         fn () => AutoLocality_Assert.check
           "explicit attribute public-plus-anonymous notes"
           (length explicit_attribute_public = 1
            andalso length explicit_attribute_observations = 1
            andalso forall
              (exact_anonymous_activation
                explicit_attribute_observations)
              explicit_attribute_public)) ]
\<close>

subsection\<open>Simproc-level checks: bare-relative indices and fixpoint decline\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Locale.loc"
  val attr = "scaler.bigval"
  val _ = AutoLocality_Assert.run_suite "Locale/simproc"
    [ \<comment>\<open>The interpreted simproc zooms into the record (arg 1), not the locale parameter
         (arg 0), so a disjoint operation cancels.\<close>
      ("interpreted cancels to scaler.bigval (...) X",
         fn () => AutoLocality_Assert.assert_simproc_cancels_to ctxt rec_name attr
                    "scaler.bigval (\<lambda>n. n + 1) (setc c X)" "scaler.bigval (\<lambda>n. n + 1) X"),
      \<comment>\<open>A footprint-sharing operation (bumpval shares [oa] with bigval) must be declined - no
         loop.\<close>
      ("declines footprint-sharing interpreted",
         fn () => AutoLocality_Assert.assert_simproc_declines ctxt rec_name attr
                    "scaler.bigval (\<lambda>n. n + 1) (scaler.bumpval (\<lambda>n. n + 1) X)") ]
\<close>

(*<*)
end
(*>*)
