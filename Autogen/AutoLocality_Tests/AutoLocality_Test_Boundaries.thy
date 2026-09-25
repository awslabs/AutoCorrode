(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Boundaries
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Naming, manual-proof, merge, and exception boundaries\<close>

datatype_record boundary_rec =
  ba :: nat
  bb :: nat
  shadow :: nat

locality_init for boundary_rec

definition boundary_attr :: \<open>boundary_rec \<Rightarrow> bool\<close> where
  \<open>boundary_attr R \<equiv> bb R > 0\<close>

definition boundary_rank_attr :: \<open>'a \<Rightarrow> boundary_rec \<Rightarrow> bool\<close> where
  \<open>boundary_rank_attr x R \<equiv> boundary_attr R\<close>

definition boundary_rank_attr2 ::
    \<open>nat \<Rightarrow> boundary_rec \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>boundary_rank_attr2 x R y \<equiv> boundary_attr R\<close>

definition manual_flip :: \<open>boundary_rec \<Rightarrow> boundary_rec\<close> where
  \<open>manual_flip R \<equiv> update_ba Suc R\<close>

locality_lemma for boundary_rec: \<open>boundary_attr\<close> footprint [bb] .

subsection\<open>Manual core certificates via @{verbatim \<open>no_proof\<close>}\<close>

locality_lemma for boundary_rec (no_proof): \<open>manual_flip\<close> footprint [ba]
  by (auto simp add: manual_flip_def)

lemma \<open>boundary_attr (manual_flip R) = boundary_attr R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_Assert.run_suite "Boundaries/manual-proof"
    [ ("manual operation retains all linear certificates",
         fn () => AutoLocality_Assert.assert_op_lemmas ctxt
           "AutoLocality_Test_Boundaries_boundary_rec" "manual_flip") ]
\<close>

subsection\<open>Expanded abbreviations remain semantic registrations\<close>

abbreviation boundary_abbreviation_attr ::
    \<open>boundary_rec \<Rightarrow> nat list\<close> where
  \<open>boundary_abbreviation_attr R \<equiv> [bb R] @ [shadow R]\<close>

locality_lemma for boundary_rec:
  \<open>boundary_abbreviation_attr\<close> footprint [bb, shadow] .

lemma boundary_abbreviation_cancel:
  shows \<open>boundary_abbreviation_attr (manual_flip R) =
    boundary_abbreviation_attr R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name =
    "AutoLocality_Test_Boundaries.boundary_rec"
  val pattern =
    Syntax.read_term ctxt "boundary_abbreviation_attr"
  val entry =
    (case select_locality_entry_for_pattern
            ctxt rec_name "attribute" pattern of
       SOME entry => entry
     | NONE => error "Missing abbreviation locality registration")
  fun is_abstraction (Abs _) = true
    | is_abstraction _ = false
  val _ = AutoLocality_Assert.run_suite "Boundaries/abbreviation"
    [ ("expanded lambda remains structurally indexed",
         fn () => AutoLocality_Assert.check "lambda structural family"
           (is_abstraction (#canonical_head (#key entry)))),
      ("expanded lambda has no physical dispatcher",
         fn () => AutoLocality_Assert.check "semantic-only abbreviation"
           (is_none (locality_dispatch_key_of_entry_opt ctxt entry))) ]
\<close>

subsection\<open>Custom @{verbatim \<open>update_\<close>} name is not a record field updater\<close>

definition update_shadow :: \<open>boundary_rec \<Rightarrow> boundary_rec\<close> where
  \<open>update_shadow R \<equiv> update_ba Suc R\<close>

locality_lemma for boundary_rec:
  \<open>AutoLocality_Test_Boundaries.update_shadow\<close> footprint [ba] .

lemma \<open>boundary_attr (AutoLocality_Test_Boundaries.update_shadow R) =
    boundary_attr R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"
  val custom =
    get_record_locality_entries_for_const rec_name
      "AutoLocality_Test_Boundaries.update_shadow" ctxt
  val field =
    get_record_locality_entries_for_const rec_name
      "AutoLocality_Test_Boundaries.boundary_rec.update_shadow" ctxt
  val _ = AutoLocality_Assert.run_suite "Boundaries/update-name"
    [ ("custom update_-prefixed operation is not a field",
         fn () => AutoLocality_Assert.check "custom operation classification"
           (case custom of [entry] => not (#field entry) | _ => false)),
      ("actual record updater remains a field operation",
         fn () => AutoLocality_Assert.check "field operation classification"
           (case field of [entry] => #field entry | _ => false)) ]
\<close>

subsection\<open>Nested non-reinitializable targets retain local state\<close>

context
  fixes nested_limit :: nat
  assumes nested_limit_positive: \<open>nested_limit > 0\<close>
begin

definition nested_nonreinitializable_attr ::
    \<open>boundary_rec \<Rightarrow> bool\<close> where
  \<open>nested_nonreinitializable_attr R \<equiv> bb R < nested_limit\<close>

local_setup \<open>Named_Target.revoke_reinitializability\<close>

locality_lemma for boundary_rec (no_proof):
  \<open>nested_nonreinitializable_attr\<close> footprint [bb]
  by (auto simp add: nested_nonreinitializable_attr_def)

context
  notes [[locality_no_cancel]]
begin

context
  notes [[locality_cancel]]
begin

lemma nested_nonreinitializable_registration:
  shows \<open>nested_limit > 0 \<and>
    nested_nonreinitializable_attr (manual_flip R) =
      nested_nonreinitializable_attr R\<close>
  using nested_limit_positive
  by simp

end

end

end

subsection\<open>Dispatcher names preserve qualified operational keys\<close>

locale dispatch_collision_B_C =
  fixes limit :: nat
begin

definition f :: \<open>boundary_rec \<Rightarrow> bool\<close> where
  \<open>f R \<equiv> bb R > limit\<close>

locality_lemma for boundary_rec (no_proof): \<open>f\<close> footprint [bb]
  by (auto simp add: f_def)

end

locale dispatch_collision_B =
  fixes limit :: nat
begin

definition C_f :: \<open>boundary_rec \<Rightarrow> bool\<close> where
  \<open>C_f R \<equiv> bb R > limit\<close>

locality_lemma for boundary_rec (no_proof): \<open>C_f\<close> footprint [bb]
  by (auto simp add: C_f_def)

end

global_interpretation dispatch_collision_left:
  dispatch_collision_B_C 0 .

global_interpretation dispatch_collision_right:
  dispatch_collision_B 0 .

lemma dispatch_collision_left_cancel:
  shows \<open>dispatch_collision_left.f (manual_flip R) =
    dispatch_collision_left.f R\<close>
  by simp

lemma dispatch_collision_right_cancel:
  shows \<open>dispatch_collision_right.C_f (manual_flip R) =
    dispatch_collision_right.C_f R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val background_lthy =
    Named_Target.theory_init (Proof_Context.theory_of ctxt)
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"

  fun require_entry label pattern =
    (case select_locality_entry_for_pattern
            ctxt rec_name "attribute" pattern of
       SOME entry => entry
     | NONE => error ("Missing dispatcher-name collision entry " ^ label))

  val left_entry =
    require_entry "left"
      \<^term>\<open>dispatch_collision_B_C.f (0 :: nat)\<close>
  val right_entry =
    require_entry "right"
      \<^term>\<open>dispatch_collision_B.C_f (0 :: nat)\<close>
  val left_key = locality_dispatch_key_of_entry ctxt left_entry
  val right_key = locality_dispatch_key_of_entry ctxt right_entry
  val left_head =
    "AutoLocality_Test_Boundaries.dispatch_collision_B_C.f"
  val right_head =
    "AutoLocality_Test_Boundaries.dispatch_collision_B.C_f"

  fun old_dispatch_name (key : locality_dispatch_key) =
    string_to_identifier (#head_name key) ^ "_locality_dispatch_"
      ^ Int.toString (#arity key) ^ "_simproc"

  val left_generated_name =
    locality_dispatch_simproc_name left_key
  val right_generated_name =
    locality_dispatch_simproc_name right_key

  fun has_relative_name relative_name full_name =
    let
      val relative_components = Long_Name.explode relative_name
      val full_components = Long_Name.explode full_name
      val prefix_count =
        length full_components - length relative_components
    in
      prefix_count >= 0
      andalso drop prefix_count full_components = relative_components
    end

  val inventory =
    LocalityDispatcherInventory.get (Context.Proof ctxt)

  fun require_inventory_entry label key =
    (case LocalityDispatchKeyTable.lookup inventory key of
       SOME entry => entry
     | _ => error ("Missing dispatcher-name inventory entry " ^ label))

  val left_inventory_entry =
    require_inventory_entry "left" left_key
  val right_inventory_entry =
    require_inventory_entry "right" right_key
  val left_alias = #alias left_inventory_entry
  val right_alias = #alias right_inventory_entry
  val left_source_name = #source_name left_inventory_entry
  val right_source_name = #source_name right_inventory_entry
  val family_inventory_entries =
    LocalityDispatchKeyTable.dest inventory
    |> filter (fn (key, _) =>
         locality_dispatch_key_eq (key, left_key)
         orelse locality_dispatch_key_eq (key, right_key))
  val inventory_names =
    [left_alias, right_alias]
  val checked_names =
    map (fn name =>
      #1 (Simplifier.check_simproc ctxt (name, Position.none)))
      inventory_names
  val raw_simprocs =
    Raw_Simplifier.simpset_of ctxt
    |> Raw_Simplifier.dest_ss
    |> #simprocs
  fun raw_count source_name =
    raw_simprocs
    |> filter (fn (name, _) => name = source_name)
    |> length
  val family_raw_count =
    raw_simprocs
    |> filter (fn (name, _) =>
         has_relative_name left_generated_name name
         orelse has_relative_name right_generated_name name)
    |> length

  val near_limit_size = 20000
  val near_limit_prefix =
    String.implode
      (replicate (near_limit_size - 1) #"q")
  val near_limit_component0 = near_limit_prefix ^ "a"
  val near_limit_component1 = near_limit_prefix ^ "b"

  fun near_limit_key component : locality_dispatch_key =
    { head_name =
        Long_Name.implode ["Synthetic", component, "f"],
      arity = 2 }

  val near_limit_key0 =
    near_limit_key near_limit_component0
  val near_limit_key1 =
    near_limit_key near_limit_component1
  val near_limit_binding0 =
    locality_dispatch_simproc_binding near_limit_key0
  val near_limit_binding1 =
    locality_dispatch_simproc_binding near_limit_key1
  val near_limit_name0 =
    locality_dispatch_simproc_name near_limit_key0
  val near_limit_name1 =
    locality_dispatch_simproc_name near_limit_key1
  val near_limit_components0 =
    Long_Name.explode near_limit_name0
  val near_limit_components1 =
    Long_Name.explode near_limit_name1
  val near_limit_spec_name0 =
    #full_name (Binding.name_spec [] [] near_limit_binding0)
  val near_limit_spec_name1 =
    #full_name (Binding.name_spec [] [] near_limit_binding1)
  val near_limit_full_name0 =
    Local_Theory.full_name background_lthy near_limit_binding0
  val near_limit_full_name1 =
    Local_Theory.full_name background_lthy near_limit_binding1
  val near_limit_chunks0 =
    Long_Name.make_chunks near_limit_full_name0
  val near_limit_chunks1 =
    Long_Name.make_chunks near_limit_full_name1
  val near_limit_payload_count0 =
    near_limit_components0
    |> filter (String.isPrefix "c1_p")
    |> length
  val near_limit_payload_count1 =
    near_limit_components1
    |> filter (String.isPrefix "c1_p")
    |> length

  val _ = AutoLocality_Assert.run_suite
    "Boundaries/dispatcher-name-encoding"
    [ ("fixture has the intended distinct qualified heads",
         fn () => AutoLocality_Assert.check "qualified collision heads"
           (#head_name left_key = left_head
            andalso #head_name right_key = right_head
            andalso #arity left_key = 2
            andalso #arity right_key = 2)),
      ("the former flattened physical names collide",
         fn () => AutoLocality_Assert.check "old physical-name collision"
           (old_dispatch_name left_key =
            old_dispatch_name right_key)),
      ("semantic and dispatch keys remain distinct",
         fn () => AutoLocality_Assert.check "distinct registrations"
           (not (locality_operational_key_eq
              (#key left_entry, #key right_entry))
            andalso not (locality_dispatch_key_eq
              (left_key, right_key)))),
      ("complete-key encodings generate distinct names",
         fn () => AutoLocality_Assert.check "injective dispatcher names"
           (left_generated_name <> right_generated_name)),
      ("near-limit keys split into bounded binding components",
         fn () => AutoLocality_Assert.check "bounded dispatcher binding"
           (size near_limit_component0 = near_limit_size
            andalso size near_limit_component1 = near_limit_size
            andalso size near_limit_name0 > 32768
            andalso size near_limit_name1 > 32768
            andalso near_limit_payload_count0 > 1
            andalso near_limit_payload_count1 > 1
            andalso forall
              (fn component => size component < 32768)
              (near_limit_components0 @ near_limit_components1)
            andalso forall Symbol_Pos.is_identifier
              (near_limit_components0 @ near_limit_components1)
            andalso forall (fn (_, mandatory) => mandatory)
              (Binding.path_of near_limit_binding0
                @ Binding.path_of near_limit_binding1)
            andalso Long_Name.implode_chunks near_limit_chunks0 =
              near_limit_full_name0
            andalso Long_Name.implode_chunks near_limit_chunks1 =
              near_limit_full_name1)),
      ("near-limit last-byte variants retain distinct bindings",
         fn () => AutoLocality_Assert.check "injective bounded binding"
           (near_limit_component0 <> near_limit_component1
            andalso near_limit_binding0 <> near_limit_binding1
            andalso near_limit_name0 <> near_limit_name1
            andalso near_limit_spec_name0 = near_limit_name0
            andalso near_limit_spec_name1 = near_limit_name1
            andalso Binding.long_name_of near_limit_binding0 =
              near_limit_name0
            andalso Binding.long_name_of near_limit_binding1 =
              near_limit_name1
            andalso near_limit_full_name0 <> near_limit_full_name1
            andalso has_relative_name near_limit_name0
              near_limit_full_name0
            andalso has_relative_name near_limit_name1
              near_limit_full_name1)),
      ("both families retain one local inventory identity",
         fn () => AutoLocality_Assert.check "two inventory identities"
           (length family_inventory_entries = 2
            andalso has_relative_name
              left_generated_name left_alias
            andalso has_relative_name
              right_generated_name right_alias
            andalso left_alias <> right_alias)),
      ("both representative names resolve with one raw dispatcher each",
         fn () => AutoLocality_Assert.check "two raw dispatchers"
           (checked_names = inventory_names
            andalso raw_count left_source_name = 1
            andalso raw_count right_source_name = 1
            andalso family_raw_count = 2)) ]
\<close>

subsection\<open>Lossy public-name collisions are rejected before proof setup\<close>

definition policy'a :: \<open>boundary_rec \<Rightarrow> boundary_rec\<close> where
  \<open>policy'a R \<equiv> update_ba Suc R\<close>

definition policyPa :: \<open>boundary_rec \<Rightarrow> boundary_rec\<close> where
  \<open>policyPa R \<equiv> update_bb Suc R\<close>

locality_lemma for boundary_rec: \<open>policy'a\<close> footprint [ba] .

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_Assert.run_suite "Boundaries/public-name-collision"
    [ ("distinct typed patterns with one generated id are rejected",
         fn () => AutoLocality_Assert.assert_raises "generated public id collision"
           (fn () =>
             state_locality NONE "boundary_rec" "policyPa" ["bb"] true 0 ctxt)) ]
\<close>

subsection\<open>Conflicting context merges fail loudly\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"
  val entry =
    hd (get_record_locality_entries_for_const rec_name
      "AutoLocality_Test_Boundaries.policy'a" ctxt)
  val conflict : locality_entry =
    { key = #key entry,
      const_name = #const_name entry,
      pattern = #pattern entry,
      footprint = ["bb"],
      field = #field entry,
      core_thms = #core_thms entry,
      disjoint_thms = #disjoint_thms entry,
      local_thm = #local_thm entry }

  fun polymorphic_var type_name var_name =
    Var ((var_name, 0),
      TVar ((type_name, 0), \<^sort>\<open>type\<close>))

  fun reflexive_certificate term =
    Thm.reflexive (Thm.cterm_of ctxt term)

  fun synthetic_entry const_name pattern core_thms =
    make_locality_entry rec_name Locality_Attribute
      const_name pattern [] ["ba"] 0 0 false
      core_thms [] NONE

  val alpha_pattern0 = polymorphic_var "'alpha" "pattern_x"
  val alpha_pattern1 = polymorphic_var "'beta" "pattern_y"
  val alpha_entry0 =
    synthetic_entry "alpha_bundle" alpha_pattern0
      [reflexive_certificate alpha_pattern0]
  val alpha_entry1 =
    synthetic_entry "alpha_bundle" alpha_pattern1
      [reflexive_certificate alpha_pattern1]
  val sharing_conflict =
    synthetic_entry "alpha_bundle" alpha_pattern1
      [reflexive_certificate
        (polymorphic_var "'beta" "certificate_z")]

  fun hidden_prop binder_name reflexive =
    let
      val bound = Free (binder_name, \<^typ>\<open>nat\<close>)
      val rhs =
        if reflexive then bound else \<^term>\<open>0 :: nat\<close>
      val body =
        HOLogic.mk_Trueprop (HOLogic.mk_eq (bound, rhs))
    in
      Logic.all_const \<^typ>\<open>nat\<close> $
        Term.lambda_name (binder_name, bound) body
    end

  val hidden_conclusion = \<^prop>\<open>True\<close>

  fun hidden_only_certificate (binder0, binder1) =
    let
      val prop0 = hidden_prop binder0 true
      val prop1 = hidden_prop binder1 false
      val implication =
        Logic.mk_implies
          (prop0, Logic.mk_implies (prop1, hidden_conclusion))
      val implication_thm =
        Thm.assume (Thm.cterm_of ctxt implication)
      val prop0_thm =
        Thm.assume (Thm.cterm_of ctxt prop0)
      val prop1_thm =
        Thm.assume (Thm.cterm_of ctxt prop1)
    in
      Thm.implies_elim implication_thm prop0_thm
      |> (fn thm => Thm.implies_elim thm prop1_thm)
    end

  val hidden_pattern = \<^term>\<open>True\<close>
  val hidden_certificate0 =
    hidden_only_certificate
      ("hidden_zeta", "hidden_alpha")
  val hidden_certificate1 =
    hidden_only_certificate
      ("hidden_beta", "hidden_omega")
  val hidden_hyps0 = Thm.hyps_of hidden_certificate0
  val hidden_hyps1 = Thm.hyps_of hidden_certificate1

  fun has_no_schematic_variables terms =
       null (fold Term.add_vars terms [])
    andalso null (fold Term.add_tvars terms [])

  val hidden_entry0 =
    synthetic_entry "hidden_bundle" hidden_pattern
      [hidden_certificate0]
  val hidden_entry1 =
    synthetic_entry "hidden_bundle" hidden_pattern
      [hidden_certificate1]

  fun merge_entries (entry0, entry1) =
    merge_locality_entry_lists ([entry0], [entry1])

  fun assert_single_merge expected entries =
    AutoLocality_Assert.check "one compatible merged bundle"
      (case entries of
         [merged] =>
           locality_entry_certificate_fingerprint_ord
             (locality_entry_certificate_fingerprint expected,
              locality_entry_certificate_fingerprint merged) = EQUAL
       | _ => false)

  val _ = AutoLocality_Assert.run_suite "Boundaries/strict-merge"
    [ ("hidden fixture uses closed alpha-renamed assumptions",
         fn () => AutoLocality_Assert.check "hidden-binder fixture"
           (Term.aconv
              (Thm.full_prop_of hidden_certificate0, hidden_conclusion)
            andalso Term.aconv
              (Thm.full_prop_of hidden_certificate1, hidden_conclusion)
            andalso not (null hidden_hyps0)
            andalso has_no_schematic_variables hidden_hyps0
            andalso has_no_schematic_variables hidden_hyps1
            andalso eq_set Term.aconv (hidden_hyps0, hidden_hyps1)
            andalso not (eq_set (op =) (hidden_hyps0, hidden_hyps1)))),
      ("alpha-renamed pattern and certificates merge left-first",
         fn () => assert_single_merge
           alpha_entry0
           (merge_entries (alpha_entry0, alpha_entry1))),
      ("alpha-renamed pattern and certificates merge right-first",
         fn () => assert_single_merge
           alpha_entry0
           (merge_entries (alpha_entry1, alpha_entry0))),
      ("hidden-hypothesis binder renaming merges left-first",
         fn () => assert_single_merge
           hidden_entry0
           (merge_entries (hidden_entry0, hidden_entry1))),
      ("hidden-hypothesis binder renaming merges right-first",
         fn () => assert_single_merge
           hidden_entry0
           (merge_entries (hidden_entry1, hidden_entry0))),
      ("changed pattern-certificate sharing rejects left-first",
         fn () => AutoLocality_Assert.assert_raises "sharing conflict"
           (fn () => merge_entries (alpha_entry0, sharing_conflict))),
      ("changed pattern-certificate sharing rejects right-first",
         fn () => AutoLocality_Assert.assert_raises "sharing conflict"
           (fn () => merge_entries (sharing_conflict, alpha_entry0))),
      ("same typed slot with a different footprint rejects left-first",
         fn () => AutoLocality_Assert.assert_raises "conflicting merge"
           (fn () => merge_entries (entry, conflict))),
      ("same typed slot with a different footprint rejects right-first",
         fn () => AutoLocality_Assert.assert_raises "conflicting merge"
           (fn () => merge_entries (conflict, entry))) ]
\<close>

subsection\<open>Physical dispatcher families merge by dispatch key\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"
  val source_entry =
    the (select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>boundary_attr\<close>)
  val dispatch_key =
    locality_dispatch_key_of_entry ctxt source_entry
  fun singleton key source_name alias =
    LocalityDispatchKeyTable.update
      (key,
       { source_name = source_name,
         alias = alias } :
         locality_dispatcher_inventory_entry)
      LocalityDispatchKeyTable.empty

  val left =
    singleton dispatch_key "z.source" "alias.left"
  val right =
    singleton dispatch_key "a.source" "alias.right"
  val merged_lr =
    merge_locality_dispatcher_inventories
      (left, right)
  val merged_rl =
    merge_locality_dispatcher_inventories
      (right, left)
  fun merged_alias inventory =
    (case LocalityDispatchKeyTable.lookup inventory dispatch_key of
       SOME entry => #alias entry
     | NONE => "")
  fun merged_source_name inventory =
    (case LocalityDispatchKeyTable.lookup inventory dispatch_key of
       SOME entry => #source_name entry
     | NONE => "")
  val _ = AutoLocality_Assert.run_suite
    "Boundaries/dispatcher-key-merge"
    [ ("same-key names and aliases choose deterministic representatives",
         fn () => AutoLocality_Assert.check
           "same-key representatives"
           (merged_source_name merged_lr = "a.source"
            andalso
            merged_source_name merged_rl = "a.source"
            andalso
            merged_alias merged_lr = "alias.left"
            andalso
            merged_alias merged_rl = "alias.left")),
      ("same-key merges retain both branch-independent entries",
         fn () => AutoLocality_Assert.check
           "same-key merge"
           (LocalityDispatchKeyTable.size merged_lr = 1
            andalso
            LocalityDispatchKeyTable.size merged_rl = 1)) ]
\<close>

subsection\<open>Semantic replay is independent of dispatcher inventory\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"
  val source_entry =
    the (select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>boundary_attr\<close>)
  val probe_rec_name = rec_name ^ ".Semantic_Replay_Probe"
  val probe_entry =
    make_locality_entry probe_rec_name
      (locality_entry_kind source_entry)
      (#const_name source_entry) (#pattern source_entry)
      (locality_entry_flexible_prefix source_entry)
      (#footprint source_entry)
      (locality_entry_args source_entry)
      (locality_entry_idx source_entry)
      (#field source_entry)
      (#core_thms source_entry)
      (#disjoint_thms source_entry)
      (#local_thm source_entry)
  val descriptor = locality_entry_descriptor probe_entry
  val facts = locality_entry_fact_bundle ctxt probe_entry
  val (run_id, counted_ctxt) =
    AutoLocality_Instrumentation.start_run ctxt
  val probe_context =
    Context.Proof counted_ctxt
    |> LocalityDispatcherInventory.put
         LocalityDispatchKeyTable.empty
  val replayed_context =
    replay_locality_registration probe_rec_name descriptor facts
      Morphism.identity probe_context
  val replayed_entries =
    get_record_locality_entries_generic
      probe_rec_name replayed_context
  val indexed_keys =
    Symtab.lookup
      (#records (LocalitySecondaryIndex.get replayed_context))
      probe_rec_name
    |> Option.map LocalityOperationalKeyTable.keys
    |> the_default []
  val snapshot =
    (case AutoLocality_Instrumentation.freeze_run run_id of
       SOME value => value
     | NONE => error "Semantic-replay run did not freeze")
  val _ =
    if AutoLocality_Instrumentation.drop_run run_id then ()
    else error "Semantic-replay run did not drop"
  fun counter name =
    AutoLocality_Instrumentation.snapshot_counter snapshot name
  val _ = AutoLocality_Assert.run_suite
    "Boundaries/semantic-dispatch-separation"
    [ ("semantic replay succeeds with an empty dispatcher inventory",
         fn () => AutoLocality_Assert.check "independent semantic replay"
           (case replayed_entries of
              [entry] =>
                locality_operational_key_eq
                  (#key entry, #key probe_entry)
            | _ => false)),
      ("semantic replay updates only semantic and secondary data",
         fn () => AutoLocality_Assert.check "separate physical inventory"
           (LocalityDispatchKeyTable.is_empty
              (LocalityDispatcherInventory.get replayed_context)
            andalso indexed_keys = [#key probe_entry])),
      ("semantic replay records one insertion",
         fn () => AutoLocality_Assert.check "semantic replay counters"
           (counter
              AutoLocality_Instrumentation.Lifecycle_Semantic_Insertions = 1
            andalso counter
              AutoLocality_Instrumentation.Lifecycle_Replays = 0
            andalso counter AutoLocality_Instrumentation.Index_Nodes = 5
            andalso counter
              AutoLocality_Instrumentation.Index_Secondary_Insertions = 1)) ]
\<close>

subsection\<open>Ranked structural lookup narrows payload loading\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"
  val const_name =
    "AutoLocality_Test_Boundaries.boundary_rank_attr"
  val selected_pattern =
    \<^term>\<open>boundary_rank_attr (0 :: nat)\<close>
  val exact_head = Term.head_of selected_pattern
  val schematic_pattern =
    exact_head $ Var (("rank_argument", 0), \<^typ>\<open>nat\<close>)
  val flexible_pattern = selected_pattern
  val short_pattern = exact_head
  val polymorphic_type =
    TVar (("'rank", 0), \<^sort>\<open>type\<close>)
  val polymorphic_head =
    Const (const_name,
      polymorphic_type --> \<^typ>\<open>boundary_rec\<close> -->
        \<^typ>\<open>bool\<close>)
  val polymorphic_pattern =
    polymorphic_head $
      Var (("rank_polymorphic_argument", 0), polymorphic_type)
  val ambiguous_const_name =
    "AutoLocality_Test_Boundaries.boundary_rank_attr2"

  fun rank_entry entry_const_name pattern flexible_prefix footprint args idx =
    make_locality_entry rec_name Locality_Attribute entry_const_name
      pattern flexible_prefix footprint args idx false [] [] NONE

  val selected_entry =
    rank_entry const_name selected_pattern [false] ["ba"] 1 0
  val same_rank_decoy =
    rank_entry const_name schematic_pattern [false] ["bb"] 1 0
  val flexible_decoy =
    rank_entry const_name flexible_pattern [true] ["bb"] 1 0
  val short_decoy =
    rank_entry const_name short_pattern [] ["bb"] 2 1
  val polymorphic_decoy =
    rank_entry const_name polymorphic_pattern [false] ["bb"] 1 0

  fun insert_rank_entry entry context =
    context
    |> RecordLocalityData.map (insert_locality_entry entry)
    |> LocalitySecondaryIndex.map
         (insert_locality_secondary_key entry)

  val ranked_ctxt =
    fold insert_rank_entry
      [selected_entry, same_rank_decoy, flexible_decoy,
       short_decoy, polymorphic_decoy]
      (Context.Proof ctxt)
    |> Context.proof_of
  val application =
    \<^term>\<open>boundary_rank_attr (0 :: nat) R\<close>
  val (head, args) = Term.strip_comb application
  val (run_id, counted_ctxt) =
    AutoLocality_Instrumentation.start_run ranked_ctxt
  val selected_result =
    Exn.capture (fn () =>
      select_locality_entry_kind_with
        (locality_direct_counter counted_ctxt)
        counted_ctxt rec_name Locality_Attribute head args) ()
  val inferred_result =
    Exn.capture (fn () =>
      select_locality_entry_for_explicit_pattern_with
        locality_no_count
        counted_ctxt rec_name Locality_Attribute
        selected_pattern NONE) ()
  val inferred_at_idx_result =
    Exn.capture (fn () =>
      select_locality_entry_for_explicit_pattern_with
        locality_no_count
        counted_ctxt rec_name Locality_Attribute
        selected_pattern (SOME 1)) ()
  val ambiguous_pattern =
    Syntax.read_term ctxt "boundary_rank_attr2 (0 :: nat)"
  val ambiguous_entry =
    rank_entry ambiguous_const_name ambiguous_pattern [false] ["ba"] 1 0
  val ambiguous_entry_conflict =
    rank_entry ambiguous_const_name ambiguous_pattern [false] ["bb"] 2 0
  val ambiguous_ctxt =
    fold insert_rank_entry
      [ambiguous_entry, ambiguous_entry_conflict]
      (Context.Proof ctxt)
    |> Context.proof_of
  val ambiguous_inference_result =
    Exn.capture (fn () =>
      select_locality_entry_for_explicit_pattern_with
        locality_no_count
        ambiguous_ctxt rec_name Locality_Attribute
        ambiguous_pattern NONE) ()
  val ambiguity_capture_result =
    Exn.capture (fn () =>
      capture_noninterrupt (fn () =>
        locality_registry_ambiguity "boundary test")) ()
  val snapshot =
    (case AutoLocality_Instrumentation.freeze_run run_id of
       SOME snapshot => snapshot
     | NONE => error "Missing ranked lookup snapshot")
  val _ =
    if AutoLocality_Instrumentation.drop_run run_id then ()
    else error "Failed to drop ranked lookup instrumentation run"
  val selected = Exn.release selected_result

  fun counter counter =
    AutoLocality_Instrumentation.snapshot_counter snapshot counter

  val _ = AutoLocality_Assert.run_suite "Boundaries/query-ranking"
    [ ("exact rigid longest registration wins over all decoys",
         fn () => AutoLocality_Assert.check "ranked registration"
           (case selected of
              SOME (1, entry) =>
                #footprint entry = ["ba"]
                andalso Term.aconv (#pattern entry, selected_pattern)
            | _ => false)),
      ("only the exact winner reaches authoritative payload loading",
         fn () => AutoLocality_Assert.check "narrowed payload counters"
           (counter AutoLocality_Instrumentation.Lookup_Requests = 1
            andalso
            counter AutoLocality_Instrumentation.Lookup_Entries_Examined = 1
            andalso
            counter AutoLocality_Instrumentation.Lookup_Candidates_Returned = 1
            andalso
            counter AutoLocality_Instrumentation.Lookup_Comparisons = 0
            andalso
            counter AutoLocality_Instrumentation.Lookup_Specializations = 1
            andalso
            counter AutoLocality_Instrumentation.Lookup_Prefix_Alternatives = 2
            andalso
            counter AutoLocality_Instrumentation.Lookup_Equality_Attempts = 0)),
      ("inferred pattern selection follows the ranked index",
         fn () => AutoLocality_Assert.check "ranked inferred registration"
           (case inferred_result of
              Exn.Res (SOME entry) =>
                #footprint entry = ["ba"]
                andalso Term.aconv (#pattern entry, selected_pattern)
            | _ => false)),
      ("inferred selection preserves the absolute slot constraint",
         fn () => AutoLocality_Assert.check "ranked inferred slot"
           (case inferred_at_idx_result of
              Exn.Res (SOME entry) =>
                #footprint entry = ["ba"]
                andalso locality_entry_absolute_idx entry = 1
            | _ => false)),
      ("registry ambiguity uses a dedicated exception",
         fn () => AutoLocality_Assert.check "typed registry ambiguity"
           (case ambiguous_inference_result of
              Exn.Exn (Locality_Registry_Ambiguity _) => true
            | _ => false)),
      ("generic exception capture preserves registry ambiguity",
         fn () => AutoLocality_Assert.check "captured registry ambiguity"
           (case ambiguity_capture_result of
              Exn.Exn (Locality_Registry_Ambiguity _) => true
            | _ => false)),
      ("generic exception capture preserves registry ambiguity",
         fn () => AutoLocality_Assert.check "captured registry ambiguity"
           (case ambiguity_capture_result of
              Exn.Exn (Locality_Registry_Ambiguity _) => true
            | _ => false)) ]
\<close>

subsection\<open>Malformed and nonmatching terms decline quickly\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Boundaries.boundary_rec"
  val entry =
    the (select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>boundary_attr\<close>)
  val unrelated = Thm.cterm_of ctxt \<^term>\<open>True\<close>
  fun declines () =
    case locality_cancellation_simproc_for_entry rec_name entry ctxt unrelated of
      NONE => true
    | SOME _ => false
  val batch_declines =
    Timeout.apply (Time.fromSeconds 2)
      (fn () => List.all (K (declines ())) (1 upto 2000)) ()
    handle Timeout.TIMEOUT _ => false
  val _ = AutoLocality_Assert.run_suite "Boundaries/exception-containment"
    [ ("malformed direct invocation returns NONE",
         fn () => AutoLocality_Assert.check "malformed decline" (declines ())),
      ("2000 nonmatching invocations finish within two seconds",
         fn () => AutoLocality_Assert.check "nonmatching workload"
           batch_declines) ]
\<close>

(*<*)
end
(*>*)
