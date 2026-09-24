(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Polymorphic
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Sort-constrained polymorphic records and definitions\<close>

datatype_record ('a::linorder, 'b::monoid_add) poly =
  pkey :: 'a
  pacc :: 'b
  pflag :: bool

locality_init for poly

definition poly_raise_key ::
    \<open>'a::linorder \<Rightarrow> ('a, 'b::monoid_add) poly \<Rightarrow> ('a, 'b) poly\<close>
  where
  \<open>poly_raise_key k R \<equiv> update_pkey (max k) R\<close>

definition poly_add_acc ::
    \<open>'b::monoid_add \<Rightarrow> ('a::linorder, 'b) poly \<Rightarrow> ('a, 'b) poly\<close>
  where
  \<open>poly_add_acc n R \<equiv> update_pacc (\<lambda>x. x + n) R\<close>

definition poly_set_flag ::
    \<open>bool \<Rightarrow> ('a::linorder, 'b::monoid_add) poly \<Rightarrow> ('a, 'b) poly\<close>
  where
  \<open>poly_set_flag b R \<equiv> update_pflag (\<lambda>_. b) R\<close>

definition poly_key_le ::
    \<open>'a::linorder \<Rightarrow> ('a, 'b::monoid_add) poly \<Rightarrow> bool\<close>
  where
  \<open>poly_key_le k R \<equiv> pkey R \<le> k\<close>

definition poly_acc_eq ::
    \<open>'b::monoid_add \<Rightarrow> ('a::linorder, 'b) poly \<Rightarrow> bool\<close>
  where
  \<open>poly_acc_eq n R \<equiv> pacc R = n\<close>

locality_lemma for poly: \<open>poly_raise_key\<close> footprint [pkey] .
locality_lemma for poly: \<open>poly_add_acc\<close> footprint [pacc] .
locality_lemma for poly: \<open>poly_set_flag\<close> footprint [pflag] .
locality_lemma for poly: \<open>poly_key_le\<close> footprint [pkey] .
locality_lemma for poly: \<open>poly_acc_eq\<close> footprint [pacc] .

lemma \<open>poly_key_le k (poly_add_acc n (poly_set_flag b R)) = poly_key_le k R\<close>
  by simp

lemma \<open>poly_acc_eq n (poly_raise_key k (poly_set_flag b R)) = poly_acc_eq n R\<close>
  by simp

lemma \<open>pflag (poly_add_acc n (poly_raise_key k R)) = pflag R\<close>
  by simp

lemma
  fixes R :: \<open>(nat, nat) poly\<close>
  shows \<open>poly_key_le 3 (poly_add_acc 5 (poly_set_flag True R)) =
    poly_key_le 3 R\<close>
  by simp

subsection\<open>Locale assumptions retain their fixed type parameters\<close>

datatype_record ('a::linorder, 'phantom) locale_poly =
  locale_payload :: 'a
  locale_mark :: bool

locality_init for locale_poly

definition locale_payload_touch ::
    \<open>'tag \<Rightarrow> ('a::linorder, 'phantom) locale_poly \<Rightarrow>
      ('a, 'phantom) locale_poly\<close> where
  \<open>locale_payload_touch _ R \<equiv> update_locale_payload id R\<close>

locality_lemma for locale_poly:
  \<open>locale_payload_touch\<close> footprint [locale_payload] .

subsection\<open>One operation at distinct phantom specializations\<close>

lemma locale_payload_phantom_schedule:
  fixes R :: \<open>(nat, bool) locale_poly\<close>
    and unit_tag :: unit
    and string_tag :: string
  shows \<open>locale_mark
      (locale_payload_touch unit_tag
        (locale_payload_touch string_tag R)) =
    locale_mark R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Polymorphic.locale_poly"
  val sample =
    Syntax.read_term ctxt
      "locale_mark \
      \(locale_payload_touch (unit_tag :: unit) \
      \(locale_payload_touch (string_tag :: string) \
      \(R :: (nat, bool) locale_poly)))"
  val (sample_head, sample_args) = Term.strip_comb sample
  val attribute =
    (case select_locality_entry ctxt rec_name "attribute"
            sample_head sample_args of
       SOME (_, entry) => entry
     | NONE => error "Missing polymorphic locale_mark attribute")
  val operation_entries =
    (case fst (decompose_locality_telescope
            ctxt rec_name attribute sample) of
       _ :: operations => map #1 operations
     | [] => [])
  val same_key =
    (case operation_entries of
       [operation0, operation1] =>
         locality_operational_key_eq
           (#key operation0, #key operation1)
     | _ => false)
  val distinct_typed_patterns =
    (case operation_entries of
       [operation0, operation1] =>
         not (Term.aconv
           (#pattern operation0, #pattern operation1))
     | _ => false)
  val expected_rhs =
    Syntax.read_term ctxt
      "locale_mark \
      \(R :: (nat, bool) locale_poly)"
  val (run_id, run_ctxt) =
    AutoLocality_Instrumentation.start_run ctxt
  val direct_outcome =
    Exn.capture
      (fn () =>
        locality_cancellation_simproc
          rec_name "locale_mark" 0 run_ctxt
          (Thm.cterm_of run_ctxt sample)) ()
  val snapshot_option =
    AutoLocality_Instrumentation.freeze_run run_id
  val dropped =
    AutoLocality_Instrumentation.drop_run run_id
  val snapshot =
    (case snapshot_option of
       SOME value => value
     | NONE => error "Missing polymorphic cancellation snapshot")
  val direct_result = Exn.release direct_outcome
  val direct_rhs_matches =
    (case direct_result of
       SOME thm => Term.aconv
         (Thm.term_of (Thm.rhs_of thm), expected_rhs)
     | NONE => false)
  val clean_freeze =
    AutoLocality_Instrumentation.snapshot_phase snapshot =
      AutoLocality_Instrumentation.Frozen
    andalso
      AutoLocality_Instrumentation.snapshot_active_callbacks snapshot = 0
    andalso
      AutoLocality_Instrumentation.snapshot_async_leases snapshot = 0
  val exact_root_rewrites =
    AutoLocality_Instrumentation.snapshot_counter snapshot
      AutoLocality_Instrumentation.Planner_Root_Rewrites = 2
  val _ = AutoLocality_Assert.run_suite
    "Polymorphic/phantom-specialization-schedule"
    [ ("two operation occurrences are decomposed",
         fn () => AutoLocality_Assert.check "two operations"
           (length operation_entries = 2)),
      ("operation occurrences share one operational key",
         fn () => AutoLocality_Assert.check "same operational key"
           same_key),
      ("operation occurrences retain distinct typed patterns",
         fn () => AutoLocality_Assert.check "distinct typed patterns"
           distinct_typed_patterns),
      ("direct cancellation reaches the typed input attribute",
         fn () => AutoLocality_Assert.check "direct cancellation RHS"
           direct_rhs_matches),
      ("direct cancellation schedules exactly two root rewrites",
         fn () => AutoLocality_Assert.check "two root rewrites"
           exact_root_rewrites),
      ("instrumentation run freezes drained",
         fn () => AutoLocality_Assert.check "clean freeze"
           clean_freeze),
      ("instrumentation run drops",
         fn () => AutoLocality_Assert.check "clean drop"
           dropped) ]
\<close>

locale polymorphic_locale =
  fixes witness :: \<open>'a::linorder\<close>
  assumes witness_bound: \<open>witness \<le> witness\<close>
begin

definition locale_marked :: \<open>('a, 'phantom) locale_poly \<Rightarrow> bool\<close> where
  \<open>locale_marked R \<equiv> locale_mark R\<close>

end

context polymorphic_locale begin

locality_lemma for locale_poly: \<open>locale_marked\<close> footprint [locale_mark] .

lemma \<open>locale_mark (update_locale_payload f R) = locale_mark R\<close>
  by simp

lemma \<open>locale_marked (update_locale_payload f R) = locale_marked R\<close>
  by simp

end

global_interpretation polymorphic_nat:
  polymorphic_locale \<open>0 :: nat\<close>
  by standard simp

global_interpretation polymorphic_int:
  polymorphic_locale \<open>0 :: int\<close>
  by standard simp

lemma polymorphic_locale_nat_interpretation:
  fixes R :: \<open>(nat, bool) locale_poly\<close>
  shows \<open>polymorphic_nat.locale_marked
      (locale_payload_touch () R) =
    polymorphic_nat.locale_marked R\<close>
  by (simp only: [[locality_cancel]])

lemma polymorphic_locale_int_interpretation:
  fixes R :: \<open>(int, unit) locale_poly\<close>
  shows \<open>polymorphic_int.locale_marked
      (locale_payload_touch True R) =
    polymorphic_int.locale_marked R\<close>
  by (simp only: [[locality_cancel]])

ML\<open>
  val ctxt = \<^context>
  val rec_name =
    "AutoLocality_Test_Polymorphic.locale_poly"
  val head_name =
    "AutoLocality_Test_Polymorphic.polymorphic_locale.locale_marked"
  val semantic_entries =
    get_record_locality_entries rec_name ctxt
    |> filter (fn entry => #const_name entry = head_name)
  val inventory_entries =
    LocalityDispatcherInventory.get (Context.Proof ctxt)
    |> LocalityDispatchKeyTable.dest
    |> filter (fn (key, _) => #head_name key = head_name)
  val physical_shape =
    (case inventory_entries of
       [(_, entry : locality_dispatcher_inventory_entry)] =>
         let
           val checked_alias =
             #1 (Simplifier.check_simproc
               ctxt (#alias entry, Position.none))
           val raw_count =
             Raw_Simplifier.simpset_of ctxt
             |> Raw_Simplifier.dest_ss
             |> #simprocs
             |> filter (fn (name, _) => name = #source_name entry)
             |> length
         in
           checked_alias = #alias entry andalso raw_count = 1
         end
     | _ => false)
  val _ = AutoLocality_Assert.run_suite
    "Polymorphic/distinct-type-interpretations"
    [ ("distinct concrete types retain two semantic entries",
         fn () => AutoLocality_Assert.check
           "typed semantic interpretations"
           (length semantic_entries = 2)),
      ("distinct concrete types share one physical dispatcher",
         fn () => AutoLocality_Assert.check
           "shared polymorphic dispatcher"
           physical_shape) ]
\<close>

ML\<open>
  val ctxt = \<^context>
  val (rec_ty, _) = prepare_rec_name ctxt "poly"
  val sorts_preserved =
    (case rec_ty of
       Type (_, [TVar (_, key_sort), TVar (_, acc_sort)]) =>
         not (null key_sort) andalso not (null acc_sort)
     | _ => false)
  val entries =
    get_record_locality_entries "AutoLocality_Test_Polymorphic.poly" ctxt
  val polymorphic_patterns =
    entries
    |> filter (fn entry =>
         member (op =)
           ["AutoLocality_Test_Polymorphic.poly_raise_key",
            "AutoLocality_Test_Polymorphic.poly_add_acc",
            "AutoLocality_Test_Polymorphic.poly_key_le",
            "AutoLocality_Test_Polymorphic.poly_acc_eq"]
           (#const_name entry))
    |> forall (fn entry => not (null (Term.add_tvars (#pattern entry) [])))
  val _ = AutoLocality_Assert.run_suite "Polymorphic/metadata"
    [ ("record type-variable sorts are retained",
         fn () => AutoLocality_Assert.check "sorts retained" sorts_preserved),
      ("registered patterns remain polymorphic",
         fn () => AutoLocality_Assert.check "polymorphic patterns"
           polymorphic_patterns) ]
\<close>

subsection\<open>Concrete type instances exercise the same registrations\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Polymorphic.poly"
  val sample =
    Syntax.read_term ctxt
      "poly_key_le (3::nat) (poly_add_acc (5::nat) (R::(nat,nat) poly))"
  val (sample_head, sample_args) = Term.strip_comb sample
  val selected_attr =
    select_locality_entry ctxt rec_name "attribute" sample_head sample_args
  val selected_op =
    let
      val (_, attr_args) = Term.strip_comb sample
      val (op_head, op_args) = Term.strip_comb (List.last attr_args)
    in
      select_locality_entry ctxt rec_name "operation" op_head op_args
    end
  val direct_result =
    (case selected_attr of
       SOME (_, entry) =>
         locality_cancellation_simproc_for_entry rec_name entry ctxt
           (Thm.cterm_of ctxt sample)
     | NONE => NONE)
  val _ = AutoLocality_Assert.run_suite "Polymorphic/concrete-selection"
    [ ("concrete attribute selects the polymorphic registration",
         fn () => AutoLocality_Assert.check "concrete attribute selected"
           (Option.isSome selected_attr)),
      ("concrete operation selects the polymorphic registration",
         fn () => AutoLocality_Assert.check "concrete operation selected"
           (Option.isSome selected_op)),
      ("concrete cancellation proof succeeds directly",
         fn () => AutoLocality_Assert.check "concrete cancellation"
           (Option.isSome direct_result)) ]

  val attrs : AutoLocality_Gen.item list =
    [ {name = "poly_key_le", fp = ["pkey"], arg = "(3::nat)"},
      {name = "poly_acc_eq", fp = ["pacc"], arg = "(7::nat)"} ]
  val ops : AutoLocality_Gen.item list =
    [ {name = "poly_raise_key", fp = ["pkey"], arg = "(4::nat)"},
      {name = "poly_add_acc", fp = ["pacc"], arg = "(5::nat)"},
      {name = "poly_set_flag", fp = ["pflag"], arg = "True"} ]
  val count =
    AutoLocality_Gen.run_matrix "Polymorphic/nat-instance" ctxt rec_name
      (Long_Name.base_name o #name) attrs ops 3
      "(R::(nat,nat) poly)"
  val _ = AutoLocality_Assert.check "polymorphic matrix has 78 cases" (count = 78)
\<close>

(*<*)
end
(*>*)
