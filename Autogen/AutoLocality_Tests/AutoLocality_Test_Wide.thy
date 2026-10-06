(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Wide
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Wide-record initialisation cost\<close>

text\<open>This theory is a regression guard for the cost of the \<^emph>\<open>first\<close> @{verbatim \<open>locality_lemma\<close>} on a
record with many fields. That first command implicitly runs @{verbatim \<open>locality_init\<close>}, which
registers a cancellation simproc and proves the three linear lemmas (commutativity, disjointness,
local action) for \<^emph>\<open>every\<close> field update of the record. The record's @{verbatim \<open>record_simps\<close>} set
grows quadratically in the number of fields, so a naive @{verbatim \<open>auto\<close>}-based discharge of those
lemmas made initialisation scale very badly: a ~20-field record took tens of seconds, with the whole
cost attributed (confusingly) to whichever lemma happened to be stated first.

The record below has 21 fields of mixed scalar and list type. \<^verbatim>\<open>wide_concat_lists\<close>
has the shape of the attribute that originally exposed the problem: a projection-only attribute
reading two list-typed fields and concatenating them (footprint of two fields, disjoint from the
rest). The timing guards below assert that initialisation-plus-first-lemma, and each subsequent
lemma, complete well within budget. The bounds are generous tripwires, not tight
benchmarks - they exist to catch an accidental return to super-linear initialisation, not to pin a
particular wall-clock number.\<close>

text\<open>We silence the locality tracer (@{verbatim \<open>locality_trace_level = 0\<close>}): initialising a wide
record fires the per-field simproc-creation trace ~20 times and would otherwise dominate the build
log. Cancellation behaviour is unaffected.\<close>

declare [[locality_trace_level = 0]]

datatype_record wide =
  w_f00 :: nat
  w_f01 :: nat
  w_f02 :: nat
  w_f03 :: \<open>nat list\<close>
  w_f04 :: \<open>nat list\<close>
  w_f05 :: \<open>nat list\<close>
  w_f06 :: \<open>nat list\<close>
  w_f07 :: nat
  w_f08 :: nat
  w_f09 :: nat
  w_f10 :: nat
  w_f11 :: nat
  w_f12 :: nat
  w_f13 :: nat
  w_f14 :: nat
  w_f15 :: \<open>nat list\<close>
  w_f16 :: \<open>nat list\<close>
  w_f17 :: nat
  w_f18 :: nat
  w_f19 :: nat
  w_f20 :: nat

text\<open>The attribute that originally exposed the cost: a projection-only attribute reading two
list-typed fields and concatenating them. Footprint = two of the list-typed fields; this is
disjoint from the other ~19 fields, so initialisation must prove a commutativity and disjointness
lemma against each of them.\<close>

definition wide_concat_lists :: \<open>wide \<Rightarrow> nat list\<close> where
  \<open>wide_concat_lists R \<equiv> w_f05 R @ w_f15 R\<close>

text\<open>The first locality lemma on \<^typ>\<open>wide\<close>: this implicitly triggers initialisation of all field
updates. With the optimised @{verbatim \<open>HOL_basic_ss\<close>}-based discharge this is fast; the timing guard
below pins the regression.\<close>

locality_lemma for wide: wide_concat_lists footprint [w_f05, w_f15] .

text\<open>A couple more attributes on the same record. Initialisation has already happened, so these only
pay for their own lemmas.\<close>

definition wide_f01_plus :: \<open>wide \<Rightarrow> nat\<close> where
  \<open>wide_f01_plus R \<equiv> w_f01 R + 1\<close>
locality_lemma for wide: wide_f01_plus footprint [w_f01] .

definition wide_f20_f00_sum :: \<open>wide \<Rightarrow> nat\<close> where
  \<open>wide_f20_f00_sum R \<equiv> w_f20 R + w_f00 R\<close>
locality_lemma for wide: wide_f20_f00_sum footprint [w_f20, w_f00] .

text\<open>An opaque operation that writes a field from its old value: the local-action lemma for such an
operation genuinely needs record extensionality, so it exercises the @{verbatim \<open>rec.expand\<close>} fallback
of @{verbatim \<open>locality_local_action_tac\<close>} rather than the pure-rewriting fast path.\<close>

definition wide_bump_f01 :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>wide_bump_f01 k R \<equiv> update_w_f01 (\<lambda>old. old + k + w_f01 R) R\<close>
locality_lemma for wide: \<open>wide_bump_f01\<close> footprint [w_f01] .

definition wide_bump_f02 :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>wide_bump_f02 k R \<equiv> update_w_f02 (\<lambda>old. old + k + w_f02 R) R\<close>
locality_lemma for wide: \<open>wide_bump_f02\<close> footprint [w_f02] .

definition wide_take_f05 ::
    \<open>nat \<Rightarrow> nat list \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>wide_take_f05 n xs R \<equiv>
    update_w_f05 (\<lambda>_. take n xs) R\<close>
locality_lemma for wide: \<open>wide_take_f05\<close> footprint [w_f05] .

definition wide_drop_f05 ::
    \<open>nat list \<Rightarrow> nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>wide_drop_f05 xs n R \<equiv>
    update_w_f05 (\<lambda>_. drop n xs) R\<close>
locality_lemma for wide: \<open>wide_drop_f05\<close> footprint [w_f05] .

subsection\<open>Cancellation still works on the wide record\<close>

text\<open>Object-level sanity: the projection attribute cancels disjoint operations under plain
@{term \<open>simp\<close>}, including across the opaque operation (which touches only \<^term>\<open>w_f01\<close>).\<close>

lemma \<open>wide_concat_lists (wide_bump_f01 k (update_w_f00 s R)) = wide_concat_lists R\<close>
  by simp

lemma \<open>w_f20 (wide_bump_f01 k (update_w_f00 (\<lambda>_. s) R)) = w_f20 R\<close>
  by simp

subsection\<open>Buried cancellation across an overlapping update pipeline\<close>

text\<open>The operation cancelled above is already adjacent to the attribute.  The expensive regression
has a different shape: two cancellable opaque operations are separated by a long pipeline of
other opaque operations that overlap the attribute.  The inner operation must first commute
outwards across that pipeline before both operations reach the attribute.

The synthetic goals below preserve that shape on this wide record.  The blockers alternate between
two registered operations with distinct argument orders, and every application has fresh
arguments, so neither theorem deduplication nor term sharing can collapse the pipeline.  Unlike raw
field updates, the blockers carry self-referential local-action certificates, matching the opaque
operations whose normalisation exposed the regression.  The depth-16 case took 11.715 seconds
before the fix.  The permanent four-second gate also checks that the planner derives the two
operation-pair swaps directly instead of rebuilding three whole-telescope record simpsets or
falling back to repeated whole-term rewrites.\<close>

ML\<open>
local

open AutoLocality_Instrumentation

val base_context = \<^context>
val attribute = Syntax.read_term base_context "wide_concat_lists"
val blockers =
  [ Syntax.read_term base_context "wide_take_f05",
    Syntax.read_term base_context "wide_drop_f05" ]
val outer_front = Syntax.read_term base_context "wide_bump_f01"
val inner_front = Syntax.read_term base_context "wide_bump_f02"
val state = Syntax.read_term base_context "R :: wide"
val list_type = HOLogic.listT HOLogic.natT

fun blocked n body =
  fold (fn i => fn inner =>
      let
        val blocker = nth blockers (i mod length blockers)
        val salt = Free ("n" ^ Int.toString i, HOLogic.natT)
        val values = Free ("xs" ^ Int.toString i, list_type)
      in
        if i mod length blockers = 0
        then blocker $ salt $ values $ inner
        else blocker $ values $ salt $ inner
      end)
    (1 upto n) body

fun buried_hoist_goal n =
  let
    val inner_body =
      inner_front $ Free ("inner_k", HOLogic.natT) $ state
    val lhs =
      outer_front
        $ Free ("outer_k", HOLogic.natT)
        $ blocked n inner_body
    val rhs = blocked n state
  in
    HOLogic.mk_Trueprop
      (HOLogic.mk_eq
        (attribute $ lhs, attribute $ rhs))
  end

fun run_buried_hoist n =
  let
    val (run_id, context) = start_run base_context
    val started = Timing.start ()
    val outcome =
      Exn.capture
        (fn () =>
          Timeout.apply (Time.fromSeconds 4)
            (fn () =>
              Goal.prove context [] [] (buried_hoist_goal n)
                (fn {context, ...} =>
                  asm_full_simp_tac context 1)) ()) ()
    val timing = Timing.result started
    val snapshot =
      (case freeze_run run_id of
         SOME result => result
       | NONE => error "Missing buried-hoist instrumentation snapshot")
    val dropped = drop_run run_id
    val _ =
      writeln
        ("Wide/buried-hoist depth " ^ Int.toString n ^ ": "
          ^ Timing.message timing
          ^ "; planner.requests="
          ^ IntInf.toString (snapshot_counter snapshot Planner_Requests)
          ^ "; planner.swap_applications="
          ^ IntInf.toString
              (snapshot_counter snapshot Planner_Swap_Applications)
          ^ "; planner.cancellations="
          ^ IntInf.toString (snapshot_counter snapshot Planner_Cancellations)
          ^ "; planner.root_rewrites="
          ^ IntInf.toString (snapshot_counter snapshot Planner_Root_Rewrites)
          ^ "; record.simpset_builds="
          ^ IntInf.toString (snapshot_counter snapshot Record_Simpset_Builds))
    val _ = Exn.release outcome
    val _ = AutoLocality_Assert.run_suite
      ("Wide/buried-hoist depth " ^ Int.toString n)
      [ ("planner entered",
          fn () => AutoLocality_Assert.check "planner entered"
            (snapshot_counter snapshot Planner_Requests > 0)),
        ("buried operation cancelled",
          fn () => AutoLocality_Assert.check "buried operation cancelled"
            (snapshot_counter snapshot Planner_Cancellations = 2)),
        ("root cancellation applied",
          fn () => AutoLocality_Assert.check "root cancellation applied"
            (snapshot_counter snapshot Planner_Root_Rewrites = 2)),
        ("two operation-pair swaps derived",
          fn () => AutoLocality_Assert.check
            "two operation-pair swaps derived"
            (snapshot_counter snapshot Planner_Swaps = 2)),
        ("all buried crossings use exact swaps",
          fn () => AutoLocality_Assert.check
            "sixteen exact adjacent swaps applied"
            (snapshot_counter snapshot Planner_Swap_Applications = 16)),
        ("avoids whole-telescope simpsets",
          fn () => AutoLocality_Assert.check
            "at most two pair-specific record simpsets"
            (snapshot_counter snapshot Record_Simpset_Builds <= 2)),
        ("avoids fallback rescans",
          fn () => AutoLocality_Assert.check "no fallback rescans"
            (snapshot_counter snapshot Fallback_Requests = 0
              andalso snapshot_counter snapshot Planner_Root_Rescans = 0
              andalso
                snapshot_counter snapshot Fallback_Whole_Term_Rewrites = 0)),
        ("instrumentation run freezes drained",
          fn () => AutoLocality_Assert.check "clean freeze"
            (snapshot_phase snapshot = Frozen
              andalso snapshot_active_callbacks snapshot = 0
              andalso snapshot_async_leases snapshot = 0)),
        ("instrumentation run drops",
          fn () => AutoLocality_Assert.check "clean drop" dropped) ]
  in
    #elapsed timing
  end

in

val _ = run_buried_hoist 16

end
\<close>

subsection\<open>Timing guards: initialisation must not regress to super-linear\<close>

text\<open>Each guard re-states a fresh attribute on a fresh wide record inside its own @{verbatim \<open>context\<close>}
so that we measure a full initialisation-plus-first-lemma, then checks it cancels within budget. The
4s budget is a tripwire: the optimised path finishes this in well under a second, whereas the old
@{verbatim \<open>auto\<close>}-based initialisation took tens of seconds on a record this wide.\<close>

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_Assert.run_suite "Wide/cancellation-within-budget"
    [ ("concat over disjoint op", fn () =>
         AutoLocality_Assert.check "concat/bump"
           (AutoLocality_Assert.cancels_within ctxt 4000
              "wide_concat_lists (wide_bump_f01 k (update_w_f00 s R)) = wide_concat_lists R")),
      ("projection over deep disjoint nest", fn () =>
         AutoLocality_Assert.check "f20/deep"
           (AutoLocality_Assert.cancels_within ctxt 4000
              "w_f20 (update_w_f01 (\<lambda>_. a) (update_w_f02 (\<lambda>_. b) (update_w_f00 (\<lambda>_. c) R))) = w_f20 R")),
      ("multi-field projection", fn () =>
         AutoLocality_Assert.check "f20_f00_sum/disjoint"
           (AutoLocality_Assert.cancels_within ctxt 4000
              "wide_f20_f00_sum (update_w_f01 (\<lambda>_. a) R) = wide_f20_f00_sum R")) ]
\<close>

text\<open>The three linear lemmas exist for the registered operations and attributes, confirming
initialisation actually ran and registered footprints (rather than silently skipping a field whose
local-action proof failed - the failure mode that a @{verbatim \<open>SOLVED'\<close>}-less local-action tactic
would produce on the opaque operation).\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_id = "AutoLocality_Test_Wide_wide"
  val _ = AutoLocality_Assert.run_suite "Wide/lemmas-registered"
    [ ("concat attr lemma",   fn () => AutoLocality_Assert.assert_attr_lemmas ctxt rec_id "wide_concat_lists" 0),
      ("opaque op lemmas",    fn () => AutoLocality_Assert.assert_op_lemmas ctxt rec_id "wide_bump_f01"),
      ("opaque op core card", fn () => AutoLocality_Assert.assert_fact_card ctxt
          (rec_id ^ "_local_op_wide_bump_f01_core") 20),
      ("opaque op disjoint card", fn () => AutoLocality_Assert.assert_fact_card ctxt
          (rec_id ^ "_local_op_wide_bump_f01_disjoint") 20),
      ("opaque op local card", fn () => AutoLocality_Assert.assert_fact_card ctxt
          (rec_id ^ "_local_op_wide_bump_f01_local") 1),
      ("no quadratic bundle", fn () => AutoLocality_Assert.assert_no_quadratic ctxt rec_id) ]
\<close>

(*<*)
end
(*>*)
