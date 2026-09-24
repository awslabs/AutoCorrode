(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Perf
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Performance guards for on-the-fly cancellation\<close>

text\<open>On-the-fly cancellation re-derives each rewrite with a tactic, so a pathological term could in
principle be slow. This suite bounds the cost: deep telescopes of footprint-disjoint operations, and
wide footprints with several attributes, must all cancel well within a few seconds. Each case is run
through @{verbatim \<open>cancels_within\<close>}, which fails on timeout. The bounds are generous (4s) - they are a
regression tripwire against accidental blow-up, not a tight benchmark.\<close>

datatype_record perf =
  qa :: nat
  qb :: nat
  qc :: nat
  qd :: nat

locality_init for perf

definition pset_a :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where \<open>pset_a k \<equiv> update_qa (\<lambda>_. k)\<close>
definition pset_b :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where \<open>pset_b k \<equiv> update_qb (\<lambda>_. k)\<close>
definition pset_c :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where \<open>pset_c k \<equiv> update_qc (\<lambda>_. k)\<close>
definition pset_d :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where \<open>pset_d k \<equiv> update_qd (\<lambda>_. k)\<close>
\<comment>\<open>An opaque operation on \<open>qc\<close> whose body uses the old value.\<close>
definition pbump_c :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where \<open>pbump_c k R \<equiv> update_qc (\<lambda>old. old + k + qc R) R\<close>
definition pdelegate_c :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where
  \<open>pdelegate_c k R \<equiv> pbump_c k R\<close>
\<comment>\<open>Only the \<open>True\<close> specialization is registered. The delegate below calls \<open>False\<close>, so
helper suppression must inspect the actual application and unfold the unmatched helper body.\<close>
definition pspecial_c :: \<open>bool \<Rightarrow> nat \<Rightarrow> perf \<Rightarrow> perf\<close> where
  \<open>pspecial_c mode k R \<equiv>
    update_qc (\<lambda>old. if mode then old + k else old + k + 1) R\<close>
definition pdelegate_special_c :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where
  \<open>pdelegate_special_c k R \<equiv> pspecial_c False k R\<close>
\<comment>\<open>The custom-attributed helper has certificates in the semantic registry but not in the
record's default locality-facts bundle. Its delegate must use those theorem objects directly.\<close>
definition pcustom_c :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where
  \<open>pcustom_c k R \<equiv> update_qc (\<lambda>old. old + k + qc R) R\<close>
definition pdelegate_custom_c :: \<open>nat \<Rightarrow> perf \<Rightarrow> perf\<close> where
  \<open>pdelegate_custom_c k R \<equiv> pcustom_c k R\<close>
\<comment>\<open>Attribute on \<open>qd\<close>: disjoint from all of pset_a/pset_b/pset_c/pbump_c.\<close>
definition phas_d :: \<open>perf \<Rightarrow> bool\<close> where \<open>phas_d R \<equiv> qd R > 0\<close>

named_theorems perf_custom_locality

locality_lemma for perf: \<open>pset_a\<close> footprint [qa] .
locality_lemma for perf: \<open>pset_b\<close> footprint [qb] .
locality_lemma for perf: \<open>pset_c\<close> footprint [qc] .
locality_lemma for perf: \<open>pset_d\<close> footprint [qd] .
locality_lemma for perf: \<open>pbump_c\<close> footprint [qc] .
locality_lemma for perf: \<open>pdelegate_c\<close> footprint [qc] .
locality_lemma for perf: \<open>pspecial_c True\<close> footprint [qc] .
locality_lemma for perf: \<open>pdelegate_special_c\<close> footprint [qc] .
locality_lemma for perf [perf_custom_locality]:
  \<open>pcustom_c\<close> footprint [qc] .
locality_lemma for perf: \<open>pdelegate_custom_c\<close> footprint [qc] .
locality_lemma for perf: \<open>phas_d\<close> footprint [qd] .

text\<open>Sanity: a deep nest cancels by plain @{term \<open>simp\<close>} as an object-level lemma too.\<close>
lemma \<open>phas_d (pset_a a (pset_b b (pset_c c (pbump_c k (pset_a a2 X))))) = phas_d X\<close>
  by simp

lemma \<open>phas_d (pdelegate_special_c k X) = phas_d X\<close>
  by simp

lemma \<open>phas_d (pdelegate_custom_c k X) = phas_d X\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  \<comment>\<open>Build an n-deep telescope of disjoint operations under phas_d and time its cancellation.\<close>
  fun deep n =
    let
      val ops = ["pset_a a", "pset_b b", "pset_c c", "pbump_c k"]
      fun wrap i body = (nth ops (i mod 4)) ^ " (" ^ body ^ ")"
      val inner = fold wrap (0 upto (n - 1)) "X"
    in "phas_d (" ^ inner ^ ") = phas_d X" end
  val _ = AutoLocality_Assert.run_suite "Perf/telescope-depth"
    [ ("depth 4 within 4s",  fn () => AutoLocality_Assert.check "depth 4"  (AutoLocality_Assert.cancels_within ctxt 4000 (deep 4))),
      ("depth 8 within 4s",  fn () => AutoLocality_Assert.check "depth 8"  (AutoLocality_Assert.cancels_within ctxt 4000 (deep 8))),
      ("depth 16 within 4s", fn () => AutoLocality_Assert.check "depth 16" (AutoLocality_Assert.cancels_within ctxt 4000 (deep 16))) ]
\<close>

text\<open>A cancellable operation can sit directly under an attribute while its record argument contains
a deep body of operations that overlap the attribute. Cancellation must remove only the front
operation without simplifying the blocked body again. Give every layer a distinct argument so term
sharing cannot collapse the telescope.\<close>
ML\<open>
  val ctxt = \<^context>
  val blocked = Syntax.read_term ctxt "pset_d"
  val front = Syntax.read_term ctxt "pset_a"
  val attribute = Syntax.read_term ctxt "phas_d"
  val state = Syntax.read_term ctxt "X :: perf"
  fun indexed_operation operation prefix i inner =
    operation $ Free (prefix ^ Int.toString i, HOLogic.natT) $ inner
  fun front_over_blocked n =
    let
      val body = fold (indexed_operation blocked "d")
        (1 upto n) state
      val front_body = front $ Free ("a", HOLogic.natT) $ body
    in
      HOLogic.mk_Trueprop
        (HOLogic.mk_eq (attribute $ front_body, attribute $ body))
    end
  fun all_front n =
    let
      val body = fold (indexed_operation front "a")
        (1 upto n) state
    in
      HOLogic.mk_Trueprop
        (HOLogic.mk_eq (attribute $ body, attribute $ state))
    end
  fun cancels context goal =
    (Goal.prove context [] [] goal
      (fn {context, ...} => asm_full_simp_tac context 1);
     true)
    handle ERROR _ => false | THM _ => false
  fun timed_cancels_within context label ms goal =
    let
      val start = Timing.start ()
      val result =
        Timeout.apply (Time.fromMilliseconds (IntInf.fromInt ms))
          (fn () => cancels context goal) ()
        handle Timeout.TIMEOUT _ => false
      val _ = writeln (label ^ ": " ^ Timing.message (Timing.result start))
    in result end
  val (blocked_run, blocked_ctxt) =
    AutoLocality_Instrumentation.start_run ctxt
  val blocked_outcome =
    Exn.capture
      (fn () =>
        timed_cancels_within blocked_ctxt
          "Perf/front-over-blocked depth 5000" 4000
          (front_over_blocked 5000)) ()
  val blocked_snapshot_option =
    AutoLocality_Instrumentation.freeze_run blocked_run
  val blocked_dropped =
    AutoLocality_Instrumentation.drop_run blocked_run
  val blocked_result = Exn.release blocked_outcome
  val blocked_snapshot =
    (case blocked_snapshot_option of
       SOME snapshot => snapshot
     | NONE => error "Missing front-over-blocked instrumentation snapshot")
  val blocked_clean_freeze =
    AutoLocality_Instrumentation.snapshot_phase blocked_snapshot =
      AutoLocality_Instrumentation.Frozen
    andalso
      AutoLocality_Instrumentation.snapshot_active_callbacks
        blocked_snapshot = 0
    andalso
      AutoLocality_Instrumentation.snapshot_async_leases
        blocked_snapshot = 0
  val blocked_avoids_record_simpset =
    AutoLocality_Instrumentation.snapshot_counter blocked_snapshot
      AutoLocality_Instrumentation.Record_Simpset_Builds = 0
  val _ = AutoLocality_Assert.run_suite "Perf/front-over-blocked"
    [ ("depth 5000 within 4s",
        fn () => AutoLocality_Assert.check "front-over-blocked depth 5000"
          blocked_result),
      ("does not build a record simpset",
        fn () => AutoLocality_Assert.check "no record simpset build"
          blocked_avoids_record_simpset),
      ("instrumentation run freezes drained",
        fn () => AutoLocality_Assert.check "clean freeze"
          blocked_clean_freeze),
      ("instrumentation run drops",
        fn () => AutoLocality_Assert.check "clean drop"
          blocked_dropped) ]
  val _ = AutoLocality_Assert.run_suite "Perf/all-front"
    [ ("depth 4096 within 4s",
        fn () => AutoLocality_Assert.check "all-front depth 4096"
          (timed_cancels_within ctxt "Perf/all-front depth 4096"
            4000 (all_front 4096))) ]
\<close>

text\<open>Wide: every field-projection attribute cancels a disjoint operation, each within budget.\<close>
ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_Assert.run_suite "Perf/wide-attrs"
    [ ("qa proj", fn () => AutoLocality_Assert.check "qa" (AutoLocality_Assert.cancels_within ctxt 4000 "qa (pset_b b (pset_c c X)) = qa X")),
      ("qb proj", fn () => AutoLocality_Assert.check "qb" (AutoLocality_Assert.cancels_within ctxt 4000 "qb (pset_a a (pset_c c X)) = qb X")),
      ("qd attr", fn () => AutoLocality_Assert.check "qd" (AutoLocality_Assert.cancels_within ctxt 4000 "phas_d (pset_a a (pset_b b (pset_c c X))) = phas_d X")) ]
\<close>

(*<*)
end
(*>*)
