(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Cancel
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>On-the-fly cancellation via the default-on simprocs\<close>

text\<open>The reworked AutoLocality discharges cancellations on the fly with per-attribute simprocs that
are part of the ambient simpset. A bare @{verbatim \<open>simp\<close>} therefore cancels operations whose
footprint is disjoint from the attribute, with no explicit lemma list or attribute. This suite
exercises the cancellation matrix: simple, nested, telescoped, through unknown functions, and the
@{verbatim \<open>simp add: <record>_locality_facts\<close>} bundle form that downstream proofs use. It also pins
the fixpoint behaviour (the simproc declines a normal-form term) and the exact rewrite the simproc
synthesises.\<close>

datatype_record cel =
  ca :: nat
  cb :: nat
  cc :: nat

locality_init for cel

\<comment>\<open>Opaque operations: bodies touch their field non-trivially, so cancellation must drive the
   definition-unfolding prover rather than bottoming out in record_simps.\<close>
definition cop_a :: \<open>nat \<Rightarrow> cel \<Rightarrow> cel\<close> where
  \<open>cop_a k R \<equiv> update_ca (\<lambda>old. old + k + ca R) R\<close>
definition cop_b :: \<open>nat \<Rightarrow> cel \<Rightarrow> cel\<close> where
  \<open>cop_b k R \<equiv> update_cb (\<lambda>old. old * k) R\<close>
definition cset_c :: \<open>nat \<Rightarrow> cel \<Rightarrow> cel\<close> where
  \<open>cset_c k \<equiv> update_cc (\<lambda>_. k)\<close>

definition chas_a :: \<open>cel \<Rightarrow> bool\<close> where
  \<open>chas_a R \<equiv> ca R > 0\<close>
definition cread_b :: \<open>cel \<Rightarrow> nat\<close> where
  \<open>cread_b R \<equiv> cb R\<close>
\<comment>\<open>Attribute with the record at a non-zero argument index (record at position 1).\<close>
definition cb_below :: \<open>nat \<Rightarrow> cel \<Rightarrow> bool\<close> where
  \<open>cb_below n R \<equiv> cb R < n\<close>

locality_lemma for cel: \<open>cop_a\<close> footprint [ca] .
locality_lemma for cel: \<open>cop_b\<close> footprint [cb] .
locality_lemma for cel: \<open>cset_c\<close> footprint [cc] .
locality_lemma for cel: \<open>chas_a\<close> footprint [ca] .
locality_lemma for cel: \<open>cread_b\<close> footprint [cb] .
locality_lemma for cel: \<open>cb_below\<close> [0] footprint [cb] .

subsection\<open>Cancellation matrix by plain @{term \<open>simp\<close>}\<close>

text\<open>Simple: a footprint-disjoint operation under an attribute cancels.\<close>
lemma \<open>chas_a (cset_c c X) = chas_a X\<close> by simp
lemma \<open>chas_a (cop_b b X) = chas_a X\<close> by simp
lemma \<open>cread_b (cop_a a X) = cread_b X\<close> by simp
lemma \<open>cread_b (cset_c c X) = cread_b X\<close> by simp

text\<open>A field selector is itself an attribute, so projections cancel disjoint operations.\<close>
lemma \<open>ca (cset_c c X) = ca X\<close> by simp
lemma \<open>cb (cop_a a X) = cb X\<close> by simp

text\<open>The record-at-index-1 attribute cancels too.\<close>
lemma \<open>cb_below n (cset_c c X) = cb_below n X\<close> by simp
lemma \<open>cb_below n (cop_a a X) = cb_below n X\<close> by simp

text\<open>Nested: only the footprint-disjoint operations are hoisted out and cancelled; the
footprint-sharing one is kept.\<close>
lemma \<open>chas_a (cset_c c (cop_b b (cop_a a X))) = chas_a (cop_a a X)\<close> by simp
lemma \<open>cread_b (cset_c c (cop_a a (cop_b b X))) = cread_b (cop_b b X)\<close> by simp

text\<open>Telescope through bare field updates as well as named operations.\<close>
lemma \<open>chas_a (update_cb g (update_cc hf X)) = chas_a X\<close> by simp
lemma \<open>chas_a (cset_c c (update_cb g X)) = chas_a X\<close> by simp

text\<open>Cancellation reaches through an unknown function applied to the record.\<close>
lemma \<open>chas_a (cset_c c (f X)) = chas_a (f X)\<close> by simp

subsection\<open>The bundle form @{verbatim \<open>simp add: <record>_locality_facts\<close>}\<close>

text\<open>Downstream proofs invoke the record's locality bundle explicitly; the simprocs ride along in
the ambient simpset, so cancellation still happens.\<close>
lemma \<open>chas_a (cset_c c (cop_a a X)) = chas_a (cop_a a X)\<close>
  by (simp add: AutoLocality_Test_Cancel_cel_locality_facts)

subsection\<open>Simproc internals: fixpoint declines and exact rewrites\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Cancel.cel"
  val _ = AutoLocality_Assert.run_suite "Cancel/simproc"
    [ \<comment>\<open>A normal-form term (only a footprint-sharing op inside) must be declined: no rewrite, no
         loop. This is the safety property underpinning always-on simprocs.\<close>
      ("declines chas_a (cop_a a X)",
         fn () => AutoLocality_Assert.assert_simproc_declines ctxt rec_name "chas_a" "chas_a (cop_a a X)"),
      ("declines cread_b (cop_b b X)",
         fn () => AutoLocality_Assert.assert_simproc_declines ctxt rec_name "cread_b" "cread_b (cop_b b X)"),
      \<comment>\<open>A cancellable term yields exactly the expected meta-eq right-hand side.\<close>
      ("cancels chas_a (cset_c c X) to chas_a X",
         fn () => AutoLocality_Assert.assert_simproc_cancels_to ctxt rec_name "chas_a" "chas_a (cset_c c X)" "chas_a X"),
      ("cancels chas_a (cset_c c (cop_a a X)) keeps cop_a",
         fn () => AutoLocality_Assert.assert_simproc_cancels_to ctxt rec_name "chas_a"
                    "chas_a (cset_c c (cop_a a X))" "chas_a (cop_a a X)") ]
\<close>

subsection\<open>Cancellation matrix as an ML suite (parsed-goal form)\<close>

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_Assert.run_suite "Cancel/by-simp"
    [ ("simple set",     fn () => AutoLocality_Assert.assert_cancels ctxt "chas_a (cset_c c X) = chas_a X"),
      ("simple op",      fn () => AutoLocality_Assert.assert_cancels ctxt "chas_a (cop_b b X) = chas_a X"),
      ("nested keep",    fn () => AutoLocality_Assert.assert_cancels ctxt
                                    "chas_a (cset_c c (cop_b b (cop_a a X))) = chas_a (cop_a a X)"),
      ("through fn",     fn () => AutoLocality_Assert.assert_cancels ctxt "chas_a (cset_c c (f X)) = chas_a (f X)"),
      \<comment>\<open>A footprint-sharing operation must NOT be cancelled - the equation is not a theorem.\<close>
      ("no spurious cancel", fn () => AutoLocality_Assert.assert_does_not_cancel ctxt "chas_a (cop_a a X) = chas_a X") ]
\<close>

(*<*)
end
(*>*)
