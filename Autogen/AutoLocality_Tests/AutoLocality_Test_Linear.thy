(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Linear
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Linear-lemma generation\<close>

text\<open>For each registered operation, @{verbatim \<open>locality_lemma\<close>} generates three linear facts -
the local-action lemma @{verbatim \<open>_local\<close>}, the field-update commutativity @{verbatim \<open>_core\<close>}, and the
disjointness @{verbatim \<open>_disjoint\<close>} - and for each attribute a single cancellation @{verbatim \<open>_core\<close>}.
This suite checks they are generated, under the expected names, with the expected statements and
cardinalities, and that the old quadratic @{verbatim \<open>*_commutativity_facts\<close>} bundle is gone.\<close>

datatype_record lin =
  la :: nat
  lb :: nat
  lc :: nat

locality_init for lin

definition lset_a :: \<open>nat \<Rightarrow> lin \<Rightarrow> lin\<close> where
  \<open>lset_a k R \<equiv> update_la (\<lambda>_. k) R\<close>
\<comment>\<open>An operation touching its field non-trivially via the old value, so the local-action lemma
   genuinely needs record extensionality.\<close>
definition lbump_b :: \<open>nat \<Rightarrow> lin \<Rightarrow> lin\<close> where
  \<open>lbump_b k R \<equiv> update_lb (\<lambda>old. old + k + lb R) R\<close>
definition lhas_a :: \<open>lin \<Rightarrow> bool\<close> where
  \<open>lhas_a R \<equiv> la R > 0\<close>
definition lread_c :: \<open>lin \<Rightarrow> nat\<close> where
  \<open>lread_c R \<equiv> lc R\<close>

locality_lemma for lin: \<open>lset_a\<close> footprint [la] .
locality_lemma for lin: \<open>lbump_b\<close> footprint [lb] .
locality_lemma for lin: \<open>lhas_a\<close> footprint [la] .
locality_lemma for lin: \<open>lread_c\<close> footprint [lc] .

subsection\<open>The generated statements are exactly as specified\<close>

text\<open>Operation @{verbatim \<open>lbump_b\<close>}: local action, field-update commutativity, and disjointness.\<close>
lemma \<open>lbump_b k R = update_lb (\<lambda>_. lb (lbump_b k R)) R\<close>
  by (rule AutoLocality_Test_Linear_lin_local_op_lbump_b_local)
lemma \<open>lbump_b k (update_la f R) = update_la f (lbump_b k R)\<close>
  by (rule AutoLocality_Test_Linear_lin_local_op_lbump_b_core)
lemma \<open>lbump_b k (update_lc f R) = update_lc f (lbump_b k R)\<close>
  by (rule AutoLocality_Test_Linear_lin_local_op_lbump_b_core)
lemma \<open>la (lbump_b k R) = la R\<close>
  by (rule AutoLocality_Test_Linear_lin_local_op_lbump_b_disjoint)
lemma \<open>lc (lbump_b k R) = lc R\<close>
  by (rule AutoLocality_Test_Linear_lin_local_op_lbump_b_disjoint)

text\<open>Attribute @{verbatim \<open>lhas_a\<close>}: cancellation against a disjoint field update.\<close>
lemma \<open>lhas_a (update_lb f R) = lhas_a R\<close>
  by (rule AutoLocality_Test_Linear_lin_local_attr_lhas_a_0_core)
lemma \<open>lhas_a (update_lc f R) = lhas_a R\<close>
  by (rule AutoLocality_Test_Linear_lin_local_attr_lhas_a_0_core)

subsection\<open>Generation metadata: presence, cardinality, no quadratic bundle\<close>

ML\<open>
  val ctxt = \<^context>
  val rec_id = "AutoLocality_Test_Linear_lin"
  val _ = AutoLocality_Assert.run_suite "Linear/generation"
    [ ("op lset_a lemmas",  fn () => AutoLocality_Assert.assert_op_lemmas ctxt rec_id "lset_a"),
      ("op lbump_b lemmas", fn () => AutoLocality_Assert.assert_op_lemmas ctxt rec_id "lbump_b"),
      ("attr lhas_a lemma", fn () => AutoLocality_Assert.assert_attr_lemmas ctxt rec_id "lhas_a" 0),
      ("attr lread_c lemma", fn () => AutoLocality_Assert.assert_attr_lemmas ctxt rec_id "lread_c" 0),
      \<comment>\<open>Two disjoint fields -> two field-update commutativity facts and two disjointness facts.\<close>
      ("lbump_b _core card",     fn () => AutoLocality_Assert.assert_fact_card ctxt (rec_id ^ "_local_op_lbump_b_core") 2),
      ("lbump_b _disjoint card", fn () => AutoLocality_Assert.assert_fact_card ctxt (rec_id ^ "_local_op_lbump_b_disjoint") 2),
      ("lbump_b _local card",    fn () => AutoLocality_Assert.assert_fact_card ctxt (rec_id ^ "_local_op_lbump_b_local") 1),
      \<comment>\<open>The attribute cancellation 'core' fact: one per disjoint field of footprint [la], i.e. lb,lc.\<close>
      ("lhas_a _0_core card",    fn () => AutoLocality_Assert.assert_fact_card ctxt (rec_id ^ "_local_attr_lhas_a_0_core") 2),
      ("no quadratic bundle",    fn () => AutoLocality_Assert.assert_no_quadratic ctxt rec_id),
      \<comment>\<open>The record-wide locality_facts bundle exists and is non-empty.\<close>
      ("locality_facts present", fn () => AutoLocality_Assert.assert_fact ctxt (rec_id ^ "_locality_facts")) ]
\<close>

(*<*)
end
(*>*)
