(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Shapes_Wide
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Body-shape coverage for \<^verbatim>\<open>locality_lemma\<close>\<close>

text\<open>This theory is a self-contained, fast-to-build regression suite that reproduces every
body-shape and invocation-shape in which @{verbatim \<open>locality_lemma\<close>} is used on a record with many
fields. It keeps the framework vetted inside the \<^verbatim>\<open>Autogen\<close> session, which builds in
seconds.

The shapes exercised here:
\<^enum> simple field projection / read (attribute);
\<^enum> simple single-field update, point-free / eta-reduced (operation);
\<^enum> constant single-field set, ignoring the old value (operation);
\<^enum> opaque single-field read-modify-write — body uses the OLD field value (operation);
\<^enum> conditional \<^verbatim>\<open>if … then … else …\<close> body, attribute;
\<^enum> conditional body, operation that writes a DIFFERENT field per branch
   (this is the \<^verbatim>\<open>w_cond_write\<close> shape);
\<^enum> \<^verbatim>\<open>let … in …\<close> body, operation (the \<^verbatim>\<open>w_apply_policy\<close> shape);
\<^enum> \<^verbatim>\<open>let\<close> body, attribute (arithmetic);
\<^enum> \<^verbatim>\<open>let\<close> + tuple/\<^verbatim>\<open>prod\<close> destructuring + multi-field update telescope (operation);
\<^enum> \<^verbatim>\<open>case … of\<close> on a record field, attribute;
\<^enum> \<^verbatim>\<open>case … of\<close> on a NON-record argument, operation;
\<^enum> multi-field update telescope (operation);
\<^enum> nested-record field update + delegation to another operation (operation);
\<^enum> attribute returning a list / set / bool / word / sum;
\<^enum> PARTIAL APPLICATION of a constant to an argument — two distinct partial applications of the
   same head constant must get DISTINCT generated fact names (the
   \<^verbatim>\<open>w_apply_policy policy_a\<close> vs \<^verbatim>\<open>w_apply_policy policy_b\<close> case);
\<^enum> over-approximated footprint (lists a field the body does not touch);
\<^enum> registration on an \<^verbatim>\<open>abbreviation\<close> rather than a \<^verbatim>\<open>definition\<close>;
\<^enum> a wide (many-field) record, to exercise initialisation cost.

We silence the tracer to keep the build log readable.\<close>

declare [[locality_trace_level = 0]]

subsection\<open>A wide record (many fields, mixed types)\<close>

text\<open>21 fields, mixed scalar / list / option / nested-record types, so initialisation must prove the
linear lemmas against ~20 disjoint fields per operation — the cost hotspot.\<close>

datatype_record inner_rec =
  ir_x :: nat
  ir_y :: nat

datatype_record wide =
  wf00 :: nat
  wf01 :: \<open>nat list\<close>
  wf02 :: nat
  wf03 :: \<open>nat list\<close>
  wf04 :: nat
  wf05 :: \<open>nat list\<close>
  wf06 :: nat
  wf07 :: \<open>nat option\<close>
  wf08 :: nat
  wf09 :: \<open>nat list\<close>
  wf10 :: nat
  wf11 :: nat
  wf12 :: nat
  wf13 :: nat
  wf14 :: nat
  wf15 :: nat
  wf16 :: nat
  wf17 :: nat
  wf18 :: nat
  wstate :: nat
  winner :: \<open>inner_rec\<close>

subsubsection\<open>Operations on \<^typ>\<open>wide\<close> — all the operation body-shapes\<close>

\<comment>\<open>(2) simple single-field update, point-free / eta-reduced.\<close>
definition w_set00 :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where \<open>w_set00 v \<equiv> update_wf00 (\<lambda>_. v)\<close>

\<comment>\<open>(3) constant single-field set.\<close>
definition w_clear00 :: \<open>wide \<Rightarrow> wide\<close> where \<open>w_clear00 \<equiv> update_wf00 (\<lambda>_. 0)\<close>

\<comment>\<open>(4) opaque single-field read-modify-write — uses the old value.\<close>
definition w_bump02 :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where \<open>w_bump02 k R \<equiv> update_wf02 (\<lambda>old. old + k + wf02 R) R\<close>

\<comment>\<open>(6) conditional body, writes a DIFFERENT field per branch (the \<open>w_cond_write\<close> shape).\<close>
definition w_cond_write :: \<open>nat \<Rightarrow> nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>w_cond_write a b R \<equiv>
     if wstate R = 0 then update_wf00 (\<lambda>_. a) R else update_wf02 (\<lambda>_. b) R\<close>

\<comment>\<open>(7) let-body operation (the \<open>w_apply_policy\<close> shape): bind locals, then a
   multi-field update telescope. Parameterised by a function argument (so partial applications of it
   below exercise shape 15).\<close>
definition w_apply_policy :: \<open>(wide \<Rightarrow> nat) \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>w_apply_policy policy R \<equiv>
     let v = policy R in
     let w = v + 1 in
     update_wf01 (\<lambda>_. [w]) (update_wf00 (\<lambda>_. v) R)\<close>

\<comment>\<open>(9) let + tuple/prod destructuring + multi-field update telescope.\<close>
definition split_pair :: \<open>nat \<Rightarrow> nat \<times> nat\<close> where \<open>split_pair k \<equiv> (k, k + 1)\<close>
definition w_split_set :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>w_split_set k R \<equiv>
     let (p, q) = split_pair k in
     update_wf02 (\<lambda>_. q) (update_wf00 (\<lambda>_. p) R)\<close>

\<comment>\<open>(11) case on a NON-record argument; one branch delegates, the other returns the record unchanged.\<close>
datatype choice = Take | Leave
definition w_maybe :: \<open>choice \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>w_maybe c R \<equiv> case c of Take \<Rightarrow> w_clear00 R | Leave \<Rightarrow> R\<close>

\<comment>\<open>(12) multi-field update telescope (sequential rewrites of several fields).\<close>
definition w_set_three :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>w_set_three k R \<equiv> update_wf00 (\<lambda>_. k) (update_wf02 (\<lambda>_. k) (update_wf04 (\<lambda>_. k) R))\<close>

\<comment>\<open>(13) nested-record field update + delegation to another operation.\<close>
definition w_nested :: \<open>nat \<Rightarrow> wide \<Rightarrow> wide\<close> where
  \<open>w_nested k R \<equiv> w_clear00 (update_winner (\<lambda>i. update_ir_x (\<lambda>_. k) i) R)\<close>

locality_lemma for wide: \<open>w_set00\<close> footprint [wf00] .
locality_lemma for wide: \<open>w_clear00\<close> footprint [wf00] .
locality_lemma for wide: \<open>w_bump02\<close> footprint [wf02] .
locality_lemma for wide: \<open>w_cond_write\<close> footprint [wstate, wf00, wf02] .
locality_lemma for wide: \<open>w_split_set\<close> footprint [wf00, wf02] .
locality_lemma for wide: \<open>w_maybe\<close> footprint [wf00] .
locality_lemma for wide: \<open>w_set_three\<close> footprint [wf00, wf02, wf04] .
locality_lemma for wide: \<open>w_nested\<close> footprint [wf00, winner] .

text\<open>The let-body operation, exercised both bare and via TWO distinct partial applications of the
same head constant — these must get distinct fact names (shape 15).\<close>

definition policy_a :: \<open>wide \<Rightarrow> nat\<close> where \<open>policy_a R \<equiv> wf04 R\<close>
definition policy_b :: \<open>wide \<Rightarrow> nat\<close> where \<open>policy_b R \<equiv> wf06 R + 1\<close>

locality_lemma for wide: \<open>w_apply_policy policy_a\<close> footprint [wf00, wf01, wf04] .
locality_lemma for wide: \<open>w_apply_policy policy_b\<close> footprint [wf00, wf01, wf06] .

subsubsection\<open>Attributes on \<^typ>\<open>wide\<close> — all the attribute body-shapes\<close>

\<comment>\<open>(1) simple field projection.\<close>
definition w_read00 :: \<open>wide \<Rightarrow> nat\<close> where \<open>w_read00 R \<equiv> wf00 R\<close>

\<comment>\<open>(5) conditional attribute.\<close>
definition w_cond_read :: \<open>wide \<Rightarrow> nat\<close> where
  \<open>w_cond_read R \<equiv> if wstate R = 0 then wf00 R else wf02 R\<close>

\<comment>\<open>(8) let-body attribute (arithmetic).\<close>
definition w_let_avg :: \<open>wide \<Rightarrow> nat\<close> where
  \<open>w_let_avg R \<equiv> let a = wf00 R in let b = wf02 R in (a + b + 1) div 2\<close>

\<comment>\<open>(10) case on a record field, attribute returning a list.\<close>
definition w_case_list :: \<open>wide \<Rightarrow> nat list\<close> where
  \<open>w_case_list R \<equiv> case wf07 R of None \<Rightarrow> [] | Some n \<Rightarrow> n # wf01 R\<close>

\<comment>\<open>(14a) attribute returning a LIST (concatenation of two field reads).\<close>
definition w_all_list :: \<open>wide \<Rightarrow> nat list\<close> where \<open>w_all_list R \<equiv> wf01 R @ wf03 R\<close>

\<comment>\<open>(14b) attribute returning a SET.\<close>
definition w_set_attr :: \<open>wide \<Rightarrow> nat set\<close> where \<open>w_set_attr R \<equiv> {wf00 R} \<union> set (wf01 R)\<close>

\<comment>\<open>(14c) attribute returning a BOOL (predicate).\<close>
definition w_pred :: \<open>wide \<Rightarrow> bool\<close> where \<open>w_pred R \<equiv> wf00 R > 0 \<and> wf02 R \<le> 10\<close>

\<comment>\<open>(14d) attribute reading a field as a function then existential (field used as a map).\<close>
definition w_exists :: \<open>wide \<Rightarrow> bool\<close> where \<open>w_exists R \<equiv> \<exists>x \<in> set (wf01 R). x > wf00 R\<close>

locality_lemma for wide: \<open>w_read00\<close> footprint [wf00] .
locality_lemma for wide: \<open>w_cond_read\<close> footprint [wstate, wf00, wf02] .
locality_lemma for wide: \<open>w_let_avg\<close> footprint [wf00, wf02] .
locality_lemma for wide: \<open>w_case_list\<close> footprint [wf07, wf01] .
locality_lemma for wide: \<open>w_all_list\<close> footprint [wf01, wf03] .
locality_lemma for wide: \<open>w_set_attr\<close> footprint [wf00, wf01] .
locality_lemma for wide: \<open>w_pred\<close> footprint [wf00, wf02] .
locality_lemma for wide: \<open>w_exists\<close> footprint [wf00, wf01] .

\<comment>\<open>(16) over-approximated footprint: body only reads wf00, but we declare wf00, wf02.\<close>
definition w_over :: \<open>wide \<Rightarrow> nat\<close> where \<open>w_over R \<equiv> wf00 R + 1\<close>
locality_lemma for wide: \<open>w_over\<close> footprint [wf00, wf02] .

\<comment>\<open>(17) registration on an abbreviation rather than a definition. The abbreviation must denote a
   term that is not already a registered attribute (an abbreviation is transparent, so aliasing an
   already-registered attribute would just re-register it and collide); here it concatenates two
   field reads directly.\<close>
abbreviation w_abbrev :: \<open>wide \<Rightarrow> nat list\<close> where \<open>w_abbrev R \<equiv> wf05 R @ wf09 R\<close>
locality_lemma for wide: \<open>w_abbrev\<close> footprint [wf05, wf09] .

subsection\<open>Assertions: the framework actually fired and the simproc cancels\<close>

text\<open>Object-level cancellations a downstream proof would rely on — each must close by plain
@{term \<open>simp\<close>} (which runs the default-on locality cancellation simprocs).\<close>

lemma \<open>w_read00 (w_bump02 k R) = w_read00 R\<close> by simp
lemma \<open>w_all_list (w_set00 v R) = w_all_list R\<close> by simp
lemma \<open>w_pred (update_wf04 (\<lambda>_. z) R) = w_pred R\<close> by simp
lemma \<open>w_let_avg (update_wf04 (\<lambda>_. z) (update_wf05 (\<lambda>_. zs) R)) = w_let_avg R\<close> by simp

text\<open>The generated linear facts exist for a representative operation and attribute, confirming
registration ran (footprint registered) rather than silently failing.\<close>

ML\<open>
  val ctxt = \<^context>
  val rid = "AutoLocality_Test_Shapes_Wide_wide"
  val _ = AutoLocality_Assert.run_suite "ShapesWide/registration"
    [ ("cond-write op lemmas",  fn () => AutoLocality_Assert.assert_op_lemmas ctxt rid "w_cond_write"),
      ("let-body op lemmas",    fn () => AutoLocality_Assert.assert_op_lemmas ctxt rid "w_split_set"),
      ("attr w_all_list lemma", fn () => AutoLocality_Assert.assert_attr_lemmas ctxt rid "w_all_list" 0),
      ("no quadratic bundle",   fn () => AutoLocality_Assert.assert_no_quadratic ctxt rid) ]
\<close>

text\<open>The two partial applications of \<^const>\<open>w_apply_policy\<close> must have produced DISTINCT fact bundles
(shape 15 — the duplicate-fact regression). We check both names resolve to a non-empty fact.\<close>

ML\<open>
  val ctxt = \<^context>
  val rid = "AutoLocality_Test_Shapes_Wide_wide"
  fun core_of nm = rid ^ "_local_op_" ^ nm ^ "_core"
  val _ = AutoLocality_Assert.run_suite "ShapesWide/partial-application-distinct"
    [ ("policy_a fact present", fn () => AutoLocality_Assert.assert_fact ctxt (core_of "w_apply_policy_policy_a")),
      ("policy_b fact present", fn () => AutoLocality_Assert.assert_fact ctxt (core_of "w_apply_policy_policy_b")) ]
\<close>

(*<*)
end
(*>*)
