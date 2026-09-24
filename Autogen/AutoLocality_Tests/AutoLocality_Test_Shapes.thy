(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Shapes
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Argument shapes: extra arguments, record position, polymorphism, and a known limitation\<close>

text\<open>Operations and attributes come in more shapes than \<open>f R\<close>. This suite covers attributes with
extra non-record arguments, the record sitting at a non-zero argument position, polymorphic records
and operations (including a partially instantiated one), and documents the one genuine
classification limitation: a function with two record-typed arguments is treated as an attribute,
not an operation.\<close>

subsection\<open>Extra arguments and non-zero record position\<close>

datatype_record shp =
  sa :: nat
  sb :: nat
  sc :: nat

locality_init for shp

definition sset_c :: \<open>nat \<Rightarrow> shp \<Rightarrow> shp\<close> where
  \<open>sset_c k \<equiv> update_sc (\<lambda>_. k)\<close>
\<comment>\<open>Attribute with an extra (non-record) argument, record at index 0.\<close>
definition sa_exceeds :: \<open>shp \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sa_exceeds R n \<equiv> sa R > n\<close>
\<comment>\<open>Attribute with the record at argument index 1 (its only record argument), match index 0.\<close>
definition sb_below :: \<open>nat \<Rightarrow> shp \<Rightarrow> bool\<close> where
  \<open>sb_below n R \<equiv> sb R < n\<close>
\<comment>\<open>Attribute with two non-record arguments straddling the record (index 1).\<close>
definition sa_between :: \<open>nat \<Rightarrow> shp \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sa_between lo R hi \<equiv> lo < sa R \<and> sa R < hi\<close>

locality_lemma for shp: \<open>sset_c\<close> footprint [sc] .
locality_lemma for shp: \<open>sa_exceeds\<close> footprint [sa] .
locality_lemma for shp: \<open>sb_below\<close> [0] footprint [sb] .
locality_lemma for shp: \<open>sa_between\<close> [0] footprint [sa] .

text\<open>Each cancels its footprint-disjoint inner operation, regardless of where the record sits or how
many extra arguments surround it.\<close>
lemma \<open>sa_exceeds (sset_c c X) n = sa_exceeds X n\<close> by simp
lemma \<open>sb_below n (sset_c c X) = sb_below n X\<close> by simp
lemma \<open>sa_between lo (sset_c c X) hi = sa_between lo X hi\<close> by simp

subsection\<open>Function-valued field selectors\<close>

datatype_record function_field_shape =
  ffs_counter :: nat
  ffs_lookup :: \<open>nat \<Rightarrow> bool\<close>

locality_init for function_field_shape

definition ffs_touch_counter ::
    \<open>nat \<Rightarrow> function_field_shape \<Rightarrow> function_field_shape\<close> where
  \<open>ffs_touch_counter k R \<equiv>
    update_ffs_counter (\<lambda>old. old + k + ffs_counter R) R\<close>

locality_lemma for function_field_shape:
  \<open>ffs_touch_counter\<close> footprint [ffs_counter] .

text\<open>A generated selector for a function-valued field is registered at its record argument, while
its physical simplifier trigger sees the selector's complete application. Cancellation rewrites
the registered selector prefix and preserves the trailing lookup argument.\<close>
lemma \<open>ffs_lookup (ffs_touch_counter k R) i = ffs_lookup R i\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_Assert.run_suite "Shapes/function-valued-field"
    [("direct simproc preserves the trailing lookup argument",
       fn () => AutoLocality_Assert.assert_simproc_cancels_to ctxt
         "AutoLocality_Test_Shapes.function_field_shape" "ffs_lookup"
         "ffs_lookup (ffs_touch_counter k R) i" "ffs_lookup R i")]
\<close>

subsection\<open>Polymorphic records and operations\<close>

datatype_record ('a, 'b) prc =
  pl :: 'a
  pr :: 'b

locality_init for prc

\<comment>\<open>A fully polymorphic operation.\<close>
definition twiddle_pl :: \<open>('a, 'b) prc \<Rightarrow> ('a, 'b) prc\<close> where
  \<open>twiddle_pl R \<equiv> update_pl id R\<close>
\<comment>\<open>An operation that partially instantiates the second type parameter to @{typ bool}.\<close>
definition set_pr_bool :: \<open>bool \<Rightarrow> ('a, bool) prc \<Rightarrow> ('a, bool) prc\<close> where
  \<open>set_pr_bool v \<equiv> update_pr (\<lambda>_. v)\<close>

locality_lemma for prc: \<open>twiddle_pl\<close> footprint [pl] .
locality_lemma for prc: \<open>set_pr_bool\<close> footprint [pr] .

text\<open>Cancellation works on polymorphic and partially-instantiated terms alike.\<close>
lemma \<open>pr (twiddle_pl X) = pr X\<close> by simp
lemma \<open>pl (set_pr_bool v X) = pl X\<close> by simp
lemma \<open>(pl :: ('a, bool) prc \<Rightarrow> 'a) (set_pr_bool v X) = pl X\<close> by simp

subsection\<open>Known limitation: two record-typed arguments classify as an attribute\<close>

text\<open>A function @{typ \<open>shp \<Rightarrow> shp \<Rightarrow> shp\<close>} has two arguments that unify with the record type, so the
classifier's "exactly one matching argument" test (@{verbatim \<open>is_fun_ty_on\<close>}) fails and the function
is treated as an \<^emph>\<open>attribute\<close> with two candidate record positions, not as an operation. This is a
genuine modelling boundary, recorded here as a checked fact rather than a bug. We assert the
classification at the ML level instead of registering it (registration would force a single record
position and is not the intended use).\<close>

definition smerge :: \<open>shp \<Rightarrow> shp \<Rightarrow> shp\<close> where
  \<open>smerge R S \<equiv> update_sa (\<lambda>_. sa S) R\<close>

ML\<open>
  val ctxt = \<^context>
  val (rec_ty, _) = prepare_rec_name ctxt "shp"
  fun classify nm =
    let val t = Syntax.read_term ctxt nm
        val is_op = is_fun_ty_on rec_ty (Term.type_of t)
        val idxs = case dest_attr_term ctxt rec_ty t of SOME (_, _, i) => i | NONE => []
    in (is_op, idxs) end
  val _ = AutoLocality_Assert.run_suite "Shapes/classification"
    [ \<comment>\<open>A genuine single-record operation is classified as an operation.\<close>
      ("sset_c is an operation",
         fn () => AutoLocality_Assert.check "sset_c is_fun_ty_on" (#1 (classify "sset_c"))),
      \<comment>\<open>A single-record attribute with extra args is NOT an operation, one record position.\<close>
      ("sa_between is an attribute at [1]",
         fn () => AutoLocality_Assert.check "sa_between attr idxs=[1]"
                    (not (#1 (classify "sa_between")) andalso #2 (classify "sa_between") = [1])),
      \<comment>\<open>The two-record-argument function: not an operation, two candidate positions [0,1].\<close>
      ("smerge classifies as attribute with idxs=[0,1]",
         fn () => AutoLocality_Assert.check "smerge not op, idxs=[0,1]"
                    (not (#1 (classify "smerge")) andalso #2 (classify "smerge") = [0, 1])) ]
\<close>

(*<*)
end
(*>*)
