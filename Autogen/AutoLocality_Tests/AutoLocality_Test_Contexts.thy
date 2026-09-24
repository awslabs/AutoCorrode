(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Contexts
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Context transport, overloading, and repeated record arguments\<close>

datatype_record ctx =
  xa :: nat
  xb :: nat
  xc :: nat

locality_init for ctx

definition set_a :: \<open>nat \<Rightarrow> ctx \<Rightarrow> ctx\<close> where
  \<open>set_a n \<equiv> update_xa (\<lambda>_. n)\<close>
definition set_b :: \<open>nat \<Rightarrow> ctx \<Rightarrow> ctx\<close> where
  \<open>set_b n \<equiv> update_xb (\<lambda>_. n)\<close>
definition set_c :: \<open>nat \<Rightarrow> ctx \<Rightarrow> ctx\<close> where
  \<open>set_c n \<equiv> update_xc (\<lambda>_. n)\<close>

locality_lemma for ctx: \<open>set_a\<close> footprint [xa] .
locality_lemma for ctx: \<open>set_b\<close> footprint [xb] .
locality_lemma for ctx: \<open>set_c\<close> footprint [xc] .

subsection\<open>Explicit sublocale transport and nested locales\<close>

locale parent_ctx =
  fixes bump :: \<open>nat \<Rightarrow> nat\<close>
begin

definition parent_attr :: \<open>ctx \<Rightarrow> bool\<close> where
  \<open>parent_attr R \<equiv> bump (xa R) > 10\<close>

definition parent_op :: \<open>ctx \<Rightarrow> ctx\<close> where
  \<open>parent_op R \<equiv> update_xa bump R\<close>

end

context parent_ctx begin

locality_lemma for ctx: \<open>parent_attr\<close> footprint [xa] .
locality_lemma for ctx: \<open>parent_op\<close> footprint [xa] .

lemma \<open>parent_attr (set_c n R) = parent_attr R\<close>
  by simp

end

locale child_ctx =
  fixes bump :: \<open>nat \<Rightarrow> nat\<close>
    and shift :: \<open>nat \<Rightarrow> nat\<close>
begin

definition child_attr :: \<open>ctx \<Rightarrow> bool\<close> where
  \<open>child_attr R \<equiv> shift (xb R) > 20\<close>

definition child_op :: \<open>ctx \<Rightarrow> ctx\<close> where
  \<open>child_op R \<equiv> update_xb shift R\<close>

end

sublocale child_ctx \<subseteq> parent_ctx bump .

context child_ctx begin

locality_lemma for ctx: \<open>child_attr\<close> footprint [xb] .
locality_lemma for ctx: \<open>child_op\<close> footprint [xb] .

lemma \<open>parent_attr (set_c n (child_op R)) = parent_attr (child_op R)\<close>
  by simp

lemma \<open>child_attr (set_c n (parent_op R)) = child_attr (parent_op R)\<close>
  by simp

end

locale grandchild_ctx = child_ctx bump shift
  for bump shift +
  fixes twist :: \<open>nat \<Rightarrow> nat\<close>
begin

definition grandchild_op :: \<open>ctx \<Rightarrow> ctx\<close> where
  \<open>grandchild_op R \<equiv> update_xc twist R\<close>

end

context grandchild_ctx begin

locality_lemma for ctx: \<open>grandchild_op\<close> footprint [xc] .

lemma \<open>parent_attr (grandchild_op (child_op R)) = parent_attr (child_op R)\<close>
  by simp

lemma \<open>child_attr (grandchild_op (parent_op R)) = child_attr (parent_op R)\<close>
  by simp

end

global_interpretation gc: grandchild_ctx Suc \<open>\<lambda>n. n + 2\<close> \<open>\<lambda>n. n * 2\<close> .

lemma \<open>gc.parent_attr (set_c n (gc.child_op R)) = gc.parent_attr (gc.child_op R)\<close>
  by simp

lemma \<open>gc.child_attr (gc.grandchild_op (gc.parent_op R)) =
    gc.child_attr (gc.parent_op R)\<close>
  by simp

subsection\<open>Locale assumptions in transported certificates\<close>

locale assumption_ctx =
  fixes projection :: \<open>ctx \<Rightarrow> nat\<close>
  assumes projection_eq: \<open>projection = xa\<close>
begin

definition assumed_attr :: \<open>ctx \<Rightarrow> bool\<close> where
  \<open>assumed_attr R \<equiv> projection R > 0\<close>

end

context assumption_ctx begin

text\<open>The declared footprint is sound only under
@{thm projection_eq}: without that assumption an arbitrary projection could
observe every field.  The generated certificate therefore carries a locale
hypothesis that standard declaration transport must preserve and discharge
during interpretation.\<close>

lemma assumed_attr_update_xb:
  shows \<open>assumed_attr (update_xb f R) = assumed_attr R\<close>
  unfolding assumed_attr_def
  using projection_eq
  by simp

lemma assumed_attr_update_xc:
  shows \<open>assumed_attr (update_xc f R) = assumed_attr R\<close>
  unfolding assumed_attr_def
  using projection_eq
  by simp

locality_lemma for ctx (no_proof):
  \<open>assumed_attr\<close> footprint [xa]
  by (auto simp only:
        assumed_attr_update_xb assumed_attr_update_xc)

lemma assumption_dependent_certificate_local:
  shows \<open>assumed_attr (set_c n R) = assumed_attr R\<close>
  by (simp only: [[locality_cancel]])

end

global_interpretation assumed_xa: assumption_ctx xa
  by standard simp

lemma assumption_dependent_certificate_interpreted:
  shows \<open>assumed_xa.assumed_attr (set_c n R) =
    assumed_xa.assumed_attr R\<close>
  by (simp only: [[locality_cancel]])

subsection\<open>Independent locales with colliding base names\<close>

locale left_ctx =
  fixes adjust :: \<open>nat \<Rightarrow> nat\<close>
begin

definition view :: \<open>ctx \<Rightarrow> bool\<close> where
  \<open>view R \<equiv> adjust (xa R) > 0\<close>

end

locale right_ctx =
  fixes adjust :: \<open>nat \<Rightarrow> nat\<close>
begin

definition view :: \<open>ctx \<Rightarrow> bool\<close> where
  \<open>view R \<equiv> adjust (xb R) > 0\<close>

end

context left_ctx begin
locality_lemma for ctx: \<open>view\<close> footprint [xa] .
end

context right_ctx begin
locality_lemma for ctx: \<open>view\<close> footprint [xb] .
end

global_interpretation lc: left_ctx Suc .
global_interpretation rc: right_ctx Suc .

lemma \<open>lc.view (set_c n R) = lc.view R\<close>
  by simp

lemma \<open>rc.view (set_a n R) = rc.view R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Contexts.ctx"
  val left_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>left_ctx.view Suc\<close>
  val right_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>right_ctx.view Suc\<close>
  val _ = AutoLocality_Assert.run_suite "Contexts/colliding-locale-base-names"
    [ ("left typed pattern selects its entry",
         fn () => AutoLocality_Assert.check "left entry"
           (case left_entry of SOME entry => #footprint entry = ["xa"] | NONE => false)),
      ("right typed pattern selects its entry",
         fn () => AutoLocality_Assert.check "right entry"
           (case right_entry of SOME entry => #footprint entry = ["xb"] | NONE => false)) ]
\<close>

subsection\<open>Ad-hoc overloading resolves to typed concrete constants\<close>

consts overloaded_attr :: \<open>'a \<Rightarrow> bool\<close>
consts overloaded_op :: \<open>'a \<Rightarrow> 'a\<close>

definition concrete_attr :: \<open>ctx \<Rightarrow> bool\<close> where
  \<open>concrete_attr R \<equiv> xa R > 0\<close>

definition concrete_op :: \<open>ctx \<Rightarrow> ctx\<close> where
  \<open>concrete_op R \<equiv> update_xa Suc R\<close>

adhoc_overloading overloaded_attr \<rightleftharpoons> concrete_attr
adhoc_overloading overloaded_op \<rightleftharpoons> concrete_op

locality_lemma for ctx: \<open>overloaded_attr :: ctx \<Rightarrow> bool\<close> footprint [xa] .
locality_lemma for ctx: \<open>overloaded_op :: ctx \<Rightarrow> ctx\<close> footprint [xa] .

lemma \<open>overloaded_attr (set_c n R :: ctx) = overloaded_attr R\<close>
  by simp

lemma \<open>xb (overloaded_op R :: ctx) = xb R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Contexts.ctx"
  val attr_entry =
    select_locality_entry_for_pattern ctxt rec_name "attribute"
      \<^term>\<open>overloaded_attr :: ctx \<Rightarrow> bool\<close>
  val op_entry =
    select_locality_entry_for_pattern ctxt rec_name "operation"
      \<^term>\<open>overloaded_op :: ctx \<Rightarrow> ctx\<close>
  val _ = AutoLocality_Assert.run_suite "Contexts/adhoc-overloading"
    [ ("attribute resolves to its concrete constant",
         fn () => AutoLocality_Assert.check "concrete overloaded attribute"
           (case attr_entry of
              SOME entry => #const_name entry = "AutoLocality_Test_Contexts.concrete_attr"
            | NONE => false)),
      ("operation resolves to its concrete constant",
         fn () => AutoLocality_Assert.check "concrete overloaded operation"
           (case op_entry of
              SOME entry => #const_name entry = "AutoLocality_Test_Contexts.concrete_op"
            | NONE => false)) ]
\<close>

subsection\<open>One attribute registered at two record argument positions\<close>

definition pair_attr :: \<open>ctx \<Rightarrow> ctx \<Rightarrow> bool\<close> where
  \<open>pair_attr L R \<equiv> xa L < xb R\<close>

locality_lemma for ctx: \<open>pair_attr\<close> [0] footprint [xa] .
locality_lemma for ctx: \<open>pair_attr\<close> [1] footprint [xb] .

lemma \<open>pair_attr (set_c n L) R = pair_attr L R\<close>
  by simp

lemma \<open>pair_attr L (set_a n R) = pair_attr L R\<close>
  by simp

lemma \<open>pair_attr (set_b n L) (set_c m R) = pair_attr L R\<close>
  by simp

lemma \<open>pair_attr (set_c n L) (set_c m R) = pair_attr L R\<close>
  by simp

lemma \<open>pair_attr (set_c n L) R = pair_attr L R\<close>
  by (simp only: [[locality_autocancellation (ctx) set_c pair_attr 0]])

lemma \<open>pair_attr L (set_a n R) = pair_attr L R\<close>
  by (simp only: [[locality_autocancellation (ctx) set_a pair_attr 1]])

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Contexts.ctx"
  val entries =
    get_record_locality_entries_for_const rec_name
      "AutoLocality_Test_Contexts.pair_attr" ctxt
    |> filter (fn entry => locality_entry_kind entry = Locality_Attribute)
  val slots =
    map (fn entry => (locality_entry_idx entry, #footprint entry)) entries
  val _ = AutoLocality_Assert.run_suite "Contexts/repeated-record-arguments"
    [ ("both record positions are registered",
         fn () => AutoLocality_Assert.check "pair_attr slots"
           (member (op =) slots (0, ["xa"]) andalso
            member (op =) slots (1, ["xb"]) andalso
            length entries = 2)) ]
\<close>

(*<*)
end
(*>*)
