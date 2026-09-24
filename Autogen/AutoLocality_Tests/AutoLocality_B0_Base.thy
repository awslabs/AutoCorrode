(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_B0_Base
  imports Autogen.AutoLocality
begin
(*>*)

section\<open>Black-box baseline and public compatibility\<close>

text\<open>
This theory provides a small shared record for the B0 black-box suite.  The
proofs deliberately use generated facts, ambient simplification, and
restricted simplification rather than inspecting AutoLocality's registry.
\<close>

ML\<open>
structure AutoLocality_B0_Blackbox = struct

  fun capture_noninterrupt f =
    (case Exn.capture f () of
       Exn.Res result => SOME result
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn else NONE)

  fun simplify_term ctxt source =
    let
      val cterm = Thm.cterm_of ctxt (Syntax.read_term ctxt source)
      val rewrite = Simplifier.rewrite ctxt cterm
    in
      Thm.term_of (Thm.rhs_of rewrite)
    end

  fun proves_by_ambient_simp ctxt source =
    let
      val goal = Syntax.read_prop ctxt source
    in
      Option.isSome (capture_noninterrupt (fn () =>
        Goal.prove ctxt [] [] goal
          (fn {context, ...} => asm_full_simp_tac context 1)))
    end

  fun assert_normal_form label ctxt source expected =
    let
      val actual = simplify_term ctxt source
      val expected_term = Syntax.read_term ctxt expected
    in
      if Term.aconv (actual, expected_term) then ()
      else error ("AutoLocality B0 normal-form probe failed: " ^ label)
    end

  fun assert_proves label ctxt source =
    if proves_by_ambient_simp ctxt source then ()
    else error ("AutoLocality B0 positive simp probe failed: " ^ label)

  fun assert_not_proves label ctxt source =
    if proves_by_ambient_simp ctxt source then
      error ("AutoLocality B0 negative simp probe failed: " ^ label)
    else ()

end
\<close>

datatype_record b0_state =
  b0_a :: nat
  b0_b :: nat
  b0_c :: nat
  b0_d :: nat

locality_init for b0_state

definition b0_set_a :: \<open>nat \<Rightarrow> b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_set_a n \<equiv> update_b0_a (\<lambda>_. n)\<close>

definition b0_set_b :: \<open>nat \<Rightarrow> b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_set_b n \<equiv> update_b0_b (\<lambda>_. n)\<close>

definition b0_set_c :: \<open>nat \<Rightarrow> b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_set_c n \<equiv> update_b0_c (\<lambda>_. n)\<close>

definition b0_set_d :: \<open>nat \<Rightarrow> b0_state \<Rightarrow> b0_state\<close> where
  \<open>b0_set_d n \<equiv> update_b0_d (\<lambda>_. n)\<close>

definition b0_has_a :: \<open>b0_state \<Rightarrow> bool\<close> where
  \<open>b0_has_a R \<equiv> b0_a R > 0\<close>

definition b0_read_b :: \<open>b0_state \<Rightarrow> nat\<close> where
  \<open>b0_read_b R \<equiv> b0_b R\<close>

locality_lemma for b0_state: \<open>b0_set_a\<close> footprint [b0_a] .
locality_lemma for b0_state: \<open>b0_set_b\<close> footprint [b0_b] .
locality_lemma for b0_state: \<open>b0_set_c\<close> footprint [b0_c] .
locality_lemma for b0_state: \<open>b0_set_d\<close> footprint [b0_d] .
locality_lemma for b0_state: \<open>b0_has_a\<close> footprint [b0_a] .
locality_lemma for b0_state: \<open>b0_read_b\<close> footprint [b0_b] .

subsection\<open>Immediate same-target duplicate registration\<close>

text\<open>
These duplicates occur immediately in the same local-theory target.  They are
distinct from descendant replay: exact registration is required to be
idempotent before any import or locale morphism is involved.
\<close>

locality_lemma for b0_state: \<open>b0_set_c\<close> footprint [b0_c] .
locality_lemma for b0_state: \<open>b0_has_a\<close> footprint [b0_a] .

subsection\<open>Ambient and restricted production paths\<close>

lemma b0_base_ambient:
  shows \<open>b0_has_a (b0_set_c n (b0_set_b m R)) = b0_has_a R\<close>
  by simp

lemma b0_base_restricted:
  shows \<open>b0_has_a (b0_set_c n R) = b0_has_a R\<close>
  by (simp only: [[locality_cancel]])

ML\<open>
  val ctxt = \<^context>
  val _ = AutoLocality_B0_Blackbox.assert_normal_form
    "same-target duplicate registrations retain one semantic rewrite"
    ctxt "b0_has_a (b0_set_c n R)" "b0_has_a R"
  val _ = AutoLocality_B0_Blackbox.assert_proves
    "same-target duplicate registrations remain usable"
    ctxt "b0_has_a (b0_set_c n R) = b0_has_a R"
\<close>

lemma b0_base_bundle:
  shows \<open>b0_has_a (b0_set_d n (b0_set_a m R)) =
    b0_has_a (b0_set_a m R)\<close>
  by (simp add: AutoLocality_B0_Base_b0_state_locality_facts)

subsection\<open>Generated linear certificate names\<close>

lemma b0_base_operation_core_name:
  shows \<open>b0_set_a n (update_b0_b f R) =
    update_b0_b f (b0_set_a n R)\<close>
  by (rule AutoLocality_B0_Base_b0_state_local_op_b0_set_a_core)

lemma b0_base_operation_disjoint_name:
  shows \<open>b0_b (b0_set_a n R) = b0_b R\<close>
  by (rule AutoLocality_B0_Base_b0_state_local_op_b0_set_a_disjoint)

lemma b0_base_attribute_core_name:
  shows \<open>b0_has_a (update_b0_b f R) = b0_has_a R\<close>
  by (rule AutoLocality_B0_Base_b0_state_local_attr_b0_has_a_0_core)

lemma b0_base_on_demand_cancellation:
  shows \<open>b0_has_a (b0_set_c n R) = b0_has_a R\<close>
  by (simp only:
    [[locality_autocancellation (b0_state) b0_set_c b0_has_a 0]])

lemma b0_base_on_demand_commutativity:
  shows \<open>b0_set_b m (b0_set_c n R) =
    b0_set_c n (b0_set_b m R)\<close>
  by (rule
    [[locality_autocommutativity (b0_state) b0_set_b b0_set_c]])

text\<open>Repeated record initialization is part of the public compatibility
surface and must remain idempotent.\<close>

locality_init for b0_state
locality_init for b0_state

(*<*)
end
(*>*)
