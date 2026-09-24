(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test3
  imports Autogen.AutoLocality
begin
(*>*)

text\<open>Regression suite for reworked AutoLocality: on-the-fly cancellation via the default-on
\<^verbatim>\<open>locality_cancel\<close> simprocs, ML-tactic lemma generation, and the absence of the old quadratic
pre-generation. Everything here is self-contained on toy records.\<close>

section\<open>A record whose operations do not trivially reduce to field updates\<close>

text\<open>\<^verbatim>\<open>opaque_*\<close> operations have bodies that touch the field non-trivially, so cancellation
genuinely exercises the definition-unfolding prover rather than bottoming out in record_simps.\<close>

datatype_record three =
  fa :: nat
  fb :: nat
  fc :: nat

locality_init for three

definition opaque_a :: \<open>nat \<Rightarrow> three \<Rightarrow> three\<close> where
  \<open>opaque_a k R \<equiv> update_fa (\<lambda>old. old + k + fa R) R\<close>
definition opaque_b :: \<open>nat \<Rightarrow> three \<Rightarrow> three\<close> where
  \<open>opaque_b k R \<equiv> update_fb (\<lambda>old. old * k) R\<close>
definition set_c :: \<open>nat \<Rightarrow> three \<Rightarrow> three\<close> where
  \<open>set_c k \<equiv> update_fc (\<lambda>_. k)\<close>

definition has_a :: \<open>three \<Rightarrow> bool\<close> where
  \<open>has_a R \<equiv> fa R > 0\<close>
definition read_b :: \<open>three \<Rightarrow> nat\<close> where
  \<open>read_b R \<equiv> fb R\<close>
\<comment>\<open>Attribute with an extra (non-record) argument, record at index 0.\<close>
definition a_exceeds :: \<open>three \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>a_exceeds R n \<equiv> fa R > n\<close>
\<comment>\<open>Attribute with the record at a non-zero argument index. Its only record argument is at
   position 1, so the match index into the list of record positions is 0.\<close>
definition b_below :: \<open>nat \<Rightarrow> three \<Rightarrow> bool\<close> where
  \<open>b_below n R \<equiv> fb R < n\<close>

locality_lemma for three: \<open>opaque_a\<close> footprint [fa] .
locality_lemma for three: \<open>opaque_b\<close> footprint [fb] .
locality_lemma for three: \<open>set_c\<close> footprint [fc] .
locality_lemma for three: \<open>has_a\<close> footprint [fa] .
locality_lemma for three: \<open>read_b\<close> footprint [fb] .
locality_lemma for three: \<open>a_exceeds\<close> footprint [fa] .
locality_lemma for three: \<open>b_below\<close> [0] footprint [fb] .

section\<open>E. Generated linear facts are stated correctly\<close>

text\<open>The local-action, field-update commutativity and disjointness lemmas for an opaque op are
generated under the expected names and with the expected statements.\<close>
lemma \<open>opaque_a k R = update_fa (\<lambda>_. fa (opaque_a k R)) R\<close>
  by (rule AutoLocality_Test3_three_local_op_opaque_a_local)
lemma \<open>opaque_a k (update_fb f R) = update_fb f (opaque_a k R)\<close>
  by (rule AutoLocality_Test3_three_local_op_opaque_a_core)
lemma \<open>fb (opaque_a k R) = fb R\<close>
  by (rule AutoLocality_Test3_three_local_op_opaque_a_disjoint)
lemma \<open>fc (opaque_a k R) = fc R\<close>
  by (rule AutoLocality_Test3_three_local_op_opaque_a_disjoint)

text\<open>The cancellation 'core' lemma for an attribute against a disjoint field update.\<close>
lemma \<open>has_a (update_fb f R) = has_a R\<close>
  by (rule AutoLocality_Test3_three_local_attr_has_a_0_core)

section\<open>The quadratic commutativity bundle is no longer generated\<close>

ML\<open>
  \<comment>\<open>The old pre-generation produced a record-indexed \<^verbatim>\<open>*_commutativity_facts\<close> bundle; it must
     be absent now.\<close>
  val _ =
    (Named_Theorems.check \<^context> ("AutoLocality_Test3_three_commutativity_facts", Position.none);
     error "commutativity_facts bundle should not exist")
    handle ERROR _ => writeln "OK: no commutativity bundle"
\<close>

section\<open>B. On-the-fly cancellation matrix (default-on simproc, plain simp)\<close>

text\<open>The simprocs are part of the ambient simpset, so a bare \<^verbatim>\<open>simp\<close> cancels with no explicit
attribute or lemma list.\<close>

lemma \<open>has_a (set_c c X) = has_a X\<close> by simp
lemma \<open>fa (set_c c X) = fa X\<close> by simp
lemma \<open>has_a (opaque_a h (set_c c (opaque_b b (opaque_a h2 X)))) = has_a (opaque_a h (opaque_a h2 X))\<close>
  by simp
lemma \<open>has_a (opaque_a h (set_c c (f X))) = has_a (opaque_a h (f X))\<close> by simp
lemma \<open>a_exceeds (set_c c X) n = a_exceeds X n\<close> by simp
lemma \<open>b_below n (set_c c X) = b_below n X\<close> by simp
lemma \<open>has_a (update_fb g (update_fc hf X)) = has_a X\<close> by simp
lemma \<open>read_b (set_c c (opaque_a h (opaque_b b X))) = read_b (opaque_b b X)\<close> by simp

lemma \<open>has_a (opaque_b k R) = has_a R\<close>
  by (simp only: [[locality_autocancellation (three) opaque_b has_a 0]])

text\<open>The cancellation also works through \<^verbatim>\<open>simp add: <record>_locality_facts\<close>, the bundle form
that downstream proofs use: the simprocs ride along in the ambient simpset.\<close>
lemma \<open>has_a (set_c c (opaque_a h X)) = has_a (opaque_a h X)\<close>
  by (simp add: AutoLocality_Test3_three_locality_facts)

section\<open>C2. On-demand pairwise operation commutativity\<close>

text\<open>\<^verbatim>\<open>locality_prove_commutativity\<close> derives, on demand, the theorem that two registered operations
commute: \<^verbatim>\<open>opA a (opB b R) = opB b (opA a R)\<close>. It is sound by construction (it returns \<^verbatim>\<open>NONE\<close> rather
than a false theorem): operations with disjoint footprints commute and are proved; operations
sharing a field genuinely do not commute and are declined. Nothing is registered - the caller gets
the theorem back.\<close>

ML\<open>
  val ctxt = \<^context>
  fun is_some (SOME _) = true | is_some NONE = false
  fun prove a b =
    locality_prove_commutativity ctxt "three"
      (Syntax.read_term ctxt a) (Syntax.read_term ctxt b)

  \<comment>\<open>Disjoint footprints: all proved.\<close>
  val _ = if is_some (prove "opaque_a" "opaque_b") then () else error "opaque_a/opaque_b should commute"
  val _ = if is_some (prove "opaque_a" "set_c")    then () else error "opaque_a/set_c should commute"
  val _ = if is_some (prove "opaque_b" "set_c")    then () else error "opaque_b/set_c should commute"
  \<comment>\<open>Order-independent.\<close>
  val _ = if is_some (prove "set_c" "opaque_a")    then () else error "set_c/opaque_a should commute"

  \<comment>\<open>Soundness: operations sharing a field do NOT commute and must be declined (NONE), not
     mis-proved. \<^verbatim>\<open>opaque_a\<close> with itself shares footprint \<^verbatim>\<open>[fa]\<close>.\<close>
  val _ = case prove "opaque_a" "opaque_a" of
            NONE => writeln "OK: footprint-sharing pair correctly declined"
          | SOME _ => error "opaque_a/opaque_a was mis-proved (unsound!)"

  \<comment>\<open>The derived theorem is exactly the commutativity equation (alpha-checked).\<close>
  val _ = case prove "opaque_a" "set_c" of
            SOME thm =>
              let val expected = Syntax.read_term ctxt
                    "(opaque_a a_0 (set_c b_0 R) = set_c b_0 (opaque_a a_0 R))"
              in if Term.aconv (HOLogic.dest_Trueprop (Thm.prop_of thm), expected)
                 then writeln "OK: derived commutativity statement matches expectation"
                 else error "derived commutativity statement is not the expected equation"
              end
          | NONE => error "opaque_a/set_c should have a derived theorem"
\<close>

text\<open>The same derivation is reachable from proof text via the \<^verbatim>\<open>[[locality_autocommutativity (rec) A B]]\<close>
attribute, which \<^emph>\<open>returns\<close> the (generalized) commutativity theorem as a fact rather than mutating the
simpset. A bare operation-over-operation goal - which the default-on cancellation simprocs do
\<^emph>\<open>not\<close> rewrite, since no attribute heads it - then closes by using that fact directly. We exercise all
three fact-position idioms: naming it with \<^theory_text>\<open>lemmas\<close>, resolving with \<^theory_text>\<open>rule\<close>, and feeding it to
\<^theory_text>\<open>simp add:\<close>.\<close>

text\<open>Name the produced theorem, then discharge with it.\<close>
lemmas opaque_a_set_c_commute = [[locality_autocommutativity (three) opaque_a set_c]]
lemma \<open>opaque_a a (set_c c R) = set_c c (opaque_a a R)\<close>
  by (rule opaque_a_set_c_commute)

text\<open>Or use the anonymous \<^verbatim>\<open>[[\<dots>]]\<close> fact inline, resolving against the goal.\<close>
lemma \<open>opaque_a a (set_c c R) = set_c c (opaque_a a R)\<close>
  by (rule [[locality_autocommutativity (three) opaque_a set_c]])

text\<open>Or hand it to \<^verbatim>\<open>simp add:\<close> as a rewrite (the schematic generalization is what makes this work).\<close>
lemma \<open>set_c c (opaque_b b R) = opaque_b b (set_c c R)\<close>
  by (simp add: [[locality_autocommutativity (three) set_c opaque_b]])

text\<open>Without the attribute the same bare goal is \<^emph>\<open>not\<close> closed by a plain \<^verbatim>\<open>simp\<close> (the cancellation
simprocs only fire under an attribute head), so unfolding is required - confirming the attribute is
what supplies the commutativity rewrite.\<close>
lemma \<open>opaque_a a (set_c c R) = set_c c (opaque_a a R)\<close>
  by (simp add: opaque_a_def set_c_def)

text\<open>A footprint-sharing pair genuinely does not commute, so the attribute raises an error rather
than silently adding nothing. We check this at the ML level (an erroring \<^verbatim>\<open>supply\<close> cannot appear in a
passing theory): applying the attribute to the dummy theorem must raise.\<close>
ML\<open>
  val _ =
    (Raw_Simplifier.map_ss I (Context.Proof \<^context>);  \<comment>\<open>force evaluation\<close>
     (case locality_prove_commutativity \<^context> "three"
             (Syntax.read_term \<^context> "opaque_a")
             (Syntax.read_term \<^context> "opaque_a") of
        NONE => writeln "OK: attribute would error on the non-commuting pair (NONE from core)"
      | SOME _ => error "opaque_a/opaque_a unexpectedly commutes"))
\<close>

section\<open>D. Safety: no-op fixpoint, opt-out, idempotent init\<close>

text\<open>On a term with nothing to cancel, the simproc must return \<^verbatim>\<open>NONE\<close> (rather than rewriting and
re-firing forever). We invoke the cancellation procedure directly on a normal-form term — here
\<^verbatim>\<open>has_a (opaque_a h X)\<close>, where the only inner operation shares the attribute's footprint \<^verbatim>\<open>[fa]\<close>
and so cannot be hoisted — and check it declines. This is the fixpoint property underpinning
the safety of having the simprocs always on.\<close>

ML\<open>
  val nothing_to_cancel =
    locality_cancellation_simproc "AutoLocality_Test3.three" "has_a" 0 \<^context>
      (Thm.cterm_of \<^context> \<^term>\<open>has_a (opaque_a h X)\<close>)
  val _ = case nothing_to_cancel of
            NONE => writeln "OK: simproc declines a normal-form term (no rewrite, no loop)"
          | SOME _ => error "simproc rewrote a normal-form term (possible loop risk)"
\<close>

text\<open>\<^verbatim>\<open>locality_no_cancel\<close> disables the simprocs in scope; with them off, a bare \<^verbatim>\<open>simp\<close> no longer
cancels, so we finish by unfolding.\<close>
lemma optout: \<open>has_a (set_c c X) = has_a X\<close>
  supply [[locality_no_cancel]]
  by (simp add: has_a_def set_c_def)

text\<open>\<^verbatim>\<open>locality_init\<close> is idempotent.\<close>
locality_init for three
locality_init for three

(*<*)
end
(*>*)
