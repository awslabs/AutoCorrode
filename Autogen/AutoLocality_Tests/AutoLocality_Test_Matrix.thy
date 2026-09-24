(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Matrix
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Generated cancellation matrix at the top level\<close>

text\<open>A four-field record with a rich set of operations and attributes - single- and multi-field
footprints, opaque operations (bodies that read the old field value), bare field updates, field
selectors, and single- and multi-field attributes. The generator enumerates every
attribute-over-telescope combination and checks each against the independent footprint oracle,
turning a handful of declarations into many hundreds of checked cases.

We silence the locality tracer for this theory (@{verbatim \<open>locality_trace_level = 0\<close>}): the matrix
fires the simproc many hundreds of times and the per-call trace would otherwise dominate the build
output. The cancellation behaviour is unaffected.\<close>

declare [[locality_trace_level = 0]]

datatype_record quad =
  ma :: nat
  mb :: nat
  mc :: nat
  md :: nat

locality_init for quad

\<comment>\<open>Opaque single-field operations (read the old value, so unfolding really runs).\<close>
definition mop_a :: \<open>nat \<Rightarrow> quad \<Rightarrow> quad\<close> where \<open>mop_a k R \<equiv> update_ma (\<lambda>old. old + k + ma R) R\<close>
definition mop_b :: \<open>nat \<Rightarrow> quad \<Rightarrow> quad\<close> where \<open>mop_b k R \<equiv> update_mb (\<lambda>old. old * k) R\<close>
\<comment>\<open>Set-style single-field operations.\<close>
definition mset_c :: \<open>nat \<Rightarrow> quad \<Rightarrow> quad\<close> where \<open>mset_c k \<equiv> update_mc (\<lambda>_. k)\<close>
definition mset_d :: \<open>nat \<Rightarrow> quad \<Rightarrow> quad\<close> where \<open>mset_d k \<equiv> update_md (\<lambda>_. k)\<close>
\<comment>\<open>A two-field operation.\<close>
definition mop_cd :: \<open>quad \<Rightarrow> quad\<close> where \<open>mop_cd R \<equiv> update_mc (\<lambda>x. x + 1) (update_md (\<lambda>y. y + 1) R)\<close>

\<comment>\<open>Attributes: single-field and multi-field.\<close>
definition mhas_a :: \<open>quad \<Rightarrow> bool\<close> where \<open>mhas_a R \<equiv> ma R > 0\<close>
definition mread_b :: \<open>quad \<Rightarrow> nat\<close> where \<open>mread_b R \<equiv> mb R + 1\<close>
definition mab_sum :: \<open>quad \<Rightarrow> nat\<close> where \<open>mab_sum R \<equiv> ma R + mb R\<close>
definition mcd_sum :: \<open>quad \<Rightarrow> nat\<close> where \<open>mcd_sum R \<equiv> mc R + md R\<close>

locality_lemma for quad: \<open>mop_a\<close> footprint [ma] .
locality_lemma for quad: \<open>mop_b\<close> footprint [mb] .
locality_lemma for quad: \<open>mset_c\<close> footprint [mc] .
locality_lemma for quad: \<open>mset_d\<close> footprint [md] .
locality_lemma for quad: \<open>mop_cd\<close> footprint [mc, md] .
locality_lemma for quad: \<open>mhas_a\<close> footprint [ma] .
locality_lemma for quad: \<open>mread_b\<close> footprint [mb] .
locality_lemma for quad: \<open>mab_sum\<close> footprint [ma, mb] .
locality_lemma for quad: \<open>mcd_sum\<close> footprint [mc, md] .

ML\<open>
  val ctxt = \<^context>
  val rn = "AutoLocality_Test_Matrix.quad"

  \<comment>\<open>User attributes and field-selector attributes; selectors are attributes too.\<close>
  val attrs : AutoLocality_Gen.item list =
    [ {name="mhas_a",  fp=["ma"],       arg=""}, {name="mread_b", fp=["mb"],       arg=""},
      {name="mab_sum", fp=["ma","mb"],  arg=""}, {name="mcd_sum", fp=["mc","md"],  arg=""},
      {name="ma", fp=["ma"], arg=""}, {name="mb", fp=["mb"], arg=""},
      {name="mc", fp=["mc"], arg=""}, {name="md", fp=["md"], arg=""} ]

  \<comment>\<open>Operations spanning all footprint shapes.\<close>
  val ops : AutoLocality_Gen.item list =
    [ {name="mop_a",  fp=["ma"],      arg="ka"}, {name="mop_b",  fp=["mb"],      arg="kb"},
      {name="mset_c", fp=["mc"],      arg="kc"}, {name="mset_d", fp=["md"],      arg="kd"},
      {name="mop_cd", fp=["mc","md"], arg=""} ]

  \<comment>\<open>Attributes are registered under their base name (match index 0).\<close>
  fun key (a : AutoLocality_Gen.item) = #name a

  fun assert_commutes a b =
    AutoLocality_Assert.check (a ^ " commutes with " ^ b)
      (Option.isSome (locality_prove_commutativity ctxt rn
        (Syntax.read_term ctxt a) (Syntax.read_term ctxt b)))

  fun normalization_result term_str =
    let
      val term = Syntax.read_term ctxt term_str
      val ctm = Thm.cterm_of ctxt term
      val (head, args) = Term.strip_comb term
      val attribute =
        (case select_locality_entry ctxt rn "attribute" head args of
           SOME (_, entry) => entry
         | NONE => error ("No attribute entry for " ^ term_str))
      val decomposed = decompose_locality_telescope ctxt rn attribute term
      val (_, hoisted, front, back) = hoist_redundant_operations decomposed
    in
      locality_prove_hoisting_by_normalization ctxt rn ctm
        decomposed hoisted front back
    end

\<close>

ML\<open>
  val _ = AutoLocality_Assert.run_suite "Matrix/normalization-fast-path"
    [ ("front-only normalization",
         fn () => AutoLocality_Assert.check "front-only normalization"
           (Option.isSome (normalization_result "mhas_a (mset_c kc R)"))),
      ("simple mixed normalization",
         fn () => AutoLocality_Assert.check "simple mixed normalization"
           (Option.isSome
             (normalization_result "mhas_a (mop_a ka (mset_c kc R))"))),
      ("multi-field mixed normalization falls back",
         fn () => AutoLocality_Assert.check "multi-field normalization boundary"
           (not (Option.isSome
             (normalization_result "mhas_a (mop_a ka (mop_cd R))")))) ]
\<close>

ML\<open>
  val n2 = AutoLocality_Gen.run_matrix "Matrix/top-level depth<=2"
    ctxt rn key attrs ops 2 "R"
  val _ = AutoLocality_Assert.check "depth<=2 matrix retained all 240 cases" (n2 = 240)
\<close>

text\<open>A depth-3 sweep over a representative subset - one single-field attribute, one multi-field
attribute, and three operations of different footprint shapes - adds longer telescopes (every
triple) without multiplying the case count across all eight attributes.\<close>

ML\<open>
  val ctxt = \<^context>
  val rn = "AutoLocality_Test_Matrix.quad"
  val attrs3 : AutoLocality_Gen.item list =
    [ {name="mhas_a", fp=["ma"], arg=""}, {name="mcd_sum", fp=["mc","md"], arg=""} ]
  val ops3 : AutoLocality_Gen.item list =
    [ {name="mop_a",  fp=["ma"],      arg="ka"}, {name="mset_c", fp=["mc"],      arg="kc"},
      {name="mop_cd", fp=["mc","md"], arg=""} ]
  fun key (a : AutoLocality_Gen.item) = #name a
\<close>

ML\<open>
  val n3 = AutoLocality_Gen.run_matrix "Matrix/top-level depth<=3"
    ctxt rn key attrs3 ops3 3 "R"
  val _ = AutoLocality_Assert.check "depth<=3 matrix retained all 78 cases" (n3 = 78)
\<close>

subsection\<open>All ordered disjoint operation pairs\<close>

text\<open>Exercise every ordered disjoint pair through the public on-demand commutativity API after the
cold cancellation matrices. No theorem is registered in the proof context.\<close>

ML\<open>val _ = assert_commutes "mop_a" "mop_b"\<close>
ML\<open>val _ = assert_commutes "mop_b" "mop_a"\<close>
ML\<open>val _ = assert_commutes "mop_a" "mset_c"\<close>
ML\<open>val _ = assert_commutes "mset_c" "mop_a"\<close>
ML\<open>val _ = assert_commutes "mop_a" "mset_d"\<close>
ML\<open>val _ = assert_commutes "mset_d" "mop_a"\<close>
ML\<open>val _ = assert_commutes "mop_a" "mop_cd"\<close>
ML\<open>val _ = assert_commutes "mop_cd" "mop_a"\<close>
ML\<open>val _ = assert_commutes "mop_b" "mset_c"\<close>
ML\<open>val _ = assert_commutes "mset_c" "mop_b"\<close>
ML\<open>val _ = assert_commutes "mop_b" "mset_d"\<close>
ML\<open>val _ = assert_commutes "mset_d" "mop_b"\<close>
ML\<open>val _ = assert_commutes "mop_b" "mop_cd"\<close>
ML\<open>val _ = assert_commutes "mop_cd" "mop_b"\<close>
ML\<open>val _ = assert_commutes "mset_c" "mset_d"\<close>
ML\<open>val _ = assert_commutes "mset_d" "mset_c"\<close>

subsection\<open>The oracle has teeth: a deliberately wrong oracle is caught\<close>

text\<open>To show the matrix is not a tautology, we run a batch of cases against a corrupted oracle that
claims \<^emph>\<open>everything\<close> cancels. The simproc must disagree on a non-trivial number of them; a count of
zero would mean the oracle and simproc were not actually cross-checking.\<close>

ML\<open>
  val ctxt = \<^context>
  val rn = "AutoLocality_Test_Matrix.quad"
  val attrs = [ {name="mab_sum", fp=["ma","mb"], arg=""} : AutoLocality_Gen.item ]
  val ops = [ {name="mop_a", fp=["ma"], arg="ka"} : AutoLocality_Gen.item,
              {name="mset_c", fp=["mc"], arg="kc"} : AutoLocality_Gen.item ]
  val cases = maps (fn a => map (fn t => (a, t)) (AutoLocality_Gen.telescopes ops 2)) attrs
  \<comment>\<open>Corrupted expectation: claim ALL operations cancel (residual = bare base). Count how many
     cases the real simproc disagrees with.\<close>
  fun caught (a, t) =
    let
      val lhs = AutoLocality_Gen.build_term a t "R"
      val wrong_rhs = AutoLocality_Gen.build_term a [] "R"
    in
      case AutoLocality_Assert.simproc_on ctxt rn (#name a) lhs of
        NONE => true
      | SOME thm =>
          (case Thm.prop_of thm of
             Const ("Pure.eq", _) $ _ $ rhs => not (Term.aconv (rhs, Syntax.read_term ctxt wrong_rhs))
           | _ => true)
    end
  val n = length (List.filter caught cases)
  val _ = AutoLocality_Assert.check
            ("wrong oracle caught on " ^ Int.toString n ^ "/" ^ Int.toString (length cases) ^ " cases")
            (n > 0)
\<close>

(*<*)
end
(*>*)
