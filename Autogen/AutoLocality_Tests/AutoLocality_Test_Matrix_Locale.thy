(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Matrix_Locale
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Generated cancellation matrix in locale and interpretation contexts\<close>

text\<open>The same generator as @{theory_text \<open>AutoLocality_Test_Matrix\<close>}, but exercising the locale code
paths that the locale fix is about: a parameter-using attribute and a parameter-using operation are
defined in a locale and registered from a @{command context} re-entry, alongside top-level
parameter-free operations to cancel against. The matrix runs three times - inside the locale, and
under two distinct @{command interpretation}s - to show the cancellation simproc transports through
interpretation across the whole telescope matrix, not just on the hand-picked cases in
@{theory_text \<open>AutoLocality_Test_Locale\<close>}.

The matrix names carry the context prefix (the bare name in-locale, @{verbatim \<open>i1.\<close>}/@{verbatim \<open>i2.\<close>}
under the interpretations), while the simproc key is always the registered base name; the
@{verbatim \<open>key\<close>} argument to @{ML AutoLocality_Gen.run_matrix} strips the prefix back to the base.\<close>

declare [[locality_trace_level = 0]]

datatype_record lrec =
  va :: nat
  vb :: nat
  vc :: nat
  vd :: nat

locality_init for lrec

\<comment>\<open>Top-level parameter-free operations on each field, to cancel against (these are found by the
   picker in every context, unlike a parameter-free op defined inside the locale).\<close>
definition vset_a :: \<open>nat \<Rightarrow> lrec \<Rightarrow> lrec\<close> where \<open>vset_a k \<equiv> update_va (\<lambda>_. k)\<close>
definition vset_b :: \<open>nat \<Rightarrow> lrec \<Rightarrow> lrec\<close> where \<open>vset_b k \<equiv> update_vb (\<lambda>_. k)\<close>
definition vset_c :: \<open>nat \<Rightarrow> lrec \<Rightarrow> lrec\<close> where \<open>vset_c k \<equiv> update_vc (\<lambda>_. k)\<close>
definition vset_d :: \<open>nat \<Rightarrow> lrec \<Rightarrow> lrec\<close> where \<open>vset_d k \<equiv> update_vd (\<lambda>_. k)\<close>

locality_lemma for lrec: \<open>vset_a\<close> footprint [va] .
locality_lemma for lrec: \<open>vset_b\<close> footprint [vb] .
locality_lemma for lrec: \<open>vset_c\<close> footprint [vc] .
locality_lemma for lrec: \<open>vset_d\<close> footprint [vd] .

locale scaler =
  fixes bump :: \<open>nat \<Rightarrow> nat\<close>
begin

\<comment>\<open>Parameter-using attributes: single- and multi-field.\<close>
definition big_a :: \<open>lrec \<Rightarrow> bool\<close> where \<open>big_a R \<equiv> bump (va R) > 10\<close>
definition sum_ab :: \<open>lrec \<Rightarrow> nat\<close> where \<open>sum_ab R \<equiv> bump (va R) + vb R\<close>
\<comment>\<open>A parameter-using operation.\<close>
definition bump_a :: \<open>lrec \<Rightarrow> lrec\<close> where \<open>bump_a R \<equiv> update_va bump R\<close>

end

text\<open>Register the locale constants from a re-entry (the auto-derivation needs the definitions to be
established), with their short names.\<close>

context scaler begin
locality_lemma for lrec: \<open>big_a\<close> footprint [va] .
locality_lemma for lrec: \<open>sum_ab\<close> footprint [va, vb] .
locality_lemma for lrec: \<open>bump_a\<close> footprint [va] .
end

subsection\<open>Matrix inside the locale\<close>

context scaler begin
ML\<open>
  val ctxt = \<^context>
  val rn = "AutoLocality_Test_Matrix_Locale.lrec"
  \<comment>\<open>In-locale: the abbreviations apply the parameter implicitly, so names are bare short names.\<close>
  val attrs : AutoLocality_Gen.item list =
    [ {name="big_a", fp=["va"], arg=""}, {name="sum_ab", fp=["va","vb"], arg=""} ]
  val ops : AutoLocality_Gen.item list =
    [ {name="bump_a", fp=["va"], arg=""}, {name="vset_b", fp=["vb"], arg="kb"},
      {name="vset_c", fp=["vc"], arg="kc"}, {name="vset_d", fp=["vd"], arg="kd"} ]
  fun key (a : AutoLocality_Gen.item) = #name a
  val n = AutoLocality_Gen.run_matrix "Locale-matrix/in-locale" ctxt rn key attrs ops 2 "R"
\<close>
end

subsection\<open>Matrix under two interpretations\<close>

interpretation i1: scaler \<open>\<lambda>n. n + 1\<close> .
interpretation i2: scaler \<open>\<lambda>n. n * 3\<close> .

ML\<open>
  val ctxt = \<^context>
  val rn = "AutoLocality_Test_Matrix_Locale.lrec"

  \<comment>\<open>Under an interpretation, attribute/operation names carry the interpretation prefix; the
     registered simproc key is the base name (strip everything up to the last dot).\<close>
  fun base nm = List.last (String.tokens (fn c => c = #".") nm)
  fun key (a : AutoLocality_Gen.item) = base (#name a)

  fun attrs pre = [ {name=pre^"big_a", fp=["va"], arg=""} : AutoLocality_Gen.item,
                    {name=pre^"sum_ab", fp=["va","vb"], arg=""} : AutoLocality_Gen.item ]
  fun ops pre = [ {name=pre^"bump_a", fp=["va"], arg=""} : AutoLocality_Gen.item,
                  {name="vset_b", fp=["vb"], arg="kb"} : AutoLocality_Gen.item,
                  {name="vset_c", fp=["vc"], arg="kc"} : AutoLocality_Gen.item,
                  {name="vset_d", fp=["vd"], arg="kd"} : AutoLocality_Gen.item ]

  val n1 = AutoLocality_Gen.run_matrix "Locale-matrix/interp i1" ctxt rn key (attrs "i1.") (ops "i1.") 2 "R"
  val n2 = AutoLocality_Gen.run_matrix "Locale-matrix/interp i2" ctxt rn key (attrs "i2.") (ops "i2.") 2 "R"
  val _ = writeln ("Locale matrix checked " ^ Int.toString (n1 + n2) ^ " interpreted cases")
\<close>

(*<*)
end
(*>*)
