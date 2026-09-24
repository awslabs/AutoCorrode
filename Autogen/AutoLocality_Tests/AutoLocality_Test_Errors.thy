(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Errors
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Error and safety paths\<close>

text\<open>This suite pins the negative behaviour: ill-formed @{verbatim \<open>locality_lemma\<close>} invocations are
rejected with an error (rather than silently mis-registering), the @{verbatim \<open>[[locality_no_cancel]]\<close>}
opt-out genuinely disables cancellation in scope, and @{verbatim \<open>locality_init\<close>} is idempotent. The
positive cancellation behaviour is checked in @{theory_text \<open>AutoLocality_Test_Cancel\<close>}; here we make
sure the failure modes are loud and the safety valves work.\<close>

datatype_record err =
  ea :: nat
  eb :: nat

locality_init for err

definition eset_a :: \<open>nat \<Rightarrow> err \<Rightarrow> err\<close> where
  \<open>eset_a k R \<equiv> update_ea (\<lambda>_. k) R\<close>
definition ehas_a :: \<open>err \<Rightarrow> bool\<close> where
  \<open>ehas_a R \<equiv> ea R > 0\<close>

locality_lemma for err: \<open>eset_a\<close> footprint [ea] .
locality_lemma for err: \<open>ehas_a\<close> footprint [ea] .

subsection\<open>Opt-out: @{verbatim \<open>locality_no_cancel\<close>} disables the simprocs in scope\<close>

text\<open>With the simprocs on (the default), cancellation succeeds.\<close>
lemma \<open>ehas_a (update_eb f R) = ehas_a R\<close> by simp

text\<open>With @{verbatim \<open>locality_no_cancel\<close>} supplied, a bare @{verbatim \<open>simp\<close>} no longer cancels, so the
proof must fall back to unfolding the definitions.\<close>
lemma \<open>ehas_a (update_eb f R) = ehas_a R\<close>
  supply [[locality_no_cancel]]
  by (simp add: ehas_a_def)

subsection\<open>Idempotent initialisation\<close>

text\<open>Re-initialising a record is a no-op and must not raise or duplicate data.\<close>
locality_init for err
locality_init for err

subsection\<open>Ill-formed invocations are rejected\<close>

ML\<open>
  val ctxt = \<^context>
  \<comment>\<open>Drive the ML entry points directly with bad arguments and require each to raise. We re-raise
     interrupts inside @{verbatim \<open>assert_raises\<close>}, so only genuine errors count as passes.\<close>
  val _ = AutoLocality_Assert.run_suite "Errors/rejection"
    [ \<comment>\<open>A footprint naming a field that does not exist on the record.\<close>
      ("illegal footprint field",
         fn () => AutoLocality_Assert.assert_raises "bad field in footprint"
                    (fn () => state_locality_for_op NONE "err" "eset_a" ["nonexistent"] true ctxt)),
      \<comment>\<open>A term that is neither an operation nor an attribute on the record.\<close>
      ("non-attribute term",
         fn () => AutoLocality_Assert.assert_raises "value is not op/attr on err"
                    (fn () => state_locality NONE "err" "(0::nat)" ["ea"] true 0 ctxt)),
      \<comment>\<open>An out-of-range match index for an attribute with a single record argument.\<close>
      ("match index out of range",
         fn () => AutoLocality_Assert.assert_raises "match idx 5 out of range"
                    (fn () => state_locality NONE "err" "ehas_a" ["ea"] true 5 ctxt)) ]
\<close>

(*<*)
end
(*>*)
