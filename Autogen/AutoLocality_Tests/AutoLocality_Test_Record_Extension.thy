(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Record_Extension
  imports AutoLocality_Test_Common
begin
(*>*)

section\<open>Standard Isabelle record extensions\<close>

record standard_base =
  std_a :: nat
  std_b :: nat

record standard_ext = standard_base +
  std_c :: nat

locality_init for standard_base
locality_init for standard_ext

definition std_bump_a :: \<open>standard_ext \<Rightarrow> standard_ext\<close> where
  \<open>std_bump_a R \<equiv> std_a_update Suc R\<close>

definition std_set_c :: \<open>nat \<Rightarrow> standard_ext \<Rightarrow> standard_ext\<close> where
  \<open>std_set_c n R \<equiv> std_c_update (\<lambda>_. n) R\<close>

definition std_has_b :: \<open>standard_ext \<Rightarrow> bool\<close> where
  \<open>std_has_b R \<equiv> std_b R > 0\<close>

definition std_apply_policy ::
    \<open>(standard_ext \<Rightarrow> nat) \<Rightarrow> standard_ext \<Rightarrow> standard_ext\<close> where
  \<open>std_apply_policy policy R \<equiv>
     std_a_update (\<lambda>_. policy R) R\<close>

definition std_policy :: \<open>standard_ext \<Rightarrow> nat\<close> where
  \<open>std_policy R \<equiv> std_b R\<close>

locality_lemma for standard_ext: \<open>std_bump_a\<close> footprint [std_a] .
locality_lemma for standard_ext: \<open>std_set_c\<close> footprint [std_c] .
locality_lemma for standard_ext: \<open>std_has_b\<close> footprint [std_b] .
locality_lemma for standard_ext:
  \<open>std_apply_policy std_policy\<close> footprint [std_a, std_b] .

lemma \<open>std_has_b (std_bump_a (std_set_c n R)) = std_has_b R\<close>
  by simp

lemma \<open>std_has_b (std_a_update f (std_c_update g R)) = std_has_b R\<close>
  by simp

lemma \<open>std_c (std_bump_a R) = std_c R\<close>
  by simp

lemma \<open>std_c (std_a_update f R) = std_c R\<close>
  by simp

lemma \<open>std_c (std_apply_policy std_policy R) = std_c R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Record_Extension.standard_ext"
  val entries = get_record_locality_entries rec_name ctxt
  fun one name =
    entries |> filter (fn entry => #const_name entry = name)
  val expected_fields =
    ["AutoLocality_Test_Record_Extension.standard_base.std_a",
     "AutoLocality_Test_Record_Extension.standard_base.std_b",
     "AutoLocality_Test_Record_Extension.standard_ext.std_c"]
  val expected_updates = map (suffix Record.updateN) expected_fields
  val registered_fields =
    entries |> filter #field |> map #const_name
  val bump_a_pattern = Syntax.read_term ctxt "std_a_update"
  val bump_b_pattern = Syntax.read_term ctxt "std_b_update"
  val has_b_pattern = Syntax.read_term ctxt "std_b"
  val cancellation_candidates =
    locality_cancellation_record_candidates ctxt
      bump_a_pattern has_b_pattern 0
  val commutativity_candidates =
    locality_commutativity_record_candidates ctxt
      bump_a_pattern bump_b_pattern
  val expected_ambiguous_records =
    ["AutoLocality_Test_Record_Extension.standard_base",
     "AutoLocality_Test_Record_Extension.standard_ext"]
  val _ = AutoLocality_Assert.run_suite "Record-extension/metadata"
    [ ("inherited and new selectors are registered",
         fn () => AutoLocality_Assert.check "all standard selectors"
           (List.all (member (op =) registered_fields) expected_fields)),
      ("inherited and new updaters are registered",
         fn () => AutoLocality_Assert.check "all standard updaters"
           (List.all (member (op =) registered_fields) expected_updates)),
      ("custom inherited-field operation remains non-field",
         fn () => AutoLocality_Assert.check "custom operation"
           (case one "AutoLocality_Test_Record_Extension.std_bump_a" of
              [entry] => not (#field entry)
            | _ => false)),
      ("cancellation inference sees both record registrations",
         fn () => AutoLocality_Assert.check
           "ambiguous cancellation records"
           (cancellation_candidates = expected_ambiguous_records)),
      ("commutativity inference sees both record registrations",
         fn () => AutoLocality_Assert.check
           "ambiguous commutativity records"
           (commutativity_candidates = expected_ambiguous_records)),
      ("ambiguous cancellation requires an explicit record",
         fn () => AutoLocality_Assert.assert_raises
           "ambiguous cancellation inference"
           (fn () =>
             locality_infer_cancellation_record ctxt
               bump_a_pattern has_b_pattern 0)),
      ("ambiguous commutativity requires an explicit record",
         fn () => AutoLocality_Assert.assert_raises
           "ambiguous commutativity inference"
           (fn () =>
             locality_infer_commutativity_record ctxt
               bump_a_pattern bump_b_pattern)) ]
\<close>

(*<*)
end
(*>*)
