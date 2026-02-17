(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Conformance_Framework
  imports
    Shallow_Micro_Rust.Numeric_Types
    "HOL-Library.Code_Target_Numeral"
begin
(*>*)

section\<open>Conformance Testing Framework\<close>

text\<open>This theory provides infrastructure for generating Rust conformance tests
that validate Micro Rust (μRust) semantics against real Rust behaviour.

The workflow is:
\<^enum> SML generates random test inputs
\<^enum> HOL computes expected results using the pure function definitions
\<^enum> SML generates Rust test files with embedded assertions
\<^enum> @{verbatim \<open>cargo test\<close>} validates that Rust matches the expected behaviour

\<^bold>\<open>Key principle:\<close> Expected values come from HOL evaluation, not SML reimplementation.
This ensures we're testing the actual formalisation.
\<close>

subsection\<open>ML Infrastructure\<close>

ML_file "random.ML"
ML_file "conformance.ML"
ML_file "rust_codegen.ML"
ML_file "coverage.ML"

(*<*)
end
(*>*)
