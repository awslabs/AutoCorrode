(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Generate_All
  imports
    Arithmetic_Conformance
    Bitwise_Conformance
    Comparison_Conformance
    Conversion_Conformance
    Panic_Conformance
    StdLib_Arithmetic_Conformance
    Option_Conformance
    Result_Conformance
    Range_Conformance
    Ordering_Conformance
    Tuple_Conformance
begin
(*>*)

section\<open>Unified Test Generation\<close>

text\<open>This theory imports all conformance test theories and triggers unified
generation of all Rust tests to a single file.

After loading this theory, all test generators will run and produce
@{verbatim \<open>rust_harness/src/lib.rs\<close>} containing all conformance tests,
plus coverage summaries in @{verbatim \<open>rust_harness/coverage_summary.{json,md}\<close>}.
\<close>

ML\<open>
(* Unified test generation - explicitly calls each generator *)
structure Conformance_Gen = struct
  val output_path = "../rust_harness/src/lib.rs"
  val coverage_json_path = "../rust_harness/coverage_summary.json"
  val coverage_markdown_path = "../rust_harness/coverage_summary.md"
  val num_random = 100
  val required_categories = [
    "arithmetic", "bitwise", "comparison", "conversion", "panic", "stdlibarith",
    "option", "result", "range", "ordering", "tuple"
  ]

  fun module_test_count modules = length (List.concat (map snd modules))

  fun collect label generator =
    let
      val _ = writeln ("[conformance] generating " ^ label)
      val modules = generator ()
      val _ = writeln ("[conformance] generated " ^ label ^ " (" ^
        Int.toString (module_test_count modules) ^ " tests)")
    in
      modules
    end

  fun generate_all_tests ctxt =
    let
      val arith_tests = collect "arithmetic" (fn () => Arith_Conformance.generate_all_tests ctxt num_random)
      val bitwise_tests = collect "bitwise" (fn () => Bitwise_Conformance.generate_all_tests ctxt num_random)
      val comparison_tests = collect "comparison" (fn () => Comparison_Conformance.generate_all_tests ctxt num_random)
      val conversion_tests = collect "conversion" (fn () => Conversion_Conformance.generate_all_tests ctxt num_random)
      val panic_tests = collect "panic" (fn () => Panic_Conformance.generate_all_tests ctxt num_random)
      val stdlib_arith_tests = collect "stdlibarith" (fn () => StdLib_Arithmetic_Conformance.generate_all_tests ctxt num_random)
      val option_tests = collect "option" (fn () => Option_Conformance.generate_all_tests ctxt num_random)
      val result_tests = collect "result" (fn () => Result_Conformance.generate_all_tests ctxt num_random)
      val range_tests = collect "range" (fn () => Range_Conformance.generate_all_tests ctxt num_random)
      val ordering_tests = collect "ordering" (fn () => Ordering_Conformance.generate_all_tests ctxt num_random)
      val tuple_tests = collect "tuple" (fn () => Tuple_Conformance.generate_all_tests ctxt num_random)
    in
      arith_tests
      @ bitwise_tests
      @ comparison_tests
      @ conversion_tests
      @ panic_tests
      @ stdlib_arith_tests
      @ option_tests
      @ result_tests
      @ range_tests
      @ ordering_tests
      @ tuple_tests
    end

  fun write_all_tests ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val modules = generate_all_tests ctxt
      val _ = Conformance_Coverage.require_categories required_categories modules
      val content = Rust_Codegen.generate_test_file modules
      val dir = Resources.master_directory thy
      val path = Path.append dir (Path.explode output_path)
      val coverage_json = Path.append dir (Path.explode coverage_json_path)
      val coverage_markdown = Path.append dir (Path.explode coverage_markdown_path)
      val path_str = File.platform_path path
      val coverage_json_str = File.platform_path coverage_json
      val coverage_markdown_str = File.platform_path coverage_markdown
      val _ = Rust_Codegen.write_test_file path_str content
      val _ =
        Conformance_Coverage.write_summary_files
          {json_path = coverage_json_str, markdown_path = coverage_markdown_str, modules = modules}
      val total = length (List.concat (map snd modules))
    in
      writeln ("Generated " ^ Int.toString total ^ " total conformance tests");
      writeln ("Output: " ^ path_str);
      writeln ("Coverage summary (JSON): " ^ coverage_json_str);
      writeln ("Coverage summary (Markdown): " ^ coverage_markdown_str)
    end

  fun regenerate_all ctxt = write_all_tests ctxt
end
\<close>

subsection\<open>Generate Tests\<close>

text\<open>Generate all conformance tests when this theory is loaded.\<close>

ML\<open>Conformance_Gen.regenerate_all \<^context>\<close>

(*<*)
end
(*>*)
