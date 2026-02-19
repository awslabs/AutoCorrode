(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Conformance coverage summary generation.
   Produces machine-readable JSON and human-readable Markdown audit artifacts. *)

signature CONFORMANCE_COVERAGE = sig
  val require_categories : string list -> (string * Rust_Codegen.test_case list) list -> unit
  val write_summary_files :
    {json_path : string, markdown_path : string, modules : (string * Rust_Codegen.test_case list) list} -> unit
end

structure Conformance_Coverage : CONFORMANCE_COVERAGE = struct
  type module_summary = {
    name : string,
    category : string,
    test_count : int,
    panic_true_count : int,
    panic_false_count : int
  }

  val tracked_types = ["u8", "u16", "u32", "u64"]

  fun add_assoc key delta [] = [(key, delta)]
    | add_assoc key delta ((k, v) :: rest) =
        if k = key then (k, v + delta) :: rest
        else (k, v) :: add_assoc key delta rest

  fun get_assoc key [] = 0
    | get_assoc key ((k, v) :: rest) =
        if k = key then v else get_assoc key rest

  fun module_category name =
    (case String.tokens (fn c => c = #"_") name of
      category :: _ => category
    | [] => "uncategorized")

  fun module_mentions_type ty name =
    List.exists (fn tok => tok = ty) (String.tokens (fn c => c = #"_") name)

  fun count_expected needle tests =
    length (List.filter (fn (tc : Rust_Codegen.test_case) => #expected tc = needle) tests)

  fun summarize_module (name, tests) =
    let
      val category = module_category name
      val test_count = length tests
      val panic_true_count = if category = "panic" then count_expected "true" tests else 0
      val panic_false_count = if category = "panic" then count_expected "false" tests else 0
    in
      {
        name = name,
        category = category,
        test_count = test_count,
        panic_true_count = panic_true_count,
        panic_false_count = panic_false_count
      }
    end

  fun sort_counts counts =
    sort (fn ((a, _), (b, _)) => String.compare (a, b)) counts

  fun json_escape s =
    String.translate
      (fn #"\"" => "\\\""
        | #"\\" => "\\\\"
        | #"\n" => "\\n"
        | #"\r" => "\\r"
        | #"\t" => "\\t"
        | c => String.str c) s

  fun json_string s = "\"" ^ json_escape s ^ "\""

  fun module_to_json {name, category, test_count, panic_true_count, panic_false_count} =
    "{"
    ^ "\"name\":" ^ json_string name
    ^ ",\"category\":" ^ json_string category
    ^ ",\"test_count\":" ^ Int.toString test_count
    ^ ",\"panic_true_count\":" ^ Int.toString panic_true_count
    ^ ",\"panic_false_count\":" ^ Int.toString panic_false_count
    ^ "}"

  fun count_to_json (key, value) =
    "{"
    ^ "\"name\":" ^ json_string key
    ^ ",\"count\":" ^ Int.toString value
    ^ "}"

  fun write_file path content =
    let
      val out = TextIO.openOut path
    in
      TextIO.output (out, content);
      TextIO.closeOut out
    end

  fun require_categories required_categories modules =
    let
      val category_module_counts =
        fold (fn (name, _) => fn acc => add_assoc (module_category name) 1 acc) modules []
      val missing =
        List.filter (fn category => get_assoc category category_module_counts = 0) required_categories
    in
      if null missing then ()
      else
        raise Fail
          ("Missing required conformance coverage categories: "
           ^ String.concatWith ", " missing)
    end

  fun write_summary_files {json_path, markdown_path, modules} =
    let
      val summaries = map summarize_module modules
      val total_modules = length summaries
      val total_tests = fold (fn s => fn acc => #test_count s + acc) summaries 0
      val total_panic_true = fold (fn s => fn acc => #panic_true_count s + acc) summaries 0
      val total_panic_false = fold (fn s => fn acc => #panic_false_count s + acc) summaries 0

      val category_module_counts =
        sort_counts (fold (fn s => add_assoc (#category s) 1) summaries [])
      val category_test_counts =
        sort_counts (fold (fn s => add_assoc (#category s) (#test_count s)) summaries [])

      val type_test_counts =
        let
          fun bump_types s acc =
            List.foldl
              (fn (ty, a) =>
                if module_mentions_type ty (#name s) then add_assoc ty (#test_count s) a else a)
              acc
              tracked_types
        in
          sort_counts (fold bump_types summaries [])
        end

      val generated_at = Time.toString (Time.now ())

      val modules_json =
        String.concatWith ",\n    " (map module_to_json summaries)
      val category_modules_json =
        String.concatWith ",\n    " (map count_to_json category_module_counts)
      val category_tests_json =
        String.concatWith ",\n    " (map count_to_json category_test_counts)
      val type_tests_json =
        String.concatWith ",\n    "
          (map (fn ty => count_to_json (ty, get_assoc ty type_test_counts)) tracked_types)

      val json_content =
        "{\n"
        ^ "  \"generated_at\": " ^ json_string generated_at ^ ",\n"
        ^ "  \"total_modules\": " ^ Int.toString total_modules ^ ",\n"
        ^ "  \"total_tests\": " ^ Int.toString total_tests ^ ",\n"
        ^ "  \"panic_true_count\": " ^ Int.toString total_panic_true ^ ",\n"
        ^ "  \"panic_false_count\": " ^ Int.toString total_panic_false ^ ",\n"
        ^ "  \"category_module_counts\": [\n    " ^ category_modules_json ^ "\n  ],\n"
        ^ "  \"category_test_counts\": [\n    " ^ category_tests_json ^ "\n  ],\n"
        ^ "  \"type_test_counts\": [\n    " ^ type_tests_json ^ "\n  ],\n"
        ^ "  \"modules\": [\n    " ^ modules_json ^ "\n  ]\n"
        ^ "}\n"

      fun category_row (name, module_count) =
        let
          val tests = get_assoc name category_test_counts
        in
          "| " ^ name ^ " | " ^ Int.toString module_count ^ " | " ^ Int.toString tests ^ " |"
        end

      fun type_row ty =
        "| " ^ ty ^ " | " ^ Int.toString (get_assoc ty type_test_counts) ^ " |"

      fun module_row {name, category, test_count, panic_true_count, panic_false_count} =
        "| " ^ name ^ " | " ^ category ^ " | "
        ^ Int.toString test_count ^ " | "
        ^ Int.toString panic_true_count ^ " | "
        ^ Int.toString panic_false_count ^ " |"

      val markdown_content =
        "# Conformance Coverage Summary\n\n"
        ^ "Generated at: `" ^ generated_at ^ "`\n\n"
        ^ "## Totals\n\n"
        ^ "- Modules: " ^ Int.toString total_modules ^ "\n"
        ^ "- Tests: " ^ Int.toString total_tests ^ "\n"
        ^ "- Panic assertions expecting panic (`true`): " ^ Int.toString total_panic_true ^ "\n"
        ^ "- Panic assertions expecting no panic (`false`): " ^ Int.toString total_panic_false ^ "\n\n"
        ^ "## Category Coverage\n\n"
        ^ "| Category | Modules | Tests |\n"
        ^ "|---|---:|---:|\n"
        ^ String.concatWith "\n" (map category_row category_module_counts) ^ "\n\n"
        ^ "## Type Coverage (tests touching type)\n\n"
        ^ "| Type | Tests |\n"
        ^ "|---|---:|\n"
        ^ String.concatWith "\n" (map type_row tracked_types) ^ "\n\n"
        ^ "## Module Breakdown\n\n"
        ^ "| Module | Category | Tests | panic=true | panic=false |\n"
        ^ "|---|---|---:|---:|---:|\n"
        ^ String.concatWith "\n" (map module_row summaries) ^ "\n"
    in
      write_file json_path json_content;
      write_file markdown_path markdown_content
    end
end

open Conformance_Coverage
