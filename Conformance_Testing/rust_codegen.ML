(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Rust test code generation for conformance testing.

   This module generates Rust test files with embedded assertions that
   validate μRust semantics against real Rust behaviour.

   Example output:
   ```rust
   #[test]
   fn test_add_u32_5_3() {
       assert_eq!(5u32.checked_add(3), Some(8));
   }
   ```
*)

signature RUST_CODEGEN = sig
  (* A single test case *)
  type test_case = {
    name : string,
    rust_expr : string,
    expected : string
  }

  (* Generate a Rust test function *)
  val test_to_rust : test_case -> string

  (* Generate a Rust test module *)
  val generate_test_module : string -> test_case list -> string

  (* Generate complete file with multiple modules *)
  val generate_test_file : (string * test_case list) list -> string

  (* Write to file *)
  val write_test_file : string -> string -> unit

  (* File header *)
  val file_header : string

  (* Helper: sanitize names for Rust identifiers *)
  val sanitize_name : string -> string

  (* Helper: generate test name from operation and operands *)
  val make_test_name : string -> string -> string -> string -> string
end

structure Rust_Codegen : RUST_CODEGEN = struct
  type test_case = {
    name : string,
    rust_expr : string,
    expected : string
  }

  val file_header =
    "// Auto-generated conformance tests\n\
    \// DO NOT EDIT - regenerate via Isabelle\n\
    \//\n\
    \// This file validates that Micro Rust (μRust) semantics match real Rust behaviour.\n\
    \// Each test embeds expected values computed by Isabelle/HOL.\n\
    \//\n\
    \// Run with: cargo test\n\n\
    \#![allow(clippy::eq_op)]\n\n"

  (* Convert non-alphanumeric characters to underscores *)
  fun sanitize_name s =
    String.translate (fn c =>
      if Char.isAlphaNum c orelse c = #"_" then String.str c
      else "_") s

  (* Generate a unique test name *)
  fun make_test_name op_name rust_type a b =
    "test_" ^ op_name ^ "_" ^ rust_type ^ "_" ^
    sanitize_name a ^ "_" ^ sanitize_name b

  fun test_to_rust {name, rust_expr, expected} =
    "    #[test]\n\
    \    fn " ^ name ^ "() {\n\
    \        assert_eq!(" ^ rust_expr ^ ", " ^ expected ^ ");\n\
    \    }\n"

  fun generate_test_module mod_name tests =
    let
      val tests_str = String.concatWith "\n" (map test_to_rust tests)
    in
      "#[cfg(test)]\n\
      \mod " ^ mod_name ^ " {\n" ^
      tests_str ^
      "}\n"
    end

  fun generate_test_file modules =
    let
      val modules_str = String.concatWith "\n" (
        map (fn (name, tests) => generate_test_module name tests) modules
      )
    in
      file_header ^ modules_str
    end

  fun write_test_file path content =
    let
      val os = TextIO.openOut path
    in
      TextIO.output (os, content);
      TextIO.closeOut os
    end
end

(* Open the structure for easy access *)
open Rust_Codegen
