(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Conversion_Conformance
  imports "../Conformance_Framework"
begin
(*>*)

section\<open>Type Conversion Conformance Tests\<close>

text\<open>This theory generates conformance tests for type conversion operations:
\<^item> Narrowing conversions via @{term word_try_from_pure} (Rust's @{verbatim \<open>TryFrom\<close>} trait)

Narrowing conversions return @{typ "'a option"}: @{term Some} if the value fits
in the target type, @{term None} if it would overflow.

Conversions tested:
\<^item> u64 \<rightarrow> u32, u16, u8
\<^item> u32 \<rightarrow> u16, u8
\<^item> u16 \<rightarrow> u8
\<close>

subsection\<open>Test Generation Infrastructure\<close>

ML\<open>
structure Conversion_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  (* Conversion specification: (source_bits, target_bits, rust_method) *)
  type conversion = {
    src_bits : int,
    tgt_bits : int,
    rust_method : string
  }

  val conversions : conversion list = [
    {src_bits = 64, tgt_bits = 32, rust_method = "u32::try_from"},
    {src_bits = 64, tgt_bits = 16, rust_method = "u16::try_from"},
    {src_bits = 64, tgt_bits = 8,  rust_method = "u8::try_from"},
    {src_bits = 32, tgt_bits = 16, rust_method = "u16::try_from"},
    {src_bits = 32, tgt_bits = 8,  rust_method = "u8::try_from"},
    {src_bits = 16, tgt_bits = 8,  rust_method = "u8::try_from"}
  ]

  fun bits_to_rust_suffix 8 = "u8"
    | bits_to_rust_suffix 16 = "u16"
    | bits_to_rust_suffix 32 = "u32"
    | bits_to_rust_suffix 64 = "u64"
    | bits_to_rust_suffix _ = raise Fail "unsupported bit width"

  fun bits_to_max 8 = 255 : IntInf.int
    | bits_to_max 16 = 65535
    | bits_to_max 32 = 4294967295
    | bits_to_max 64 = 18446744073709551615
    | bits_to_max _ = raise Fail "unsupported bit width"

  (* Build term string for word_try_from_pure with explicit types *)
  fun mk_term_string src_bits tgt_bits (v : IntInf.int) =
    "(word_try_from_pure (" ^ IntInf.toString v ^ " :: " ^
    Int.toString src_bits ^ " word) :: " ^
    Int.toString tgt_bits ^ " word option)"

  fun parse_term ctxt s = Syntax.read_term ctxt s

  (* Evaluate and convert to Rust *)
  fun eval_option_to_rust ctxt term =
    let
      val result = Value_Command.value ctxt term
      val test_res = term_to_option_result result
    in
      option_result_to_rust test_res
    end

  (* Generate a single test case *)
  fun gen_test ctxt (conv : conversion) idx (v : IntInf.int) =
    let
      val term_str = mk_term_string (#src_bits conv) (#tgt_bits conv) v
      val term = parse_term ctxt term_str
      val expected = eval_option_to_rust ctxt term
      val src_suffix = bits_to_rust_suffix (#src_bits conv)
      val tgt_suffix = bits_to_rust_suffix (#tgt_bits conv)
      val rust_expr = (#rust_method conv) ^ "(" ^ IntInf.toString v ^ src_suffix ^ ")"
      (* Add .ok() to convert Result to Option for Rust's TryFrom *)
      val rust_expr_with_ok = rust_expr ^ ".ok()"
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr_with_ok, expected = expected}
    end

  (* Edge cases for conversion testing *)
  fun conversion_edge_cases (conv : conversion) =
    let
      val src_max = bits_to_max (#src_bits conv)
      val tgt_max = bits_to_max (#tgt_bits conv)
    in [
      0,                      (* zero always fits *)
      1,                      (* small value *)
      tgt_max - 1,            (* just below target max *)
      tgt_max,                (* exactly target max (fits) *)
      tgt_max + 1,            (* just above target max (overflow) *)
      src_max div 2,          (* mid source range *)
      src_max - 1,            (* near source max *)
      src_max                 (* source max (overflow unless same size) *)
    ] end

  (* Generate random source values *)
  fun gen_random_values src_bits seed n =
    case src_bits of
      8 => next_list seed n (fn s =>
             let val (w, s') = next_word8 s in (Word8.toLargeInt w, s') end)
    | 16 => next_list seed n (fn s =>
              let val (w, s') = next_word16 s in (Word.toLargeInt w, s') end)
    | 32 => next_list seed n (fn s =>
              let val (w, s') = next_word32 s in (Word32.toLargeInt w, s') end)
    | 64 => next_list seed n (fn s =>
              let val (w, s') = next_word64 s in (Word64.toLargeInt w, s') end)
    | _ => raise Fail "unsupported bit width"

  (* Generate all tests for a single conversion *)
  fun gen_conversion_tests ctxt (conv : conversion) seed num_random =
    let
      val edges = conversion_edge_cases conv
      val (randoms, _) = gen_random_values (#src_bits conv) seed num_random
      val all_values = edges @ randoms
      val src_suffix = bits_to_rust_suffix (#src_bits conv)
      val tgt_suffix = bits_to_rust_suffix (#tgt_bits conv)
      val mod_name = "conversion_" ^ src_suffix ^ "_to_" ^ tgt_suffix
    in
      (mod_name, map_index (fn (i, v) => gen_test ctxt conv i v) all_values)
    end

  (* Generate tests for all conversions *)
  fun generate_all_tests ctxt num_random =
    let
      val seed = default_seed
    in
      map (fn conv => gen_conversion_tests ctxt conv seed num_random) conversions
    end

end
\<close>

(*<*)
end
(*>*)
