(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Arithmetic_Conformance
  imports
    "../Conformance_Framework"
begin
(*>*)

section\<open>Stdlib Arithmetic Conformance Tests\<close>

text\<open>This theory generates conformance tests for arithmetic APIs in the Micro Rust standard
library, including overflow-reporting, checked, wrapping, saturating, and NonZero operations.
\<close>

ML\<open>
structure StdLib_Arithmetic_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  datatype uint_type = U8 | U16 | U32 | U64

  fun uint_bits U8 = 8 | uint_bits U16 = 16 | uint_bits U32 = 32 | uint_bits U64 = 64
  fun uint_rust_suffix U8 = "u8" | uint_rust_suffix U16 = "u16"
    | uint_rust_suffix U32 = "u32" | uint_rust_suffix U64 = "u64"
  fun uint_max U8 = 255 : IntInf.int
    | uint_max U16 = 65535
    | uint_max U32 = 4294967295
    | uint_max U64 = 18446744073709551615

  fun parse_term ctxt s = Syntax.read_term ctxt s

  fun eval_word_to_rust ctxt term =
    (case extract_word_nat (Value_Command.value ctxt term) of
      SOME n => IntInf.toString n
    | NONE => raise Fail "Failed to extract word result")

  fun eval_bool_to_rust ctxt term =
    (case term_to_bool (Value_Command.value ctxt term) of
      SOME true => "true"
    | SOME false => "false"
    | NONE => raise Fail "Failed to extract bool result")

  fun eval_option_to_rust ctxt term =
    option_result_to_rust (term_to_option_result (Value_Command.value ctxt term))

  fun mk_overflowing_add_value_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt ("(" ^ a_word ^ " + " ^ b_word ^ ")")
    end

  fun mk_overflowing_add_overflow_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt
        ("(unat " ^ a_word ^ " + unat " ^ b_word ^ " >= 2^" ^ bits ^ ")")
    end

  fun mk_overflowing_mul_value_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt ("(" ^ a_word ^ " * " ^ b_word ^ ")")
    end

  fun mk_overflowing_mul_overflow_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt
        ("(unat " ^ a_word ^ " * unat " ^ b_word ^ " >= 2^" ^ bits ^ ")")
    end

  fun mk_wrapping_add_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt ("(" ^ a_word ^ " + " ^ b_word ^ ")")
    end

  fun mk_saturating_sub_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt
        ("(if " ^ b_word ^ " <= " ^ a_word ^ " then " ^ a_word ^ " - " ^ b_word
         ^ " else (0 :: " ^ bits ^ " word))")
    end

  fun mk_checked_add_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt ("(word_add_no_wrap_pure " ^ a_word ^ " " ^ b_word ^ ")")
    end

  fun mk_checked_mul_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt ("(word_mul_no_wrap_pure " ^ a_word ^ " " ^ b_word ^ ")")
    end

  fun mk_div_ceil_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val a_word = "(" ^ a_str ^ " :: " ^ bits ^ " word)"
      val b_word = "(" ^ b_str ^ " :: " ^ bits ^ " word)"
    in
      parse_term ctxt
        ("(word_of_nat ((unat " ^ a_word ^ " + unat " ^ b_word ^ " - 1) div unat "
         ^ b_word ^ ") :: " ^ bits ^ " word)")
    end

  fun mk_nonzero_new_is_some_term ctxt n =
    let
      val n_str = IntInf.toString n
    in
      parse_term ctxt ("((" ^ n_str ^ " :: 64 word) ~= (0 :: 64 word))")
    end

  fun mk_nonzero_get_roundtrip_term ctxt n =
    let
      val n_str = IntInf.toString n
    in
      parse_term ctxt ("((" ^ n_str ^ " :: 64 word) ~= (0 :: 64 word))")
    end

  fun arith_edge_cases utype =
    let
      val max = uint_max utype
      val mid = max div 2
    in
      [(0, 0), (0, 1), (1, 0), (1, 1), (max, 0), (max, 1),
       (max, max), (max - 1, max), (mid, mid), (mid + 1, mid)]
    end

  fun div_ceil_edge_cases utype =
    let
      val max = uint_max utype
      val mid = max div 2
    in
      [(0, 1), (1, 1), (2, 1), (5, 2), (10, 3), (max, 1),
       (max, 2), (mid, 2), (mid + 1, 2), (max - 1, max)]
    end

  fun nonzero_edge_values () =
    [0 : IntInf.int, 1, 2, 3, 18446744073709551615]

  fun positive_u64_edge_values () =
    [1 : IntInf.int, 2, 3, 4, 18446744073709551615, 18446744073709551614]

  fun gen_random_pairs_for utype seed n =
    (case utype of
      U8 =>
        next_list seed n (fn s =>
          let
            val (a, s') = next_word8 s
            val (b, s'') = next_word8 s'
          in
            ((Word8.toLargeInt a, Word8.toLargeInt b), s'')
          end)
    | U16 =>
        next_list seed n (fn s =>
          let
            val (a, s') = next_word16 s
            val (b, s'') = next_word16 s'
          in
            ((Word.toLargeInt a, Word.toLargeInt b), s'')
          end)
    | U32 =>
        next_list seed n (fn s =>
          let
            val (a, s') = next_word32 s
            val (b, s'') = next_word32 s'
          in
            ((Word32.toLargeInt a, Word32.toLargeInt b), s'')
          end)
    | U64 =>
        next_list seed n (fn s =>
          let
            val (a, s') = next_word64 s
            val (b, s'') = next_word64 s'
          in
            ((Word64.toLargeInt a, Word64.toLargeInt b), s'')
          end))

  fun gen_random_nonzero_pairs_for utype seed n =
    let
      val (pairs, st) = gen_random_pairs_for utype seed n
      val fixed = map (fn (a, b) => if b = 0 then (a, 1) else (a, b)) pairs
    in
      (fixed, st)
    end

  fun gen_random_u64_values seed n =
    next_list seed n (fn s =>
      let
        val (w, s') = next_word64 s
      in
        (Word64.toLargeInt w, s')
      end)

  fun gen_binary_tests ctxt utype mk_term eval_expected rust_expr edge_cases random_pairs =
    let
      val suffix = uint_rust_suffix utype
      val all_pairs = edge_cases @ random_pairs
    in
      map_index
        (fn (i, pair) =>
          let
            val expected = eval_expected ctxt (mk_term ctxt utype pair)
            val name = "test_" ^ Int.toString i
          in
            {name = name, rust_expr = rust_expr suffix pair, expected = expected}
          end)
        all_pairs
    end

  fun gen_u64_value_tests ctxt mk_term eval_expected rust_expr edge_values random_values =
    let
      val values = edge_values @ random_values
    in
      map_index
        (fn (i, n) =>
          let
            val expected = eval_expected ctxt (mk_term ctxt n)
            val name = "test_" ^ Int.toString i
          in
            {name = name, rust_expr = rust_expr n, expected = expected}
          end)
        values
    end

  fun generate_type_tests ctxt utype seed num_random =
    let
      val suffix = uint_rust_suffix utype
      val (random_pairs, _) = gen_random_pairs_for utype seed num_random
      val (random_div_pairs, _) = gen_random_nonzero_pairs_for utype seed num_random
      val arith_edges = arith_edge_cases utype
      val div_edges = div_ceil_edge_cases utype

      fun mk_method_expr method suffix' (a, b) =
        IntInf.toString a ^ suffix' ^ "." ^ method ^ "(" ^ IntInf.toString b ^ suffix' ^ ")"

      fun mk_overflow_expr method field suffix' pair =
        mk_method_expr method suffix' pair ^ "." ^ field
    in
      [("stdlibarith_" ^ suffix ^ "_overflowing_add_value",
        gen_binary_tests ctxt utype mk_overflowing_add_value_term eval_word_to_rust
          (mk_overflow_expr "overflowing_add" "0") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_overflowing_add_overflow",
        gen_binary_tests ctxt utype mk_overflowing_add_overflow_term eval_bool_to_rust
          (mk_overflow_expr "overflowing_add" "1") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_overflowing_mul_value",
        gen_binary_tests ctxt utype mk_overflowing_mul_value_term eval_word_to_rust
          (mk_overflow_expr "overflowing_mul" "0") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_overflowing_mul_overflow",
        gen_binary_tests ctxt utype mk_overflowing_mul_overflow_term eval_bool_to_rust
          (mk_overflow_expr "overflowing_mul" "1") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_wrapping_add",
        gen_binary_tests ctxt utype mk_wrapping_add_term eval_word_to_rust
          (mk_method_expr "wrapping_add") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_saturating_sub",
        gen_binary_tests ctxt utype mk_saturating_sub_term eval_word_to_rust
          (mk_method_expr "saturating_sub") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_checked_add",
        gen_binary_tests ctxt utype mk_checked_add_term eval_option_to_rust
          (mk_method_expr "checked_add") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_checked_mul",
        gen_binary_tests ctxt utype mk_checked_mul_term eval_option_to_rust
          (mk_method_expr "checked_mul") arith_edges random_pairs),
       ("stdlibarith_" ^ suffix ^ "_div_ceil",
        gen_binary_tests ctxt utype mk_div_ceil_term eval_word_to_rust
          (mk_method_expr "div_ceil") div_edges random_div_pairs)]
    end

  fun generate_u64_nonzero_tests ctxt seed num_random =
    let
      val (random_values, _) = gen_random_u64_values seed num_random
      val all_edges = nonzero_edge_values ()
      val positive_edges = positive_u64_edge_values ()
      val random_positive = map (fn n => if n = 0 then 1 else n) random_values
      fun rust_new_is_some n =
        "std::num::NonZeroU64::new(" ^ IntInf.toString n ^ "u64).is_some()"
      fun rust_get_roundtrip n =
        "std::num::NonZeroU64::new(" ^ IntInf.toString n ^ "u64).unwrap().get() == "
        ^ IntInf.toString n ^ "u64"
    in
      [("stdlibarith_u64_nonzerou64_new_is_some",
        gen_u64_value_tests ctxt mk_nonzero_new_is_some_term eval_bool_to_rust
          rust_new_is_some all_edges random_values),
       ("stdlibarith_u64_nonzerou64_get_roundtrip",
        gen_u64_value_tests ctxt mk_nonzero_get_roundtrip_term eval_bool_to_rust
          rust_get_roundtrip positive_edges random_positive)]
    end

  fun generate_all_tests ctxt num_random =
    let
      val seed = default_seed
      val types = [U8, U16, U32, U64]
      val type_modules = List.concat (map (fn t => generate_type_tests ctxt t seed num_random) types)
      val nonzero_modules = generate_u64_nonzero_tests ctxt seed num_random
    in
      type_modules @ nonzero_modules
    end
end
\<close>

(*<*)
end
(*>*)
