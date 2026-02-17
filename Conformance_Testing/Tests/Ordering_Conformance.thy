(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Ordering_Conformance
  imports
    "../Conformance_Framework"
begin
(*>*)

section\<open>Ordering Conformance Tests\<close>

text\<open>This theory generates conformance tests for ordering comparisons via Rust's ordering API.
\<close>

ML\<open>
structure Ordering_Conformance = struct
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

  fun eval_bool_to_rust ctxt term =
    (case term_to_bool (Value_Command.value ctxt term) of
      SOME true => "true"
    | SOME false => "false"
    | NONE => raise Fail "Failed to extract bool result")

  fun mk_cmp_is_less_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
    in
      parse_term ctxt
        ("((" ^ a_str ^ " :: " ^ bits ^ " word) < (" ^ b_str ^ " :: " ^ bits ^ " word))")
    end

  fun mk_cmp_is_equal_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
    in
      parse_term ctxt
        ("((" ^ a_str ^ " :: " ^ bits ^ " word) = (" ^ b_str ^ " :: " ^ bits ^ " word))")
    end

  fun mk_cmp_is_greater_term ctxt utype (a, b) =
    let
      val bits = Int.toString (uint_bits utype)
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
    in
      parse_term ctxt
        ("((" ^ a_str ^ " :: " ^ bits ^ " word) > (" ^ b_str ^ " :: " ^ bits ^ " word))")
    end

  fun cmp_edge_cases utype =
    let
      val max = uint_max utype
    in
      [(0, 0), (0, 1), (1, 0), (max, max), (max - 1, max), (max, max - 1),
       (0, max), (max, 0), (max div 2, max div 2), (max div 2, max div 2 + 1)]
    end

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

  fun generate_type_tests ctxt utype seed num_random =
    let
      val suffix = uint_rust_suffix utype
      val edges = cmp_edge_cases utype
      val (random_pairs, _) = gen_random_pairs_for utype seed num_random
      val pairs = edges @ random_pairs

      fun mk_tests module_suffix mk_term ord_tag =
        ("ordering_" ^ suffix ^ "_" ^ module_suffix,
          map_index
            (fn (i, pair as (a, b)) =>
              {name = "test_" ^ Int.toString i,
               rust_expr =
                 "matches!(" ^ IntInf.toString a ^ suffix ^ ".cmp(&" ^ IntInf.toString b ^ suffix
                 ^ "), std::cmp::Ordering::" ^ ord_tag ^ ")",
               expected = eval_bool_to_rust ctxt (mk_term ctxt utype pair)})
            pairs)
    in
      [mk_tests "cmp_is_less" mk_cmp_is_less_term "Less",
       mk_tests "cmp_is_equal" mk_cmp_is_equal_term "Equal",
       mk_tests "cmp_is_greater" mk_cmp_is_greater_term "Greater"]
    end

  fun generate_all_tests ctxt num_random =
    let
      val seed = default_seed
      val types = [U8, U16, U32, U64]
    in
      List.concat (map (fn t => generate_type_tests ctxt t seed num_random) types)
    end
end
\<close>

(*<*)
end
(*>*)
