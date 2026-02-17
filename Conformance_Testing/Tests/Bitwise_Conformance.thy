(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Bitwise_Conformance
  imports "../Conformance_Framework"
begin
(*>*)

section\<open>Bitwise Conformance Tests\<close>

text\<open>This theory generates conformance tests for bitwise operations:
\<^item> AND (@{term word_bitwise_and_pure})
\<^item> OR (@{term word_bitwise_or_pure})
\<^item> XOR (@{term word_bitwise_xor_pure})
\<^item> NOT (@{term word_bitwise_not_pure})
\<^item> Shift left (@{term word_shift_left_pure})
\<^item> Shift right (@{term word_shift_right_pure})

Basic bitwise operations never fail. Shifts return @{typ "'a option"} because
shifting by >= bit width is undefined behaviour in Rust (returns @{term None}).
\<close>

subsection\<open>Test Generation Infrastructure\<close>

ML\<open>
(* Test generation for bitwise and shift operations. *)

structure Bitwise_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  (* Type information *)
  datatype uint_type = U8 | U16 | U32 | U64

  fun uint_rust_suffix U8 = "u8" | uint_rust_suffix U16 = "u16"
    | uint_rust_suffix U32 = "u32" | uint_rust_suffix U64 = "u64"
  fun uint_max U8 = 255 : IntInf.int
    | uint_max U16 = 65535
    | uint_max U32 = 4294967295
    | uint_max U64 = 18446744073709551615
  fun uint_bits U8 = 8 | uint_bits U16 = 16 | uint_bits U32 = 32 | uint_bits U64 = 64

  fun mk_word_type U8 = \<^typ>\<open>8 word\<close>
    | mk_word_type U16 = \<^typ>\<open>16 word\<close>
    | mk_word_type U32 = \<^typ>\<open>32 word\<close>
    | mk_word_type U64 = \<^typ>\<open>64 word\<close>

  fun mk_word utype (n : IntInf.int) =
    HOLogic.mk_number (mk_word_type utype) n

  (* Term constructors for basic bitwise operations *)
  fun mk_and_term utype (a, b) =
    Const (\<^const_name>\<open>word_bitwise_and_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> mk_word_type utype)
    $ mk_word utype a $ mk_word utype b

  fun mk_or_term utype (a, b) =
    Const (\<^const_name>\<open>word_bitwise_or_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> mk_word_type utype)
    $ mk_word utype a $ mk_word utype b

  fun mk_xor_term utype (a, b) =
    Const (\<^const_name>\<open>word_bitwise_xor_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> mk_word_type utype)
    $ mk_word utype a $ mk_word utype b

  fun mk_not_term utype a =
    Const (\<^const_name>\<open>word_bitwise_not_pure\<close>,
           mk_word_type utype --> mk_word_type utype)
    $ mk_word utype a

  (* Term constructors for shift operations.
     In HOL: word_shift_left_pure :: 'l0 word => 'l1 word => 'l0 word option
     The shift amount type ('l1) is fixed to 32 word (matches Rust's u32 shift amount) *)
  fun mk_shl_term utype (value, shift) =
    let
      val result_ty = Type (\<^type_name>\<open>option\<close>, [mk_word_type utype])
    in
      Const (\<^const_name>\<open>word_shift_left_pure\<close>,
             mk_word_type utype --> \<^typ>\<open>32 word\<close> --> result_ty)
      $ mk_word utype value
      $ HOLogic.mk_number \<^typ>\<open>32 word\<close> shift
    end

  fun mk_shr_term utype (value, shift) =
    let
      val result_ty = Type (\<^type_name>\<open>option\<close>, [mk_word_type utype])
    in
      Const (\<^const_name>\<open>word_shift_right_pure\<close>,
             mk_word_type utype --> \<^typ>\<open>32 word\<close> --> result_ty)
      $ mk_word utype value
      $ HOLogic.mk_number \<^typ>\<open>32 word\<close> shift
    end

  (* Evaluate a HOL term and extract the word value as a string *)
  fun eval_word_to_rust ctxt term =
    let
      val result = Value_Command.value ctxt term
    in
      case extract_word_nat result of
        SOME n => IntInf.toString n
      | NONE => "/* extraction failed */"
    end

  (* Evaluate option term to Rust *)
  fun eval_option_to_rust ctxt term =
    let
      val result = Value_Command.value ctxt term
      val test_res = term_to_option_result result
    in
      option_result_to_rust test_res
    end

  (* Generate a single binary test case for basic bitwise ops *)
  fun gen_binary_test ctxt utype mk_term rust_op idx (a, b) =
    let
      val term = mk_term utype (a, b)
      val expected = eval_word_to_rust ctxt term
      val suffix = uint_rust_suffix utype
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val rust_expr = a_str ^ suffix ^ " " ^ rust_op ^ " " ^ b_str ^ suffix
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr, expected = expected ^ suffix}
    end

  (* Generate a single unary test case (for NOT) *)
  fun gen_unary_test ctxt utype mk_term rust_op idx a =
    let
      val term = mk_term utype a
      val expected = eval_word_to_rust ctxt term
      val suffix = uint_rust_suffix utype
      val a_str = IntInf.toString a
      val rust_expr = rust_op ^ a_str ^ suffix
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr, expected = expected ^ suffix}
    end

  (* Generate a single shift test case (returns Option) *)
  fun gen_shift_test ctxt utype mk_term rust_op idx (value, shift) =
    let
      val term = mk_term utype (value, shift)
      val expected = eval_option_to_rust ctxt term
      val suffix = uint_rust_suffix utype
      val val_str = IntInf.toString value
      val shift_str = IntInf.toString shift
      val rust_expr = val_str ^ suffix ^ "." ^ rust_op ^ "(" ^ shift_str ^ ")"
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr, expected = expected}
    end

  (* Edge cases for bitwise operations *)
  fun bitwise_edge_cases utype =
    let val max = uint_max utype
    in [
      (0, 0), (0, max), (max, 0), (max, max),
      (0, 1), (1, 0), (1, 1),
      (max - 1, 1), (1, max - 1),
      (max div 2, max div 2 + 1)
    ] end

  fun unary_edge_cases utype =
    let val max = uint_max utype
    in [0, 1, max - 1, max, max div 2, max div 2 + 1] end

  (* Edge cases for shift operations - includes invalid shifts (>= bit width) *)
  fun shift_edge_cases utype =
    let
      val max = uint_max utype
      val bits = uint_bits utype
    in [
      (1, 0),                    (* no shift *)
      (1, 1),                    (* shift by 1 *)
      (max, 0),                  (* max, no shift *)
      (max, 1),                  (* max, shift 1 *)
      (1, bits - 1),             (* shift to MSB *)
      (1, bits),                 (* invalid: shift == width *)
      (1, bits + 1),             (* invalid: shift > width *)
      (max, bits - 1),           (* max, shift to MSB *)
      (0, bits),                 (* zero, invalid shift *)
      (max div 2, bits div 2)    (* mid value, mid shift *)
    ] end

  (* Generate random pairs for a given type *)
  fun gen_random_pairs_for utype seed n =
    case utype of
      U8 => next_list seed n (fn s =>
              let val (a, s') = next_word8 s
                  val (b, s'') = next_word8 s'
              in ((Word8.toLargeInt a, Word8.toLargeInt b), s'') end)
    | U16 => next_list seed n (fn s =>
              let val (a, s') = next_word16 s
                  val (b, s'') = next_word16 s'
              in ((Word.toLargeInt a, Word.toLargeInt b), s'') end)
    | U32 => next_list seed n (fn s =>
              let val (a, s') = next_word32 s
                  val (b, s'') = next_word32 s'
              in ((Word32.toLargeInt a, Word32.toLargeInt b), s'') end)
    | U64 => next_list seed n (fn s =>
              let val (a, s') = next_word64 s
                  val (b, s'') = next_word64 s'
              in ((Word64.toLargeInt a, Word64.toLargeInt b), s'') end)

  fun gen_random_values_for utype seed n =
    case utype of
      U8 => next_list seed n (fn s =>
              let val (a, s') = next_word8 s in (Word8.toLargeInt a, s') end)
    | U16 => next_list seed n (fn s =>
              let val (a, s') = next_word16 s in (Word.toLargeInt a, s') end)
    | U32 => next_list seed n (fn s =>
              let val (a, s') = next_word32 s in (Word32.toLargeInt a, s') end)
    | U64 => next_list seed n (fn s =>
              let val (a, s') = next_word64 s in (Word64.toLargeInt a, s') end)

  (* Generate random (value, shift) pairs for shift tests *)
  fun gen_random_shift_pairs_for utype seed n =
    let
      val bits = uint_bits utype
    in
      case utype of
        U8 => next_list seed n (fn s =>
                let val (v, s') = next_word8 s
                    val (sh, s'') = next_int s' 0 (bits + 5)  (* some invalid *)
                in ((Word8.toLargeInt v, IntInf.fromInt sh), s'') end)
      | U16 => next_list seed n (fn s =>
                let val (v, s') = next_word16 s
                    val (sh, s'') = next_int s' 0 (bits + 5)
                in ((Word.toLargeInt v, IntInf.fromInt sh), s'') end)
      | U32 => next_list seed n (fn s =>
                let val (v, s') = next_word32 s
                    val (sh, s'') = next_int s' 0 (bits + 5)
                in ((Word32.toLargeInt v, IntInf.fromInt sh), s'') end)
      | U64 => next_list seed n (fn s =>
                let val (v, s') = next_word64 s
                    val (sh, s'') = next_int s' 0 (bits + 5)
                in ((Word64.toLargeInt v, IntInf.fromInt sh), s'') end)
    end

  (* Generate all tests for a binary operation on a type *)
  fun gen_binary_op_tests ctxt utype mk_term rust_op seed num_random =
    let
      val edges = bitwise_edge_cases utype
      val (random_pairs, _) = gen_random_pairs_for utype seed num_random
      val all_pairs = edges @ random_pairs
    in
      map_index (fn (i, pair) => gen_binary_test ctxt utype mk_term rust_op i pair) all_pairs
    end

  (* Generate all tests for NOT on a type *)
  fun gen_not_tests ctxt utype seed num_random =
    let
      val edges = unary_edge_cases utype
      val (random_values, _) = gen_random_values_for utype seed num_random
      val all_values = edges @ random_values
    in
      map_index (fn (i, v) => gen_unary_test ctxt utype mk_not_term "!" i v) all_values
    end

  (* Generate all tests for a shift operation on a type *)
  fun gen_shift_op_tests ctxt utype mk_term rust_op seed num_random =
    let
      val edges = shift_edge_cases utype
      val (random_pairs, _) = gen_random_shift_pairs_for utype seed num_random
      val all_pairs = edges @ random_pairs
    in
      map_index (fn (i, pair) => gen_shift_test ctxt utype mk_term rust_op i pair) all_pairs
    end

  (* Generate tests for all bitwise operations on a single type *)
  fun generate_type_tests ctxt utype seed num_random =
    let
      val suffix = uint_rust_suffix utype
    in
      [("bitwise_" ^ suffix ^ "_and",
        gen_binary_op_tests ctxt utype mk_and_term "&" seed num_random),
       ("bitwise_" ^ suffix ^ "_or",
        gen_binary_op_tests ctxt utype mk_or_term "|" seed num_random),
       ("bitwise_" ^ suffix ^ "_xor",
        gen_binary_op_tests ctxt utype mk_xor_term "^" seed num_random),
       ("bitwise_" ^ suffix ^ "_not",
        gen_not_tests ctxt utype seed num_random),
       ("bitwise_" ^ suffix ^ "_shl",
        gen_shift_op_tests ctxt utype mk_shl_term "checked_shl" seed num_random),
       ("bitwise_" ^ suffix ^ "_shr",
        gen_shift_op_tests ctxt utype mk_shr_term "checked_shr" seed num_random)]
    end

  (* Generate tests for all unsigned types *)
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
