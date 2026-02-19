(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Arithmetic_Conformance
  imports "../Conformance_Framework"
begin
(*>*)

section\<open>Arithmetic Conformance Tests\<close>

text\<open>This theory generates conformance tests for arithmetic operations across
multiple unsigned integer types:
\<^item> u8 (8-bit), u16 (16-bit), u32 (32-bit), u64 (64-bit)

Operations tested:
\<^item> Addition (@{term word_add_no_wrap_pure})
\<^item> Subtraction (@{term word_minus_no_wrap_pure})
\<^item> Multiplication (@{term word_mul_no_wrap_pure})
\<^item> Division (pure version defined below)
\<^item> Modulo (pure version defined below)

The tests validate that our HOL definitions match Rust's @{verbatim \<open>checked_*\<close>} methods.

\<^bold>\<open>Key principle:\<close> Expected values are computed by evaluating the HOL definitions,
not by reimplementing the logic in SML.
\<close>

subsection\<open>Pure Division and Modulo\<close>

text\<open>The core theory defines division/modulo as expression-level functions that panic
on division by zero. For conformance testing against Rust's @{verbatim \<open>checked_div\<close>}
and @{verbatim \<open>checked_rem\<close>}, we need pure versions that return @{typ "'a option"}.\<close>

definition word_div_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word option\<close> where
  \<open>word_div_pure a b \<equiv> if b = 0 then None else Some (a div b)\<close>

definition word_mod_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word option\<close> where
  \<open>word_mod_pure a b \<equiv> if b = 0 then None else Some (a mod b)\<close>

subsection\<open>Test Generation Infrastructure\<close>

ML\<open>
(* Test generation for arithmetic operations on unsigned integer types.
   Supports u8, u16, u32, u64 with the same HOL definitions (polymorphic). *)

structure Arith_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  (* Type information for each unsigned integer type *)
  datatype uint_type = U8 | U16 | U32 | U64

  fun uint_bits U8 = 8 | uint_bits U16 = 16 | uint_bits U32 = 32 | uint_bits U64 = 64
  fun uint_rust_suffix U8 = "u8" | uint_rust_suffix U16 = "u16"
    | uint_rust_suffix U32 = "u32" | uint_rust_suffix U64 = "u64"
  fun uint_max U8 = 255 : IntInf.int
    | uint_max U16 = 65535
    | uint_max U32 = 4294967295
    | uint_max U64 = 18446744073709551615

  (* Build HOL type for word of given bit width *)
  fun mk_word_type U8 = \<^typ>\<open>8 word\<close>
    | mk_word_type U16 = \<^typ>\<open>16 word\<close>
    | mk_word_type U32 = \<^typ>\<open>32 word\<close>
    | mk_word_type U64 = \<^typ>\<open>64 word\<close>

  (* Build a HOL term for a word literal of given type *)
  fun mk_word utype (n : IntInf.int) =
    HOLogic.mk_number (mk_word_type utype) n

  (* Term constructors for each operation, parameterized by type *)
  fun mk_add_term utype (a, b) =
    Const (\<^const_name>\<open>word_add_no_wrap_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> Type (\<^type_name>\<open>option\<close>, [mk_word_type utype]))
    $ mk_word utype a $ mk_word utype b

  fun mk_sub_term utype (a, b) =
    Const (\<^const_name>\<open>word_minus_no_wrap_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> Type (\<^type_name>\<open>option\<close>, [mk_word_type utype]))
    $ mk_word utype a $ mk_word utype b

  fun mk_mul_term utype (a, b) =
    Const (\<^const_name>\<open>word_mul_no_wrap_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> Type (\<^type_name>\<open>option\<close>, [mk_word_type utype]))
    $ mk_word utype a $ mk_word utype b

  fun mk_div_term utype (a, b) =
    Const (\<^const_name>\<open>word_div_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> Type (\<^type_name>\<open>option\<close>, [mk_word_type utype]))
    $ mk_word utype a $ mk_word utype b

  fun mk_mod_term utype (a, b) =
    Const (\<^const_name>\<open>word_mod_pure\<close>,
           mk_word_type utype --> mk_word_type utype --> Type (\<^type_name>\<open>option\<close>, [mk_word_type utype]))
    $ mk_word utype a $ mk_word utype b

  (* Evaluate a HOL term and convert the result to Rust syntax *)
  fun eval_option_to_rust ctxt term =
    let
      val result = Value_Command.value ctxt term
      val test_res = term_to_option_result result
    in
      option_result_to_rust test_res
    end

  (* Generate a single test case *)
  fun gen_test ctxt utype mk_term rust_op idx (a, b) =
    let
      val term = mk_term utype (a, b)
      val expected = eval_option_to_rust ctxt term
      val suffix = uint_rust_suffix utype
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val rust_expr = a_str ^ suffix ^ "." ^ rust_op ^ "(" ^ b_str ^ ")"
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr, expected = expected}
    end

  (* Edge cases for a given type *)
  fun arith_edge_cases utype =
    let val max = uint_max utype
        val mid = max div 2
    in [
      (0, 0), (0, 1), (1, 0), (1, 1),
      (max, 0), (max, 1), (max - 1, 1),
      (mid, mid), (mid + 1, mid), (mid + 1, mid + 1)
    ] end

  fun div_edge_cases utype =
    let val max = uint_max utype
        val mid = max div 2
    in [
      (0, 1), (1, 1), (10, 3), (10, 0),
      (max, 1), (max, 2), (max, max),
      (0, 0), (100 mod (max + 1), 7), (mid, 2)
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

  (* Generate all tests for an operation on a type *)
  fun gen_op_tests ctxt utype mk_term rust_op edge_cases seed num_random =
    let
      val (random_pairs, _) = gen_random_pairs_for utype seed num_random
      val all_pairs = edge_cases @ random_pairs
    in
      map_index (fn (i, pair) => gen_test ctxt utype mk_term rust_op i pair) all_pairs
    end

  (* Generate tests for all operations on a single type *)
  fun generate_type_tests ctxt utype seed num_random =
    let
      val suffix = uint_rust_suffix utype
      val arith_edges = arith_edge_cases utype
      val div_edges = div_edge_cases utype
    in
      [("arithmetic_" ^ suffix ^ "_add",
        gen_op_tests ctxt utype mk_add_term "checked_add" arith_edges seed num_random),
       ("arithmetic_" ^ suffix ^ "_sub",
        gen_op_tests ctxt utype mk_sub_term "checked_sub" arith_edges seed num_random),
       ("arithmetic_" ^ suffix ^ "_mul",
        gen_op_tests ctxt utype mk_mul_term "checked_mul" arith_edges seed num_random),
       ("arithmetic_" ^ suffix ^ "_div",
        gen_op_tests ctxt utype mk_div_term "checked_div" div_edges seed num_random),
       ("arithmetic_" ^ suffix ^ "_mod",
        gen_op_tests ctxt utype mk_mod_term "checked_rem" div_edges seed num_random)]
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
