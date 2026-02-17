(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Comparison_Conformance
  imports "../Conformance_Framework"
begin
(*>*)

section\<open>Comparison Conformance Tests\<close>

text\<open>This theory generates conformance tests for comparison operations:
\<^item> Equality (=) / (==)
\<^item> Inequality (\<noteq>) / (!=)
\<^item> Less than (<)
\<^item> Less than or equal (\<le>) / (<=)
\<^item> Greater than (>)
\<^item> Greater than or equal (\<ge>) / (>=)

Comparison operations return @{typ bool}, which maps to Rust's @{verbatim \<open>bool\<close>}.
\<close>

subsection\<open>Test Generation Infrastructure\<close>

ML\<open>
(* Test generation for comparison operations. *)

structure Comparison_Conformance = struct
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

  fun mk_word_type U8 = \<^typ>\<open>8 word\<close>
    | mk_word_type U16 = \<^typ>\<open>16 word\<close>
    | mk_word_type U32 = \<^typ>\<open>32 word\<close>
    | mk_word_type U64 = \<^typ>\<open>64 word\<close>

  fun mk_word utype (n : IntInf.int) =
    HOLogic.mk_number (mk_word_type utype) n

  (* Term constructors for comparison operations *)
  fun mk_eq_term utype (a, b) =
    HOLogic.mk_eq (mk_word utype a, mk_word utype b)

  fun mk_neq_term utype (a, b) =
    HOLogic.mk_not (mk_eq_term utype (a, b))

  fun mk_less_term utype (a, b) =
    Const (\<^const_name>\<open>less\<close>, mk_word_type utype --> mk_word_type utype --> \<^typ>\<open>bool\<close>)
    $ mk_word utype a $ mk_word utype b

  fun mk_less_eq_term utype (a, b) =
    Const (\<^const_name>\<open>less_eq\<close>, mk_word_type utype --> mk_word_type utype --> \<^typ>\<open>bool\<close>)
    $ mk_word utype a $ mk_word utype b

  fun mk_greater_term utype (a, b) =
    mk_less_term utype (b, a)  (* a > b is b < a *)

  fun mk_greater_eq_term utype (a, b) =
    mk_less_eq_term utype (b, a)  (* a >= b is b <= a *)

  (* Evaluate a HOL bool term and convert to Rust syntax *)
  fun eval_bool_to_rust ctxt term =
    let
      val result = Value_Command.value ctxt term
    in
      case term_to_bool result of
        SOME true => "true"
      | SOME false => "false"
      | NONE => "/* bool extraction failed */"
    end

  (* Generate a single comparison test case *)
  fun gen_cmp_test ctxt utype mk_term rust_op idx (a, b) =
    let
      val term = mk_term utype (a, b)
      val expected = eval_bool_to_rust ctxt term
      val suffix = uint_rust_suffix utype
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val rust_expr = a_str ^ suffix ^ " " ^ rust_op ^ " " ^ b_str ^ suffix
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr, expected = expected}
    end

  (* Edge cases for comparison operations *)
  fun cmp_edge_cases utype =
    let val max = uint_max utype
    in [
      (0, 0),                    (* equal: min *)
      (max, max),                (* equal: max *)
      (0, 1),                    (* less *)
      (1, 0),                    (* greater *)
      (0, max),                  (* min vs max *)
      (max, 0),                  (* max vs min *)
      (max - 1, max),            (* adjacent *)
      (max, max - 1),            (* adjacent reversed *)
      (max div 2, max div 2),    (* equal: mid *)
      (max div 2, max div 2 + 1) (* mid vs mid+1 *)
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

  (* Generate all tests for a comparison operation on a type *)
  fun gen_cmp_op_tests ctxt utype mk_term rust_op seed num_random =
    let
      val edges = cmp_edge_cases utype
      val (random_pairs, _) = gen_random_pairs_for utype seed num_random
      val all_pairs = edges @ random_pairs
    in
      map_index (fn (i, pair) => gen_cmp_test ctxt utype mk_term rust_op i pair) all_pairs
    end

  (* Generate tests for all comparison operations on a single type *)
  fun generate_type_tests ctxt utype seed num_random =
    let
      val suffix = uint_rust_suffix utype
    in
      [("comparison_" ^ suffix ^ "_eq",
        gen_cmp_op_tests ctxt utype mk_eq_term "==" seed num_random),
       ("comparison_" ^ suffix ^ "_ne",
        gen_cmp_op_tests ctxt utype mk_neq_term "!=" seed num_random),
       ("comparison_" ^ suffix ^ "_lt",
        gen_cmp_op_tests ctxt utype mk_less_term "<" seed num_random),
       ("comparison_" ^ suffix ^ "_le",
        gen_cmp_op_tests ctxt utype mk_less_eq_term "<=" seed num_random),
       ("comparison_" ^ suffix ^ "_gt",
        gen_cmp_op_tests ctxt utype mk_greater_term ">" seed num_random),
       ("comparison_" ^ suffix ^ "_ge",
        gen_cmp_op_tests ctxt utype mk_greater_eq_term ">=" seed num_random)]
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
