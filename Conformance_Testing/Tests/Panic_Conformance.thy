(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Panic_Conformance
  imports "../Conformance_Framework"
begin
(*>*)

section\<open>Panic Conformance Tests\<close>

text\<open>This theory generates conformance tests for expression-level operations that may panic:
\<^item> Arithmetic overflow: @{term word_add_no_wrap_core}, @{term word_minus_no_wrap_core}, @{term word_mul_no_wrap_core}
\<^item> Division/modulo by zero: @{term word_udiv_core}, @{term word_umod_core}
\<^item> Invalid shifts: @{term word_shift_left_core}, @{term word_shift_right_core}

For each generated test case:
\<^enum> HOL evaluates the corresponding \<^emph>\<open>expression-level\<close> term using @{term evaluate}
\<^enum> We extract whether the result has shape @{verbatim \<open>Abort (Panic msg) \<sigma>\<close>}
\<^enum> Rust checks panic behaviour via @{verbatim \<open>std::panic::catch_unwind\<close>}

This directly validates panic-path conformance, not only successful executions.
\<close>

subsection\<open>Test Generation Infrastructure\<close>

ML\<open>
structure Panic_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  datatype uint_type = U8 | U16 | U32 | U64
  datatype panic_op = Add | Sub | Mul | Div | Mod | Shl | Shr

  fun uint_bits U8 = 8 | uint_bits U16 = 16 | uint_bits U32 = 32 | uint_bits U64 = 64
  fun uint_rust_suffix U8 = "u8" | uint_rust_suffix U16 = "u16"
    | uint_rust_suffix U32 = "u32" | uint_rust_suffix U64 = "u64"
  fun uint_max U8 = 255 : IntInf.int
    | uint_max U16 = 65535
    | uint_max U32 = 4294967295
    | uint_max U64 = 18446744073709551615

  fun op_suffix Add = "add"
    | op_suffix Sub = "sub"
    | op_suffix Mul = "mul"
    | op_suffix Div = "div"
    | op_suffix Mod = "mod"
    | op_suffix Shl = "shl"
    | op_suffix Shr = "shr"

  fun is_shift_op Shl = true
    | is_shift_op Shr = true
    | is_shift_op _ = false

  fun mk_term_string op_kind bits (a : IntInf.int, b : IntInf.int) =
    let
      val bits_str = Int.toString bits
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
      val core_call =
        (case op_kind of
          Add => "word_add_no_wrap_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: " ^ bits_str ^ " word)"
        | Sub => "word_minus_no_wrap_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: " ^ bits_str ^ " word)"
        | Mul => "word_mul_no_wrap_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: " ^ bits_str ^ " word)"
        | Div => "word_udiv_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: " ^ bits_str ^ " word)"
        | Mod => "word_umod_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: " ^ bits_str ^ " word)"
        | Shl => "word_shift_left_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: 32 word)"
        | Shr => "word_shift_right_core (" ^ a_str ^ " :: " ^ bits_str ^ " word) (" ^ b_str ^ " :: 32 word)")
    in
      "(evaluate (" ^ core_call ^ " :: (unit, " ^ bits_str ^ " word, unit, unit, unit, unit) expression) ())"
    end

  fun parse_term ctxt s = Syntax.read_term ctxt s

  fun eval_panic_to_rust ctxt term =
    (case term_to_panic_abort (Value_Command.value ctxt term) of
      SOME true => "true"
    | SOME false => "false"
    | NONE => raise Fail "Failed to extract panic result from continuation term")

  fun mk_checked_expr op_kind suffix (a : IntInf.int, b : IntInf.int) =
    let
      val a_str = IntInf.toString a
      val b_str = IntInf.toString b
    in
      (case op_kind of
        Add => a_str ^ suffix ^ ".checked_add(" ^ b_str ^ suffix ^ ").unwrap()"
      | Sub => a_str ^ suffix ^ ".checked_sub(" ^ b_str ^ suffix ^ ").unwrap()"
      | Mul => a_str ^ suffix ^ ".checked_mul(" ^ b_str ^ suffix ^ ").unwrap()"
      | Div => a_str ^ suffix ^ ".checked_div(" ^ b_str ^ suffix ^ ").unwrap()"
      | Mod => a_str ^ suffix ^ ".checked_rem(" ^ b_str ^ suffix ^ ").unwrap()"
      | Shl => a_str ^ suffix ^ ".checked_shl(" ^ b_str ^ "u32).unwrap()"
      | Shr => a_str ^ suffix ^ ".checked_shr(" ^ b_str ^ "u32).unwrap()")
    end

  fun mk_rust_panic_check_expr op_kind suffix pair =
    "std::panic::catch_unwind(|| { let _ = " ^ mk_checked_expr op_kind suffix pair ^ "; }).is_err()"

  fun overflow_edge_cases utype =
    let
      val max = uint_max utype
      val mid = max div 2
    in
      [(0, 0), (1, 1), (max, 0), (max, 1), (max, max), (max, max - 1),
       (mid, mid), (mid + 1, mid + 1), (0, max), (1, max)]
    end

  fun underflow_edge_cases utype =
    let
      val max = uint_max utype
      val mid = max div 2
    in
      [(0, 0), (0, 1), (1, 0), (max, max), (max, 1), (1, max),
       (mid, mid + 1), (mid + 1, mid), (max, 0), (0, max)]
    end

  fun div_mod_edge_cases utype =
    let
      val max = uint_max utype
      val mid = max div 2
    in
      [(0, 1), (1, 1), (10, 3), (10, 0), (max, 1), (max, max),
       (0, 0), (1, 0), (max, 0), (mid, 2)]
    end

  fun shift_edge_cases utype =
    let
      val max = uint_max utype
      val bits = IntInf.fromInt (uint_bits utype)
    in
      [(1, 0), (1, 1), (1, bits - 1), (1, bits), (1, bits + 1),
       (max, 0), (max, 1), (max, bits - 1), (max, bits), (max, bits + 2)]
    end

  fun edge_cases_for op_kind utype =
    (case op_kind of
      Add => overflow_edge_cases utype
    | Sub => underflow_edge_cases utype
    | Mul => overflow_edge_cases utype
    | Div => div_mod_edge_cases utype
    | Mod => div_mod_edge_cases utype
    | Shl => shift_edge_cases utype
    | Shr => shift_edge_cases utype)

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

  fun gen_random_shift_pairs_for utype seed n =
    let
      val bits = uint_bits utype
    in
      (case utype of
        U8 =>
          next_list seed n (fn s =>
            let
              val (value, s') = next_word8 s
              val (shift, s'') = next_int s' 0 (bits + 5)
            in
              ((Word8.toLargeInt value, IntInf.fromInt shift), s'')
            end)
      | U16 =>
          next_list seed n (fn s =>
            let
              val (value, s') = next_word16 s
              val (shift, s'') = next_int s' 0 (bits + 5)
            in
              ((Word.toLargeInt value, IntInf.fromInt shift), s'')
            end)
      | U32 =>
          next_list seed n (fn s =>
            let
              val (value, s') = next_word32 s
              val (shift, s'') = next_int s' 0 (bits + 5)
            in
              ((Word32.toLargeInt value, IntInf.fromInt shift), s'')
            end)
      | U64 =>
          next_list seed n (fn s =>
            let
              val (value, s') = next_word64 s
              val (shift, s'') = next_int s' 0 (bits + 5)
            in
              ((Word64.toLargeInt value, IntInf.fromInt shift), s'')
            end))
    end

  fun gen_test ctxt utype op_kind idx pair =
    let
      val bits = uint_bits utype
      val suffix = uint_rust_suffix utype
      val term = parse_term ctxt (mk_term_string op_kind bits pair)
      val expected = eval_panic_to_rust ctxt term
      val rust_expr = mk_rust_panic_check_expr op_kind suffix pair
      val name = "test_" ^ Int.toString idx
    in
      {name = name, rust_expr = rust_expr, expected = expected}
    end

  fun gen_op_tests ctxt utype op_kind seed num_random =
    let
      val edges = edge_cases_for op_kind utype
      val (random_pairs, _) =
        if is_shift_op op_kind
        then gen_random_shift_pairs_for utype seed num_random
        else gen_random_pairs_for utype seed num_random
      val all_pairs = edges @ random_pairs
    in
      map_index (fn (i, pair) => gen_test ctxt utype op_kind i pair) all_pairs
    end

  fun generate_type_tests ctxt utype seed num_random =
    let
      val suffix = uint_rust_suffix utype
      fun mod_name op_kind = "panic_" ^ suffix ^ "_" ^ op_suffix op_kind
      fun tests op_kind = gen_op_tests ctxt utype op_kind seed num_random
    in
      [(mod_name Add, tests Add),
       (mod_name Sub, tests Sub),
       (mod_name Mul, tests Mul),
       (mod_name Div, tests Div),
       (mod_name Mod, tests Mod),
       (mod_name Shl, tests Shl),
       (mod_name Shr, tests Shr)]
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
