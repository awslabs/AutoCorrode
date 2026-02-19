(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Tuple_Conformance
  imports
    "../Conformance_Framework"
    Micro_Rust_Std_Lib.StdLib_Tuple
begin
(*>*)

section\<open>Tuple Conformance Tests\<close>

text\<open>This theory generates conformance tests for tuple/list zipping APIs by
evaluating the actual Micro Rust function body, then comparing to real Rust
behaviour.\<close>

ML\<open>
structure Tuple_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  datatype uint_type = U8 | U16 | U32 | U64

  fun uint_bits U8 = 8 | uint_bits U16 = 16 | uint_bits U32 = 32 | uint_bits U64 = 64
  fun uint_rust_suffix U8 = "u8" | uint_rust_suffix U16 = "u16"
    | uint_rust_suffix U32 = "u32" | uint_rust_suffix U64 = "u64"

  fun parse_term ctxt s = Syntax.read_term ctxt s

  fun eval_bool_to_rust ctxt term =
    (case term_to_bool (Value_Command.value ctxt term) of
      SOME true => "true"
    | SOME false => "false"
    | NONE => raise Fail "Failed to extract bool result")

  fun hol_word bits n = "(" ^ IntInf.toString n ^ " :: " ^ Int.toString bits ^ " word)"

  fun hol_word_list bits xs =
    "[" ^ String.concatWith ", " (map (hol_word bits) xs) ^ "]"

  fun rust_vec suffix xs =
    "vec![" ^ String.concatWith ", " (map (fn x => IntInf.toString x ^ suffix) xs) ^ "]"

  fun zip_short (x :: xs) (y :: ys) = (x, y) :: zip_short xs ys
    | zip_short _ _ = []

  fun hol_tuple3_list bits pairs =
    let
      fun elem (a, b) = "(" ^ hol_word bits a ^ ", " ^ hol_word bits b ^ ", TNil)"
    in
      "[" ^ String.concatWith ", " (map elem pairs) ^ "]"
    end

  fun rust_pair_vec suffix pairs =
    let
      fun elem (a, b) = "(" ^ IntInf.toString a ^ suffix ^ ", " ^ IntInf.toString b ^ suffix ^ ")"
    in
      "vec![" ^ String.concatWith ", " (map elem pairs) ^ "]"
    end

  fun mk_call_eq_term ctxt body expected =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => (r = " ^ expected ^ ") | _ => False)")

  fun next_random_value utype seed =
    (case utype of
      U8 => let val (v, s') = next_word8 seed in (Word8.toLargeInt v, s') end
    | U16 => let val (v, s') = next_word16 seed in (Word.toLargeInt v, s') end
    | U32 => let val (v, s') = next_word32 seed in (Word32.toLargeInt v, s') end
    | U64 => let val (v, s') = next_word64 seed in (Word64.toLargeInt v, s') end)

  fun gen_random_list utype seed max_len =
    let
      val (len, seed') = next_int seed 0 max_len
      fun go 0 acc s = (rev acc, s)
        | go n acc s =
            let
              val (v, s') = next_random_value utype s
            in
              go (n - 1) (v :: acc) s'
            end
    in
      go len [] seed'
    end

  fun gen_random_list_pairs utype seed n =
    next_list seed n (fn s =>
      let
        val (xs, s') = gen_random_list utype s 6
        val (ys, s'') = gen_random_list utype s' 6
      in
        ((xs, ys), s'')
      end)

  fun edge_pairs utype =
    let
      val bits = uint_bits utype
      val one = 1 : IntInf.int
      val two = 2 : IntInf.int
      val three = 3 : IntInf.int
      val max =
        (case utype of
          U8 => 255
        | U16 => 65535
        | U32 => 4294967295
        | U64 => 18446744073709551615)
      val cap = fn n => if n > max then max else n
      val _ = bits
    in
      [([], []),
       ([cap one], []),
       ([], [cap two]),
       ([cap one], [cap two]),
       ([cap one, cap two, cap three], [cap three, cap two, cap one]),
       ([cap 10, cap 20, cap 30, cap 40], [cap 1, cap 2]),
       ([cap 5], [cap 6, cap 7, cap 8, cap 9]),
       ([cap max, cap (max - 1)], [cap 0, cap 1])]
    end

  fun generate_type_tests ctxt utype seed num_random =
    let
      val bits = uint_bits utype
      val suffix = uint_rust_suffix utype
      val (random_pairs, _) = gen_random_list_pairs utype seed num_random
      val cases = edge_pairs utype @ random_pairs

      val tests =
        map_index
          (fn (i, (xs, ys)) =>
            let
              val zipped = zip_short xs ys
              val body = "list_zip " ^ hol_word_list bits xs ^ " " ^ hol_word_list bits ys
              val expected = hol_tuple3_list bits zipped
              val rust_expr =
                "{ let xs = " ^ rust_vec suffix xs ^ "; let ys = " ^ rust_vec suffix ys ^ "; "
                ^ "xs.into_iter().zip(ys.into_iter()).collect::<Vec<(" ^ suffix ^ ", " ^ suffix ^ ")>>() == "
                ^ rust_pair_vec suffix zipped ^ " }"
            in
              {name = "test_" ^ Int.toString i,
               rust_expr = rust_expr,
               expected = eval_bool_to_rust ctxt (mk_call_eq_term ctxt body expected)}
            end)
          cases
    in
      [("tuple_" ^ suffix ^ "_list_zip", tests)]
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
