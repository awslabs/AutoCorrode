(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Range_Conformance
  imports
    "../Conformance_Framework"
    Shallow_Micro_Rust.Range_Type
begin
(*>*)

section\<open>Range Conformance Tests\<close>

text\<open>This theory generates conformance tests for Range/slice APIs by evaluating the
actual Micro Rust function bodies (via @{term evaluate} and @{term call}), then
comparing against real Rust behaviour.\<close>

ML\<open>
structure Range_Conformance = struct
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

  val container_len = 5

  fun parse_term ctxt s = Syntax.read_term ctxt s

  fun eval_bool_to_rust ctxt term =
    (case term_to_bool (Value_Command.value ctxt term) of
      SOME true => "true"
    | SOME false => "false"
    | NONE => raise Fail "Failed to extract bool result")

  fun hol_word bits n = "(" ^ IntInf.toString n ^ " :: " ^ Int.toString bits ^ " word)"

  fun hol_word_list bits xs =
    "[" ^ String.concatWith ", " (map (hol_word bits) xs) ^ "]"

  fun rust_array suffix xs =
    "[" ^ String.concatWith ", " (map (fn x => IntInf.toString x ^ suffix) xs) ^ "]"

  fun rust_vec suffix xs =
    "vec![" ^ String.concatWith ", " (map (fn x => IntInf.toString x ^ suffix) xs) ^ "]"

  fun mk_call_bool_term ctxt body =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => r | _ => False)")

  fun mk_call_eq_term ctxt body expected =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => (r = " ^ expected ^ ") | _ => False)")

  fun mk_call_dangling_term ctxt body =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Abort DanglingPointer _ => True | _ => False)")

  fun gen_random_values_for utype seed n =
    (case utype of
      U8 => next_list seed n (fn s =>
              let val (a, s') = next_word8 s in (Word8.toLargeInt a, s') end)
    | U16 => next_list seed n (fn s =>
              let val (a, s') = next_word16 s in (Word.toLargeInt a, s') end)
    | U32 => next_list seed n (fn s =>
              let val (a, s') = next_word32 s in (Word32.toLargeInt a, s') end)
    | U64 => next_list seed n (fn s =>
              let val (a, s') = next_word64 s in (Word64.toLargeInt a, s') end))

  fun gen_random_small_values seed n upper =
    next_list seed n (fn s =>
      let
        val (i, s') = next_int s 0 upper
      in
        (IntInf.fromInt i, s')
      end)

  fun zip3 (x :: xs, y :: ys, z :: zs) = (x, y, z) :: zip3 (xs, ys, zs)
    | zip3 _ = []

  fun base_values_for utype =
    let
      val max = uint_max utype
      val cap = fn n => if n > max then max else n
    in
      [cap 11, cap 22, cap 33, cap 44, cap 55]
    end

  fun slice_list xs s e =
    let
      val s_nat = IntInf.toInt s
      val e_nat = IntInf.toInt e
    in
      List.take (List.drop (xs, s_nat), e_nat - s_nat)
    end

  fun range_values s e =
    let
      val s_nat = IntInf.toInt s
      val e_nat = IntInf.toInt e
    in
      if s_nat >= e_nat then []
      else List.tabulate (e_nat - s_nat, fn i => IntInf.fromInt (s_nat + i))
    end

  fun clamp_for_eq_new utype e =
    let
      val max = uint_max utype
    in
      if e = max then max - 1 else e
    end

  fun generate_type_tests ctxt utype seed num_random =
    let
      val bits = uint_bits utype
      val bits_str = Int.toString bits
      val suffix = uint_rust_suffix utype
      val values = base_values_for utype
      val values_list_hol = hol_word_list bits values
      val values_array_hol = "(array_of_list " ^ values_list_hol ^ " :: (" ^ bits_str ^ " word, 5) array)"
      val values_vector_hol = "(vector_of_list " ^ values_list_hol ^ " :: (" ^ bits_str ^ " word, 5) vector)"
      val values_rust_array = rust_array suffix values
      val values_rust_vec = rust_vec suffix values

      val random_small = Int.min (num_random, 30)
      val (rand_a, seed') = gen_random_values_for utype seed num_random
      val (rand_b, seed'') = gen_random_values_for utype seed' num_random
      val (rand_c, seed''') = gen_random_values_for utype seed'' num_random
      val (rand_idx_a, seed'''') = gen_random_small_values seed''' random_small 8
      val (rand_idx_b, _) = gen_random_small_values seed'''' random_small 8

      val range_edge_pairs =
        let
          val max = uint_max utype
        in
          [(0, 0), (0, 1), (1, 1), (1, 2), (2, 1), (max - 1, max), (max, max), (0, max), (max, 0)]
        end
      val contains_edge_triples =
        let
          val max = uint_max utype
        in
          [(0, 0, 0), (0, 1, 0), (0, 1, 1), (1, 3, 2), (1, 3, 3),
           (5, 9, 7), (5, 9, 9), (max - 2, max, max - 1), (max - 2, max, max)]
        end

      val range_pairs = range_edge_pairs @ ListPair.zip (rand_a, rand_b)
      val contains_triples = contains_edge_triples @ zip3 (rand_a, rand_b, rand_c)

      val idx_value_cases = [0, 1, 2, 3, 4] @ rand_idx_a
      val idx_abort_cases = [5, 6, 7, 8] @ rand_idx_a

      val range_value_cases =
        [(0, 0), (0, 1), (1, 3), (2, 5), (4, 5), (0, 5), (3, 3)]
        @ List.filter (fn (s, e) => s <= e andalso e <= 5) (ListPair.zip (rand_idx_a, rand_idx_b))

      val range_abort_cases =
        [(3, 2), (0, 6), (5, 6), (6, 6), (7, 1), (8, 0)]
        @ List.filter (fn (s, e) => s > e orelse e > 5) (ListPair.zip (rand_idx_a, rand_idx_b))

      val range_iter_cases =
        [(0, 0), (0, 1), (0, 5), (1, 4), (2, 2), (4, 5), (5, 5), (0, 8), (7, 8)]
        @ List.filter (fn (s, e) => s <= e andalso e <= 8) (ListPair.zip (rand_idx_a, rand_idx_b))

      fun eval_test mk_expected mk_rust cases =
        map_index
          (fn (i, x) =>
            {name = "test_" ^ Int.toString i,
             rust_expr = mk_rust x,
             expected = eval_bool_to_rust ctxt (mk_expected x)})
          cases

      val is_empty_tests =
        ("range_" ^ suffix ^ "_is_empty",
         eval_test
           (fn (s, e) =>
             mk_call_bool_term ctxt
               ("is_empty (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")"))
           (fn (s, e) =>
             "(" ^ IntInf.toString s ^ suffix ^ ".." ^ IntInf.toString e ^ suffix ^ ").is_empty()")
           range_pairs)

      val contains_tests =
        ("range_" ^ suffix ^ "_contains",
         eval_test
           (fn (s, e, x) =>
             mk_call_bool_term ctxt
               ("contains (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ") " ^ hol_word bits x))
           (fn (s, e, x) =>
             "(" ^ IntInf.toString s ^ suffix ^ ".." ^ IntInf.toString e ^ suffix ^ ").contains(&"
             ^ IntInf.toString x ^ suffix ^ ")")
           contains_triples)

      val range_new_tests =
        ("range_" ^ suffix ^ "_new_roundtrip",
         eval_test
           (fn (s, e) =>
             mk_call_eq_term ctxt
               ("range_new " ^ hol_word bits s ^ " " ^ hol_word bits e)
               ("make_range " ^ hol_word bits s ^ " " ^ hol_word bits e))
           (fn (s, e) =>
             "{ let r = " ^ IntInf.toString s ^ suffix ^ ".." ^ IntInf.toString e ^ suffix
             ^ "; r.start == " ^ IntInf.toString s ^ suffix ^ " && r.end == " ^ IntInf.toString e ^ suffix ^ " }")
           range_pairs)

      val range_eq_new_contains_tests =
        ("range_" ^ suffix ^ "_eq_new_contains",
         eval_test
           (fn (s, e0, x) =>
             let
               val e = clamp_for_eq_new utype e0
             in
               parse_term ctxt
                 ("(case evaluate (call (range_eq_new " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")) () of "
                  ^ "Success r _ => (case evaluate (call (contains r " ^ hol_word bits x ^ ")) () of "
                  ^ "Success b _ => b | _ => False) | _ => False)")
             end)
           (fn (s, e0, x) =>
             let
               val e = clamp_for_eq_new utype e0
             in
               "(" ^ IntInf.toString s ^ suffix ^ "..=" ^ IntInf.toString e ^ suffix ^ ").contains(&"
               ^ IntInf.toString x ^ suffix ^ ")"
             end)
           contains_triples)

      val range_into_list_tests =
        ("range_" ^ suffix ^ "_into_list",
         eval_test
           (fn (s, e) =>
             let
               val els = range_values s e
             in
               parse_term ctxt
                 ("(range_into_list (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ") = "
                  ^ hol_word_list bits els ^ ")")
             end)
           (fn (s, e) =>
             let
               val els = range_values s e
             in
               "{ let v = (" ^ IntInf.toString s ^ suffix ^ ".." ^ IntInf.toString e ^ suffix
               ^ ").collect::<Vec<" ^ suffix ^ ">>(); v == " ^ rust_vec suffix els ^ " }"
             end)
           range_iter_cases)

      val make_iterator_from_range_collect_tests =
        ("range_" ^ suffix ^ "_make_iterator_collect",
         eval_test
           (fn (s, e) =>
             let
               val els = range_values s e
             in
               mk_call_eq_term ctxt
                 ("collect (make_iterator_from_range (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ "))")
                 (hol_word_list bits els)
             end)
           (fn (s, e) =>
             let
               val els = range_values s e
             in
               "{ let v = (" ^ IntInf.toString s ^ suffix ^ ".." ^ IntInf.toString e ^ suffix
               ^ ").collect::<Vec<" ^ suffix ^ ">>(); v == " ^ rust_vec suffix els ^ " }"
             end)
           range_iter_cases)

      val range_into_iter_collect_tests =
        ("range_" ^ suffix ^ "_into_iter_collect",
         eval_test
           (fn (s, e) =>
             let
               val els = range_values s e
             in
               parse_term ctxt
                 ("(case evaluate (call (range_into_iter (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e
                  ^ "))) () of Success it _ => "
                  ^ "(case evaluate (call (collect it)) () of Success xs _ => (xs = "
                  ^ hol_word_list bits els ^ ") | _ => False) "
                  ^ "| _ => False)")
             end)
           (fn (s, e) =>
             let
               val els = range_values s e
             in
               "{ let v = (" ^ IntInf.toString s ^ suffix ^ ".." ^ IntInf.toString e ^ suffix
               ^ ").collect::<Vec<" ^ suffix ^ ">>(); v == " ^ rust_vec suffix els ^ " }"
             end)
           range_iter_cases)

      val len_tests =
        ("range_" ^ suffix ^ "_len",
         eval_test
           (fn _ => mk_call_eq_term ctxt ("len " ^ values_list_hol) "(5 :: 64 word)")
           (fn _ => "(" ^ values_rust_array ^ ".len() as u64) == 5u64")
           [()])

      val list_index_value_tests =
        ("range_" ^ suffix ^ "_list_index_value",
         eval_test
           (fn i =>
             let
               val i_nat = IntInf.toInt i mod container_len
               val expected = List.nth (values, i_nat)
             in
               mk_call_eq_term ctxt
                 ("list_index " ^ values_list_hol ^ " " ^ hol_word bits i)
                 (hol_word bits expected)
             end)
           (fn i =>
             let
               val i_nat = IntInf.toInt i mod container_len
               val expected = List.nth (values, i_nat)
             in
               "{ let arr = " ^ values_rust_array ^ "; let idx = " ^ Int.toString i_nat ^ "usize; arr[idx] == "
               ^ IntInf.toString expected ^ suffix ^ " }"
             end)
           idx_value_cases)

      val list_index_abort_tests =
        ("range_" ^ suffix ^ "_list_index_abort",
         eval_test
           (fn i => mk_call_dangling_term ctxt ("list_index " ^ values_list_hol ^ " " ^ hol_word bits i))
           (fn i =>
             "std::panic::catch_unwind(|| { let arr = " ^ values_rust_array ^ "; let idx = std::hint::black_box("
             ^ IntInf.toString i ^ " as usize); let _ = arr[idx]; }).is_err()")
           idx_abort_cases)

      val array_index_value_tests =
        ("range_" ^ suffix ^ "_array_index_value",
         eval_test
           (fn i =>
             let
               val i_nat = IntInf.toInt i mod container_len
               val expected = List.nth (values, i_nat)
             in
               mk_call_eq_term ctxt
                 ("array_index " ^ values_array_hol ^ " " ^ hol_word bits i)
                 (hol_word bits expected)
             end)
           (fn i =>
             let
               val i_nat = IntInf.toInt i mod container_len
               val expected = List.nth (values, i_nat)
             in
               "{ let arr = " ^ values_rust_array ^ "; let idx = " ^ Int.toString i_nat ^ "usize; arr[idx] == "
               ^ IntInf.toString expected ^ suffix ^ " }"
             end)
           idx_value_cases)

      val array_index_abort_tests =
        ("range_" ^ suffix ^ "_array_index_abort",
         eval_test
           (fn i => mk_call_dangling_term ctxt ("array_index " ^ values_array_hol ^ " " ^ hol_word bits i))
           (fn i =>
             "std::panic::catch_unwind(|| { let arr = " ^ values_rust_array ^ "; let idx = std::hint::black_box("
             ^ IntInf.toString i ^ " as usize); let _ = arr[idx]; }).is_err()")
           idx_abort_cases)

      val vector_index_value_tests =
        ("range_" ^ suffix ^ "_vector_index_value",
         eval_test
           (fn i =>
             let
               val i_nat = IntInf.toInt i mod container_len
               val expected = List.nth (values, i_nat)
             in
               mk_call_eq_term ctxt
                 ("vector_index " ^ values_vector_hol ^ " " ^ hol_word bits i)
                 (hol_word bits expected)
             end)
           (fn i =>
             let
               val i_nat = IntInf.toInt i mod container_len
               val expected = List.nth (values, i_nat)
             in
               "{ let v = " ^ values_rust_vec ^ "; let idx = " ^ Int.toString i_nat ^ "usize; v[idx] == "
               ^ IntInf.toString expected ^ suffix ^ " }"
             end)
           idx_value_cases)

      val vector_index_abort_tests =
        ("range_" ^ suffix ^ "_vector_index_abort",
         eval_test
           (fn i => mk_call_dangling_term ctxt ("vector_index " ^ values_vector_hol ^ " " ^ hol_word bits i))
           (fn i =>
             "std::panic::catch_unwind(|| { let v = " ^ values_rust_vec ^ "; let idx = std::hint::black_box("
             ^ IntInf.toString i ^ " as usize); let _ = v[idx]; }).is_err()")
           idx_abort_cases)

      val list_index_range_value_tests =
        ("range_" ^ suffix ^ "_list_index_range_value",
         eval_test
           (fn (s, e) =>
             let
               val sub = slice_list values s e
               val expected = hol_word_list bits sub
             in
               mk_call_eq_term ctxt
                 ("list_index_range " ^ values_list_hol ^ " (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")")
                 expected
             end)
           (fn (s, e) =>
             let
               val sub = slice_list values s e
             in
               "{ let arr = " ^ values_rust_array ^ "; let s = " ^ IntInf.toString s ^ "usize; let e = "
               ^ IntInf.toString e ^ "usize; arr[s..e].to_vec() == " ^ rust_vec suffix sub ^ " }"
             end)
           range_value_cases)

      val list_index_range_abort_tests =
        ("range_" ^ suffix ^ "_list_index_range_abort",
         eval_test
           (fn (s, e) =>
             mk_call_dangling_term ctxt
               ("list_index_range " ^ values_list_hol ^ " (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")"))
           (fn (s, e) =>
             "std::panic::catch_unwind(|| { let arr = " ^ values_rust_array ^ "; let s = "
             ^ IntInf.toString s ^ "usize; let e = " ^ IntInf.toString e ^ "usize; let _ = &arr[s..e]; }).is_err()")
           range_abort_cases)

      val array_index_range_value_tests =
        ("range_" ^ suffix ^ "_array_index_range_value",
         eval_test
           (fn (s, e) =>
             let
               val sub = slice_list values s e
               val expected = hol_word_list bits sub
             in
               mk_call_eq_term ctxt
                 ("array_index_range " ^ values_array_hol ^ " (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")")
                 expected
             end)
           (fn (s, e) =>
             let
               val sub = slice_list values s e
             in
               "{ let arr = " ^ values_rust_array ^ "; let s = " ^ IntInf.toString s ^ "usize; let e = "
               ^ IntInf.toString e ^ "usize; arr[s..e].to_vec() == " ^ rust_vec suffix sub ^ " }"
             end)
           range_value_cases)

      val array_index_range_abort_tests =
        ("range_" ^ suffix ^ "_array_index_range_abort",
         eval_test
           (fn (s, e) =>
             mk_call_dangling_term ctxt
               ("array_index_range " ^ values_array_hol ^ " (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")"))
           (fn (s, e) =>
             "std::panic::catch_unwind(|| { let arr = " ^ values_rust_array ^ "; let s = "
             ^ IntInf.toString s ^ "usize; let e = " ^ IntInf.toString e ^ "usize; let _ = &arr[s..e]; }).is_err()")
           range_abort_cases)

      val vector_index_range_value_tests =
        ("range_" ^ suffix ^ "_vector_index_range_value",
         eval_test
           (fn (s, e) =>
             let
               val sub = slice_list values s e
               val expected = hol_word_list bits sub
             in
               mk_call_eq_term ctxt
                 ("vector_index_range " ^ values_vector_hol ^ " (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")")
                 expected
             end)
           (fn (s, e) =>
             let
               val sub = slice_list values s e
             in
               "{ let v = " ^ values_rust_vec ^ "; let s = " ^ IntInf.toString s ^ "usize; let e = "
               ^ IntInf.toString e ^ "usize; v[s..e].to_vec() == " ^ rust_vec suffix sub ^ " }"
             end)
           range_value_cases)

      val vector_index_range_abort_tests =
        ("range_" ^ suffix ^ "_vector_index_range_abort",
         eval_test
           (fn (s, e) =>
             mk_call_dangling_term ctxt
               ("vector_index_range " ^ values_vector_hol ^ " (make_range " ^ hol_word bits s ^ " " ^ hol_word bits e ^ ")"))
           (fn (s, e) =>
             "std::panic::catch_unwind(|| { let v = " ^ values_rust_vec ^ "; let s = "
             ^ IntInf.toString s ^ "usize; let e = " ^ IntInf.toString e ^ "usize; let _ = &v[s..e]; }).is_err()")
           range_abort_cases)
    in
      [is_empty_tests,
       contains_tests,
       range_new_tests,
       range_eq_new_contains_tests,
       range_into_list_tests,
       make_iterator_from_range_collect_tests,
       range_into_iter_collect_tests,
       len_tests,
       list_index_value_tests,
       list_index_abort_tests,
       array_index_value_tests,
       array_index_abort_tests,
       vector_index_value_tests,
       vector_index_abort_tests,
       list_index_range_value_tests,
       list_index_range_abort_tests,
       array_index_range_value_tests,
       array_index_range_abort_tests,
       vector_index_range_value_tests,
       vector_index_range_abort_tests]
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
