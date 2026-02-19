(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Result_Conformance
  imports
    "../Conformance_Framework"
    Micro_Rust_Std_Lib.StdLib_Result
begin
(*>*)

section\<open>Result Conformance Tests\<close>

text\<open>This theory generates conformance tests for Result APIs by evaluating the
actual Micro Rust function bodies (via @{term evaluate} and @{term call}), then
comparing against real Rust behaviour.\<close>

ML\<open>
structure Result_Conformance = struct
  open Conformance_Random
  open Conformance
  open Rust_Codegen

  datatype uint_type = U8 | U16 | U32 | U64
  datatype res_case = OK of IntInf.int | ERR of IntInf.int

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

  fun hol_word bits n = "(" ^ IntInf.toString n ^ " :: " ^ Int.toString bits ^ " word)"

  fun hol_result_literal bits (OK v) =
        "(Ok " ^ hol_word bits v ^ " :: (" ^ Int.toString bits ^ " word, "
        ^ Int.toString bits ^ " word) result)"
    | hol_result_literal bits (ERR e) =
        "(Err " ^ hol_word bits e ^ " :: (" ^ Int.toString bits ^ " word, "
        ^ Int.toString bits ^ " word) result)"

  fun rust_result_literal suffix (OK v) =
        "Ok::<" ^ suffix ^ ", " ^ suffix ^ ">(" ^ IntInf.toString v ^ suffix ^ ")"
    | rust_result_literal suffix (ERR e) =
        "Err::<" ^ suffix ^ ", " ^ suffix ^ ">(" ^ IntInf.toString e ^ suffix ^ ")"

  fun mk_call_bool_term ctxt body =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => r | _ => False)")

  fun mk_call_eq_term ctxt body expected =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => (r = " ^ expected ^ ") | _ => False)")

  fun mk_call_panic_term ctxt body =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Abort (Panic _) _ => True | _ => False)")

  fun mk_result_is_ok_term ctxt bits res =
    let
      val res_str = hol_result_literal bits res
    in
      parse_term ctxt
        ("(case evaluate (call (urust_func_result_is_ok " ^ res_str ^ ")) () of "
         ^ "Success r _ => r | _ => False)")
    end

  fun mk_result_is_err_term ctxt bits res =
    let
      val res_str = hol_result_literal bits res
    in
      parse_term ctxt
        ("(case evaluate (call (urust_func_result_is_err " ^ res_str ^ ")) () of "
         ^ "Success r _ => r | _ => False)")
    end

  fun mk_result_ok_is_some_term ctxt bits res =
    let
      val res_str = hol_result_literal bits res
    in
      parse_term ctxt
        ("(case evaluate (call (ok " ^ res_str ^ ")) () of "
         ^ "Success r _ => (case r of Some _ => True | None => False) | _ => False)")
    end

  fun mk_result_ok_value_term ctxt bits res =
    let
      val res_str = hol_result_literal bits res
      val expected =
        (case res of
          OK v => hol_word bits v
        | ERR _ => hol_word bits 0)
    in
      parse_term ctxt
        ("(case evaluate (call (ok " ^ res_str ^ ")) () of "
         ^ "Success r _ => (case r of Some v => (v = " ^ expected ^ ") | None => False) | _ => False)")
    end

  fun mk_result_or_is_ok_term ctxt bits (res, fallback) =
    let
      val res_str = hol_result_literal bits res
      val fb_str = hol_result_literal bits fallback
    in
      parse_term ctxt
        ("(case evaluate (call (result_or " ^ res_str ^ " " ^ fb_str ^ ")) () of "
         ^ "Success r _ => (case r of Ok _ => True | Err _ => False) | _ => False)")
    end

  fun mk_result_or_ok_value_term ctxt bits (res, fallback) =
    let
      val res_str = hol_result_literal bits res
      val fb_str = hol_result_literal bits fallback
      val expected =
        (case res of
          OK v => SOME v
        | ERR _ => (case fallback of OK v => SOME v | ERR _ => NONE))
      val expected_str =
        (case expected of
          SOME v => hol_word bits v
        | NONE => hol_word bits 0)
    in
      parse_term ctxt
        ("(case evaluate (call (result_or " ^ res_str ^ " " ^ fb_str ^ ")) () of "
         ^ "Success r _ => (case r of Ok v => (v = " ^ expected_str ^ ") | Err _ => False) | _ => False)")
    end

  fun mk_result_or_err_value_term ctxt bits (res, fallback) =
    let
      val res_str = hol_result_literal bits res
      val fb_str = hol_result_literal bits fallback
      val expected =
        (case res of
          OK _ => NONE
        | ERR _ => (case fallback of OK _ => NONE | ERR e => SOME e))
      val expected_str =
        (case expected of
          SOME e => hol_word bits e
        | NONE => hol_word bits 0)
    in
      parse_term ctxt
        ("(case evaluate (call (result_or " ^ res_str ^ " " ^ fb_str ^ ")) () of "
         ^ "Success r _ => (case r of Err e => (e = " ^ expected_str ^ ") | Ok _ => False) | _ => False)")
    end

  fun mk_unwrap_or_term ctxt bits (res, fallback) =
    let
      val res_str = hol_result_literal bits res
      val fb_str = hol_word bits fallback
      val expected =
        (case res of OK v => hol_word bits v | ERR _ => fb_str)
    in
      parse_term ctxt
        ("(case evaluate (call (result_unwrap_or " ^ res_str ^ " " ^ fb_str ^ ")) () of "
         ^ "Success r _ => (r = " ^ expected ^ ") | _ => False)")
    end

  fun mk_map_err_term ctxt bits res =
    let
      val res_str = hol_result_literal bits res
      val mapper = "(%e. FunctionBody (literal (e + (1 :: " ^ Int.toString bits ^ " word))))"
      val expected_ok =
        (case res of OK v => SOME v | ERR _ => NONE)
      val expected_err =
        (case res of ERR e => SOME e | OK _ => NONE)
      val ok_case =
        (case expected_ok of
          SOME v => "Ok v => (v = " ^ hol_word bits v ^ ")"
        | NONE => "Ok _ => False")
      val err_case =
        (case expected_err of
          SOME e => "Err e => (e = (" ^ hol_word bits e ^ " + (1 :: " ^ Int.toString bits ^ " word)))"
        | NONE => "Err _ => False")
    in
      parse_term ctxt
        ("(case evaluate (call (map_err " ^ res_str ^ " " ^ mapper ^ ")) () of "
         ^ "Success r _ => (case r of " ^ ok_case ^ " | " ^ err_case ^ ") | _ => False)")
    end

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

  fun result_edge_cases utype =
    let
      val max = uint_max utype
    in
      [OK 0, OK 1, OK max, ERR 0, ERR 1, ERR max]
    end

  fun result_pair_edge_cases utype =
    let
      val max = uint_max utype
    in
      [(OK 1, OK 2), (OK max, ERR 7), (ERR 3, OK 4), (ERR 5, ERR 6),
       (OK 0, ERR max), (ERR max, OK 0), (OK max, OK max), (ERR 0, ERR max),
       (ERR 1, OK max), (OK 7, ERR 8)]
    end

  fun inject_results values =
    map_index (fn (i, v) => if i mod 2 = 0 then OK v else ERR v) values

  fun make_result_pairs vals_a vals_b =
    map_index
      (fn (i, (a, b)) =>
        (if i mod 2 = 0 then OK a else ERR a, if i mod 3 = 0 then OK b else ERR b))
      (ListPair.zip (vals_a, vals_b))

  fun generate_type_tests ctxt utype seed num_random =
    let
      val bits = uint_bits utype
      val suffix = uint_rust_suffix utype
      val (rand_a, seed') = gen_random_values_for utype seed num_random
      val (rand_b, _) = gen_random_values_for utype seed' num_random

      val res_cases = result_edge_cases utype @ inject_results rand_a
      val unwrap_ok_values = map_filter (fn r => case r of OK v => SOME v | ERR _ => NONE) res_cases
      val res_pairs = result_pair_edge_cases utype @ make_result_pairs rand_a rand_b
      val unwrap_or_pairs = ListPair.zip (res_cases, rand_b)

      fun eval_test mk_expected mk_rust cases =
        map_index
          (fn (i, x) =>
            {name = "test_" ^ Int.toString i,
             rust_expr = mk_rust x,
             expected = eval_bool_to_rust ctxt (mk_expected x)})
          cases

      val is_ok_tests =
        ("result_" ^ suffix ^ "_is_ok",
         eval_test
           (fn res => mk_result_is_ok_term ctxt bits res)
           (fn res => rust_result_literal suffix res ^ ".is_ok()")
           res_cases)

      val is_err_tests =
        ("result_" ^ suffix ^ "_is_err",
         eval_test
           (fn res => mk_result_is_err_term ctxt bits res)
           (fn res => rust_result_literal suffix res ^ ".is_err()")
           res_cases)

      val ok_is_some_tests =
        ("result_" ^ suffix ^ "_ok_is_some",
         eval_test
           (fn res => mk_result_ok_is_some_term ctxt bits res)
           (fn res => rust_result_literal suffix res ^ ".ok().is_some()")
           res_cases)

      val ok_value_tests =
        ("result_" ^ suffix ^ "_ok_value",
         eval_test
           (fn res => mk_result_ok_value_term ctxt bits res)
           (fn res =>
              "(match " ^ rust_result_literal suffix res ^ ".ok() { Some(v) => "
              ^ (case res of OK v => "v == " ^ IntInf.toString v ^ suffix | ERR _ => "false")
              ^ ", None => false })")
           res_cases)

      val or_is_ok_tests =
        ("result_" ^ suffix ^ "_or_is_ok",
         eval_test
           (fn pair => mk_result_or_is_ok_term ctxt bits pair)
           (fn (r, fb) => rust_result_literal suffix r ^ ".or(" ^ rust_result_literal suffix fb ^ ").is_ok()")
           res_pairs)

      val or_ok_value_tests =
        ("result_" ^ suffix ^ "_or_ok_value",
         eval_test
           (fn pair => mk_result_or_ok_value_term ctxt bits pair)
           (fn (r, fb) =>
              "(match " ^ rust_result_literal suffix r ^ ".or(" ^ rust_result_literal suffix fb ^ ") { "
              ^ "Ok(v) => "
              ^ (case r of
                  OK v => "v == " ^ IntInf.toString v ^ suffix
                | ERR _ => (case fb of OK v => "v == " ^ IntInf.toString v ^ suffix | ERR _ => "false"))
              ^ ", Err(_) => false })")
           res_pairs)

      val or_err_value_tests =
        ("result_" ^ suffix ^ "_or_err_value",
         eval_test
           (fn pair => mk_result_or_err_value_term ctxt bits pair)
           (fn (r, fb) =>
              "(match " ^ rust_result_literal suffix r ^ ".or(" ^ rust_result_literal suffix fb ^ ") { "
              ^ "Err(e) => "
              ^ (case r of
                  OK _ => "false"
                | ERR _ => (case fb of ERR e => "e == " ^ IntInf.toString e ^ suffix | OK _ => "false"))
              ^ ", Ok(_) => false })")
           res_pairs)

      val unwrap_panic_tests =
        ("result_" ^ suffix ^ "_unwrap_panics",
         eval_test
           (fn res => mk_call_panic_term ctxt ("result_unwrap " ^ hol_result_literal bits res))
           (fn res => "std::panic::catch_unwind(|| { let _ = "
                      ^ rust_result_literal suffix res ^ ".unwrap(); }).is_err()")
           res_cases)

      val unwrap_value_tests =
        ("result_" ^ suffix ^ "_unwrap_value",
         eval_test
           (fn v => mk_call_eq_term ctxt
                        ("result_unwrap " ^ hol_result_literal bits (OK v))
                        (hol_word bits v))
           (fn v => "Ok::<" ^ suffix ^ ", " ^ suffix ^ ">(" ^ IntInf.toString v ^ suffix ^ ").unwrap() == "
                    ^ IntInf.toString v ^ suffix)
           unwrap_ok_values)

      val expect_panic_tests =
        ("result_" ^ suffix ^ "_expect_panics",
         eval_test
           (fn res => mk_call_panic_term ctxt ("result_expect " ^ hol_result_literal bits res ^ " (STR ''expect'')"))
           (fn res => "std::panic::catch_unwind(|| { let _ = "
                      ^ rust_result_literal suffix res ^ ".expect(\"expect\"); }).is_err()")
           res_cases)

      val expect_value_tests =
        ("result_" ^ suffix ^ "_expect_value",
         eval_test
           (fn v => mk_call_eq_term ctxt
                        ("result_expect " ^ hol_result_literal bits (OK v) ^ " (STR ''expect'')")
                        (hol_word bits v))
           (fn v => "Ok::<" ^ suffix ^ ", " ^ suffix ^ ">(" ^ IntInf.toString v ^ suffix ^ ").expect(\"expect\") == "
                    ^ IntInf.toString v ^ suffix)
           unwrap_ok_values)

      val unwrap_or_tests =
        ("result_" ^ suffix ^ "_unwrap_or",
         eval_test
           (fn pair => mk_unwrap_or_term ctxt bits pair)
           (fn (res, fallback) =>
              rust_result_literal suffix res ^ ".unwrap_or(" ^ IntInf.toString fallback ^ suffix ^ ") == "
              ^ (case res of OK v => IntInf.toString v | ERR _ => IntInf.toString fallback) ^ suffix)
           unwrap_or_pairs)

      val map_err_tests =
        ("result_" ^ suffix ^ "_map_err",
         eval_test
           (fn res => mk_map_err_term ctxt bits res)
           (fn res =>
              "(match " ^ rust_result_literal suffix res ^ ".map_err(|e| e.wrapping_add(1" ^ suffix ^ ")) { "
              ^ "Ok(v) => "
              ^ (case res of
                  OK v => "v == " ^ IntInf.toString v ^ suffix
                | ERR _ => "false")
              ^ ", Err(e) => "
              ^ (case res of
                  ERR e => "e == " ^ IntInf.toString ((e + 1) mod (uint_max utype + 1)) ^ suffix
                | OK _ => "false")
              ^ " })")
           res_cases)
    in
      [is_ok_tests,
       is_err_tests,
       ok_is_some_tests,
       ok_value_tests,
       or_is_ok_tests,
       or_ok_value_tests,
       or_err_value_tests,
       unwrap_panic_tests,
       unwrap_value_tests,
       expect_panic_tests,
       expect_value_tests,
       unwrap_or_tests,
       map_err_tests]
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
