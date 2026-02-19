(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Option_Conformance
  imports
    "../Conformance_Framework"
    Micro_Rust_Std_Lib.StdLib_Option
begin
(*>*)

section\<open>Option Conformance Tests\<close>

text\<open>This theory generates conformance tests for Option APIs by evaluating the
actual Micro Rust function bodies (via @{term evaluate} and @{term call}), then
comparing against real Rust behaviour.\<close>

ML\<open>
structure Option_Conformance = struct
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

  fun hol_word bits n = "(" ^ IntInf.toString n ^ " :: " ^ Int.toString bits ^ " word)"

  fun hol_option_literal bits NONE =
        "(None :: " ^ Int.toString bits ^ " word option)"
    | hol_option_literal bits (SOME v) =
        "(Some " ^ hol_word bits v ^ ")"

  fun rust_option_literal suffix NONE =
        "None::<" ^ suffix ^ ">"
    | rust_option_literal suffix (SOME v) =
        "Some(" ^ IntInf.toString v ^ suffix ^ ")"

  fun mk_call_bool_term ctxt body =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => r | _ => False)")

  fun mk_call_eq_term ctxt body expected =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Success r _ => (r = " ^ expected ^ ") | _ => False)")

  fun mk_call_panic_term ctxt body =
    parse_term ctxt
      ("(case evaluate (call (" ^ body ^ ")) () of Abort (Panic _) _ => True | _ => False)")

  fun mk_ok_or_is_ok_term ctxt bits opt err =
    let
      val opt_str = hol_option_literal bits opt
      val err_str = hol_word bits err
      val body = "ok_or " ^ opt_str ^ " " ^ err_str
    in
      parse_term ctxt
        ("(case evaluate (call (" ^ body ^ ")) () of "
         ^ "Success r _ => (case r of Ok _ => True | Err _ => False) | _ => False)")
    end

  fun mk_ok_or_ok_value_term ctxt bits opt err =
    let
      val opt_str = hol_option_literal bits opt
      val err_str = hol_word bits err
      val body = "ok_or " ^ opt_str ^ " " ^ err_str
      val expected_ok =
        (case opt of
          SOME v => hol_word bits v
        | NONE => hol_word bits 0)
    in
      parse_term ctxt
        ("(case evaluate (call (" ^ body ^ ")) () of "
         ^ "Success r _ => (case r of Ok v => (v = " ^ expected_ok ^ ") | Err _ => False) "
         ^ "| _ => False)")
    end

  fun mk_ok_or_err_value_term ctxt bits opt err =
    let
      val opt_str = hol_option_literal bits opt
      val err_str = hol_word bits err
      val body = "ok_or " ^ opt_str ^ " " ^ err_str
    in
      parse_term ctxt
        ("(case evaluate (call (" ^ body ^ ")) () of "
         ^ "Success r _ => (case r of Err e => (e = " ^ err_str ^ ") | Ok _ => False) "
         ^ "| _ => False)")
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

  fun option_edge_cases utype =
    let
      val max = uint_max utype
    in
      [NONE, SOME 0, SOME 1, SOME (max - 1), SOME max]
    end

  fun ok_or_edge_cases utype =
    let
      val max = uint_max utype
    in
      [(NONE, 0), (NONE, 1), (SOME 0, 0), (SOME 1, max), (SOME max, 1),
       (SOME (max - 1), max), (NONE, max), (SOME 42, 7), (SOME 7, 42), (NONE, 42)]
    end

  fun inject_nones values =
    map_index (fn (i, v) => if i mod 4 = 0 then NONE else SOME v) values

  fun make_ok_or_random_pairs values errs =
    map (fn (v, e) => (if IntInf.mod (v, 5) = 0 then NONE else SOME v, e))
      (ListPair.zip (values, errs))

  fun generate_type_tests ctxt utype seed num_random =
    let
      val bits = uint_bits utype
      val suffix = uint_rust_suffix utype
      val (rand_vals_a, seed') = gen_random_values_for utype seed num_random
      val (rand_vals_b, _) = gen_random_values_for utype seed' num_random

      val opt_cases = option_edge_cases utype @ inject_nones rand_vals_a
      val unwrap_values = map_filter I opt_cases
      val ok_or_cases = ok_or_edge_cases utype @ make_ok_or_random_pairs rand_vals_a rand_vals_b

      fun eval_test mk_expected mk_rust cases =
        map_index
          (fn (i, x) =>
            {name = "test_" ^ Int.toString i,
             rust_expr = mk_rust x,
             expected = eval_bool_to_rust ctxt (mk_expected x)})
          cases

      fun mk_option_body fn_name opt =
        fn_name ^ " " ^ hol_option_literal bits opt

      val is_none_tests =
        ("option_" ^ suffix ^ "_is_none",
         eval_test
           (fn opt => mk_call_bool_term ctxt (mk_option_body "urust_func_option_is_none" opt))
           (fn opt => rust_option_literal suffix opt ^ ".is_none()")
           opt_cases)

      val is_some_tests =
        ("option_" ^ suffix ^ "_is_some",
         eval_test
           (fn opt => mk_call_bool_term ctxt (mk_option_body "urust_func_option_is_some" opt))
           (fn opt => rust_option_literal suffix opt ^ ".is_some()")
           opt_cases)

      val unwrap_panic_tests =
        ("option_" ^ suffix ^ "_unwrap_panics",
         eval_test
           (fn opt => mk_call_panic_term ctxt (mk_option_body "option_unwrap" opt))
           (fn opt => "std::panic::catch_unwind(|| { let _ = "
                      ^ rust_option_literal suffix opt ^ ".unwrap(); }).is_err()")
           opt_cases)

      val unwrap_value_tests =
        ("option_" ^ suffix ^ "_unwrap_value",
         eval_test
           (fn v =>
             mk_call_eq_term ctxt
               (mk_option_body "option_unwrap" (SOME v))
               (hol_word bits v))
           (fn v => "Some(" ^ IntInf.toString v ^ suffix ^ ").unwrap() == " ^ IntInf.toString v ^ suffix)
           unwrap_values)

      val expect_panic_tests =
        ("option_" ^ suffix ^ "_expect_panics",
         eval_test
           (fn opt =>
             mk_call_panic_term ctxt
               ("option_expect " ^ hol_option_literal bits opt ^ " (STR ''expect'')"))
           (fn opt => "std::panic::catch_unwind(|| { let _ = "
                      ^ rust_option_literal suffix opt ^ ".expect(\"expect\"); }).is_err()")
           opt_cases)

      val expect_value_tests =
        ("option_" ^ suffix ^ "_expect_value",
         eval_test
           (fn v =>
             mk_call_eq_term ctxt
               ("option_expect " ^ hol_option_literal bits (SOME v) ^ " (STR ''expect'')")
               (hol_word bits v))
           (fn v => "Some(" ^ IntInf.toString v ^ suffix ^ ").expect(\"expect\") == "
                    ^ IntInf.toString v ^ suffix)
           unwrap_values)

      val ok_or_is_ok_tests =
        ("option_" ^ suffix ^ "_ok_or_is_ok",
         eval_test
           (fn (opt, err) => mk_ok_or_is_ok_term ctxt bits opt err)
           (fn (opt, err) =>
              rust_option_literal suffix opt ^ ".ok_or(" ^ IntInf.toString err ^ suffix ^ ").is_ok()")
           ok_or_cases)

      val ok_or_ok_value_tests =
        ("option_" ^ suffix ^ "_ok_or_ok_value",
         eval_test
           (fn (opt, err) => mk_ok_or_ok_value_term ctxt bits opt err)
           (fn (opt, err) =>
              let
                val expected =
                  (case opt of SOME v => IntInf.toString v | NONE => "0")
              in
                "(match " ^ rust_option_literal suffix opt ^ ".ok_or(" ^ IntInf.toString err ^ suffix ^ ") { "
                ^ "Ok(v) => v == " ^ expected ^ suffix ^ ", Err(_) => false })"
              end)
           ok_or_cases)

      val ok_or_err_value_tests =
        ("option_" ^ suffix ^ "_ok_or_err_value",
         eval_test
           (fn (opt, err) => mk_ok_or_err_value_term ctxt bits opt err)
           (fn (opt, err) =>
              "(match " ^ rust_option_literal suffix opt ^ ".ok_or(" ^ IntInf.toString err ^ suffix ^ ") { "
              ^ "Err(e) => e == " ^ IntInf.toString err ^ suffix ^ ", Ok(_) => false })")
           ok_or_cases)
    in
      [is_none_tests,
       is_some_tests,
       unwrap_panic_tests,
       unwrap_value_tests,
       expect_panic_tests,
       expect_value_tests,
       ok_or_is_ok_tests,
       ok_or_ok_value_tests,
       ok_or_err_value_tests]
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
