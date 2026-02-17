(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Core conformance testing infrastructure.
   Provides result type representation, HOL term evaluation, and conversion utilities.

   The main workflow is:
   1. Generate random test inputs (word values)
   2. Construct HOL terms representing function applications
   3. Evaluate terms using Isabelle's code evaluation
   4. Extract results and serialize to Rust syntax
*)

signature CONFORMANCE = sig
  (* Result representation matching HOL's option type *)
  datatype 'a test_result = Some of 'a | None

  (* Convert test_result to Rust syntax *)
  val option_result_to_rust : string test_result -> string

  (* Convert a boolean to Rust syntax *)
  val bool_to_rust : bool -> string

  (* Word value formatting for different sizes *)
  val word32_to_rust : Word32.word -> string -> string  (* value, type_suffix *)
  val word64_to_rust : Word64.word -> string -> string

  (* Evaluate a HOL term and extract the result *)
  val eval_term : Proof.context -> term -> term

  (* Extract word value from evaluated term *)
  val extract_word_nat : term -> IntInf.int option

  (* Convert evaluated option term to test_result *)
  val term_to_option_result : term -> string test_result

  (* Convert evaluated bool term to bool *)
  val term_to_bool : term -> bool option

  (* Detect whether an evaluated continuation term is an Abort *)
  val term_to_abort : term -> bool option

  (* Detect whether an evaluated continuation term is specifically Abort (Panic _) *)
  val term_to_panic_abort : term -> bool option

  (* Type utilities *)
  val rust_type_suffix : int -> string  (* bit width to Rust suffix *)
end

structure Conformance : CONFORMANCE = struct
  datatype 'a test_result = Some of 'a | None

  fun option_result_to_rust None = "None"
    | option_result_to_rust (Some v) = "Some(" ^ v ^ ")"

  fun bool_to_rust true = "true"
    | bool_to_rust false = "false"

  fun rust_type_suffix 8 = "u8"
    | rust_type_suffix 16 = "u16"
    | rust_type_suffix 32 = "u32"
    | rust_type_suffix 64 = "u64"
    | rust_type_suffix n = raise Fail ("Unsupported bit width: " ^ Int.toString n)

  fun word32_to_rust w suffix =
    Word32.fmt StringCvt.DEC w ^ suffix

  fun word64_to_rust w suffix =
    Word64.fmt StringCvt.DEC w ^ suffix

  (* Evaluate a term using Isabelle's code evaluation *)
  fun eval_term ctxt t =
    Value_Command.value ctxt t

  (* Try to extract a natural number from a numeral term *)
  fun extract_numeral t =
    case t of
      Const (@{const_name "Groups.zero_class.zero"}, _) => SOME 0
    | Const (@{const_name "Groups.one_class.one"}, _) => SOME 1
    | Const (@{const_name "Num.numeral_class.numeral"}, _) $ num =>
        SOME (HOLogic.dest_numeral num)
    | _ $ Const (@{const_name "Groups.zero_class.zero"}, _) => SOME 0
    | _ $ Const (@{const_name "Groups.one_class.one"}, _) => SOME 1
    | _ $ (Const (@{const_name "Num.numeral_class.numeral"}, _) $ num) =>
        SOME (HOLogic.dest_numeral num)
    | _ => NONE
    handle TERM _ => NONE

  (* Extract the nat value from a word term *)
  fun extract_word_nat t =
    case t of
      (* Direct numeral *)
      _ => extract_numeral t
    handle TERM _ => NONE

  (* Convert an evaluated option term to test_result *)
  fun term_to_option_result t =
    case t of
      Const (@{const_name "Option.option.None"}, _) => None
    | Const (@{const_name "Option.option.Some"}, _) $ v =>
        (case extract_word_nat v of
          SOME n => Some (IntInf.toString n)
        | NONE => None)  (* Fall back to None if we can't extract *)
    | _ => None

  (* Convert an evaluated bool term to bool *)
  fun term_to_bool t =
    case t of
      @{term "True"} => SOME true
    | @{term "False"} => SOME false
    | Const (@{const_name "HOL.True"}, _) => SOME true
    | Const (@{const_name "HOL.False"}, _) => SOME false
    | _ => NONE

  (* Convert an evaluated continuation term to an abort flag *)
  fun term_to_abort t =
    case t of
      Const (@{const_name Success}, _) $ _ $ _ => SOME false
    | Const (@{const_name Return}, _) $ _ $ _ => SOME false
    | Const (@{const_name Abort}, _) $ _ $ _ => SOME true
    | _ => NONE

  (* Convert an evaluated continuation term to a panic-abort flag *)
  fun term_to_panic_abort t =
    case t of
      Const (@{const_name Success}, _) $ _ $ _ => SOME false
    | Const (@{const_name Return}, _) $ _ $ _ => SOME false
    | Const (@{const_name Abort}, _) $ abort_reason $ _ =>
        (case abort_reason of
          Const (@{const_name Panic}, _) $ _ => SOME true
        | _ => SOME false)
    | _ => NONE
end

(* Open the structure for easy access *)
open Conformance
