(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Deterministic random number generation for conformance testing.
   Uses a linear congruential generator with fixed seed for reproducibility.

   The default seed is 42, ensuring tests are deterministic across runs.
*)

signature CONFORMANCE_RANDOM = sig
  type seed

  (* Initialize with a seed value (default: 42) *)
  val init : int -> seed
  val default_seed : seed

  (* Generate random integers in range [lo, hi] *)
  val next_int : seed -> int -> int -> int * seed

  (* Generate random word values for different sizes *)
  val next_word8 : seed -> Word8.word * seed
  val next_word16 : seed -> Word.word * seed  (* 16-bit *)
  val next_word32 : seed -> Word32.word * seed
  val next_word64 : seed -> Word64.word * seed

  (* Generate lists of random values *)
  val next_list : seed -> int -> (seed -> 'a * seed) -> 'a list * seed

  (* Generate pairs of random values *)
  val next_pair : seed -> (seed -> 'a * seed) -> (seed -> 'b * seed) -> ('a * 'b) * seed

  (* Boundary values for testing edge cases *)
  val word8_boundaries : Word8.word list
  val word16_boundaries : Word.word list
  val word32_boundaries : Word32.word list
  val word64_boundaries : Word64.word list

  (* Generate a mix of boundary and random values *)
  val word32_test_values : seed -> int -> Word32.word list * seed
  val word64_test_values : seed -> int -> Word64.word list * seed
end

structure Conformance_Random : CONFORMANCE_RANDOM = struct
  type seed = Word64.word

  (* LCG parameters (same as glibc) *)
  val a : Word64.word = 0w1103515245
  val c : Word64.word = 0w12345
  val m : Word64.word = 0wx80000000 (* 2^31 *)

  fun init s = Word64.fromInt s
  val default_seed = init 42

  fun next seed =
    Word64.mod (Word64.+ (Word64.* (seed, a), c), m)

  fun next_int seed lo hi =
    let
      val seed' = next seed
      val range = hi - lo + 1
      val value = lo + Word64.toInt (Word64.mod (seed', Word64.fromInt range))
    in (value, seed') end

  fun next_word8 seed =
    let
      val seed' = next seed
      val w = Word8.fromInt (Word64.toInt (Word64.mod (seed', 0w256)))
    in (w, seed') end

  fun next_word16 seed =
    let
      val seed' = next seed
      val w = Word.fromInt (Word64.toInt (Word64.mod (seed', 0w65536)))
    in (w, seed') end

  fun next_word32 seed =
    let
      val seed1 = next seed
      val seed2 = next seed1
      val lo = Word32.fromInt (Word64.toInt (Word64.mod (seed1, 0wx10000)))
      val hi = Word32.fromInt (Word64.toInt (Word64.mod (seed2, 0wx10000)))
      val w = Word32.orb (lo, Word32.<< (hi, 0w16))
    in (w, seed2) end

  fun next_word64 seed =
    let
      val seed1 = next seed
      val seed2 = next seed1
      val seed3 = next seed2
      val seed4 = next seed3
      val w0 = Word64.mod (seed1, 0wx10000)
      val w1 = Word64.mod (seed2, 0wx10000)
      val w2 = Word64.mod (seed3, 0wx10000)
      val w3 = Word64.mod (seed4, 0wx10000)
      val lo = Word64.orb (w0, Word64.<< (w1, 0w16))
      val hi = Word64.orb (w2, Word64.<< (w3, 0w16))
      val w = Word64.orb (lo, Word64.<< (hi, 0w32))
    in (w, seed4) end

  fun next_list seed 0 _ = ([], seed)
    | next_list seed n gen =
        let
          val (x, seed') = gen seed
          val (xs, seed'') = next_list seed' (n - 1) gen
        in (x :: xs, seed'') end

  fun next_pair seed gen_a gen_b =
    let
      val (a, seed') = gen_a seed
      val (b, seed'') = gen_b seed'
    in ((a, b), seed'') end

  (* Boundary values for edge case testing *)
  val word8_boundaries : Word8.word list = [
    0w0,              (* min *)
    0w1,              (* min + 1 *)
    0w127,            (* mid-1 *)
    0w128,            (* mid (2^7) *)
    0w254,            (* max - 1 *)
    0w255             (* max *)
  ]

  val word16_boundaries : Word.word list = [
    0w0,              (* min *)
    0w1,              (* min + 1 *)
    0w32767,          (* mid-1 *)
    0w32768,          (* mid (2^15) *)
    0w65534,          (* max - 1 *)
    0w65535           (* max *)
  ]

  val word32_boundaries : Word32.word list = [
    0w0,              (* min *)
    0w1,              (* min + 1 *)
    0w2147483647,     (* mid-1 (2^31 - 1) *)
    0w2147483648,     (* mid (2^31) *)
    0w4294967294,     (* max - 1 *)
    0w4294967295      (* max *)
  ]

  val word64_boundaries : Word64.word list = [
    0w0,                          (* min *)
    0w1,                          (* min + 1 *)
    0w9223372036854775807,        (* mid-1 (2^63 - 1) *)
    0w9223372036854775808,        (* mid (2^63) *)
    0w18446744073709551614,       (* max - 1 *)
    0w18446744073709551615        (* max *)
  ]

  (* Generate test values: all boundaries plus n random values *)
  fun word32_test_values seed n =
    let
      val (randoms, seed') = next_list seed n next_word32
    in (word32_boundaries @ randoms, seed') end

  fun word64_test_values seed n =
    let
      val (randoms, seed') = next_list seed n next_word64
    in (word64_boundaries @ randoms, seed') end
end
