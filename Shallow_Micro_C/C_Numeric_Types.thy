(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Numeric_Types
  imports
    C_Abort
    "Shallow_Micro_Rust.Numeric_Types"
    "Word_Lib.Signed_Words"
begin

section \<open>C Numeric Type Aliases\<close>

text \<open>
  We define type synonyms for C's standard integer types using Isabelle's
  fixed-width word types. Unsigned types use @{typ "'l word"}, signed types
  use @{typ "'l sword"} (from Word\_Lib).
\<close>

type_synonym c_char  = "8 word"
type_synonym c_schar = "8 sword"
type_synonym c_short = "16 sword"
type_synonym c_ushort = "16 word"
type_synonym c_int   = "32 sword"
type_synonym c_uint  = "32 word"
type_synonym c_long  = "64 sword"
type_synonym c_ulong = "64 word"

section \<open>C Signed Arithmetic with Overflow Detection\<close>

text \<open>
  In C, signed integer overflow is undefined behavior. We model this by
  aborting with @{const SignedOverflow} via @{const c_abort}. Unsigned
  arithmetic wraps as in standard word arithmetic.
\<close>

text \<open>
  Check whether a signed operation result fits in the representable range.
  For a signed \<open>'l sword\<close>, the representable range is
  \<open>[-2^(LENGTH('l) - 1), 2^(LENGTH('l) - 1) - 1]\<close> when interpreted
  as integers via @{const sint}.
\<close>

definition c_signed_add :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_add a b \<equiv>
     let result_int = sint a + sint b in
       if result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
         c_signed_overflow
       else
         literal (word_of_int result_int)\<close>

definition c_signed_sub :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_sub a b \<equiv>
     let result_int = sint a - sint b in
       if result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
         c_signed_overflow
       else
         literal (word_of_int result_int)\<close>

definition c_signed_mul :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_mul a b \<equiv>
     let result_int = sint a * sint b in
       if result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
         c_signed_overflow
       else
         literal (word_of_int result_int)\<close>

definition c_signed_div :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_div a b \<equiv>
     if b = 0 then c_abort DivisionByZero
     else let result_int = sint a div sint b in
       if result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
         c_signed_overflow
       else
         literal (word_of_int result_int)\<close>

definition c_signed_mod :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_mod a b \<equiv>
     if b = 0 then c_abort DivisionByZero
     else literal (word_of_int (sint a mod sint b))\<close>

section \<open>C Unsigned Arithmetic (Wrapping)\<close>

text \<open>
  Unsigned arithmetic in C wraps modulo \<open>2^LENGTH('l)\<close>, which is
  exactly the behavior of Isabelle's word arithmetic. Division by zero is
  still undefined behavior.
\<close>

definition c_unsigned_add :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_add a b \<equiv> literal (a + b)\<close>

definition c_unsigned_sub :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_sub a b \<equiv> literal (a - b)\<close>

definition c_unsigned_mul :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_mul a b \<equiv> literal (a * b)\<close>

definition c_unsigned_div :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_div a b \<equiv>
     if b = 0 then c_abort DivisionByZero
     else literal (a div b)\<close>

definition c_unsigned_mod :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_mod a b \<equiv>
     if b = 0 then c_abort DivisionByZero
     else literal (a mod b)\<close>

section \<open>C Bitwise Operations\<close>

text \<open>
  Bitwise AND, OR, XOR, and NOT have no undefined behavior in C —
  they operate on the bit representation for both signed and unsigned types.
\<close>

definition c_signed_and :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_and a b \<equiv> literal (a AND b)\<close>

definition c_signed_or :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_or a b \<equiv> literal (a OR b)\<close>

definition c_signed_xor :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_xor a b \<equiv> literal (a XOR b)\<close>

definition c_signed_not :: \<open>'l::{len} sword \<Rightarrow>
    ('s, 'l sword, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_not a \<equiv> literal (NOT a)\<close>

definition c_unsigned_and :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_and a b \<equiv> literal (a AND b)\<close>

definition c_unsigned_or :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_or a b \<equiv> literal (a OR b)\<close>

definition c_unsigned_xor :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_xor a b \<equiv> literal (a XOR b)\<close>

definition c_unsigned_not :: \<open>'l::{len} word \<Rightarrow>
    ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_not a \<equiv> literal (NOT a)\<close>

section \<open>C Shift Operations\<close>

text \<open>
  Shift operations have undefined behavior when the shift amount is
  greater than or equal to the bit width. Signed left shift additionally
  has UB for negative operands or when the result overflows.
  Signed right shift of a negative operand is implementation-defined
  in C11/C17; we conservatively abort.
\<close>

definition c_unsigned_shl :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_shl a b \<equiv>
     if unat b \<ge> LENGTH('l) then c_shift_out_of_range
     else literal (push_bit (unat b) a)\<close>

definition c_unsigned_shr :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_shr a b \<equiv>
     if unat b \<ge> LENGTH('l) then c_shift_out_of_range
     else literal (drop_bit (unat b) a)\<close>

definition c_signed_shl :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_shl a b \<equiv>
     if unat b \<ge> LENGTH('l) then c_shift_out_of_range
     else let result_int = sint a * 2 ^ unat b in
       if sint a < 0 \<or> result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
         c_signed_overflow
       else literal (word_of_int result_int)\<close>

definition c_signed_shr :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_shr a b \<equiv>
     if unat b \<ge> LENGTH('l) then c_shift_out_of_range
     else if sint a < 0 then c_signed_overflow
     else literal (word_of_int (sint a div 2 ^ unat b))\<close>

section \<open>C Unsigned Comparison Operations\<close>

definition c_unsigned_less :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_less a b \<equiv> literal (a < b)\<close>

definition c_unsigned_le :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_le a b \<equiv> literal (a \<le> b)\<close>

definition c_unsigned_eq :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_eq a b \<equiv> literal (a = b)\<close>

definition c_unsigned_neq :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_neq a b \<equiv> literal (a \<noteq> b)\<close>

section \<open>C Comparison Operations\<close>

definition c_signed_less :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_less a b \<equiv> literal (sint a < sint b)\<close>

definition c_signed_le :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_le a b \<equiv> literal (sint a \<le> sint b)\<close>

definition c_signed_eq :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_eq a b \<equiv> literal (a = b)\<close>

definition c_signed_neq :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_neq a b \<equiv> literal (a \<noteq> b)\<close>

section \<open>C Type Cast Operations\<close>

definition c_ucast :: \<open>'a::{len} word \<Rightarrow> ('s, 'b::{len} word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_ucast w \<equiv> literal (ucast w)\<close>

definition c_scast :: \<open>'a::{len} word \<Rightarrow> ('s, 'b::{len} word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_scast w \<equiv> literal (scast w)\<close>

end
