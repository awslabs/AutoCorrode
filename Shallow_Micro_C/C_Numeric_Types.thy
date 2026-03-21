theory C_Numeric_Types
  imports
    C_Abort
    "Shallow_Micro_Rust.Numeric_Types"
    "Word_Lib.Signed_Words"
begin

section \<open>C numeric type aliases\<close>

text \<open>
  We define type synonyms for C's standard integer types using Isabelle's
  fixed-width word types. Unsigned types use @{typ "'l word"}, signed types
  use @{typ "'l sword"} (from Word\_Lib).
\<close>

text \<open>
  These type synonyms are fixed-width and do not vary with ABI.
  ABI-dependent sizing (e.g.\ @{text long} being 32-bit on ILP32
  vs 64-bit on LP64) is handled by @{text hol_type_of} in
  @{text C_Ast_Utilities}, which maps @{text CLong} to
  @{text c_int} or @{text c_long} depending on the ABI profile.
  The @{text sizeof} correctness in translated code follows from
  this indirection: the Isabelle type always matches the ABI's
  bit width for the C type.
\<close>
type_synonym c_char  = \<open>8 word\<close>
type_synonym c_schar = \<open>8 sword\<close>
type_synonym c_short = \<open>16 sword\<close>
type_synonym c_ushort = \<open>16 word\<close>
type_synonym c_int   = \<open>32 sword\<close>
type_synonym c_uint  = \<open>32 word\<close>
type_synonym c_long  = \<open>64 sword\<close>
type_synonym c_ulong = \<open>64 word\<close>
type_synonym c_int128  = \<open>128 sword\<close>
type_synonym c_uint128 = \<open>128 word\<close>

section \<open>C signed arithmetic with overflow detection\<close>

text \<open>
  C11 \<section>6.5p5: if an exceptional condition occurs during the evaluation
  of an expression (that is, if the result is not mathematically defined or
  not in the range of representable values for its type), the behavior is
  undefined.  We model signed integer overflow by aborting with
  @{const SignedOverflow} via @{const c_abort}.

  C11 \<section>6.2.5p9: unsigned arithmetic wraps modulo \<open>2\<^sup>N\<close>, which is
  exactly the behavior of Isabelle's word arithmetic.
\<close>

text \<open>
  Check whether a signed operation result fits in the representable range.
  For a signed \<open>'l sword\<close>, the representable range is
  \<open>[-2^(LENGTH('l) - 1), 2^(LENGTH('l) - 1) - 1]\<close> when interpreted
  as integers via @{const sint}.
\<close>

text \<open>
  C11 \<section>6.5.5p6: when integers are divided, the result of the @{text "/"}
  operator is the algebraic quotient with any fractional part discarded
  (truncation toward zero).  Isabelle/HOL \<open>div\<close> on @{typ int} is
  Euclidean (flooring), so we define helper operations with C semantics
  and use those in signed @{text "/"} and @{text "%"}.
\<close>

definition c_trunc_div_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>c_trunc_div_int a b \<equiv>
     if b = 0 then 0
     else
       let q = abs a div abs b
       in if (a < 0) = (b < 0) then q else - q\<close>

definition c_trunc_mod_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>c_trunc_mod_int a b \<equiv> a - c_trunc_div_int a b * b\<close>

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

text \<open>
  Signed division and modulo hardcode @{typ c_abort} because they must
  construct @{const DivisionByZero}, a @{typ c_abort} value.  This means
  they cannot be used in locales whose @{typ "'abort"} parameter differs
  from @{typ c_abort} --- see also @{text c_unsigned_div} below.
\<close>

definition c_signed_div :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_div a b \<equiv>
     if b = 0 then
       c_abort DivisionByZero
     else
       let result_int = c_trunc_div_int (sint a) (sint b) in
         if result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
           c_signed_overflow
         else
           literal (word_of_int result_int)\<close>

text \<open>
  @{text "c_signed_mod"} checks the \emph{quotient} for overflow, not the remainder itself.
  Per C11 6.5.5p6, if \<open>a/b\<close> is not representable, both \<open>a/b\<close> and \<open>a%b\<close> are undefined.
  The canonical case is @{text "INT_MIN % (-1)"}: the remainder is 0, but
  @{text "INT_MIN / (-1)"} overflows, so the operation is UB.
\<close>

definition c_signed_mod :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_mod a b \<equiv>
     if b = 0 then
       c_abort DivisionByZero
     else
       let q_int = c_trunc_div_int (sint a) (sint b);
           result_int = c_trunc_mod_int (sint a) (sint b)
       in if q_int < -(2^(LENGTH('l) - 1)) \<or> q_int \<ge> 2^(LENGTH('l) - 1) then
            c_signed_overflow
          else
            literal (word_of_int result_int)\<close>

section \<open>C unsigned arithmetic (wrapping)\<close>

text \<open>
  C11 \<section>6.2.5p9: unsigned arithmetic wraps modulo \<open>2^LENGTH('l)\<close>,
  which is exactly the behavior of Isabelle's word arithmetic.
  C11 \<section>6.5.5p5: division by zero is undefined behavior.
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

text \<open>
  Like the signed variants, unsigned division and modulo hardcode
  @{typ c_abort} to construct @{const DivisionByZero}.  Unlike
  @{const c_unsigned_add}/@{const c_unsigned_sub}/@{const c_unsigned_mul}
  which are polymorphic in @{typ "'abort"}, these two fix it to
  @{typ c_abort}.  Consequence: in a locale whose abort type parameter
  differs from @{typ c_abort}, using division or modulo causes a type
  unification error.  Avoid division in examples that also require
  locale-specific abort types (e.g.\ pointer operations).
\<close>

definition c_unsigned_div :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_div a b \<equiv>
     if b = 0 then
       c_abort DivisionByZero
     else
       literal (a div b)\<close>

definition c_unsigned_mod :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_mod a b \<equiv>
     if b = 0 then
       c_abort DivisionByZero
     else
       literal (a mod b)\<close>

section \<open>C bitwise operations\<close>

text \<open>
  C11 \<section>6.5.10--12 (bitwise AND/XOR/OR): these operators have no
  undefined behavior --- they operate on the bit representation for both
  signed and unsigned types.  C11 \<section>6.5.3.3p4 (bitwise NOT, @{text "~"}):
  integer promotions are performed, then the result is the bitwise complement.
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

section \<open>C shift operations\<close>

text \<open>
  C11 \<section>6.5.7p3: if the shift count is negative or \<open>\<ge>\<close> the bit width
  of the promoted left operand, the behavior is undefined.
  C11 \<section>6.5.7p4: for signed left shift, if the left operand is negative
  or the result would overflow, the behavior is undefined.
  C11 \<section>6.5.7p5: for signed right shift of a negative operand, the result
  is implementation-defined (arithmetic vs logical shift).
\<close>

definition c_unsigned_shl :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_shl a b \<equiv>
     if unat b \<ge> LENGTH('l) then
       c_shift_out_of_range
     else
       literal (push_bit (unat b) a)\<close>

definition c_unsigned_shr :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('s, 'l word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_shr a b \<equiv>
     if unat b \<ge> LENGTH('l) then
       c_shift_out_of_range
     else
       literal (drop_bit (unat b) a)\<close>

definition c_signed_shl :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_shl a b \<equiv>
     if unat b \<ge> LENGTH('l) then
       c_shift_out_of_range
     else
       let result_int = sint a * 2 ^ unat b in
         if sint a < 0 \<or> result_int < -(2^(LENGTH('l) - 1)) \<or> result_int \<ge> 2^(LENGTH('l) - 1) then
           c_signed_overflow
         else
           literal (word_of_int result_int)\<close>

text \<open>Arithmetic right shift: implementation-defined in C11 but universally
  implemented as sign-extending shift (floor division by 2\^n). We match
  GCC/Clang behavior rather than aborting on negative operands.\<close>

definition c_signed_shr :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_shr a b \<equiv>
     if unat b \<ge> LENGTH('l) then
       c_shift_out_of_range
     else
       literal (word_of_int (sint a div 2 ^ unat b))\<close>

text \<open>Conservative right shift: aborts on negative operands instead of relying
  on implementation-defined arithmetic shift. Used by the @{text "conservative"}
  compiler profile where no specific compiler behavior is assumed.\<close>

definition c_signed_shr_conservative :: \<open>'l::{len} sword \<Rightarrow> 'l sword \<Rightarrow>
    ('s, 'l sword, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_shr_conservative a b \<equiv>
     if unat b \<ge> LENGTH('l) then
       c_shift_out_of_range
     else if sint a < 0 then
       c_signed_overflow
     else
       literal (word_of_int (sint a div 2 ^ unat b))\<close>

text \<open>
  C11 \<section>6.5.8--9: relational and equality operators compare values after
  the usual arithmetic conversions.  The result type is @{typ int} (we use
  @{typ bool} internally and convert at the translation layer).
\<close>

section \<open>C unsigned comparison operations\<close>

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

section \<open>C comparison operations\<close>

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

section \<open>C truthiness conversion\<close>

text \<open>
  C11 \<section>6.3.1.2: when any scalar value is converted to @{text "_Bool"},
  the result is 0 if the value compares equal to 0; otherwise the result is 1.
  These helpers model the implicit conversion used by conditionals (\<section>6.5.15)
  and logical operators (\<section>6.5.13--14).
\<close>

definition c_signed_truthy :: \<open>'l::{len} sword \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_signed_truthy a \<equiv> literal (a \<noteq> 0)\<close>

definition c_unsigned_truthy :: \<open>'l::{len} word \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_unsigned_truthy a \<equiv> literal (a \<noteq> 0)\<close>

section \<open>C type cast operations\<close>

text \<open>
  C11 \<section>6.3.1.3 (signed and unsigned integer conversions):
  \<^item> Conversion to unsigned: value is reduced modulo \<open>2\<^sup>N\<close> (\<section>6.3.1.3p2).
  \<^item> Conversion to signed where the value cannot be represented: the result
    is implementation-defined or an implementation-defined signal is raised
    (\<section>6.3.1.3p3).  We model this with @{text c_scast} (truncating, matching
    GCC/Clang) and @{text c_scast_checked} (aborting, for the conservative profile).
\<close>

definition c_ucast :: \<open>'a::{len} word \<Rightarrow> ('s, 'b::{len} word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_ucast w \<equiv> literal (ucast w)\<close>

definition c_scast :: \<open>'a::{len} word \<Rightarrow> ('s, 'b::{len} word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>c_scast w \<equiv> literal (scast w)\<close>

text \<open>Checked signed narrowing cast: aborts with @{text "SignedOverflow"} when
  @{text "sint w"} does not fit in the target type's signed range. Used by the
  @{text "conservative"} compiler profile where implementation-defined narrowing
  truncation is not assumed.\<close>

definition c_scast_checked :: \<open>'a::{len} word \<Rightarrow> ('s, 'b::{len} word, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_scast_checked w \<equiv>
     let v = sint w
     in if v < -(2^(LENGTH('b) - 1)) \<or> v \<ge> 2^(LENGTH('b) - 1) then
       c_signed_overflow
     else
       literal (word_of_int v)\<close>

end
