theory Mlkem_Native_Examples
  imports Simple_C_Functions C_While_Examples
begin

section \<open>Abstract polynomial arithmetic\<close>

text \<open>We model mlkem-native polynomials abstractly as fixed-size coefficient
  lists over the integers. This gives a clean mathematical specification
  independent of machine word sizes.\<close>

abbreviation MLKEM_N :: nat where
  \<open>MLKEM_N \<equiv> 256\<close>

type_synonym int_poly = \<open>int list\<close>

definition poly_add_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_add_int ps qs = map2 (+) ps qs\<close>

definition poly_sub_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_sub_int ps qs = map2 (-) ps qs\<close>

subsection \<open>Barrett reduction\<close>

abbreviation MLKEM_Q :: int where
  \<open>MLKEM_Q \<equiv> 3329\<close>

definition barrett_reduce_int :: \<open>int \<Rightarrow> int\<close> where
  \<open>barrett_reduce_int a = a - ((20159 * a + 2^25) div 2^26) * MLKEM_Q\<close>

lemma barrett_reduce_mod:
  shows \<open>barrett_reduce_int a mod MLKEM_Q = a mod MLKEM_Q\<close>
unfolding barrett_reduce_int_def by algebra

section \<open>Concrete types and refinement\<close>

datatype_record c_mlk_poly =
  c_mlk_poly_coeffs :: \<open>c_short list\<close>

text \<open>
  Refinement relation: a concrete @{typ c_mlk_poly} refines an abstract
  @{typ int_poly} when its coefficient list has the correct length and its
  signed interpretation matches the abstract polynomial.
\<close>
definition refines_mlk_poly :: \<open>c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> bool\<close> where
  \<open>refines_mlk_poly cp ap \<longleftrightarrow>
    length (c_mlk_poly_coeffs cp) = MLKEM_N \<and>
    List.map sint (c_mlk_poly_coeffs cp) = ap\<close>

text \<open>
  No-overflow condition: the mathematical sum of each coefficient pair
  fits in a signed 16-bit integer. This is required both for the C code
  to not abort (since @{const c_signed_add} checks for overflow) and for
  the refinement to integer arithmetic to hold.
\<close>
definition no_overflow_add :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> bool\<close> where
  \<open>no_overflow_add ps qs \<longleftrightarrow>
    (\<forall>i < min (length ps) (length qs).
      ps ! i + qs ! i \<in> {-(2^15) ..< 2^15})\<close>

definition no_overflow_sub :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> bool\<close> where
  \<open>no_overflow_sub ps qs \<longleftrightarrow>
    (\<forall>i < min (length ps) (length qs).
      ps ! i - qs ! i \<in> {-(2^15) ..< 2^15})\<close>

text \<open>
  The concrete (word-level) result of polynomial addition — internal helper
  for proofs.
\<close>
definition poly_add_c :: \<open>c_mlk_poly \<Rightarrow> c_mlk_poly \<Rightarrow> c_mlk_poly\<close> where
  \<open>poly_add_c p q = update_c_mlk_poly_coeffs
    (\<lambda>_. map2 (+) (c_mlk_poly_coeffs p) (c_mlk_poly_coeffs q)) p\<close>

subsection \<open>Refinement lemmas\<close>

lemma sint_plus_no_overflow:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>sint a + sint b \<in> {-(2^(LENGTH('l) - 1)) ..< 2^(LENGTH('l) - 1)}\<close>
    shows \<open>sint (a + b) = sint a + sint b\<close>
using assms by (intro signed_arith_sint) (auto simp: word_size)

lemma sint_minus_no_overflow:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>sint a - sint b \<in> {-(2^(LENGTH('l) - 1)) ..< 2^(LENGTH('l) - 1)}\<close>
    shows \<open>sint (a - b) = sint a - sint b\<close>
using assms by (intro signed_arith_sint) (auto simp: word_size)

text \<open>
  The key refinement theorem: under the no-overflow condition, the concrete
  word-level addition produces a result that refines the abstract integer sum.
\<close>
lemma poly_add_c_refines:
  assumes \<open>refines_mlk_poly p ap\<close>
      and \<open>refines_mlk_poly q aq\<close>
      and \<open>no_overflow_add ap aq\<close>
    shows \<open>refines_mlk_poly (poly_add_c p q) (poly_add_int ap aq)\<close>
using assms by (auto simp add: c_mlk_poly.record_simps map2_map_map word_size refines_mlk_poly_def
  poly_add_c_def poly_add_int_def no_overflow_add_def intro!: nth_equalityI sint_plus_no_overflow)

subsection \<open>Auxiliary Lemmas\<close>

lemma nth_map2:
  assumes \<open>i < length xs\<close>
      and \<open>i < length ys\<close>
    shows \<open>map2 f xs ys ! i = f (xs ! i) (ys ! i)\<close>
using assms by (induction xs arbitrary: i ys) (auto simp: less_Suc_eq_0_disj split: list.splits)

lemma inv_list_step:
  assumes \<open>n < length xs\<close>
      and \<open>n < length ys\<close>
      and \<open>length xs = length ys\<close>
    shows \<open>(take n (map2 f xs ys) @ drop n xs)[n := f (xs ! n) (ys ! n)] =
              take (Suc n) (map2 f xs ys) @ drop (Suc n) xs\<close>
proof -
  let ?zs = \<open>map2 f xs ys\<close>
  from assms have ln: \<open>n < length ?zs\<close>
    by simp
  from assms have zn: \<open>?zs ! n = f (xs ! n) (ys ! n)\<close>
    by (simp add: nth_map2)
  from assms have drop_eq: \<open>drop n xs = xs ! n # drop (Suc n) xs\<close>
    by (metis Cons_nth_drop_Suc)
  have \<open>(take n ?zs @ drop n xs)[n := ?zs ! n] = take n ?zs @ (drop n xs)[0 := ?zs ! n]\<close>
    using ln by (simp add: list_update_append)
  also have \<open>\<dots> = take n ?zs @ ?zs ! n # drop (Suc n) xs\<close>
    using drop_eq by simp
  also have \<open>\<dots> = take (Suc n) ?zs @ drop (Suc n) xs\<close>
    using ln by (simp add: take_Suc_conv_app_nth)
  finally show ?thesis
    using zn by simp
qed

lemma no_overflow_add_bounds:
  assumes \<open>refines_mlk_poly vr ar\<close>
      and \<open>refines_mlk_poly vb ab\<close>
      and \<open>no_overflow_add ar ab\<close> \<open>i < MLKEM_N\<close>
    shows \<open>sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
      and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i)\<close>
proof -
  from assms(1) have lr: \<open>length (c_mlk_poly_coeffs vr) = MLKEM_N\<close>
          and mr: \<open>List.map sint (c_mlk_poly_coeffs vr) = ar\<close>
    unfolding refines_mlk_poly_def by auto
  from assms(2) have lb: \<open>length (c_mlk_poly_coeffs vb) = MLKEM_N\<close>
          and mb: \<open>List.map sint (c_mlk_poly_coeffs vb) = ab\<close>
    unfolding refines_mlk_poly_def by auto
  have \<open>ar ! i + ab ! i \<in> {-(2^15) ..< 2^15}\<close>
    using assms(3,4) lr lb mr mb unfolding no_overflow_add_def by auto
  moreover have \<open>ar ! i = sint (c_mlk_poly_coeffs vr ! i)\<close>
    using mr lr assms(4) by (simp add: nth_map[symmetric])
  moreover have \<open>ab ! i = sint (c_mlk_poly_coeffs vb ! i)\<close>
    using mb lb assms(4) by (simp add: nth_map[symmetric])
  ultimately show \<open>sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
          and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i)\<close>
    by auto
qed

lemma no_overflow_sub_bounds:
  assumes \<open>refines_mlk_poly vr ar\<close>
      and \<open>refines_mlk_poly vb ab\<close>
      and \<open>no_overflow_sub ar ab\<close> \<open>i < MLKEM_N\<close>
    shows \<open>sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
      and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i)\<close>
proof -
  from assms(1) have lr: \<open>length (c_mlk_poly_coeffs vr) = MLKEM_N\<close>
          and mr: \<open>List.map sint (c_mlk_poly_coeffs vr) = ar\<close>
    unfolding refines_mlk_poly_def by auto
  from assms(2) have lb: \<open>length (c_mlk_poly_coeffs vb) = MLKEM_N\<close>
          and mb: \<open>List.map sint (c_mlk_poly_coeffs vb) = ab\<close>
    unfolding refines_mlk_poly_def by auto
  have \<open>ar ! i - ab ! i \<in> {-(2^15) ..< 2^15}\<close>
    using assms(3,4) lr lb mr mb unfolding no_overflow_sub_def by auto
  moreover have \<open>ar ! i = sint (c_mlk_poly_coeffs vr ! i)\<close>
    using mr lr assms(4) by (simp add: nth_map[symmetric])
  moreover have \<open>ab ! i = sint (c_mlk_poly_coeffs vb ! i)\<close>
    using mb lb assms(4) by (simp add: nth_map[symmetric])
  ultimately show \<open>sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
          and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i)\<close>
    by auto
qed

lemma MLKEM_N_sub_step [simp]:
  assumes \<open>k < MLKEM_N\<close>
    shows \<open> MLKEM_N - k = Suc (255 - k)\<close>
using assms by simp

section \<open>C verification\<close>

locale c_mlk_poly_verification_ctx =
    reference reference_types +
    ref_c_mlk_poly: reference_allocatable reference_types _ _ _ _ _ _ _ c_mlk_poly_prism +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_short: reference_allocatable reference_types _ _ _ _ _ _ _ c_short_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and c_mlk_poly_prism :: \<open>('gv, c_mlk_poly) prism\<close>
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
  and c_short_prism :: \<open>('gv, c_short) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_mlk_poly.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_short.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text \<open>The C code below is taken verbatim from mlkem-native
  (\url{https://github.com/pq-code-package/mlkem-native}), with only the
  following unavoidable adaptations for our C front-end:
  \begin{itemize}
    \item @{verbatim "typedef"} declarations replace @{verbatim "#include <stdint.h>"}
    \item @{verbatim "MLKEM_N"} / @{verbatim "MLKEM_Q"} are inlined (no preprocessor)
    \item CBMC annotations (@{verbatim "__contract__"}, @{verbatim "__loop__"},
          @{verbatim "mlk_assert_abs_bound"}) and @{verbatim "MLK_INTERNAL_API"} /
          @{verbatim "static MLK_INLINE"} qualifiers are omitted
  \end{itemize}\<close>

subsection \<open>Translation\<close>

micro_c_translate \<open>
typedef short int16_t;
typedef int int32_t;

typedef struct {
  int16_t coeffs[256];
} mlk_poly;

/* Reference: `poly_add()` in the reference implementation @[REF].
 *            - We use destructive version (output=first input) to avoid
 *              reasoning about aliasing in the CBMC specification */
void mlk_poly_add(mlk_poly *r, const mlk_poly *b)
{
  unsigned i;
  for (i = 0; i < 256; i++)
  {
    /* The preconditions imply that the addition stays within int16_t. */
    r->coeffs[i] = (int16_t)(r->coeffs[i] + b->coeffs[i]);
  }
}

/* Reference: `poly_sub()` in the reference implementation @[REF].
 *            - We use destructive version (output=first input) to avoid
 *              reasoning about aliasing in the CBMC specification */
void mlk_poly_sub(mlk_poly *r, const mlk_poly *b)
{
  unsigned i;
  for (i = 0; i < 256; i++)
  {
    /* The preconditions imply that the subtraction stays within int16_t. */
    r->coeffs[i] = (int16_t)(r->coeffs[i] - b->coeffs[i]);
  }
}

/* Reference: `barrett_reduce()` in the reference implementation @[REF]. */
int16_t mlk_barrett_reduce(int16_t a)
{
  /* Barrett reduction approximates
   *     round(a/MLKEM_Q)
   *   = round(a*(2^N/MLKEM_Q))/2^N)
   *  ~= round(a*round(2^N/MLKEM_Q)/2^N)
   * Here, we pick N=26.
   */
  const int32_t magic = 20159; /* check-magic: 20159 == round(2^26 / MLKEM_Q) */

  /*
   * PORTABILITY: Right-shift on a signed integer is
   * implementation-defined for negative left argument.
   * Here, we assume it's sign-preserving "arithmetic" shift right.
   * See (C99 6.5.7 (5))
   */
  const int32_t t = (magic * a + ((int32_t)1 << 25)) >> 26;

  /*
   * t is in -10 .. +10, so we need 32-bit math to
   * evaluate t * MLKEM_Q and the subsequent subtraction
   */
  int16_t res = (int16_t)(a - t * 3329);

  return res;
}
\<close>

subsection \<open>\<^verbatim>\<open>mlk\_barrett\_reduce\<close> contract\<close>

definition c_mlk_barrett_reduce_contract ::
    \<open>c_short \<Rightarrow> ('s::{sepalg}, c_short, 'b) function_contract\<close> where
  \<open>c_mlk_barrett_reduce_contract a \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>True\<rangle>;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>sint r mod MLKEM_Q = sint a mod MLKEM_Q\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_barrett_reduce_contract

lemma barrett_sint_bounds:
    fixes a :: \<open>16 sword\<close>
  defines \<open>sa \<equiv> sint a\<close>
    shows \<open>sa \<ge> -32768\<close> \<open>sa < 32768\<close>
      and \<open>20159 * sa \<ge> -(2^31)\<close> \<open>20159 * sa < 2^31\<close>
      and \<open>20159 * sa + 2^25 \<ge> -(2^31)\<close> \<open>20159 * sa + 2^25 < 2^31\<close>
proof -
  have \<open>sa \<ge> -32768\<close> and \<open>sa < 32768\<close>
    using sint_range_size[where w=a] by (auto simp: sa_def word_size)
  then show \<open>sa \<ge> -32768\<close> and \<open>sa < 32768\<close> and
        \<open>20159 * sa \<ge> -(2^31)\<close> \<open>20159 * sa < 2^31\<close> and
        \<open>20159 * sa + 2^25 \<ge> -(2^31)\<close> \<open>20159 * sa + 2^25 < 2^31\<close>
    by auto
qed

lemma barrett_stb31_prod:
  shows \<open>signed_take_bit 31 (20159 * sint (a :: 16 sword)) = 20159 * sint a\<close>
using barrett_sint_bounds[of a] by (intro signed_take_bit_int_eq_self) auto

lemma barrett_stb31_sum:
  shows \<open>signed_take_bit 31 (20159 * sint (a :: 16 sword) + 33554432) =
          20159 * sint a + 33554432\<close>
using barrett_sint_bounds[of a] by (intro signed_take_bit_int_eq_self) auto

lemma barrett_quotient_bounds:
    fixes a :: \<open>16 sword\<close>
  defines \<open>t \<equiv> (20159 * sint a + 33554432) div (67108864 :: int)\<close>
    shows \<open>t \<ge> -10\<close>
      and \<open>t \<le> 10\<close>
proof -
  have sa: \<open>sint a \<ge> -32768\<close> \<open>sint a < 32768\<close>
    using barrett_sint_bounds[of a] by auto
  have m1: \<open>(20159::int) * (-32768) \<le> 20159 * sint a\<close>
    using sa by (intro mult_left_mono) auto
  have m2: \<open>(20159::int) * sint a \<le> 20159 * 32767\<close>
    using sa by (intro mult_left_mono) auto
  have lower: \<open>(-627015680::int) \<le> 20159 * sint a + 33554432\<close>
    using m1 by simp
  have upper: \<open>20159 * sint a + 33554432 \<le> (694104385::int)\<close>
    using m2 by simp
  have \<open>(-627015680::int) div 67108864 \<le> (20159 * sint a + 33554432) div 67108864\<close>
    using lower by (rule zdiv_mono1) auto
  thus \<open>t \<ge> -10\<close> unfolding t_def by simp
  have \<open>(20159 * sint a + 33554432) div 67108864 \<le> (694104385::int) div 67108864\<close>
    using upper by (rule zdiv_mono1) auto
  thus \<open>t \<le> 10\<close> unfolding t_def by simp
qed

lemma barrett_sint_woi:
  shows \<open>sint ((word_of_int ((20159 * sint (a::16 sword) + 33554432) div 67108864)) :: 32 sword) =
          (20159 * sint a + 33554432) div 67108864\<close>
proof -
  have t: \<open>(20159 * sint a + 33554432) div 67108864 \<ge> -10\<close>
          \<open>(20159 * sint a + 33554432) div 67108864 \<le> 10\<close>
    using barrett_quotient_bounds[of a] by auto
  show ?thesis by (rule sint_of_int_eq) (use t in auto)
qed

lemma barrett_stb31_tq:
  shows \<open>signed_take_bit 31 ((20159 * sint (a::16 sword) + 33554432) div 67108864 * 3329) =
          (20159 * sint a + 33554432) div 67108864 * 3329\<close>
proof -
  have \<open>(20159 * sint a + 33554432) div 67108864 \<ge> -10\<close> and \<open>(20159 * sint a + 33554432) div 67108864 \<le> 10\<close>
    using barrett_quotient_bounds[of a] by auto
  moreover from this have \<open>(3329::int) * (-10) \<le> 3329 * ((20159 * sint a + 33554432) div 67108864)\<close>
    by (intro mult_left_mono) auto
  moreover from calculation have \<open>(3329::int) * ((20159 * sint a + 33554432) div 67108864) \<le> 3329 * 10\<close>
    by (intro mult_left_mono) auto
  ultimately show ?thesis
    by (intro signed_take_bit_int_eq_self) (simp_all add: algebra_simps)
qed

lemma barrett_result_bounds:
    fixes a :: \<open>16 sword\<close>
  defines \<open>sa \<equiv> sint a\<close>
  defines \<open>t \<equiv> (20159 * sa + 33554432) div (67108864 :: int)\<close>
    shows \<open>-1664 \<le> sa - t * 3329\<close>
      and \<open>sa - t * 3329 \<le> 1664\<close>
proof -
  define r where
    \<open>r = (20159 * sa + 33554432) mod (67108864 :: int)\<close>
  have sa: \<open>sa \<ge> -32768\<close> \<open>sa < 32768\<close>
    using barrett_sint_bounds[of a] by (auto simp: sa_def)
  have r_ge: \<open>r \<ge> 0\<close>
    unfolding r_def by (intro pos_mod_sign) auto
  have r_lt: \<open>r < 67108864\<close>
    unfolding r_def by (intro pos_mod_bound) auto
  have t_r_eq: \<open>t * 67108864 + r = 20159 * sa + 33554432\<close>
    unfolding t_def r_def using div_mult_mod_eq[of \<open>20159 * sa + 33554432\<close> 67108864]
    by (simp add: algebra_simps)
  \<comment> \<open>Key: 67108864 * (sa - t * 3329) = 3329 * r - 447 * sa - 111702704128
     using 20159 * 3329 = 67108864 + 447\<close>
  have key: \<open>67108864 * (sa - t * 3329) = 3329 * r - 447 * sa - 111702704128\<close>
  proof -
    from t_r_eq have \<open>3329 * (t * 67108864 + r) = 3329 * (20159 * sa + 33554432)\<close>
      by auto
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  show \<open>-1664 \<le> sa - t * 3329\<close>
  proof (rule ccontr)
    assume \<open>\<not> (-1664 \<le> sa - t * 3329)\<close>
    hence \<open>sa - t * 3329 \<le> -1665\<close>
      by auto
    hence \<open>67108864 * (sa - t * 3329) \<le> 67108864 * (-1665)\<close>
      by (intro mult_left_mono) auto
    moreover have \<open>3329 * r - 447 * sa - 111702704128 \<ge> 0 - 447 * 32767 - 111702704128\<close>
      using r_ge sa by (intro diff_mono diff_mono) auto
    ultimately show False
      using key by simp
  qed
  show \<open>sa - t * 3329 \<le> 1664\<close>
  proof (rule ccontr)
    assume \<open>\<not> (sa - t * 3329 \<le> 1664)\<close>
    hence \<open>sa - t * 3329 \<ge> 1665\<close>
      by auto
    hence \<open>67108864 * (sa - t * 3329) \<ge> 67108864 * 1665\<close>
      by (intro mult_left_mono) auto
    moreover have \<open>3329 * r - 447 * sa - 111702704128 \<le> 3329 * 67108863 + 447 * 32768 - 111702704128\<close>
      using r_lt sa by linarith
    ultimately show False
      using key by simp
  qed
qed

lemma barrett_result_sint:
    fixes a :: \<open>16 sword\<close>
  defines \<open>t \<equiv> (20159 * sint a + 33554432) div (67108864 :: int)\<close>
    shows \<open>sint (SCAST(32 signed \<rightarrow> 16 signed)
            (SCAST(16 signed \<rightarrow> 32 signed) a -
             word_of_int t * (0xD01 :: 32 sword)))
           = sint a - t * 3329\<close>
proof -
  have res: \<open>-1664 \<le> sint a - t * 3329\<close> \<open>sint a - t * 3329 \<le> 1664\<close>
    using barrett_result_bounds[of a] by (auto simp: t_def)
  \<comment> \<open>sint of the multiplication\<close>
  have mult_sint: \<open>sint (word_of_int t * (0xD01 :: 32 sword)) = t * 3329\<close>
  proof -
    have \<open>sint (word_of_int t :: 32 sword) = t\<close>
      using barrett_sint_woi[of a] by (simp add: t_def)
    moreover have \<open>sint (0xD01 :: 32 sword) = (3329 :: int)\<close>
      by simp
    moreover have \<open>signed_take_bit 31 (t * 3329) = t * 3329\<close>
      using barrett_stb31_tq[of a] by (simp add: t_def)
    ultimately show ?thesis
      by (simp add: sint_word_mult word_size)
  qed
  \<comment> \<open>sint of the subtraction\<close>
  have sub_sint: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a - word_of_int t * 0xD01) = sint a - t * 3329\<close>
  proof -
    have up: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
      by (simp add: sint_up_scast is_up)
    have \<open>signed_take_bit 31 (sint a - t * 3329) = sint a - t * 3329\<close>
      using res by (intro signed_take_bit_int_eq_self) auto
    thus ?thesis
      by (simp add: sint_word_diff word_size up mult_sint)
  qed
  \<comment> \<open>sint of the downcast\<close>
  have scast_sint: \<open>sint (SCAST(32 signed \<rightarrow> 16 signed) w) = signed_take_bit 15 (sint w)\<close> for w :: \<open>32 sword\<close>
    by (simp only: of_int_sint_scast[symmetric] Word.sint_sbintrunc') simp
  have \<open>signed_take_bit 15 (sint a - t * 3329) = sint a - t * 3329\<close>
    using res by (intro signed_take_bit_int_eq_self) auto
  thus ?thesis
    by (simp add: scast_sint sub_sint)
qed

lemma c_mlk_barrett_reduce_spec:
  shows \<open>\<Gamma>; c_mlk_barrett_reduce a \<Turnstile>\<^sub>F c_mlk_barrett_reduce_contract a\<close>
  apply (crush_boot f: c_mlk_barrett_reduce_def contract: c_mlk_barrett_reduce_contract_def)
  apply crush_base
  apply (simp_all add: sint_up_scast is_up sint_word_ariths
            barrett_stb31_prod barrett_stb31_sum
            signed_take_bit_int_eq_self barrett_sint_bounds)
  apply (simp_all add: barrett_sint_woi barrett_stb31_tq)
  apply (all \<open>(insert barrett_result_bounds[of a] barrett_quotient_bounds[of a]
               barrett_sint_bounds[of a]; linarith)?\<close>)
  apply (simp add: barrett_result_sint mod_diff_right_eq[symmetric])
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_add\<close> contract\<close>

text \<open>
  The contract is self-contained: refinement, well-formedness, and
  no-overflow are all expressed as pure assertions in the precondition.
  The postcondition asserts the result refines the abstract polynomial sum.
  No external assumptions needed on the specification theorem.
\<close>
definition c_mlk_poly_add_contract ::
    \<open>('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('s, 'a, 'b) function_contract\<close> where
  \<open>c_mlk_poly_add_contract r gr vr ar b gb vb ab \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb \<star> \<langle>refines_mlk_poly vb ab\<rangle> \<star>
               \<langle>no_overflow_add ar ab\<rangle>;
        post = \<lambda>_.
               can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star> \<langle>refines_mlk_poly vr' (poly_add_int ar ab)\<rangle>) \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_add_contract

lemma c_mlk_poly_add_spec:
  shows \<open>\<Gamma>; c_mlk_poly_add MLKEM_N r b \<Turnstile>\<^sub>F c_mlk_poly_add_contract r gr vr ar b gb vb ab\<close>
  apply (crush_boot f: c_mlk_poly_add_def contract: c_mlk_poly_add_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - k) (map2 (+) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_add ar ab\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - Suc k) (map2 (+) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - Suc k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_add ar ab\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  subgoal \<comment> \<open>Initialization + frame\<close>
    apply crush_base
    apply (auto simp: refines_mlk_poly_def c_mlk_poly.record_simps
                   poly_add_int_def no_overflow_add_def
                   map2_map_map word_size
             intro!: nth_equalityI sint_plus_no_overflow)
    done
  subgoal \<comment> \<open>Condition\<close>
    apply crush_base
    apply (simp_all add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat)
    done
  subgoal \<comment> \<open>Loop body\<close>
    apply crush_base
    apply (simp_all add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
                         c_mlk_poly.record_simps nth_append
                         refines_mlk_poly_def inv_list_step)
  done
done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_sub\<close> contract\<close>

definition c_mlk_poly_sub_contract ::
    \<open>('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('s, 'a, 'b) function_contract\<close> where
  \<open>c_mlk_poly_sub_contract r gr vr ar b gb vb ab \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb \<star> \<langle>refines_mlk_poly vb ab\<rangle> \<star>
               \<langle>no_overflow_sub ar ab\<rangle>;
        post = \<lambda>_.
               can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star> \<langle>refines_mlk_poly vr' (poly_sub_int ar ab)\<rangle>) \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_sub_contract

lemma c_mlk_poly_sub_spec:
  shows \<open>\<Gamma>; c_mlk_poly_sub MLKEM_N r b \<Turnstile>\<^sub>F c_mlk_poly_sub_contract r gr vr ar b gb vb ab\<close>
  apply (crush_boot f: c_mlk_poly_sub_def contract: c_mlk_poly_sub_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - k) (map2 (-) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_sub ar ab\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - Suc k) (map2 (-) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - Suc k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_sub ar ab\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  subgoal \<comment> \<open>Initialization + frame\<close>
    apply crush_base
    apply (auto simp: refines_mlk_poly_def c_mlk_poly.record_simps
                   poly_sub_int_def no_overflow_sub_def
                   map2_map_map word_size
             intro!: nth_equalityI sint_minus_no_overflow)
    done
  subgoal \<comment> \<open>Condition\<close>
    apply crush_base
    apply (simp_all add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat)
    done
  subgoal \<comment> \<open>Loop body\<close>
    apply crush_base
    apply (simp_all add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
                         c_mlk_poly.record_simps nth_append
                         refines_mlk_poly_def inv_list_step)
  done
done

end

end

