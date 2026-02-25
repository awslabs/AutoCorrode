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
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and c_mlk_poly_prism :: \<open>('gv, c_mlk_poly) prism\<close>
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_mlk_poly.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

subsection \<open>\<^verbatim>\<open>poly\_add\<close> translation\<close>

micro_c_translate \<open>
  typedef short int16_t;

  struct mlk_poly {
    int16_t coeffs[256];
  };

  void poly_add(struct mlk_poly *r, struct mlk_poly *b) {
    unsigned int i;

    for (i = 0; i < 256; i++) {
      r->coeffs[i] = (int16_t)((int16_t)(r->coeffs[i]) + b->coeffs[i]);
    }
  }

  void poly_sub(struct mlk_poly *r, struct mlk_poly *b) {
    unsigned int i;

    for (i = 0; i < 256; i++) {
      r->coeffs[i] = (int16_t)((int16_t)(r->coeffs[i]) - b->coeffs[i]);
    }
  }
\<close>

subsection \<open>\<^verbatim>\<open>poly\_add\<close> contract\<close>

text \<open>
  The contract is self-contained: refinement, well-formedness, and
  no-overflow are all expressed as pure assertions in the precondition.
  The postcondition asserts the result refines the abstract polynomial sum.
  No external assumptions needed on the specification theorem.
\<close>
definition c_poly_add_contract ::
    \<open>('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('s, 'a, 'b) function_contract\<close> where
  \<open>c_poly_add_contract r gr vr ar b gb vb ab \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb \<star> \<langle>refines_mlk_poly vb ab\<rangle> \<star>
               \<langle>no_overflow_add ar ab\<rangle>;
        post = \<lambda>_.
               can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star> \<langle>refines_mlk_poly vr' (poly_add_int ar ab)\<rangle>) \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
     in make_function_contract pre post\<close>
ucincl_auto c_poly_add_contract

lemma c_poly_add_spec:
  shows \<open>\<Gamma>; c_poly_add MLKEM_N r b \<Turnstile>\<^sub>F c_poly_add_contract r gr vr ar b gb vb ab\<close>
  apply (crush_boot f: c_poly_add_def contract: c_poly_add_contract_def)
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
    apply (fold refines_mlk_poly_def)
    apply (auto intro: no_overflow_add_bounds[simplified])
  done
done

subsection \<open>\<^verbatim>\<open>poly\\_sub\<close> contract\<close>

definition c_poly_sub_contract ::
    \<open>('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
     ('s, 'a, 'b) function_contract\<close> where
  \<open>c_poly_sub_contract r gr vr ar b gb vb ab \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb \<star> \<langle>refines_mlk_poly vb ab\<rangle> \<star>
               \<langle>no_overflow_sub ar ab\<rangle>;
        post = \<lambda>_.
               can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star> \<langle>refines_mlk_poly vr' (poly_sub_int ar ab)\<rangle>) \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
     in make_function_contract pre post\<close>
ucincl_auto c_poly_sub_contract

lemma c_poly_sub_spec:
  shows \<open>\<Gamma>; c_poly_sub MLKEM_N r b \<Turnstile>\<^sub>F c_poly_sub_contract r gr vr ar b gb vb ab\<close>
  apply (crush_boot f: c_poly_sub_def contract: c_poly_sub_contract_def)
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
    apply (fold refines_mlk_poly_def)
    by (auto intro: no_overflow_sub_bounds[simplified])
  done

end

end

