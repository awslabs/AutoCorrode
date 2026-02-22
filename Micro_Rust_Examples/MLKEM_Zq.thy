(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory MLKEM_Zq
  imports
    MLKEM_Specification
    Micro_Rust_Std_Lib.StdLib_All
    Crush.Crush
begin

text\<open>
  \<mu>Rust implementations of Z\_q arithmetic operations with contracts proving refinement
  against the pure specifications from @{theory Micro_Rust_Examples.MLKEM_Specification}.
\<close>

section\<open>Locale\<close>

locale mlkem_zq_context =
    reference reference_types +
    ref_word16: reference_allocatable reference_types _ _ _ _ _ _ _ word16_prism +
    ref_word32: reference_allocatable reference_types _ _ _ _ _ _ _ word32_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
      'o prompt_output \<Rightarrow> unit\<close>
  and word16_prism :: \<open>('gv, 16 word) prism\<close>
  and word32_prism :: \<open>('gv, 32 word) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word16.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_word32.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

section\<open>Helper lemmas for cast equivalence\<close>

lemma ucast_u16_u32_unat:
  shows \<open>unat (ucast (x::16 word)::32 word) = unat x\<close>
by (simp add: unat_ucast_up)

lemma zq_mul_ucast_equiv:
  assumes \<open>unat a < mlkem_q\<close>
      and \<open>unat b < mlkem_q\<close>
    shows \<open>ucast ((ucast (a::16 word)::32 word) * ucast b mod ucast mlkem_q_word) =
            MLKEM_Specification.zq_mul a b\<close>
proof -
  have ua: \<open>unat (ucast a::32 word) = unat a\<close>
    by (rule ucast_u16_u32_unat)
  have ub: \<open>unat (ucast b::32 word) = unat b\<close>
    by (rule ucast_u16_u32_unat)
  have uq: \<open>unat (ucast mlkem_q_word::32 word) = mlkem_q\<close>
    by (simp add: ucast_u16_u32_unat mlkem_q_word_unat)
  have no_ov: \<open>unat a * unat b < 2 ^ 32\<close>
    using assms by (rule zq_mul_no_overflow_32)
  have prod_eq: \<open>unat ((ucast a::32 word) * ucast b) = unat a * unat b\<close>
    using no_ov by (simp add: ua ub unat_mult_lem[THEN iffD1])
  have mod_eq: \<open>unat ((ucast a::32 word) * ucast b mod ucast mlkem_q_word::32 word)
                = (unat a * unat b) mod mlkem_q\<close>
    by (simp add: unat_mod uq prod_eq)
  have mod_fits: \<open>(unat a * unat b) mod mlkem_q < 2 ^ 16\<close>
    using assms by (rule zq_mul_result_fits_16)
  have lhs_unat: \<open>unat (ucast ((ucast a::32 word) * ucast b mod ucast mlkem_q_word::32 word)::16 word) =
                    (unat a * unat b) mod mlkem_q\<close>
  proof -
    have \<open>unat (ucast ((ucast a::32 word) * ucast b mod ucast mlkem_q_word :: 32 word)::16 word)
          = unat ((ucast a::32 word) * ucast b mod ucast mlkem_q_word::32 word) mod 2 ^ 16\<close>
      by (simp add: unat_ucast)
    also have \<open>\<dots> = ((unat a * unat b) mod mlkem_q) mod 2 ^ 16\<close>
      by (simp add: mod_eq)
    also have \<open>\<dots> = (unat a * unat b) mod mlkem_q\<close>
      using mod_fits by simp
    finally show ?thesis .
  qed
  have rhs_unat: \<open>unat (MLKEM_Specification.zq_mul a b :: 16 word) = (unat a * unat b) mod mlkem_q\<close>
    using mod_fits by (simp add: MLKEM_Specification.zq_mul_def unat_of_nat take_bit_nat_eq_self_iff)
  show ?thesis
    by (rule word_eq_unatI) (simp add: lhs_unat rhs_unat)
qed

section\<open>Modular addition\<close>

definition zq_add :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
      ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>zq_add a b \<equiv> FunctionBody \<lbrakk>
     let sum = a + b;
     sum % mlkem_q_word
  \<rbrakk>\<close>

definition zq_add_contract :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
      ('s::{sepalg}, 16 word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>zq_add_contract a b \<equiv>
    let pre  = \<langle>unat a < mlkem_q\<rangle> \<star>
               \<langle>unat b < mlkem_q\<rangle>;
        post = \<lambda>r. \<langle>r = MLKEM_Specification.zq_add a b\<rangle> \<star>
               \<langle>unat r < mlkem_q\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto zq_add_contract

lemma zq_add_spec [crush_specs]:
  shows \<open>\<Gamma>; zq_add a b \<Turnstile>\<^sub>F zq_add_contract a b\<close>
  apply (crush_boot f: zq_add_def contract: zq_add_contract_def, goal_cases)
  using zq_add_no_overflow mlkem_q_nonzero_word zq_add_range
    apply (crush_base simp add: MLKEM_Specification.zq_add_def mlkem_q_word_unat mlkem_q_def)
  done

section\<open>Modular subtraction\<close>

definition zq_sub :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
     ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>zq_sub a b \<equiv> FunctionBody \<lbrakk>
     let sum = a + mlkem_q_word - b;

     sum % mlkem_q_word
  \<rbrakk>\<close>

definition zq_sub_contract :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
      ('s::{sepalg}, 16 word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>zq_sub_contract a b \<equiv>
     let pre  = \<langle>unat a < mlkem_q\<rangle> \<star>
                \<langle>unat b < mlkem_q\<rangle>;
         post = \<lambda>r. \<langle>r = MLKEM_Specification.zq_sub a b\<rangle> \<star>
                \<langle>unat r < mlkem_q\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto zq_sub_contract

lemma zq_sub_spec [crush_specs]:
  shows \<open>\<Gamma>; zq_sub a b \<Turnstile>\<^sub>F zq_sub_contract a b\<close>
proof (crush_boot f: zq_sub_def contract: zq_sub_contract_def, goal_cases)
case 1
  moreover have \<open>\<And>a b. \<lbrakk>unat a < mlkem_q; unat b < mlkem_q\<rbrakk> \<Longrightarrow> b \<le> a + mlkem_q_word\<close>
    by (simp add: word_le_nat_alt mlkem_q_word_def mlkem_q_def unat_add_lem[THEN iffD1])
  ultimately show ?case
    using zq_sub_no_overflow mlkem_q_nonzero_word zq_sub_range
      by (crush_base simp add: MLKEM_Specification.zq_sub_def mlkem_q_word_unat mlkem_q_def)
qed

section\<open>Modular multiplication\<close>

definition zq_mul :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
      ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>zq_mul a b \<equiv> FunctionBody \<lbrakk>
     let a32 = a as u32;
     let b32 = b as u32;

     let product = a32 * b32;
     let q32 = mlkem_q_word as u32;
     let reduced = product % q32;

     reduced as u16
  \<rbrakk>\<close>

definition zq_mul_contract :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow>
      ('s::{sepalg}, 16 word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>zq_mul_contract a b \<equiv>
    let pre  = \<langle>unat a < mlkem_q\<rangle> \<star>
               \<langle>unat b < mlkem_q\<rangle>;
        post = \<lambda>r. \<langle>r = MLKEM_Specification.zq_mul a b\<rangle> \<star>
               \<langle>unat r < mlkem_q\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto zq_mul_contract

lemma zq_mul_spec [crush_specs]:
  shows \<open>\<Gamma>; zq_mul a b \<Turnstile>\<^sub>F zq_mul_contract a b\<close>
proof (crush_boot f: zq_mul_def contract: zq_mul_contract_def, goal_cases)
case 1
  moreover have q_nz32: \<open>(ucast mlkem_q_word::32 word) \<noteq> 0\<close>
    by (simp add: mlkem_q_word_def)
  ultimately show ?case
    using zq_mul_no_overflow_32 mlkem_q_nonzero_word zq_mul_range zq_mul_ucast_equiv
      by (crush_base simp add: MLKEM_Specification.zq_mul_def mlkem_q_word_unat mlkem_q_def
        ucast_u16_u32_unat zq_mul_ucast_equiv)
qed

end

end
