(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory MLKEM_Polynomial
  imports
    MLKEM_Zq
    Micro_Rust_Std_Lib.StdLib_Slice
begin

text\<open>
  \<mu>Rust polynomial operations with contracts proving refinement against the
  pure specifications from @{theory Micro_Rust_Examples.MLKEM_Specification}.
\<close>

section\<open>Locale\<close>

locale mlkem_polynomial_context =
    mlkem_zq_context _ _ _ _ _ _ _ reference_types word16_prism word32_prism
  + ref_poly: reference_allocatable reference_types _ _ _ _ _ _ _ poly_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and word16_prism :: \<open>('gv, 16 word) prism\<close>
  and word32_prism :: \<open>('gv, 32 word) prism\<close>
  and poly_prism :: \<open>('gv, mlkem_poly) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_poly.new

section\<open>Splice helper lemmas\<close>

text\<open>These lemmas relate the loop body operation (array update at index i) to the
\<^verbatim>\<open>array\_splice\<close> characterization used in the loop invariant.\<close>

lemma poly_add_splice_step:
  assumes \<open>i < mlkem_n\<close>
    shows \<open>array_update (array_splice i (MLKEM_Specification.poly_add a b) a) i
             (MLKEM_Specification.zq_add (array_nth a i) (array_nth b i)) =
            array_splice (Suc i) (MLKEM_Specification.poly_add a b) a\<close>
using assms by (simp add: array_splice_Suc MLKEM_Specification.poly_add_def array_map2_nth mlkem_n_def)

lemma poly_add_splice_full:
  shows \<open>array_splice mlkem_n (MLKEM_Specification.poly_add a b) a =
          MLKEM_Specification.poly_add a b\<close>
by (intro array_extI) (simp add: mlkem_n_def)

lemma poly_sub_splice_step:
  assumes \<open>i < mlkem_n\<close>
    shows \<open>array_update (array_splice i (MLKEM_Specification.poly_sub a b) a) i
             (MLKEM_Specification.zq_sub (array_nth a i) (array_nth b i)) =
            array_splice (Suc i) (MLKEM_Specification.poly_sub a b) a\<close>
using assms by (simp add: array_splice_Suc MLKEM_Specification.poly_sub_def array_map2_nth mlkem_n_def)

lemma poly_sub_splice_full:
  shows \<open>array_splice mlkem_n (MLKEM_Specification.poly_sub a b) a =
          MLKEM_Specification.poly_sub a b\<close>
by (intro array_extI) (simp add: mlkem_n_def)

section\<open>Polynomial addition\<close>

definition poly_add :: \<open>mlkem_poly \<Rightarrow> mlkem_poly \<Rightarrow>
     ('s, mlkem_poly, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_add a b \<equiv> FunctionBody \<lbrakk>
     let mut result = a;

     for i in 0..256_u64 {
       let elem_ref = result[i];

       let ai = *elem_ref;
       let bi = b[i];

       elem_ref = zq_add(ai, bi)
     };

     *result
  \<rbrakk>\<close>

definition poly_add_contract :: \<open>mlkem_poly \<Rightarrow> mlkem_poly \<Rightarrow>
        ('s::{sepalg}, mlkem_poly, 'b) function_contract\<close> where
  [crush_contracts]: \<open>poly_add_contract a b \<equiv>
     let pre  = can_alloc_reference \<star>
                \<langle>poly_wf a\<rangle> \<star>
                \<langle>poly_wf b\<rangle>;
         post = \<lambda>r. can_alloc_reference \<star>
                \<langle>r = MLKEM_Specification.poly_add a b\<rangle> \<star>
                \<langle>poly_wf r\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto poly_add_contract

lemma poly_add_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_add a b \<Turnstile>\<^sub>F poly_add_contract a b\<close>
  apply (crush_boot f: poly_add_def contract: poly_add_contract_def)
  apply crush_base
  subgoal for result_ref
    apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g.
            result_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(array_splice i (MLKEM_Specification.poly_add a b) a)\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
    using poly_add_splice_step poly_add_splice_full MLKEM_Specification.poly_add_wf
      apply (crush_base
            specs add: zq_add_spec
            contracts add: zq_add_contract_def
            simp add: poly_wf_nth mlkem_n_def
                     poly_add_splice_step
                     MLKEM_Specification.poly_add_def array_map2_nth
                     nth_focus_array_components unat_ucast_eq)
  done
done

section\<open>Polynomial subtraction\<close>

definition poly_sub :: \<open>mlkem_poly \<Rightarrow> mlkem_poly \<Rightarrow>
     ('s, mlkem_poly, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>poly_sub a b \<equiv> FunctionBody \<lbrakk>
     let mut result = a;

     for i in 0..256_u64 {
       let elem_ref = result[i];
       let ai = *elem_ref;
       let bi = b[i];

       elem_ref = zq_sub(ai, bi)
     };

     *result
  \<rbrakk>\<close>

definition poly_sub_contract :: \<open>mlkem_poly \<Rightarrow> mlkem_poly \<Rightarrow>
      ('s::{sepalg}, mlkem_poly, 'b) function_contract\<close> where
  [crush_contracts]: \<open>poly_sub_contract a b \<equiv>
     let pre  = can_alloc_reference \<star>
                \<langle>poly_wf a\<rangle> \<star>
                \<langle>poly_wf b\<rangle>;
         post = \<lambda>r. can_alloc_reference \<star>
                \<langle>r = MLKEM_Specification.poly_sub a b\<rangle> \<star>
                \<langle>poly_wf r\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto poly_sub_contract

lemma poly_sub_spec [crush_specs]:
  shows \<open>\<Gamma>; poly_sub a b \<Turnstile>\<^sub>F poly_sub_contract a b\<close>
  apply (crush_boot f: poly_sub_def contract: poly_sub_contract_def)
  apply crush_base
  subgoal for result_ref
    apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g.
            result_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(array_splice i (MLKEM_Specification.poly_sub a b) a)\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
    using poly_sub_splice_step poly_sub_splice_full MLKEM_Specification.poly_sub_wf
      apply (crush_base
            specs add: zq_sub_spec
            contracts add: zq_sub_contract_def
            simp add: poly_wf_nth mlkem_n_def
                     poly_sub_splice_step
                     MLKEM_Specification.poly_sub_def array_map2_nth
                     nth_focus_array_components unat_ucast_eq)
  done
done

end

end
