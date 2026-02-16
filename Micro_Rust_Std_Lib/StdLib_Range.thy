(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Range                            
  imports Crush.Crush Shallow_Micro_Rust.Range_Type
begin
(*>*)

definition is_empty_contract :: \<open>'a::{ord} range \<Rightarrow> ('machine::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>is_empty_contract r \<equiv>
    let pre  = \<top>;
        post = \<lambda>res. \<langle>res \<longleftrightarrow>
          (if end_inclusive r then start r > end r else \<not>start r < end r)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto is_empty_contract

lemma is_empty_spec [crush_specs]:
  shows \<open>\<Gamma> ; is_empty r \<Turnstile>\<^sub>F is_empty_contract r\<close>
by (contract f: is_empty_def contract: is_empty_contract_def) crush_base

definition contains_contract :: \<open>'a::{ord} range \<Rightarrow> 'a \<Rightarrow> ('machine::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>contains_contract r e \<equiv>
    let pre  = \<top>;
        post = \<lambda>res. \<langle>res \<longleftrightarrow>
          (if end_inclusive r then start r \<le> e \<and> e \<le> end r else start r \<le> e \<and> e < end r)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto contains_contract

lemma contains_spec [crush_specs]:  
  shows \<open>\<Gamma> ; contains r e \<Turnstile>\<^sub>F contains_contract r e\<close>
by (contract f: contains_def contract: contains_contract_def) crush_base

lemma range_into_list_make_range [micro_rust_simps]:
  shows \<open>range_into_list (make_range s e incl) =
    (if incl then list.map word_of_nat [unat s..<Suc (unat e)]
     else list.map word_of_nat [unat s..<unat e])\<close>
by (clarsimp simp add: range_into_list_def)

(*<*)
end
(*>*)
