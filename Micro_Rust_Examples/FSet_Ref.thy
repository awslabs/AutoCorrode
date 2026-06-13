(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory FSet_Ref
  imports
    Micro_Rust_Std_Lib.StdLib_All
    "HOL-Library.FSet"
begin

section\<open>Finite Set References\<close>

text\<open>Makes HOL-Library.FSet available as a reference-backed uRust type with contains and insert operations.\<close>

locale fset_ref =
  reference reference_types
  + ref_fset: reference_allocatable reference_types _ _ _ _ _ _ _ fset_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and fset_prism :: \<open>('gv, 't fset) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_fset.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

abbreviation fset_points_to :: \<open>'t fset \<Rightarrow> ('addr, 'gv, 't fset) Global_Store.ref \<Rightarrow> 's assert\<close>
  where \<open>fset_points_to xs s \<equiv> (\<Squnion>g. s \<mapsto>\<langle>\<top>\<rangle> g\<down>xs)\<close>

definition contains :: \<open>('addr, 'gv, 't fset) Global_Store.ref \<Rightarrow> 't \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>contains s x \<equiv> FunctionBody \<lbrakk>
     let xs = *s;
     \<llangle>x |\<in>| xs\<rrangle>
  \<rbrakk>\<close>

definition contains_contract ::
    \<open>'t fset \<Rightarrow> ('addr, 'gv, 't fset) Global_Store.ref \<Rightarrow> 't \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>contains_contract xs s x \<equiv>
     let pre = fset_points_to xs s in
     let post = \<lambda>b. fset_points_to xs s \<star> \<langle>b = (x |\<in>| xs)\<rangle> in
     make_function_contract pre post\<close>
ucincl_auto contains_contract

lemma contains_spec [crush_specs]:
  shows \<open>\<Gamma>; contains s x \<Turnstile>\<^sub>F contains_contract xs s x\<close>
  apply (crush_boot f: contains_def contract: contains_contract_def)
  apply crush_base
  done

definition fset_insert ::
  \<open>('addr, 'gv, 't fset) Global_Store.ref \<Rightarrow> 't \<Rightarrow>
     ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fset_insert s x \<equiv> FunctionBody \<lbrakk>
     let xs = *s;
     s = \<llangle>finsert x xs\<rrangle>
   \<rbrakk>\<close>

definition fset_insert_contract ::
  \<open>('addr, 'gv, 't fset) Global_Store.ref \<Rightarrow> 't \<Rightarrow> 't fset \<Rightarrow>
   ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>fset_insert_contract s x xs \<equiv>
     let pre = fset_points_to xs s in
     let post = \<lambda>_. fset_points_to (finsert x xs) s in
     make_function_contract pre post\<close>
ucincl_auto fset_insert_contract

lemma fset_insert_spec [crush_specs]:
  shows \<open>\<Gamma>; fset_insert s x \<Turnstile>\<^sub>F fset_insert_contract s x xs\<close>
  apply (crush_boot f: fset_insert_def contract: fset_insert_contract_def)
  apply crush_base
  done

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

end
