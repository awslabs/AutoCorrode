(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Option    
  imports Crush.Crush StdLib_References Misc.Result
begin
(*>*)

consts take_const :: \<open>'a\<close>
notation_nano_rust_function take_const ("take")

definition option_expect :: \<open>'v option \<Rightarrow> String.literal \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_expect self msg \<equiv> FunctionBody \<lbrakk>
      match self {
        Some(v) \<Rightarrow> v,
        None \<Rightarrow> panic!(msg) 
      }      
   \<rbrakk>\<close>
adhoc_overloading expect \<rightleftharpoons> option_expect

definition option_expect_contract :: \<open>'a option \<Rightarrow> String.literal \<Rightarrow>
    ('s::{sepalg}, 'a, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>option_expect_contract opt msg \<equiv>
     let pre  = \<langle>opt \<noteq> None\<rangle>;
         post = \<lambda>r. \<langle>r = the opt\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto option_expect_contract

lemma option_expect_spec [crush_specs]:
  shows \<open>\<Gamma>; option_expect res m \<Turnstile>\<^sub>F option_expect_contract res v\<close>
  by (crush_boot f: option_expect_def contract: option_expect_contract_def)
     (crush_base split!: option.splits)

definition option_unwrap :: \<open>'v option \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_unwrap self \<equiv> FunctionBody \<lbrakk>
     self.expect("unwrap")
  \<rbrakk>\<close>
adhoc_overloading unwrap \<rightleftharpoons> option_unwrap

definition option_unwrap_contract :: 
  \<open>'a option \<Rightarrow> 'a \<Rightarrow> ('s::{sepalg}, 'a, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>option_unwrap_contract self v \<equiv>
    let pre = \<langle>self = Some v\<rangle>; post = \<lambda>r. \<langle>r = v\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto option_unwrap_contract

lemma option_unwrap_spec [crush_specs]:
  shows \<open>\<Gamma>; option_unwrap res \<Turnstile>\<^sub>F option_unwrap_contract res v\<close>
  by (crush_boot f: option_unwrap_def contract: option_unwrap_contract_def)
     (crush_base split!: option.splits)

definition urust_func_option_is_none :: \<open>'v option \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>urust_func_option_is_none self \<equiv> FunctionBody \<lbrakk>
     match self {
       Some(_) \<Rightarrow> False,
       None \<Rightarrow> True
     }
  \<rbrakk>\<close>
notation_nano_rust_function urust_func_option_is_none ("is_none")

definition option_is_none_contract :: 
  \<open>'a option \<Rightarrow> ('s::{sepalg}, bool, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>option_is_none_contract res \<equiv>
    let pre = UNIV; post = \<lambda>r. \<langle>r = Option.is_none res\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto option_is_none_contract

lemma option_is_none_spec [crush_specs]:
  shows \<open>\<Gamma>; urust_func_option_is_none res \<Turnstile>\<^sub>F option_is_none_contract res\<close>
  by (crush_boot f: urust_func_option_is_none_def contract: option_is_none_contract_def)
     (crush_base simp add: Option.is_none_def split!: option.splits)

definition urust_func_option_is_some :: \<open>'v option \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>urust_func_option_is_some self \<equiv> FunctionBody \<lbrakk>
     match self {
       Some(_) \<Rightarrow> True,
       None \<Rightarrow> False
     }
  \<rbrakk>\<close>
notation_nano_rust_function urust_func_option_is_some ("is_some")

definition option_is_some_contract :: 
  \<open>'a option \<Rightarrow> ('s::{sepalg}, bool, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>option_is_some_contract res \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r \<longleftrightarrow> \<not>Option.is_none res\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto option_is_some_contract

lemma option_is_some_spec [crush_specs]:
  shows \<open>\<Gamma>; urust_func_option_is_some res \<Turnstile>\<^sub>F option_is_some_contract res\<close>
  by (crush_boot f: urust_func_option_is_some_def contract: option_is_some_contract_def)
     (crush_base simp add: Option.is_none_def split!: option.splits)

definition ok_or :: \<open>'v option \<Rightarrow> 'e \<Rightarrow> ('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>ok_or self e \<equiv> FunctionBody \<lbrakk>
     match self {
        Some(v) \<Rightarrow> Ok(v),
        None \<Rightarrow> Err(e)
     } 
  \<rbrakk>\<close>

definition ok_or_pure :: \<open>'v option \<Rightarrow> 'e \<Rightarrow> ('v, 'e) result\<close> where
  \<open>ok_or_pure opt e \<equiv> case opt of Some(v) \<Rightarrow> Ok(v) | None \<Rightarrow> Err(e)\<close>

lemma ok_or_pure_simps [simp]:
  shows \<open>ok_or_pure None     e = Err(e)\<close>
    and \<open>ok_or_pure (Some v) e = Ok(v)\<close>
by (auto simp add: ok_or_pure_def)

definition option_ok_or_contract :: \<open>'v option \<Rightarrow> 'e \<Rightarrow> ('s::{sepalg}, ('v, 'e) result, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>option_ok_or_contract opt e \<equiv>
    let pre = UNIV;
        post = \<lambda>r. \<langle>r = ok_or_pure opt e\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto option_ok_or_contract

lemma option_ok_or_spec [crush_specs]:
  shows \<open>\<Gamma>; ok_or opt e \<Turnstile>\<^sub>F option_ok_or_contract opt e\<close>
  apply (crush_boot f: ok_or_def contract: option_ok_or_contract_def)
  apply (crush_base simp add: ok_or_pure_def split!: option.splits)
  done

context reference
begin
       
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

definition option_as_mut ::
  \<open>('a, 'b, 'v option) Global_Store.ref \<Rightarrow> ('s, ('a, 'b, 'v) Global_Store.ref option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>option_as_mut self \<equiv> FunctionBody \<lbrakk>
    if (*self).is_some() {
      Some (\<llangle>focus_option self\<rrangle>)
    } else {
      None
    }\<rbrakk>\<close>

definition option_as_mut_contract :: \<open>'b \<Rightarrow> ('a, 'b, 'v option) Global_Store.ref \<Rightarrow> 'v option \<Rightarrow>
    ('s::{sepalg}, ('a, 'b, 'v) Global_Store.ref option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>option_as_mut_contract g ref opt \<equiv>
    let pre  = ref \<mapsto>\<langle>\<top>\<rangle> g\<down>opt;
        post = \<lambda>res. ref \<mapsto>\<langle>\<top>\<rangle> g\<down>opt \<star> \<langle>res = 
           (if opt = None then None else Some (focus_option ref))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto option_as_mut_contract

lemma option_as_mut_spec [crush_specs]:
  shows \<open>\<Gamma>; option_as_mut ref \<Turnstile>\<^sub>F option_as_mut_contract g ref opt\<close>
  apply (crush_boot f: option_as_mut_def contract: option_as_mut_contract_def)
  apply (crush_base simp add: option_focus_def split: option.splits)
  done

definition take_mut_ref_option :: \<open>('a, 'b, 'v option) Global_Store.ref \<Rightarrow>
      ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>take_mut_ref_option ptr \<equiv> FunctionBody \<lbrakk>
    let val = *ptr;
    ptr = None;
    val
  \<rbrakk>\<close> 
adhoc_overloading take_const \<rightleftharpoons>
  take_mut_ref_option

definition take_mut_ref_option_contract :: \<open>('a, 'b, 'v option) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v option \<Rightarrow>
    ('s::{sepalg}, 'v option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>take_mut_ref_option_contract ptr g v \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post = \<lambda>r. (\<langle>r=v\<rangle> \<star> ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. None)\<sqdot>(g\<down>v))
     in make_function_contract pre post\<close>
ucincl_auto take_mut_ref_option_contract

lemma take_mut_ref_option_spec[crush_specs]:
  shows \<open>\<Gamma>; take_mut_ref_option ptr \<Turnstile>\<^sub>F take_mut_ref_option_contract ptr g v\<close>
  apply (crush_boot f: take_mut_ref_option_def contract: take_mut_ref_option_contract_def)
  apply crush_base
  done

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

(*<*)
end
(*>*)

instantiation option :: (generate_debug)generate_debug
begin

fun generate_debug_option :: \<open>'a option \<Rightarrow> log_data\<close> where
  \<open>generate_debug_option (Some  k) = str ''Some(''#generate_debug k@[str '')'']\<close> |
  \<open>generate_debug_option None      = [str ''None'']\<close>

instance ..

end

end
(*>*)