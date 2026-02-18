(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Result
  imports Crush.Crush Misc.Result StdLib_References
begin
(*>*)

section\<open>Core material related to the \<^emph>\<open>Result\<close> type\<close>

text\<open>Returns \<^verbatim>\<open>x\<close> if the element of \<^verbatim>\<open>Result\<close> type is of the form \<^verbatim>\<open>Ok x\<close>.  Panics otherwise with
the defined error message.\<close>
definition result_expect :: \<open>('v,'e) result \<Rightarrow> String.literal \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_expect self msg \<equiv> FunctionBody \<lbrakk>
      match self {
        Ok(v) \<Rightarrow> v,
        Err(_) \<Rightarrow> panic!(msg) 
      }
  \<rbrakk>\<close>
adhoc_overloading expect \<rightleftharpoons> result_expect

definition result_expect_contract :: 
  \<open>('a, 'e) result \<Rightarrow> 'a \<Rightarrow> ('s::{sepalg}, 'a, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_expect_contract self v \<equiv>
    let pre = \<langle>self = Ok v\<rangle>; post = \<lambda>r. \<langle>r = v\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_expect_contract

lemma result_expect_spec [crush_specs]:
  shows \<open>\<Gamma>; result_expect res m \<Turnstile>\<^sub>F result_expect_contract res v\<close>
  by (crush_boot f: result_expect_def contract: result_expect_contract_def)
     (crush_base split!: result.splits)

text\<open>Returns \<^verbatim>\<open>x\<close> if the element of \<^verbatim>\<open>Result\<close> type is of the form \<^verbatim>\<open>Ok x\<close>.  Panics otherwise.\<close>
definition result_unwrap :: \<open>('v,'e) result \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_unwrap self \<equiv> FunctionBody \<lbrakk>
      self.expect("result_unwrap")
  \<rbrakk>\<close>
adhoc_overloading unwrap \<rightleftharpoons> result_unwrap

definition result_unwrap_contract :: 
  \<open>('a, 'e) result \<Rightarrow> 'a \<Rightarrow> ('s::{sepalg}, 'a, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_unwrap_contract self v \<equiv>
    let pre = \<langle>self = Ok v\<rangle>; post = \<lambda>r. \<langle>r = v\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_unwrap_contract

lemma result_unwrap_spec [crush_specs]:
  shows \<open>\<Gamma>; result_unwrap res \<Turnstile>\<^sub>F result_unwrap_contract res v\<close>
  by (crush_boot f: result_unwrap_def contract: result_unwrap_contract_def)
     (crush_base split!: result.splits)

text\<open>Tests whether an element of \<^verbatim>\<open>Result\<close> type is the \<^verbatim>\<open>Err\<close> constructor:\<close>
definition urust_func_result_is_err :: \<open>('v,'e) result \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>urust_func_result_is_err self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(_) \<Rightarrow> False,
       Err(_) \<Rightarrow> True
     }
  \<rbrakk>\<close>

definition result_is_err_contract :: 
  \<open>('a, 'e) result \<Rightarrow> ('s::{sepalg}, bool, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_is_err_contract res \<equiv>
    let pre = UNIV; post = \<lambda>r. \<langle>r = result_is_err res\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_is_err_contract

lemma result_is_err_spec [crush_specs]:
  shows \<open>\<Gamma>; urust_func_result_is_err res \<Turnstile>\<^sub>F result_is_err_contract res\<close>
  by (crush_boot f: urust_func_result_is_err_def contract: result_is_err_contract_def)
     (crush_base simp add: result_is_err_def split!: result.splits)

text\<open>Tests whether an element of \<^verbatim>\<open>Result\<close> type is the \<^verbatim>\<open>Ok\<close> constructor:\<close>
definition urust_func_result_is_ok :: \<open>('v,'e) result \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>urust_func_result_is_ok self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(_) \<Rightarrow> True,
       Err(_) \<Rightarrow> False
     }
  \<rbrakk>\<close>

definition result_is_ok_contract :: 
  \<open>('a, 'e) result \<Rightarrow> ('s::{sepalg}, bool, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_is_ok_contract res \<equiv>
    let pre = UNIV; post = \<lambda>r. \<langle>r = result_is_ok res\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_is_ok_contract

lemma result_is_ok_spec [crush_specs]:
  shows \<open>\<Gamma>; urust_func_result_is_ok res \<Turnstile>\<^sub>F result_is_ok_contract res\<close>
  by (crush_boot f: urust_func_result_is_ok_def contract: result_is_ok_contract_def)
     (crush_base simp add: result_is_ok_def split!: result.splits)

definition result_or :: \<open>('a, 'f) result \<Rightarrow> ('a, 'e) result \<Rightarrow> ('s, ('a, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_or self e \<equiv> FunctionBody \<lbrakk>
     match self {
        Ok(v) \<Rightarrow> Ok(v),
        Err(_) \<Rightarrow> e
     } 
  \<rbrakk>\<close>
notation_nano_rust_function result_or ("or")

definition result_or_pure :: \<open>('a, 'f) result \<Rightarrow> ('a, 'e) result \<Rightarrow> ('a, 'e) result\<close> where
  \<open>result_or_pure v e \<equiv> case v of Ok(v) \<Rightarrow> Ok(v) | Err(_) \<Rightarrow> e\<close>

lemma result_or_pure_simps[simp]:
  shows \<open>result_or_pure (Ok v) f = Ok v\<close>
    and \<open>result_or_pure (Err e) f = f\<close>
  by (auto simp add: result_or_pure_def)

definition result_or_contract :: 
  \<open>('a, 'e) result \<Rightarrow> ('a, 'f) result \<Rightarrow> ('s::{sepalg}, ('a, 'f) result, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_or_contract res if_err \<equiv>
    let pre = UNIV; post = \<lambda>r. \<langle>r = result_or_pure res if_err\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_or_contract

lemma result_or_spec [crush_specs]:
  shows \<open>\<Gamma>; result_or res if_err \<Turnstile>\<^sub>F result_or_contract res if_err\<close>
  by (crush_boot f: result_or_def contract: result_or_contract_def)
     (crush_base simp add: result_or_pure_def split!: result.splits)

definition map_err :: \<open>('a, 'e) result \<Rightarrow> ('e \<Rightarrow> ('machine, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('machine, ('a, 'f) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>map_err x f \<equiv> FunctionBody \<lbrakk>
     match x {
       Ok(a)  \<Rightarrow> Ok(a),
       Err(e) \<Rightarrow> Err(f(e))
     }
  \<rbrakk>\<close>

definition ok :: \<open>('v, 'e) result \<Rightarrow> ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>ok self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(r) \<Rightarrow> Some(r),
       Err(e) \<Rightarrow> None
     }
   \<rbrakk>\<close>

definition ok_contract ::  \<open>('v, 'e) result \<Rightarrow> ('s::{sepalg}, 'v option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>ok_contract res \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case res of Err(_) \<Rightarrow> None | Ok(k) \<Rightarrow> Some k)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto ok_contract

lemma ok_spec [crush_specs]:
  shows \<open>\<Gamma>; ok res \<Turnstile>\<^sub>F ok_contract res\<close>
  apply (crush_boot f: ok_def contract: ok_contract_def)
  apply (cases res)
  apply crush_base
  done

definition result_unwrap_or :: \<open>('a, 'b) result \<Rightarrow> 'a \<Rightarrow> ('machine, 'a, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_unwrap_or res e \<equiv> FunctionBody \<lbrakk>
     if let Ok(r) = res {
       r
     } else {
       e
     }
   \<rbrakk>\<close>

context reference
begin       
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

definition result_as_mut :: \<open>('a, 'b, ('v, 'e) result) Global_Store.ref \<Rightarrow>
    ('s, (('a, 'b, 'v) Global_Store.ref, ('a, 'b, 'e) Global_Store.ref) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_as_mut self \<equiv> FunctionBody \<lbrakk>
     match *self {
       Ok(_)  \<Rightarrow> Ok (\<llangle>focus_result_ok self\<rrangle>),
       Err(_) \<Rightarrow> Err (\<llangle>focus_result_err self\<rrangle>)
     }
  \<rbrakk>\<close>

definition result_as_mut_contract :: \<open>'b \<Rightarrow> ('a, 'b, ('v, 'e) result) Global_Store.ref
     \<Rightarrow> ('v, 'e) result \<Rightarrow> ('s::{sepalg}, (('a, 'b, 'v) Global_Store.ref, ('a, 'b, 'e) Global_Store.ref) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_as_mut_contract g ref opt \<equiv>
    let pre  = ref \<mapsto>\<langle>\<top>\<rangle> g\<down>opt;
        post = \<lambda>res. ref \<mapsto>\<langle>\<top>\<rangle> g\<down>opt \<star> 
            \<langle>res = (if result_is_ok opt then
                      Ok (focus_result_ok ref)
                   else
                      Err (focus_result_err ref))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_as_mut_contract

lemma result_as_mut_spec [crush_specs]:
  shows \<open>\<Gamma>; result_as_mut ref \<Turnstile>\<^sub>F result_as_mut_contract g ref opt\<close>
  apply (crush_boot f: result_as_mut_def contract: result_as_mut_contract_def)
  apply (crush_base simp add: result_is_ok_def split: result.splits)
  done

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

(*<*)
end
(*>*)

instantiation result :: (generate_debug,generate_debug)generate_debug
begin

fun generate_debug_result :: \<open>('a, 'b) result \<Rightarrow> log_data\<close> where
  \<open>generate_debug_result (Ok  k) = str ''Ok(''#generate_debug k@[str '')'']\<close> |
  \<open>generate_debug_result (Err e) = str ''Err(''#generate_debug e@[str '')'']\<close>

instance ..

end

end
(*>*)