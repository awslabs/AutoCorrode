(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Result
  imports Crush.Crush Misc.Result StdLib_References
begin
(*>*)

section\<open>Preamble\<close>

text\<open>The following two declarations are needed for contracts where we pass a function as an argument,
since this is needed multiple places, we're including the declarations here.\<close>

declare lift_pure_to_contract_def [crush_contracts]
ucincl_auto lift_pure_to_contract

section\<open>Core material related to the \<^emph>\<open>Result\<close> type\<close>

text\<open>Methods for Result enum as part of std::result implemented here 
based on documentation at \<^url>\<open>https://doc.rust-lang.org/std/result/enum.Result.html\<close>.
The ordering is identical to that found on the documentation page.\<close>

subsection\<open>and\<close>

text\<open>Returns second argument if first \<^verbatim>\<open>Result\<close> is of constructor \<^verbatim>\<open>Ok\<close>,
 otherwise returns \<^verbatim>\<open>Err\<close> value of first argument.\<close>

definition result_and :: \<open>('v, 'e) result \<Rightarrow> ('v, 'e) result \<Rightarrow>
 ('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_and self res \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(_) \<Rightarrow> res,
       Err(e) \<Rightarrow> Err(e)
     }
   \<rbrakk>\<close>

definition result_and_contract ::  \<open>('v, 'e) result \<Rightarrow> ('v, 'e) result \<Rightarrow>
 ('s::{sepalg}, ('v, 'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_and_contract self res \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case self of Ok(_) \<Rightarrow> res | Err(e) \<Rightarrow> Err(e))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_and_contract

lemma result_and_spec [crush_specs]:
  shows \<open>\<Gamma>; result_and self res \<Turnstile>\<^sub>F result_and_contract self res\<close>
  by (crush_boot f: result_and_def contract: result_and_contract_def)
     (cases self; crush_base)

subsection\<open>and_then\<close>

text\<open>Takes \<^verbatim>\<open>Result\<close> and some function, if \<^verbatim>\<open>Result\<close> constructor is \<^verbatim>\<open>Ok\<close>,
 pass \<^verbatim>\<open>Result\<close> to the function, otherwise return the value of \<^verbatim>\<open>Err\<close>.\<close>

definition result_and_then :: \<open>('v ,'e) result \<Rightarrow> 
('v \<Rightarrow> ('s, ('v ,'e) result, 'abort, 'i, 'o) function_body) \<Rightarrow> 
('s, ('v ,'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_and_then self f \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v) \<Rightarrow> f(v),
      Err(e) \<Rightarrow> Err(e)
    }
  \<rbrakk>\<close>

definition result_and_then_contract :: \<open>('v, 'e) result \<Rightarrow> ('v \<Rightarrow> ('v, 'e) result) \<Rightarrow> 
('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
('v \<Rightarrow> ('s, ('v ,'e) result, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('s, ('v ,'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_and_then_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> Err(e) | Ok(v) \<Rightarrow> pure_fun v)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_and_then_contract

lemma result_and_then_spec [crush_specs]:
  shows \<open>\<Gamma>; result_and_then self rust_fun \<Turnstile>\<^sub>F result_and_then_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_and_then_def contract: result_and_then_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  next
    case (Err x2)
    then show ?thesis by crush_base
  qed
qed

subsection\<open>as_deref\<close>

text\<open>Converts a shared reference to a \<^verbatim>\<open>Result\<close> whose \<^verbatim>\<open>Ok\<close> variant holds a reference into a \<^verbatim>\<open>Result\<close>
 of shared references, coercing the inner reference to a shared reference to its target.\<close>

context reference
begin

definition result_as_deref :: \<open>('a, 'b, (('c, 'd, 'v) ref, 'e) result) ro_ref \<Rightarrow>
    ('s, (('c, 'd, 'v) ro_ref, ('a, 'b, 'e) ro_ref) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_as_deref self \<equiv> FunctionBody \<lbrakk>
    match *self {
      Ok(v)  \<Rightarrow> Ok (\<llangle>ro_ref_from_ref v\<rrangle>),
      Err(_) \<Rightarrow> Err (\<llangle>focus_focused result_err_focus self\<rrangle>)
    }
  \<rbrakk>\<close>

definition result_as_deref_contract ::
  \<open>'b \<Rightarrow> share \<Rightarrow> ('a, 'b, (('c, 'd, 'v) ref, 'e) result) ro_ref \<Rightarrow>
   (('c, 'd, 'v) ref, 'e) result \<Rightarrow>
   ('s::{sepalg}, (('c, 'd, 'v) ro_ref, ('a, 'b, 'e) ro_ref) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_as_deref_contract g p self opt \<equiv>
    let pre  = (unsafe_ref_from_ro_ref self) \<mapsto>\<langle>p\<rangle> g\<down>opt;
        post = \<lambda>res. (unsafe_ref_from_ro_ref self) \<mapsto>\<langle>p\<rangle> g\<down>opt \<star> 
            \<langle>res = (case opt of
                      Ok(v)  \<Rightarrow> Ok(ro_ref_from_ref v)
                    | Err(_) \<Rightarrow> Err(focus_focused result_err_focus self))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_as_deref_contract

lemma result_as_deref_spec [crush_specs]:
  shows \<open>\<Gamma>; result_as_deref self \<Turnstile>\<^sub>F result_as_deref_contract g p self opt\<close>
  by (crush_boot f: result_as_deref_def contract: result_as_deref_contract_def)
     (crush_base split: result.splits)

end

subsection\<open>as_deref_mut\<close>

text\<open>Converts a mutable reference to a \<^verbatim>\<open>Result\<close> whose \<^verbatim>\<open>Ok\<close> variant holds a reference into a \<^verbatim>\<open>Result\<close> 
of mutable references, returning the inner reference as the mutable dereference target.\<close>

context reference
begin

definition result_as_deref_mut :: \<open>('a, 'b, (('c, 'd, 'v) ref, 'e) result) ref \<Rightarrow>
    ('s, (('c, 'd, 'v) ref, ('a, 'b, 'e) ref) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_as_deref_mut self \<equiv> FunctionBody \<lbrakk>
     match *self {
       Ok(_)  \<Rightarrow> Ok (*(\<llangle>focus_result_ok self\<rrangle>)),
       Err(_) \<Rightarrow> Err (\<llangle>focus_result_err self\<rrangle>)
     }
  \<rbrakk>\<close>

definition result_as_deref_mut_contract ::
  \<open>'b  \<Rightarrow> ('a, 'b, (('c, 'd, 'v) ref, 'e) result) ref \<Rightarrow>
   (('c, 'd, 'v) ref, 'e) result \<Rightarrow>
   ('s::{sepalg}, (('c, 'd, 'v) ref, ('a, 'b, 'e) ref) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_as_deref_mut_contract g self opt \<equiv>
    let pre  = self \<mapsto>\<langle>\<top>\<rangle> g\<down>opt;
        post = \<lambda>res. self \<mapsto>\<langle>\<top>\<rangle> g\<down>opt \<star> 
            \<langle>res = (case opt of
                      Ok(v)  \<Rightarrow> Ok(v)
                    | Err(_) \<Rightarrow> Err(focus_focused result_err_focus self))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_as_deref_mut_contract

lemma result_ok_focus_view_Ok:
  shows \<open>\<down>{result_ok_focus} (Ok x) \<doteq> x\<close>
  by (simp add: focus_view_def result_ok_focus.rep_eq make_focus_raw_via_view_modify_def)

lemma result_as_deref_mut_spec [crush_specs]:
  shows \<open>\<Gamma>; result_as_deref_mut self \<Turnstile>\<^sub>F result_as_deref_mut_contract g self opt\<close>
  by (crush_boot f: result_as_deref_mut_def contract: result_as_deref_mut_contract_def)
     (crush_base simp add: result_ok_focus_view_Ok split: result.splits)

end

subsection\<open>as_mut\<close>

text\<open>Converts a mutable reference to a \<^verbatim>\<open>Result\<close> 
into a \<^verbatim>\<open>Result\<close> of mutable references to the \<^verbatim>\<open>Ok\<close> or \<^verbatim>\<open>Err\<close> inner value.\<close>

context reference
begin       

definition result_as_mut :: \<open>('a, 'b, ('v, 'e) result) ref \<Rightarrow>
    ('s, (('a, 'b, 'v) ref, ('a, 'b, 'e) ref) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_as_mut self \<equiv> FunctionBody \<lbrakk>
     match *self {
       Ok(_)  \<Rightarrow> Ok (\<llangle>focus_result_ok self\<rrangle>),
       Err(_) \<Rightarrow> Err (\<llangle>focus_result_err self\<rrangle>)
     }
  \<rbrakk>\<close>

definition result_as_mut_contract :: \<open>'b \<Rightarrow> ('a, 'b, ('v, 'e) result) ref
     \<Rightarrow> ('v, 'e) result \<Rightarrow> ('s::{sepalg}, (('a, 'b, 'v) ref, ('a, 'b, 'e) ref) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_as_mut_contract g self opt \<equiv>
    let pre  = self \<mapsto>\<langle>\<top>\<rangle> g\<down>opt;
        post = \<lambda>res. self \<mapsto>\<langle>\<top>\<rangle> g\<down>opt \<star> 
            \<langle>res = (case opt of
                        Ok(_)  \<Rightarrow> Ok(focus_result_ok self)
                      | Err(_) \<Rightarrow> Err(focus_result_err self))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_as_mut_contract

lemma result_as_mut_spec [crush_specs]:
  shows \<open>\<Gamma>; result_as_mut self \<Turnstile>\<^sub>F result_as_mut_contract g self opt\<close>
  by (crush_boot f: result_as_mut_def contract: result_as_mut_contract_def)
     (crush_base split: result.splits)

end

subsection\<open>as_ref\<close>

text\<open>Converts a shared reference to a \<^verbatim>\<open>Result\<close> 
into a \<^verbatim>\<open>Result\<close> of shared references to the \<^verbatim>\<open>Ok\<close> or \<^verbatim>\<open>Err\<close> inner value.\<close>

context reference
begin       

definition result_as_ref :: \<open>('a, 'b, ('v, 'e) result) ro_ref \<Rightarrow> 
('s, (('a, 'b, 'v) ro_ref, ('a, 'b, 'e) ro_ref) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_as_ref self \<equiv> FunctionBody \<lbrakk>
    match *self {
       Ok(_)  \<Rightarrow> Ok (\<llangle>focus_focused result_ok_focus self\<rrangle>),
       Err(_) \<Rightarrow> Err (\<llangle>focus_focused result_err_focus self\<rrangle>)
    }
  \<rbrakk>\<close>

definition result_as_ref_contract :: \<open>'b \<Rightarrow> share \<Rightarrow> ('a, 'b, ('v, 'e) result) ro_ref
     \<Rightarrow> ('v, 'e) result \<Rightarrow> ('s::{sepalg}, (('a, 'b, 'v) ro_ref, ('a, 'b, 'e) ro_ref) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_as_ref_contract g p self opt \<equiv>
    let pre  = (unsafe_ref_from_ro_ref self) \<mapsto>\<langle>p\<rangle> g\<down>opt;
        post = \<lambda>res. (unsafe_ref_from_ro_ref self) \<mapsto>\<langle>p\<rangle> g\<down>opt \<star> 
            \<langle>res = (case opt of
                        Ok(_)  \<Rightarrow> Ok(focus_focused result_ok_focus self)
                      | Err(_) \<Rightarrow> Err (focus_focused result_err_focus self))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_as_ref_contract

lemma result_as_ref_spec [crush_specs]:
  shows \<open>\<Gamma>; result_as_ref self \<Turnstile>\<^sub>F result_as_ref_contract g p self opt\<close>
  by (crush_boot f: result_as_ref_def contract: result_as_ref_contract_def)
     (crush_base split: result.splits)

end

subsection\<open>cloned\<close>

text\<open>Takes a \<^verbatim>\<open>Result\<close> type with a shared reference (ro_ref) in the \<^verbatim>\<open>ok\<close> constructor and returns a
 \<^verbatim>\<open>Result\<close> type with simply the value of the reference in the \<^verbatim>\<open>ok\<close> constructor.\<close>

context reference
begin 

definition result_cloned :: \<open>(('a, 'b, 'v) ro_ref, 'e) result \<Rightarrow> 
('s, ('v, 'e) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_cloned self \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> Ok(*v),
      Err(e) \<Rightarrow> Err(e)
    }
  \<rbrakk>\<close>

definition result_cloned_contract ::
  \<open>'b \<Rightarrow> share \<Rightarrow> ('a, 'b, 'v) ro_ref \<Rightarrow> 'v \<Rightarrow>
   (('a, 'b, 'v) ro_ref, 'e) result \<Rightarrow>
   ('s::{sepalg}, ('v, 'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_cloned_contract g p r v self \<equiv>
    let pre  = \<langle>self = Ok (r)\<rangle> \<star> (unsafe_ref_from_ro_ref r) \<mapsto>\<langle>p\<rangle> g\<down>v;
        post = \<lambda>res. \<langle>res = Ok (v)\<rangle> \<star> (unsafe_ref_from_ro_ref r) \<mapsto>\<langle>p\<rangle> g\<down>v
    in make_function_contract pre post\<close>
ucincl_auto result_cloned_contract

lemma result_cloned_spec [crush_specs]:
  shows \<open>\<Gamma>; result_cloned self \<Turnstile>\<^sub>F result_cloned_contract g p r v self\<close>
  by (crush_boot f: result_cloned_def contract: result_cloned_contract_def) 
     (crush_base)

end

subsection\<open>copied\<close>

text\<open>Identical to cloned for the purposes of use in µRust\<close>

subsection\<open>err\<close>

text\<open>Converts a \<^verbatim>\<open>Result\<close> type into a \<^verbatim>\<open>Option\<close> type where only the \<^verbatim>\<open>Err\<close> constructor 
is kept while \<^verbatim>\<open>Ok\<close> is discarded.\<close>

definition result_err :: \<open>('v, 'e) result \<Rightarrow> ('s, 'e option, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_err self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(r) \<Rightarrow> None,
       Err(e) \<Rightarrow> Some(e)
     }
   \<rbrakk>\<close>

definition result_err_contract ::  \<open>('v, 'e) result \<Rightarrow> ('s::{sepalg}, 'e option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_err_contract res \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case res of Ok(_) \<Rightarrow> None | Err(k) \<Rightarrow> Some k)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_err_contract

lemma result_err_spec [crush_specs]:
  shows \<open>\<Gamma>; result_err res \<Turnstile>\<^sub>F result_err_contract res\<close>
  by (crush_boot f: result_err_def contract: result_err_contract_def)
     (crush_base split: result.splits)

subsection\<open>expect\<close>

text\<open>Returns \<^verbatim>\<open>x\<close> if the element of \<^verbatim>\<open>Result\<close> type is of the form \<^verbatim>\<open>Ok x\<close>. Panics otherwise with
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
     (crush_base split: result.splits)

subsection\<open>expect_err\<close>

text\<open>Returns \<^verbatim>\<open>x\<close> if the element of \<^verbatim>\<open>Result\<close> type is of the form \<^verbatim>\<open>Err x\<close>. Panics otherwise with
the defined error message.\<close>

definition result_expect_err :: \<open>('v, 'e) result \<Rightarrow> String.literal \<Rightarrow> ('s, 'e, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_expect_err self msg \<equiv> FunctionBody \<lbrakk>
      match self {
        Ok(_) \<Rightarrow> panic!(msg),
        Err(e) \<Rightarrow> e 
      }
  \<rbrakk>\<close>

definition result_expect_err_contract :: 
  \<open>('a, 'e) result \<Rightarrow> 'e \<Rightarrow> ('s::{sepalg}, 'e, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_expect_err_contract self e \<equiv>
    let pre = \<langle>self = Err e\<rangle>; post = \<lambda>r. \<langle>r = e\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_expect_err_contract

lemma result_expect_err_spec [crush_specs]:
  shows \<open>\<Gamma>; result_expect_err res m \<Turnstile>\<^sub>F result_expect_err_contract res e\<close>
  by (crush_boot f: result_expect_err_def contract: result_expect_err_contract_def)
     (crush_base split: result.splits)

subsection\<open>flatten\<close>

text\<open>Takes a type \<^verbatim>\<open>Result\<close> that contains another \<^verbatim>\<open>Result\<close> in its \<^verbatim>\<open>Ok\<close> constructor and 
returns the inner result on the \<^verbatim>\<open>Ok\<close> branch, otherwise returns self.\<close>

definition result_flatten :: 
\<open>(('v, 'e) result, 'e) result \<Rightarrow> ('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_flatten self \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> v,
      Err(e) \<Rightarrow> Err(e)
    }
  \<rbrakk>\<close>

definition result_flatten_contract ::
  \<open>(('v, 'e) result, 'e) result \<Rightarrow> ('s::{sepalg}, ('v, 'e) result, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_flatten_contract self \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case self of Ok v \<Rightarrow> v | Err e \<Rightarrow> Err e)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_flatten_contract

lemma result_flatten_spec [crush_specs]:
  shows \<open>\<Gamma>; result_flatten self \<Turnstile>\<^sub>F result_flatten_contract self\<close>
  by (crush_boot f: result_flatten_def contract: result_flatten_contract_def)
  (crush_base split: result.splits)

subsection\<open>inspect\<close>

text\<open>Applies a function to the contained value if \<^verbatim>\<open>Result\<close> is \<^verbatim>\<open>Ok\<close>,
then returns the original \<^verbatim>\<open>Result\<close> unchanged.\<close>

definition result_inspect :: \<open>('v, 'e) result \<Rightarrow> 
('v \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
 \<open>result_inspect self f \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> {
                  f(v);
                  Ok(v)
                },
      Err(e) \<Rightarrow> Err(e)
    }
  \<rbrakk>\<close>

definition result_inspect_contract ::
  \<open>('v, 'e) result \<Rightarrow> ('v \<Rightarrow> 'f) \<Rightarrow> ('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('v \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('s, ('v, 'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_inspect_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = self\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_inspect_contract

lemma result_inspect_spec [crush_specs]:
  shows \<open>\<Gamma>; result_inspect self rust_fun \<Turnstile>\<^sub>F result_inspect_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_inspect_def contract: result_inspect_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  next
    case (Err x2)
    then show ?thesis by crush_base
  qed
qed

subsection\<open>inspect_err\<close>

text\<open>Applies a function to the contained error if \<^verbatim>\<open>Result\<close> is \<^verbatim>\<open>Err\<close>,
then returns the original \<^verbatim>\<open>Result\<close> unchanged.\<close>

definition result_inspect_err :: \<open>('v, 'e) result \<Rightarrow> 
('e \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
 \<open>result_inspect_err self f \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> Ok(v),
      Err(e) \<Rightarrow> {
                  f(e);
                  Err(e)
                }
    }
  \<rbrakk>\<close>

definition result_inspect_err_contract ::
  \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('e \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('s, ('v, 'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_inspect_err_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = self\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_inspect_err_contract

lemma result_inspect_err_spec [crush_specs]:
  shows \<open>\<Gamma>; result_inspect_err self rust_fun \<Turnstile>\<^sub>F result_inspect_err_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_inspect_err_def contract: result_inspect_err_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by crush_base
  next
    case (Err x2)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  qed
qed

subsection\<open>into_err\<close>

text\<open>Returns the value inside the \<^verbatim>\<open>Err\<close> constructor of the \<^verbatim>\<open>Result\<close> type.
The \<^verbatim>\<open>Ok\<close> branch is unreachable and panics.\<close>

definition result_into_err :: \<open>('v, 'e) result \<Rightarrow> ('s, 'e, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_into_err self \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(_)  \<Rightarrow> panic!("result_into_err: This should be unreachable"),
      Err(e) \<Rightarrow> e
    }
  \<rbrakk>\<close>

definition result_into_err_contract :: 
  \<open>('v, 'e) result \<Rightarrow> 'e \<Rightarrow> ('s::{sepalg}, 'e, 'abort) function_contract\<close> 
  where [crush_contracts]: \<open>result_into_err_contract self e \<equiv>
    let pre  = \<langle>self = Err e\<rangle>;
        post = \<lambda>r. \<langle>r = e\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_into_err_contract

lemma result_into_err_spec [crush_specs]:
  shows \<open>\<Gamma>; result_into_err self \<Turnstile>\<^sub>F result_into_err_contract self e\<close>
  by (crush_boot f: result_into_err_def contract: result_into_err_contract_def)
     (crush_base)

subsection\<open>into_ok\<close>

text\<open>Returns the value inside the \<^verbatim>\<open>Ok\<close> constructor of the \<^verbatim>\<open>Result\<close> type.
The \<^verbatim>\<open>Err\<close> branch is unreachable and panics.\<close>

definition result_into_ok :: \<open>('v, 'e) result \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_into_ok self \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> v,
      Err(_) \<Rightarrow> panic!("result_into_ok: This should be unreachable")
    }
  \<rbrakk>\<close>

definition result_into_ok_contract :: 
  \<open>('v, 'e) result \<Rightarrow> 'v \<Rightarrow> ('s::{sepalg}, 'v, 'abort) function_contract\<close> 
  where [crush_contracts]: \<open>result_into_ok_contract self v \<equiv>
    let pre  = \<langle>self = Ok v\<rangle>;
        post = \<lambda>r. \<langle>r = v\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_into_ok_contract

lemma result_into_ok_spec [crush_specs]:
  shows \<open>\<Gamma>; result_into_ok self \<Turnstile>\<^sub>F result_into_ok_contract self v\<close>
  by (crush_boot f: result_into_ok_def contract: result_into_ok_contract_def)
     (crush_base)

subsection\<open>is_err\<close>

text\<open>Tests whether an element of \<^verbatim>\<open>Result\<close> type is the \<^verbatim>\<open>Err\<close> constructor:\<close>

definition urust_func_result_is_err :: \<open>('v, 'e) result \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>urust_func_result_is_err self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(_) \<Rightarrow> False,
       Err(_) \<Rightarrow> True
     }
  \<rbrakk>\<close>
micro_rust_notation (call) urust_func_result_is_err ("is_err")

definition result_is_err_contract ::
  \<open>('a, 'e) result \<Rightarrow> ('s::{sepalg}, bool, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_is_err_contract res \<equiv>
    let pre = UNIV; post = \<lambda>r. \<langle>r = result_is_err res\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_is_err_contract

lemma result_is_err_spec [crush_specs]:
  shows \<open>\<Gamma>; urust_func_result_is_err res \<Turnstile>\<^sub>F result_is_err_contract res\<close>
  by (crush_boot f: urust_func_result_is_err_def contract: result_is_err_contract_def)
     (crush_base simp add: result_is_err_def split: result.splits)

subsection\<open>is_err_and\<close>

text\<open>Tests whether an element of \<^verbatim>\<open>Result\<close> type is the \<^verbatim>\<open>Err\<close> constructor 
and matches the supplied predicate.\<close>

definition result_is_err_and :: \<open>('v, 'e) result \<Rightarrow> 
('e \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_is_err_and self f \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(_)  \<Rightarrow> False,
      Err(e) \<Rightarrow> f(e)
    }
  \<rbrakk>\<close>

definition result_is_err_and_contract ::
  \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> ('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('e \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('s, bool, 'abort) function_contract\<close> 
  where [crush_contracts]: \<open>result_is_err_and_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> (pure_fun e) | Ok(v) \<Rightarrow> False)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_is_err_and_contract

lemma result_is_err_and_spec [crush_specs]:
  shows \<open>\<Gamma>; result_is_err_and self rust_fun \<Turnstile>\<^sub>F result_is_err_and_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_is_err_and_def contract: result_is_err_and_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by crush_base
  next
    case (Err x2)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  qed
qed

subsection\<open>is_ok\<close>

text\<open>Tests whether an element of \<^verbatim>\<open>Result\<close> type is the \<^verbatim>\<open>Ok\<close> constructor:\<close>

definition urust_func_result_is_ok :: \<open>('v,'e) result \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>urust_func_result_is_ok self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(_) \<Rightarrow> True,
       Err(_) \<Rightarrow> False
     }
  \<rbrakk>\<close>
micro_rust_notation (call) urust_func_result_is_ok ("is_ok")

definition result_is_ok_contract ::
  \<open>('a, 'e) result \<Rightarrow> ('s::{sepalg}, bool, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_is_ok_contract res \<equiv>
    let pre = UNIV; post = \<lambda>r. \<langle>r = result_is_ok res\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_is_ok_contract

lemma result_is_ok_spec [crush_specs]:
  shows \<open>\<Gamma>; urust_func_result_is_ok res \<Turnstile>\<^sub>F result_is_ok_contract res\<close>
  by (crush_boot f: urust_func_result_is_ok_def contract: result_is_ok_contract_def)
     (crush_base simp add: result_is_ok_def split: result.splits)

subsection\<open>is_ok_and\<close>

text\<open>Tests whether an element of \<^verbatim>\<open>Result\<close> type is the \<^verbatim>\<open>Ok\<close> constructor 
and matches the supplied predicate.\<close>

definition result_is_ok_and :: \<open>('v, 'e) result \<Rightarrow> 
('v \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_is_ok_and self f \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> f(v),
      Err(_) \<Rightarrow> False
    }
  \<rbrakk>\<close>

definition result_is_ok_and_contract ::
  \<open>('v, 'e) result \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('s, bool, 'abort) function_contract\<close> 
  where [crush_contracts]: \<open>result_is_ok_and_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> False | Ok(v) \<Rightarrow> (pure_fun v))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_is_ok_and_contract

lemma result_is_ok_and_spec [crush_specs]:
  shows \<open>\<Gamma>; result_is_ok_and self rust_fun \<Turnstile>\<^sub>F result_is_ok_and_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_is_ok_and_def contract: result_is_ok_and_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  next
    case (Err x2)
    then show ?thesis by crush_base
  qed
qed

subsection\<open>iter\<close>

text\<open>Returns an iterator over the possibly contained value, yielding \<^verbatim>\<open>Ok\<close>'s payload as a
single element, or nothing for \<^verbatim>\<open>Err\<close>.\<close>

definition result_iter :: \<open>('v, 'e) result \<Rightarrow>
  ('s, ('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_iter self \<equiv> FunctionBody \<lbrakk>
    \<llangle>make_iterator_from_list (case self of Ok v \<Rightarrow> [v] | Err _ \<Rightarrow> [])\<rrangle>
  \<rbrakk>\<close>

definition result_iter_contract :: \<open>('v, 'e) result \<Rightarrow>
  ('s::{sepalg}, ('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_iter_contract self \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = make_iterator_from_list (case self of Ok v \<Rightarrow> [v] | Err _ \<Rightarrow> [])\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_iter_contract

lemma result_iter_spec [crush_specs]:
  shows \<open>\<Gamma>; result_iter self \<Turnstile>\<^sub>F result_iter_contract self\<close>
  by (crush_boot f: result_iter_def contract: result_iter_contract_def) crush_base

subsection\<open>iter_mut\<close>

text\<open>Returns a mutable iterator over the possibly contained value, yielding \<^verbatim>\<open>Ok\<close>'s payload as a
mutable reference to the single element, or nothing for \<^verbatim>\<open>Err\<close>.\<close>

context reference
begin

definition result_iter_mut :: \<open>('a, 'b, ('v, 'e) result) ref \<Rightarrow>
  ('s, ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_iter_mut self \<equiv> FunctionBody \<lbrakk>
    match *self {
      Ok(_)  \<Rightarrow> \<llangle>make_iterator_from_list [(focus_result_ok self)]\<rrangle>,
      Err(_) \<Rightarrow> \<llangle>make_iterator_from_list []\<rrangle>
    }
  \<rbrakk>\<close>

definition result_iter_mut_contract :: \<open>'b \<Rightarrow> ('a, 'b, ('v, 'e) result) ref \<Rightarrow> ('v, 'e) result \<Rightarrow>
  ('s::{sepalg}, ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_iter_mut_contract g self opt \<equiv>
    let pre  = self \<mapsto>\<langle>\<top>\<rangle> g\<down>opt;
        post = \<lambda>res. self \<mapsto>\<langle>\<top>\<rangle> g\<down>opt \<star> 
          \<langle>res = (case opt of 
            Ok _  \<Rightarrow> make_iterator_from_list [focus_focused result_ok_focus self] | 
            Err _ \<Rightarrow> make_iterator_from_list [])\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_iter_mut_contract

lemma result_iter_mut_spec [crush_specs]:
  shows \<open>\<Gamma>; result_iter_mut self \<Turnstile>\<^sub>F result_iter_mut_contract g self opt\<close>
  by (crush_boot f: result_iter_mut_def contract: result_iter_mut_contract_def)
     (crush_base split: result.splits)

end

subsection\<open>map\<close>

text\<open>Maps a function to the \<^verbatim>\<open>Ok\<close> constructor of the \<^verbatim>\<open>Result\<close> type.\<close>

definition result_map :: \<open>('v, 'e) result \<Rightarrow> ('v \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('s, ('f, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_map self f \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(v)  \<Rightarrow> Ok(f(v)),
       Err(e) \<Rightarrow> Err(e)
     }
  \<rbrakk>\<close>

definition result_map_contract :: \<open>('v, 'e) result \<Rightarrow> ('v \<Rightarrow> 'f) \<Rightarrow> 
('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
('v \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('s, ('f, 'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_map_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> Err(e) | Ok(v) \<Rightarrow> Ok(pure_fun v))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_map_contract

lemma result_map_spec [crush_specs]:
  shows \<open>\<Gamma>; result_map self rust_fun \<Turnstile>\<^sub>F result_map_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_map_def contract: result_map_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  next
    case (Err x2)
    then show ?thesis by crush_base
  qed
qed

subsection\<open>map_err\<close>

text\<open>Maps a function to the \<^verbatim>\<open>Err\<close> constructor of the \<^verbatim>\<open>Result\<close> type.\<close>

definition result_map_err :: \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('s, ('v, 'f) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_map_err self f \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(v)  \<Rightarrow> Ok(v),
       Err(e) \<Rightarrow> Err(f(e))
     }
  \<rbrakk>\<close>

definition result_map_err_contract :: \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> 
('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
('e \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('s, ('v, 'f) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_map_err_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> Err(pure_fun e) | Ok(v) \<Rightarrow> Ok(v))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_map_err_contract

lemma result_map_err_spec [crush_specs]:
  shows \<open>\<Gamma>; result_map_err self rust_fun \<Turnstile>\<^sub>F result_map_err_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_map_err_def contract: result_map_err_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by crush_base
  next
    case (Err x2)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  qed
qed

subsection\<open>map_or\<close>

text\<open>Applies a function to the contained value if \<^verbatim>\<open>Result\<close> is \<^verbatim>\<open>Ok\<close> and returns the resulting value.
Else, if \<^verbatim>\<open>Result\<close> is \<^verbatim>\<open>Err\<close>, returns the supplied default value.\<close>

definition result_map_or :: \<open>('v, 'e) result \<Rightarrow> 'f \<Rightarrow>
    ('v \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('s, 'f, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_map_or self d f \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(v)  \<Rightarrow> f(v),
       Err(_) \<Rightarrow> d
     }
  \<rbrakk>\<close>

definition result_map_or_contract :: \<open>('v, 'e) result \<Rightarrow> 'f \<Rightarrow> ('v \<Rightarrow> 'f) \<Rightarrow> 
('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
('v \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('s, 'f, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_map_or_contract self d pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> d | Ok(v) \<Rightarrow> pure_fun v)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_map_or_contract

lemma result_map_or_spec [crush_specs]:
  shows \<open>\<Gamma>; result_map_or self d rust_fun \<Turnstile>\<^sub>F result_map_or_contract self d pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_map_or_def contract: result_map_or_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  next
    case (Err x2)
    then show ?thesis by crush_base
  qed
qed

subsection\<open>map_or_default\<close>

text\<open>Default values are not implemented for µRust types, therefore result_map_or is the closest
functional equivalent and should be used in place of result_map_or_default.\<close>

subsection\<open>map_or_else\<close>

text\<open>Applies a function to the contained value if \<^verbatim>\<open>Result\<close> is \<^verbatim>\<open>Ok\<close> and returns the resulting value.
Else, if \<^verbatim>\<open>Result\<close> is \<^verbatim>\<open>Err\<close>, same as for \<^verbatim>\<open>Ok\<close> but with another function for the contained \<^verbatim>\<open>Err\<close> value.\<close>

definition result_map_or_else :: \<open>('v, 'e) result \<Rightarrow>
    ('e \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('v \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('s, 'f, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_map_or_else self d f \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(v)  \<Rightarrow> f(v),
       Err(e) \<Rightarrow> d(e)
     }
  \<rbrakk>\<close>

definition result_map_or_else_contract :: \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('v \<Rightarrow> 'f) \<Rightarrow> 
('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
('e \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('v \<Rightarrow> ('s, 'f, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('s, 'f, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_map_or_else_contract self pure_fun_def pure_fun \<Gamma> rust_fun_def rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle> \<star>
               \<langle>\<forall> j. \<Gamma>; rust_fun_def j \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun_def j)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> pure_fun_def e | Ok(v) \<Rightarrow> pure_fun v)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_map_or_else_contract

lemma result_map_or_else_spec [crush_specs]:
  shows \<open>\<Gamma>; result_map_or_else self rust_fun_def rust_fun \<Turnstile>\<^sub>F 
            result_map_or_else_contract self pure_fun_def pure_fun \<Gamma> rust_fun_def rust_fun\<close>
proof (crush_boot f: result_map_or_else_def contract: result_map_or_else_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  next
    case (Err x2)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  qed
qed

subsection\<open>ok\<close>

text\<open>Converts a \<^verbatim>\<open>Result\<close> type into a \<^verbatim>\<open>Option\<close> type where only the ok constructor 
is kept while err is discarded.\<close>

definition result_ok :: \<open>('v, 'e) result \<Rightarrow> ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_ok self \<equiv> FunctionBody \<lbrakk>
     match self {
       Ok(r) \<Rightarrow> Some(r),
       Err(e) \<Rightarrow> None
     }
   \<rbrakk>\<close>

definition result_ok_contract ::  \<open>('v, 'e) result \<Rightarrow> ('s::{sepalg}, 'v option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_ok_contract res \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case res of Err(_) \<Rightarrow> None | Ok(k) \<Rightarrow> Some k)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_ok_contract

lemma result_ok_spec [crush_specs]:
  shows \<open>\<Gamma>; result_ok res \<Turnstile>\<^sub>F result_ok_contract res\<close>
  by (crush_boot f: result_ok_def contract: result_ok_contract_def)
     (crush_base split: result.splits)

subsection\<open>or\<close>

text\<open>Returns first argument of type \<^verbatim>\<open>Result\<close> if it is the \<^verbatim>\<open>Ok\<close> constructor, returns the 
second argument of type \<^verbatim>\<open>Result\<close> otherwise.\<close>

definition result_or :: \<open>('a, 'f) result \<Rightarrow> ('a, 'e) result \<Rightarrow> ('s, ('a, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_or self e \<equiv> FunctionBody \<lbrakk>
     match self {
        Ok(v) \<Rightarrow> Ok(v),
        Err(_) \<Rightarrow> e
     } 
  \<rbrakk>\<close>
micro_rust_notation (call) result_or ("or")

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
     (crush_base simp add: result_or_pure_def split: result.splits)

subsection\<open>or_else\<close>

text\<open>Returns self if \<^verbatim>\<open>Result\<close> is of the \<^verbatim>\<open>Ok\<close> constructor, else applies the supplied function
to the value of \<^verbatim>\<open>Err\<close> and returns a type \<^verbatim>\<open>Result\<close>.\<close>

definition result_or_else :: \<open>('v, 'e) result \<Rightarrow>
  ('e \<Rightarrow> ('s, ('v, 'e) result, 'abort, 'i, 'o) function_body) \<Rightarrow>
  ('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_or_else self op \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> Ok(v),
      Err(e) \<Rightarrow> op(e)
    }
  \<rbrakk>\<close>

definition result_or_else_contract :: \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> ('v, 'e) result) \<Rightarrow> 
('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
('e \<Rightarrow> ('s, ('v, 'e) result, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
('s, ('v, 'e) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_or_else_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> pure_fun e | Ok(v) \<Rightarrow> Ok(v))\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_or_else_contract

lemma result_or_else_spec [crush_specs]:
  shows \<open>\<Gamma>; result_or_else self rust_fun \<Turnstile>\<^sub>F result_or_else_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_or_else_def contract: result_or_else_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by crush_base
  next
    case (Err x2)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  qed
qed

subsection\<open>transpose\<close>

text\<open>Takes a type \<^verbatim>\<open>Result\<close> that matches either an \<^verbatim>\<open>Ok\<close> constructor
 with a value of type \<^verbatim>\<open>Option\<close> or an \<^verbatim>\<open>Err\<close> constructor with any value. 
Returns a type \<^verbatim>\<open>Option\<close> with a value of type \<^verbatim>\<open>Result\<close>, except in the case
 where the input \<^verbatim>\<open>Option\<close> matched the \<^verbatim>\<open>None\<close> constructor, in which case returns \<^verbatim>\<open>None\<close>.
Other than the \<^verbatim>\<open>None\<close> case, the value of the inner \<^verbatim>\<open>Option\<close> is transposed into the inner \<^verbatim>\<open>Result\<close>.\<close>

definition result_transpose :: \<open>(('v) option, 'e) result \<Rightarrow>
('s, (('v, 'e) result) option, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_transpose self \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(Some(x)) \<Rightarrow> Some(Ok(x)),
      Ok(None) \<Rightarrow> None,
      Err(e) \<Rightarrow> Some(Err(e))
    }
  \<rbrakk>\<close>

definition result_transpose_contract :: \<open>(('v) option, 'e) result \<Rightarrow>
  ('s::{sepalg}, (('v, 'e) result) option, 'abort) function_contract\<close> 
  where [crush_contracts]: \<open>result_transpose_contract self \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case self of 
          Ok(Some(x)) \<Rightarrow> Some(Ok(x)) |
          Ok(None)    \<Rightarrow> None |
          Err(e)      \<Rightarrow> Some(Err(e)) )\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_transpose_contract

lemma result_transpose_spec [crush_specs]:
  shows \<open>\<Gamma>; result_transpose self \<Turnstile>\<^sub>F result_transpose_contract self\<close>
proof (crush_boot f: result_transpose_def contract: result_transpose_contract_def, goal_cases)
  case 1
  then show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis 
     proof (cases x1)
       case None
       with Ok show ?thesis by crush_base
     next
       case (Some a)
       with Ok show ?thesis by crush_base
     qed
  next
    case (Err x2)
    then show ?thesis by crush_base
  qed
qed

(*
The above is left explicit for the reader, the Ok x1 can be proven by (cases x1; crush_base).
*)

subsection\<open>unwrap\<close>

text\<open>Returns \<^verbatim>\<open>x\<close> if the element of type \<^verbatim>\<open>Result\<close> is of the form \<^verbatim>\<open>Ok x\<close>.  Panics otherwise.\<close>

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
     (crush_base split: result.splits)

subsection\<open>unwrap_err\<close>

text\<open>Returns \<^verbatim>\<open>x\<close> if the element of type \<^verbatim>\<open>Result\<close> is of form \<^verbatim>\<open>Err x\<close>, otherwise panics.\<close>

definition result_unwrap_err :: \<open>('v, 'e) result \<Rightarrow> ('s, 'e, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_unwrap_err self \<equiv> FunctionBody \<lbrakk>
    result_expect_err(self, "result_unwrap_err")
  \<rbrakk>\<close>

(*
Note that should expect_err be added to the Core_Syntax consts, then the above could be refactored
to match result_unwrap.
*)

definition result_unwrap_err_contract ::
  \<open>('v, 'e) result \<Rightarrow> 'e \<Rightarrow> ('s::{sepalg}, 'e, 'abort) function_contract\<close>
  where [crush_contracts]: \<open>result_unwrap_err_contract self e \<equiv>
    let pre = \<langle>self = Err e\<rangle>; post = \<lambda>r. \<langle>r = e\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_unwrap_err_contract

lemma result_unwrap_err_spec [crush_specs]:
  shows \<open>\<Gamma>; result_unwrap_err self \<Turnstile>\<^sub>F result_unwrap_err_contract self e\<close>
  by (crush_boot f: result_unwrap_err_def contract: result_unwrap_err_contract_def)
     (crush_base split: result.splits)

subsection\<open>unwrap_err_unchecked\<close>

text\<open>Unimplemented as this method is functionally identical to unwrap_err in µRust / HOL.\<close>

subsection\<open>unwrap_or\<close>

text\<open>Returns the \<^verbatim>\<open>Ok\<close> constructor of \<^verbatim>\<open>Result\<close> or the provided default, 
dependant on the content of \<^verbatim>\<open>Result\<close>.\<close>

definition result_unwrap_or :: \<open>('a, 'b) result \<Rightarrow> 'a \<Rightarrow> ('s, 'a, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>result_unwrap_or res e \<equiv> FunctionBody \<lbrakk>
     match res {
      Ok(r) \<Rightarrow> r,
      Err(_) \<Rightarrow> e
    }
   \<rbrakk>\<close>

definition result_unwrap_or_contract ::  \<open>('a, 'b) result \<Rightarrow> 'a \<Rightarrow> ('s::{sepalg}, 'a, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_unwrap_or_contract res e \<equiv>
    let pre  = UNIV;
        post = \<lambda>r. \<langle>r = (case res of Ok(v) \<Rightarrow> v | Err(_) \<Rightarrow> e)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_unwrap_or_contract

lemma result_unwrap_or_spec [crush_specs]:
  shows \<open>\<Gamma>; result_unwrap_or res e \<Turnstile>\<^sub>F result_unwrap_or_contract res e\<close>
  by (crush_boot f: result_unwrap_or_def contract: result_unwrap_or_contract_def)
     (crush_base split: result.splits)

subsection\<open>unwrap_or_default\<close>

text\<open>Default values are not implemented for µRust types, therefore unwrap_or is the closest
functional equivalent and should be used in place of unwrap_or_default.\<close>

subsection\<open>unwrap_or_else\<close>

text\<open>Returns the \<^verbatim>\<open>Ok\<close> value of \<^verbatim>\<open>Result\<close>, or applies the supplied function
to the \<^verbatim>\<open>Err\<close> value and returns the result.\<close>

definition result_unwrap_or_else :: \<open>('v, 'e) result \<Rightarrow> 
  ('e \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body) \<Rightarrow>
  ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_unwrap_or_else self f \<equiv> FunctionBody \<lbrakk>
    match self {
      Ok(v)  \<Rightarrow> v,
      Err(e) \<Rightarrow> f(e)
    }
  \<rbrakk>\<close>

definition result_unwrap_or_else_contract :: \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> 'v) \<Rightarrow> 
  ('s::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('e \<Rightarrow> ('s, 'v, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('s, 'v, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>result_unwrap_or_else_contract self pure_fun \<Gamma> rust_fun \<equiv>
    let pre  = \<langle>\<forall> i. \<Gamma>; rust_fun i \<Turnstile>\<^sub>F lift_pure_to_contract (pure_fun i)\<rangle>;
        post = \<lambda>r. \<langle>r = (case self of Err(e) \<Rightarrow> pure_fun e | Ok(v) \<Rightarrow> v)\<rangle>
    in make_function_contract pre post\<close>
ucincl_auto result_unwrap_or_else_contract

lemma result_unwrap_or_else_spec [crush_specs]:
  shows \<open>\<Gamma>; result_unwrap_or_else self rust_fun \<Turnstile>\<^sub>F result_unwrap_or_else_contract self pure_fun \<Gamma> rust_fun\<close>
proof (crush_boot f: result_unwrap_or_else_def contract: result_unwrap_or_else_contract_def, goal_cases)
  case 1
  note rust_fun_spec = this[THEN spec]
  show ?case
  proof (cases self)
    case (Ok x1)
    then show ?thesis by crush_base
  next
    case (Err x2)
    then show ?thesis by (crush_base specs add: rust_fun_spec)
  qed
qed

subsection\<open>unwrap_unchecked\<close>

text\<open>Unimplemented as this method is functionally identical to unwrap in µRust / HOL.\<close>

section\<open>Debug\<close>

instantiation result :: (generate_debug,generate_debug)generate_debug
begin

fun generate_debug_result :: \<open>('a, 'b) result \<Rightarrow> log_data\<close> where
  \<open>generate_debug_result (Ok  k) = str ''Ok(''#generate_debug k@[str '')'']\<close> |
  \<open>generate_debug_result (Err e) = str ''Err(''#generate_debug e@[str '')'']\<close>

instance ..

end

end
(*>*)