(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Slice
  imports Crush.Crush StdLib_References StdLib_Logging
begin
(*>*)

definition range_new_contract :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('s::sepalg, 'a range, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>range_new_contract b e \<equiv>
     let pre  = \<langle>True\<rangle>;
         post = \<lambda>r. \<langle>r = make_range b e\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto range_new_contract

lemma range_new_spec [crush_specs]:
  shows \<open>\<Gamma> ; range_new b e \<Turnstile>\<^sub>F range_new_contract b e\<close>
  apply (crush_boot f: range_new_def contract: range_new_contract_def simp: fun_literal_def)
  apply crush_base
  done

definition list_index_contract where [crush_contracts]:
  \<open>list_index_contract lst idx \<equiv>
     let pre = \<langle>unat idx < length lst\<rangle> in
     let post = \<lambda>r. \<langle>r = lst ! (unat idx)\<rangle> in
       make_function_contract pre post\<close>
ucincl_auto list_index_contract

lemma list_index_spec [crush_specs]:
  shows \<open>\<Gamma> ; list_index lst idx \<Turnstile>\<^sub>F list_index_contract lst idx\<close>
  apply (crush_boot f: list_index_def contract: list_index_contract_def)
  apply (crush_base simp add: nth_opt_spec)
  done

definition array_index_contract where [crush_contracts]:
  \<open>array_index_contract (lst :: ('a, 'l::len) array) idx \<equiv>
     let pre = \<langle>unat idx < LENGTH('l)\<rangle> in
     let post = \<lambda>r. \<langle>r = array_nth lst (unat idx)\<rangle> in
       make_function_contract pre post\<close>
ucincl_auto array_index_contract

lemma array_index_spec [crush_specs]:
  shows \<open>\<Gamma> ; array_index lst idx \<Turnstile>\<^sub>F array_index_contract lst idx\<close>
  by (crush_boot f: array_index_def contract: array_index_contract_def) crush_base

context reference begin

definition slice_index :: \<open>('a, 'b, 'v list) ref \<Rightarrow> 'w::{len} word \<Rightarrow>
        ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_index r i \<equiv> FunctionBody \<lbrakk>
     let ls = *r;
     if \<llangle>unat i\<rrangle> < \<llangle>length\<rrangle>\<^sub>1(ls) {
        return \<llangle>focus_nth (unat i) r\<rrangle>;
     };
     \<epsilon>\<open>abort DanglingPointer\<close>
  \<rbrakk>\<close>

definition slice_index_contract :: \<open>(('a, 'b) gref, 'b, 'c list) focused \<Rightarrow> 'b \<Rightarrow> 'c list \<Rightarrow>
      'd::{len} word \<Rightarrow> share \<Rightarrow> ('s, (('a, 'b) gref, 'b, 'c) focused, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_index_contract ptr g ls idx sh \<equiv>
    let pre = ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star>
              \<langle>unat idx < length ls\<rangle> in
    let post = \<lambda>r. (ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star> \<langle>r = focus_nth (unat idx) ptr\<rangle>) in
      make_function_contract pre post\<close>
ucincl_auto slice_index_contract

lemma slice_index_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_index ptr idx \<Turnstile>\<^sub>F slice_index_contract ptr g ls idx sh\<close>
  apply (crush_boot f: slice_index_def contract: slice_index_contract_def)
  apply crush_base
  done

definition slice_index_array ::
  \<open>('a, 'b, ('v, 'l::{len}) array) ref \<Rightarrow> 'w::{len} word \<Rightarrow> ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where \<open>slice_index_array r idx \<equiv> FunctionBody (
     if unat idx < LENGTH('l) then
         literal (focus_nth_array (unat idx) r)
       else
         abort DanglingPointer)\<close>

definition slice_index_array_contract :: \<open>(('a, 'b) gref, 'b, ('t, 'l::{len}) array) focused \<Rightarrow> 'b \<Rightarrow>
      ('t, 'l) array \<Rightarrow> 'c::{len} word \<Rightarrow> share \<Rightarrow> ('s, (('a, 'b) gref, 'b, 't) focused, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_index_array_contract ptr g ls idx sh \<equiv>
    let pre = ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star>
              \<langle>unat idx < LENGTH('l)\<rangle> in
    let post = \<lambda>r. (ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star> \<langle>r = focus_nth_array (unat idx) ptr\<rangle>) in
      make_function_contract pre post\<close>
ucincl_auto slice_index_array_contract

lemma slice_index_array_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_index_array ptr idx \<Turnstile>\<^sub>F slice_index_array_contract ptr g ls idx sh\<close>
  apply (crush_boot f: slice_index_array_def contract: slice_index_array_contract_def)
  apply crush_base
  done

definition slice_index_vector :: \<open>('a, 'b, ('v, 'l::{len}) vector) ref \<Rightarrow> 'w::{len} word \<Rightarrow>
      ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_index_vector r idx \<equiv> FunctionBody \<lbrakk>
     let v = *r;
     if \<llangle>unat idx\<rrangle> < \<llangle>vector_len v\<rrangle> {
        return \<llangle>focus_nth_vector (unat idx) r\<rrangle>;
     };
     \<epsilon>\<open>abort DanglingPointer\<close>
  \<rbrakk>\<close>

definition slice_index_vector_contract :: \<open>(('a, 'b) gref, 'b, ('t, 'l::{len}) vector) focused \<Rightarrow> 'b \<Rightarrow>
      ('t, 'l) vector \<Rightarrow> 'c::{len} word \<Rightarrow> share \<Rightarrow> ('s, (('a, 'b) gref, 'b, 't) focused, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_index_vector_contract ptr g ls idx sh \<equiv>
    let pre = ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star>
              \<langle>unat idx < vector_len ls\<rangle> in
    let post = \<lambda>r. (ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star> \<langle>r = focus_nth_vector (unat idx) ptr\<rangle>) in
      make_function_contract pre post\<close>
ucincl_auto slice_index_vector_contract

lemma slice_index_vector_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_index_vector ptr idx \<Turnstile>\<^sub>F slice_index_vector_contract ptr g ls idx sh\<close>
  apply (crush_boot f: slice_index_vector_def contract: slice_index_vector_contract_def)
  apply crush_base
  done

\<comment>\<open>TODO: The subrange focus is not valid, and with focus validity baked into the focus type,
the following does not work anymore. Once we actually use subrange slices, this needs to be
revisited.\<close>
(*
definition slice_index_range :: \<open>('a, 'b, 'v list) ref \<Rightarrow> 'w::{len} word range \<Rightarrow>
    ('s, ('a, 'b, 'v list) ref, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_index_range r rng \<equiv> FunctionBody (
    bind (call (dereference_fun r)) (\<lambda>xs.
    case rng of
      Range s e \<Rightarrow>
        if s \<ge> e then
          literal (ref_subrange 0 0 r)
        else
          if unat e \<le> length xs then
            literal (ref_subrange (unat s) (unat (e - s)) r)
          else
            Expression (\<lambda>\<sigma>. Abort DanglingPointer)
    | RangeEq s e \<Rightarrow>
        if s > e then
          literal (ref_subrange 0 0 r)
        else
          if unat e < length xs then
            literal (ref_subrange (unat s) (1 + unat (e - s)) r)
          else
            Expression (\<lambda>\<sigma>. Abort DanglingPointer)
  ))\<close>
*)

definition list_index_range_contract :: \<open>'t list \<Rightarrow> 'w::{len} word range \<Rightarrow> ('s, 't list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>list_index_range_contract xs r \<equiv>
     let pre  = \<langle>unat (end r) \<le> length xs\<rangle>;
         post = \<lambda>res.
                  if start r \<ge> end r then
                    \<langle>res = []\<rangle>
                  else
                    \<langle>res = List.take (unat (end r - start r)) (List.drop (unat (start r)) xs)\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto list_index_range_contract

lemma list_index_range_spec [crush_specs]:
  shows \<open>\<Gamma> ; list_index_range xs r \<Turnstile>\<^sub>F list_index_range_contract xs r\<close>
by (crush_boot f: list_index_range_def contract: list_index_range_contract_def)
     (crush_base split!: range.splits)

adhoc_overloading index_const \<rightleftharpoons>
  slice_index
  slice_index_array
  slice_index_vector
  \<comment>\<open>TODO: Add back in once subrange slices are working again: \<^verbatim>\<open>slice_index_range\<close>\<close>

(*<*)
end
(*>*)

subsection\<open>Debug printing\<close>

instantiation range :: (generate_debug)generate_debug
begin

fun generate_debug_range :: \<open>'a range \<Rightarrow> log_data\<close> where
  \<open>generate_debug_range r =
     str ''(''#generate_debug (start r)@[str ''..<'']@generate_debug (end r)@[str '')'']\<close>

instance ..

end

(*<*)
end
(*>*)