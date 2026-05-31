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
         post = \<lambda>r. \<langle>r = make_range b e False\<rangle>
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

adhoc_overloading store_update_const \<rightleftharpoons> update_fun

definition slice_index :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'w::{len} word \<Rightarrow>
        ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
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
  \<open>('a, 'b, ('v, 'l::{len}) array) Global_Store.ref \<Rightarrow> 'w::{len} word \<Rightarrow> ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
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

definition slice_index_vector :: \<open>('a, 'b, ('v, 'l::{len}) vector) Global_Store.ref \<Rightarrow> 'w::{len} word \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
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
definition slice_index_range :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'w::{len} word range \<Rightarrow>
    ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i, 'o) function_body\<close> where
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
     let pre  = \<langle>start r \<le> end r \<and>
                     (end_inclusive r \<longrightarrow> unat (end r) < length xs) \<and>
                     (\<not> end_inclusive r \<longrightarrow> unat (end r) \<le> length xs)\<rangle>;
         post = \<lambda>res. \<langle>(end_inclusive r \<longrightarrow>
                             res = List.take (Suc (unat (end r) - unat (start r)))
                               (List.drop (unat (start r)) xs)) \<and>
                            (\<not> end_inclusive r \<longrightarrow>
                             res = List.take (unat (end r) - unat (start r))
                               (List.drop (unat (start r)) xs))\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto list_index_range_contract

lemma list_index_range_spec [crush_specs]:
  shows \<open>\<Gamma> ; list_index_range xs r \<Turnstile>\<^sub>F list_index_range_contract xs r\<close>
  by (crush_boot f: list_index_range_def contract: list_index_range_contract_def)
     (crush_base split!: range.splits; simp)

adhoc_overloading index_const \<rightleftharpoons>
  slice_index
  slice_index_array
  slice_index_vector
  \<comment>\<open>TODO: Add back in once subrange slices are working again: \<^verbatim>\<open>slice_index_range\<close>\<close>

definition slice_len :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_len r \<equiv> FunctionBody \<lbrakk>
    let ls = *r;
    \<llangle>length ls\<rrangle>
\<rbrakk>\<close>

definition slice_len_contract :: \<open>(('a, 'b) gref, 'b, 'c list) focused \<Rightarrow> 'b \<Rightarrow> 'c list \<Rightarrow>
      share \<Rightarrow> ('s, nat, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_len_contract ptr g ls sh \<equiv>
    let pre = ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls in
    let post = \<lambda>r. ptr \<mapsto>\<langle>sh\<rangle> g\<down>ls \<star> \<langle> r = length ls\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto slice_len_contract

lemma slice_len_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_len ptr  \<Turnstile>\<^sub>F slice_len_contract ptr g ls sh\<close>
  apply (crush_boot f: slice_len_def contract: slice_len_contract_def)
  apply crush_base
  done

micro_rust_notation (call) slice_len ("len")

definition slice_len_array :: \<open>('a, 'b, ('v, 'l::{len}) array) Global_Store.ref \<Rightarrow>
      ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_len_array arr \<equiv> FunctionBody (literal LENGTH('l))\<close>

definition slice_len_array_contract :: \<open>(('a, 'b) gref, 'b, ('t, 'l::{len}) array) focused \<Rightarrow> 'b \<Rightarrow>
      ('t, 'l) array \<Rightarrow> share \<Rightarrow> ('s, nat, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_len_array_contract ptr g arr sh \<equiv>
    let pre = ptr \<mapsto>\<langle>sh\<rangle> g\<down>arr in
    let post = \<lambda>r. ptr \<mapsto>\<langle>sh\<rangle> g\<down>arr \<star> \<langle> r = LENGTH('l)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto slice_len_array_contract

lemma slice_len_spec_array [crush_specs]:
  shows \<open>\<Gamma> ; slice_len_array ptr  \<Turnstile>\<^sub>F slice_len_array_contract ptr g arr sh\<close>
  apply (crush_boot f: slice_len_array_def contract: slice_len_array_contract_def)
  apply crush_base
  done

micro_rust_notation (call) slice_len_array ("len")

definition  slice_len_vector :: \<open>('a, 'b, ('v, 'l::{len}) vector) Global_Store.ref  \<Rightarrow>
      ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_len_vector vec \<equiv> FunctionBody \<lbrakk>
    let v = *vec;
    return \<llangle>vector_len v\<rrangle>;
\<rbrakk>\<close>

definition slice_len_vector_contract :: \<open>(('a, 'b) gref, 'b, ('t, 'l::{len}) vector) focused \<Rightarrow> 'b \<Rightarrow>
      ('t, 'l) vector \<Rightarrow> share \<Rightarrow> ('s, nat, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_len_vector_contract ptr g vec sh \<equiv>
    let pre = ptr \<mapsto>\<langle>sh\<rangle> g\<down>vec in
    let post = \<lambda>r. ptr \<mapsto>\<langle>sh\<rangle> g\<down>vec \<star> \<langle> r = vector_len vec\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto slice_len_vector_contract

lemma slice_len_spec_vector [crush_specs]:
  shows \<open>\<Gamma> ; slice_len_vector ptr  \<Turnstile>\<^sub>F slice_len_vector_contract ptr g vec sh\<close>
  apply (crush_boot f: slice_len_vector_def contract: slice_len_vector_contract_def)
  apply crush_base
  done

micro_rust_notation (call) slice_len_vector ("len")

definition slice_swap :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_swap r i j \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    let vi = \<llangle>xs ! i\<rrangle>;
    let vj = \<llangle>xs ! j\<rrangle>;
    let xs' =\<llangle>list_update xs i vj\<rrangle>;
    r = \<llangle>list_update xs' j vi\<rrangle>
  \<rbrakk>\<close>

definition slice_swap_contract :: \<open>(('a, 'b) gref, 'b, 'v list) focused \<Rightarrow> 'b \<Rightarrow> 'v list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_swap_contract ptr g ls i j \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>ls \<star> \<langle>i < length ls\<rangle> \<star> \<langle>j < length ls\<rangle> in
    let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. list_update (list_update ls i (ls ! j)) j (ls ! i)) \<sqdot> (g\<down>ls) in
      make_function_contract pre post\<close>
ucincl_auto slice_swap_contract

lemma slice_swap_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_swap ptr i j \<Turnstile>\<^sub>F slice_swap_contract ptr g ls i j\<close>
  apply (crush_boot f: slice_swap_def contract: slice_swap_contract_def) 
  apply crush_base
  done

micro_rust_notation (call) slice_swap ("swap")

definition vec_swap :: \<open>('a, 'b, ('v,'l::{len}) vector) Global_Store.ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
 \<open>vec_swap r i j \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    let vi = \<llangle> vector_nth xs i\<rrangle>;
    let vj = \<llangle>vector_nth xs j\<rrangle>;
    let xs' = \<llangle>vector_update xs i vj\<rrangle>;
    r = \<llangle>vector_update xs' j vi\<rrangle>
  \<rbrakk>\<close>

definition vec_swap_contract ::\<open>(('a, 'b) gref, 'b, ('v,'l) vector) focused \<Rightarrow> 'b \<Rightarrow> ('v,'l::{len}) vector \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>vec_swap_contract ptr g xs i j \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>xs \<star> \<langle>i < vector_len xs\<rangle> \<star> \<langle>j < vector_len xs\<rangle> in
    let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. vector_update (vector_update xs i (vector_nth xs j)) j (vector_nth xs i)) \<sqdot> (g\<down>xs) in
      make_function_contract pre post\<close>
ucincl_auto vec_swap_contract

lemma vec_swap_spec [crush_specs]:
  shows \<open>\<Gamma>; vec_swap ptr i j \<Turnstile>\<^sub>F vec_swap_contract ptr g xs i j\<close>
  apply (crush_boot f: vec_swap_def contract: vec_swap_contract_def)
  apply crush_base
  done

micro_rust_notation (call) vec_swap ("swap")

definition slice_contains :: \<open>'v list \<Rightarrow> 'v \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_contains xs v \<equiv> FunctionBody \<lbrakk>
    \<llangle>v \<in> set xs\<rrangle>
  \<rbrakk>\<close>

definition slice_contains_contract :: \<open>'v list \<Rightarrow> 'v \<Rightarrow>
    ('s::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_contains_contract xs v \<equiv>
    make_function_contract \<top> (\<lambda>r. \<langle>r = (v \<in> set xs)\<rangle>)\<close>
ucincl_auto slice_contains_contract

lemma slice_contains_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_contains xs v \<Turnstile>\<^sub>F slice_contains_contract xs v\<close>
  apply (crush_boot f: slice_contains_def contract: slice_contains_contract_def)
  apply crush_base
  done

micro_rust_notation (call) slice_contains ("contains")

definition vec_contains :: \<open>('a, 'b, ('v,'l::{len}) vector) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_contains r v \<equiv> FunctionBody \<lbrakk>
     let xs = *r;
     \<llangle>v \<in> set (vector_to_list xs)\<rrangle>
   \<rbrakk>\<close>

definition vec_contains_contract :: \<open>(('a, 'b) gref, 'b, ('v,'l::{len}) vector) focused \<Rightarrow> 'b \<Rightarrow>
    ('v,'l) vector \<Rightarrow> 'v \<Rightarrow> share \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>vec_contains_contract ptr g xs v sh \<equiv>
    let pre  = ptr \<mapsto>\<langle>sh\<rangle> g\<down>xs in
    let post = \<lambda>r. ptr \<mapsto>\<langle>sh\<rangle> g\<down>xs \<star> \<langle>r = (v \<in> set (vector_to_list xs))\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto vec_contains_contract

lemma vec_contains_spec [crush_specs]:
  shows\<open>\<Gamma> ; vec_contains ptr v \<Turnstile>\<^sub>F vec_contains_contract ptr g xs v sh\<close>
  apply (crush_boot f: vec_contains_def contract: vec_contains_contract_def)
  apply crush_base
  done

micro_rust_notation (call) vec_contains ("contains")

definition slice_copy_from_slice :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v list \<Rightarrow>
    ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_copy_from_slice dst src \<equiv> FunctionBody \<lbrakk>
    dst = src
  \<rbrakk>\<close>

definition slice_copy_from_slice_contract :: \<open>(('a, 'b) gref, 'b, 'v list) focused \<Rightarrow> 'b \<Rightarrow>
    'v list \<Rightarrow> 'v list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_copy_from_slice_contract dst g dst_ls src_ls \<equiv>
    let pre = dst \<mapsto>\<langle>\<top>\<rangle> g\<down>dst_ls \<star> \<langle>length src_ls = length dst_ls\<rangle> in
    let post = \<lambda>_. dst \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. src_ls) \<sqdot> (g\<down>dst_ls) in
      make_function_contract pre post\<close>
ucincl_auto slice_copy_from_slice_contract

lemma slice_copy_from_slice_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_copy_from_slice dst src \<Turnstile>\<^sub>F slice_copy_from_slice_contract dst g dst_ls src\<close>
  apply (crush_boot f: slice_copy_from_slice_def contract: slice_copy_from_slice_contract_def)
  apply crush_base
  done

micro_rust_notation (call) slice_copy_from_slice ("copy_from_slice")

definition slice_reverse :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
    ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_reverse r \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    r = \<llangle>rev xs\<rrangle>
  \<rbrakk>\<close>

definition slice_reverse_contract :: \<open>(('a, 'b) gref, 'b, 'v list) focused \<Rightarrow> 'b \<Rightarrow>
    'v list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_reverse_contract ptr g ls \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>ls in
    let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. rev ls) \<sqdot> (g\<down>ls) in
      make_function_contract pre post\<close>
ucincl_auto slice_reverse_contract

lemma slice_reverse_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_reverse ptr \<Turnstile>\<^sub>F slice_reverse_contract ptr g ls\<close>
  apply (crush_boot f: slice_reverse_def contract: slice_reverse_contract_def)
  apply crush_base
  done

micro_rust_notation (call) slice_reverse ("reverse")

definition slice_fill :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
    ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_fill r v \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    r = \<llangle>replicate (length xs) v\<rrangle>
  \<rbrakk>\<close>

definition slice_fill_contract :: \<open>(('a, 'b) gref, 'b, 'v list) focused \<Rightarrow> 'b \<Rightarrow>
    'v list \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_fill_contract ptr g ls v \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>ls in
    let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. replicate (length ls) v) \<sqdot> (g\<down>ls) in
      make_function_contract pre post\<close>
ucincl_auto slice_fill_contract

lemma slice_fill_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_fill ptr v \<Turnstile>\<^sub>F slice_fill_contract ptr g ls v\<close>
  by (crush_boot f: slice_fill_def contract: slice_fill_contract_def) crush_base

micro_rust_notation (call) slice_fill ("fill")

definition slice_split_at :: \<open>'v list \<Rightarrow> nat \<Rightarrow>
    ('s, 'v list \<times> 'v list \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_split_at xs mid \<equiv> FunctionBody \<lbrakk>
    (\<llangle>take mid xs\<rrangle>, \<llangle>drop mid xs\<rrangle>)
  \<rbrakk>\<close>

definition slice_split_at_contract :: \<open>'v list \<Rightarrow> nat \<Rightarrow>
    ('s::{sepalg}, 'v list \<times> 'v list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_split_at_contract xs mid \<equiv>
    let pre = \<langle>mid \<le> length xs\<rangle> in
    let post = \<lambda>r. \<langle>r = (take mid xs, drop mid xs, TNil)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto slice_split_at_contract

lemma slice_split_at_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_split_at xs mid \<Turnstile>\<^sub>F slice_split_at_contract xs mid\<close>
  by (crush_boot f: slice_split_at_def contract: slice_split_at_contract_def) crush_base

micro_rust_notation (call) slice_split_at ("split_at")

definition vec_push :: \<open>('a, 'b, ('v, 'l::{len}) vector) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
    ('s, (unit, 'v) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_push r v \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    match \<llangle>vector_push v xs\<rrangle> {
      Some(xs') \<Rightarrow> { r = xs'; Ok(())},
      None \<Rightarrow> Err(v)
    }
  \<rbrakk>\<close>

definition vec_push_contract :: \<open>(('a, 'b) gref, 'b, ('v, 'l::{len}) vector) focused \<Rightarrow> 'b \<Rightarrow>
    ('v, 'l) vector \<Rightarrow> 'v \<Rightarrow> ('s, (unit, 'v) result, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>vec_push_contract ptr g vs v \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>vector_len vs < LENGTH('l)\<rangle> in
    let post = \<lambda>r. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. vector_push_raw v vs) \<sqdot> (g\<down>vs) \<star>
      \<langle>r = Ok ()\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto vec_push_contract

lemma vec_push_spec [crush_specs]:
  shows \<open>\<Gamma> ; vec_push ptr v \<Turnstile>\<^sub>F vec_push_contract ptr g vs v\<close>
  apply (crush_boot f: vec_push_def contract: vec_push_contract_def)
  apply (unfold vector_push_def)
  apply crush_base
done

micro_rust_notation (call) vec_push ("push")

definition vec_pop :: \<open>('a, 'b, ('v, 'l::{len}) vector) Global_Store.ref \<Rightarrow>
    ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_pop r \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    match \<llangle>vector_pop xs\<rrangle> {
      Some(p) \<Rightarrow> { 
        r = \<llangle>snd p\<rrangle>; 
        Some(\<llangle>fst p\<rrangle>)
      },
      None \<Rightarrow> None
  }
  \<rbrakk>\<close>

definition vec_pop_contract :: \<open>(('a, 'b) gref, 'b, ('v, 'l::{len}) vector) focused \<Rightarrow> 'b \<Rightarrow>
    ('v, 'l) vector \<Rightarrow> ('s, 'v option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>vec_pop_contract ptr g vs \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>vector_len vs > 0\<rangle> in
    let post = \<lambda>r. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. snd (the (vector_pop vs))) \<sqdot> (g\<down>vs) \<star>
                   \<langle>r = Some (fst (the (vector_pop vs)))\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto vec_pop_contract

lemma vec_pop_spec [crush_specs]:
  shows \<open>\<Gamma> ; vec_pop ptr \<Turnstile>\<^sub>F vec_pop_contract ptr g vs\<close>
  apply (crush_boot f: vec_pop_def contract: vec_pop_contract_def)
  apply (unfold vector_pop_def)
  apply crush_base
  done


micro_rust_notation (call) vec_pop ("pop")

definition slice_sort :: \<open>('a, 'b, ('v::linorder) list) Global_Store.ref \<Rightarrow>
    ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_sort r \<equiv> FunctionBody \<lbrakk>
    let xs = *r;
    r = \<llangle>sort xs\<rrangle>
  \<rbrakk>\<close>

definition slice_sort_contract :: \<open>(('a, 'b) gref, 'b, ('v::linorder) list) focused \<Rightarrow> 'b \<Rightarrow>
    'v list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>slice_sort_contract ptr g ls \<equiv>
    let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>ls in
    let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. sort ls) \<sqdot> (g\<down>ls) in
      make_function_contract pre post\<close>
ucincl_auto slice_sort_contract

lemma slice_sort_spec [crush_specs]:
  shows \<open>\<Gamma> ; slice_sort ptr \<Turnstile>\<^sub>F slice_sort_contract ptr g ls\<close>
  by (crush_boot f: slice_sort_def contract: slice_sort_contract_def) crush_base

micro_rust_notation (call) slice_sort ("sort")

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

(*<*)
end
(*>*)

subsection\<open>Debug printing\<close>

instantiation range :: (generate_debug)generate_debug
begin

fun generate_debug_range :: \<open>'a range \<Rightarrow> log_data\<close> where
  \<open>generate_debug_range r =
     (if end_inclusive r then
        str ''(''#generate_debug (start r)@[str ''..='']@generate_debug (end r)@[str '')'']
      else
        str ''(''#generate_debug (start r)@[str ''..<'']@generate_debug (end r)@[str '')''])\<close>

instance ..

end

(*<*)
end
(*>*)
