(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Range_Type
  imports Core_Expression Rust_Iterator "HOL-Library.Datatype_Records"
begin
(*>*)

section\<open>The \<^emph>\<open>Range\<close> type\<close>

datatype_record 'a range =
  start :: \<open>'a\<close>
  "end"  :: \<open>'a\<close>

text\<open>A range contains all values with \<^term>\<open>start \<le> x \<and> x < end\<close>.  It is empty if \<^term>\<open>start \<ge> end\<close>.\<close>

subsection\<open>Core material related to the \<^emph>\<open>Range\<close> type\<close>

definition is_empty :: \<open>'a::{ord} range \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close>  where
  \<open>is_empty r \<equiv> FunctionBody (literal (\<not> (start r < end r)))\<close>

definition contains :: \<open>'a::ord range \<Rightarrow> 'a \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>contains r x \<equiv> FunctionBody (literal (start r \<le> x \<and> x < end r))\<close>

definition range_new :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('s, 'a range, 'abort, 'i, 'o) function_body\<close> where
  \<open>range_new \<equiv> lift_fun2 make_range\<close>

definition range_eq_new :: \<open>'a::{one, plus} \<Rightarrow> 'a \<Rightarrow> ('s, 'a range, 'abort, 'i, 'o) function_body\<close> where
  \<open>range_eq_new \<equiv> lift_fun2 (\<lambda>x y. make_range x (y + 1))\<close>

text\<open>Iterator for a range\<close>

definition range_into_list :: \<open>'a::{len} word range \<Rightarrow> 'a word list\<close> where
  \<open>range_into_list r \<equiv> List.map of_nat [unat (start r) ..< unat (end r)]\<close>

definition make_iterator_from_range :: \<open>'b::{len} word range \<Rightarrow> ('a, 'b word, 'abort, 'i, 'o) iterator\<close> where
  [micro_rust_simps]: \<open>make_iterator_from_range r \<equiv> make_iterator_from_list (range_into_list r)\<close>

definition range_into_iter :: \<open>'a::{len} word range \<Rightarrow> ('s, ('s, 'a word, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  [micro_rust_simps]: \<open>range_into_iter r \<equiv> fun_literal (make_iterator_from_range r)\<close>

adhoc_overloading into_iter \<rightleftharpoons> range_into_iter

subsection\<open>Slice-like behavior from lists\<close>

definition len :: \<open>'a list \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>len xs \<equiv> FunctionBody (literal (of_nat (length xs)))\<close>

definition list_index :: \<open>'a list \<Rightarrow> 'w::len word \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>list_index xs idx \<equiv> FunctionBody (
     case nth_opt (unat idx) xs of
       None \<Rightarrow> abort DanglingPointer
     | Some x \<Rightarrow> literal x)\<close>

definition array_index :: \<open>('a, 'l::{len}) array \<Rightarrow> 'w::{len} word \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>array_index xs idx \<equiv> FunctionBody (
     if unat idx < array_len xs then
       literal (array_nth xs (unat idx))
     else
       abort DanglingPointer)\<close>
 
definition vector_index :: \<open>('a, 'l::{len}) vector \<Rightarrow> 'w::{len} word \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>vector_index xs idx \<equiv> FunctionBody (
     if unat idx < vector_len xs then
       literal (vector_nth xs (unat idx))
     else
       abort DanglingPointer)\<close>

definition list_index_range :: \<open>'a list \<Rightarrow> 'w::{len} word range \<Rightarrow> ('s,'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>list_index_range xs rng \<equiv> FunctionBody (
    if start rng > end rng then
      abort DanglingPointer
    else if unat (end rng) > length xs then
      abort DanglingPointer
    else
      literal (take (unat ((end rng) - (start rng))) (drop (unat (start rng)) xs)))
\<close>

definition array_index_range :: \<open>('a, 'l::{len}) array \<Rightarrow> 'w::{len} word range \<Rightarrow>
      ('s, 'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>array_index_range arr rng \<equiv> list_index_range (array_to_list arr) rng\<close>

definition vector_index_range :: \<open>('a, 'l::{len}) vector \<Rightarrow> 'w::{len} word range \<Rightarrow>
      ('s, 'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>vector_index_range arr rng \<equiv> list_index_range (vector_to_list arr) rng\<close>

(*<*)
end
(*>*)
