(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Rust_Iterator
  imports "HOL-Library.Datatype_Records" Core_Expression
    Misc.Array Misc.Vector
begin
(*>*)

text\<open>Here we model the Micro Rust iterator type as simply a list.  This isn't completely faithful to
the Rust iterator trait, which models a self-mutating cursor.\<close>
datatype_record ('s, 'r, 'abort, 'i, 'o) iterator =
  iterator_thunks :: \<open>('s, 'r, 'abort, 'i, 'o) function_body list\<close>

definition iterator_ethunks :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression list\<close> where
  \<open>iterator_ethunks it \<equiv> List.map call (iterator_thunks it)\<close>

definition iterator_len :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> nat\<close> where
  \<open>iterator_len it \<equiv> length (iterator_thunks it)\<close>

definition make_iterator_from_list :: \<open>'a list \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) iterator\<close> where
  \<open>make_iterator_from_list xs \<equiv> make_iterator (List.map fun_literal xs)\<close>

definition iter_pull :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> 64 word \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_pull iter i \<equiv> (iterator_thunks iter) ! (unat i)\<close>

consts into_iter :: \<open>'a \<Rightarrow> ('s, ('s, 'b, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close>

definition iterator_into_iter :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> ('s, ('s, 'a, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  \<open>iterator_into_iter i \<equiv> FunctionBody (literal i)\<close>

definition list_into_iter :: \<open>'a list \<Rightarrow> ('s, ('s, 'a, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  \<open>list_into_iter xs \<equiv> fun_literal (make_iterator_from_list xs)\<close>

definition array_into_iter :: \<open>('a, 'l::{len}) array \<Rightarrow> ('s, ('s, 'a, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  \<open>array_into_iter xs \<equiv> fun_literal (make_iterator_from_list (array_to_list xs))\<close>

definition vector_into_iter :: \<open>('a, 'l::{len}) vector \<Rightarrow> ('s, ('s, 'a, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  \<open>vector_into_iter xs \<equiv> fun_literal (make_iterator_from_list (vector_to_list xs))\<close>

adhoc_overloading into_iter \<rightleftharpoons> iterator_into_iter list_into_iter array_into_iter vector_into_iter

subsection \<open>Bulk operations on iterators\<close>

abbreviation compose_func :: \<open>('a \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body \<Rightarrow>
    ('s, 'b, 'abort, 'i, 'o) function_body\<close> where
  \<open>compose_func g f \<equiv> FunctionBody (bind (call f) (\<lambda>v. call (g v)))\<close>

definition map :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> ('a \<Rightarrow> ('s,'b, 'abort, 'i, 'o) function_body) \<Rightarrow>
    ('s, ('s, 'b, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> where
  \<open>map iter f \<equiv> fun_literal (make_iterator (List.map (compose_func f) (iterator_thunks iter)))\<close>

subsection\<open>Looping over iterators\<close>

text\<open>The following is our ``ur loop'', our generic looping construct implemented in terms of a
generic iterator, as introduced above:\<close>
lemma fold_via_foldr:
  shows \<open>fold f ls = foldr (\<lambda>a g. g o (f a)) ls (\<lambda>x. x)\<close>
  by (induction ls) auto

text\<open>We need to use foldr for the sequencing even though we're lifting a normal fold.  This
generalizes the \<^verbatim>\<open>fold_via_foldr\<close> identity above, replacing \<^term>\<open>(o)\<close> by the monadic bind.\<close>
definition foldM :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression list \<Rightarrow> 'b \<Rightarrow> ('s, 'b, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>foldM op thunks \<equiv> List.foldr (\<lambda>fa f b. bind fa (\<lambda>a. f (op a b))) thunks literal\<close>

definition gather' :: \<open>('s,'a,'r, 'abort, 'i, 'o) expression list \<Rightarrow> 'a list \<Rightarrow> ('s, 'a list, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>gather' els \<equiv> foldM (\<lambda>x xs. xs @ [x]) els\<close>

definition gather :: \<open>('s,'a,'r, 'abort, 'i, 'o) expression list \<Rightarrow> ('s, 'a list, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>gather els \<equiv> gather' els []\<close>

definition sequence' :: \<open>('s,'a,'r, 'abort, 'i, 'o) expression list \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>sequence' els \<equiv> foldr sequence els skip\<close>

definition collect :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> ('s,'a list, 'abort, 'i, 'o) function_body\<close> where
  \<open>collect iter \<equiv> FunctionBody (gather (iterator_ethunks iter))\<close>

definition drain :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>drain iter \<equiv> FunctionBody (sequence' (iterator_ethunks iter))\<close>

\<comment> \<open>Generic fold operator on Rust iterators. NOTE: untested\<close>
definition iterator_fold :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow>
  'c \<Rightarrow>
  ('c \<Rightarrow> 'a \<Rightarrow> ('s, 'c, 'abort, 'i, 'o) function_body) \<Rightarrow>
  ('s, 'c, 'abort, 'i, 'o) function_body\<close> 
  where
  \<open>iterator_fold iter z f \<equiv> FunctionBody (
    List.foldr (\<lambda> thunk_a acc_z.
      bind thunk_a (\<lambda> val_a.
        bind acc_z (\<lambda> val_z.
          call (f val_z val_a)
        )
      ) 
    ) (iterator_ethunks iter) (literal z)
  )\<close>

\<comment> \<open>Generic filter operator on Rust iterators, defined using above fold. NOTE: untested\<close>
definition iterator_filter :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow>
  ('a \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<Rightarrow>
  ('s, ('s, 'a, 'abort, 'i, 'o) iterator, 'abort, 'i, 'o) function_body\<close> 
  where
  \<open>iterator_filter iter f \<equiv> FunctionBody (
    bind (call (iterator_fold iter [] (\<lambda> xs el. FunctionBody (
      bind (call (f el)) (\<lambda> test.
        case test of
          True \<Rightarrow> literal (xs @ [el])
        | False \<Rightarrow> literal xs
      )
    )))) (\<lambda> els.
      call (list_into_iter els)
    )
  )\<close>

definition raw_for_loop :: \<open>'a list \<Rightarrow> ('a \<Rightarrow> ('s,'v,'r, 'abort, 'i, 'o) expression) \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>raw_for_loop ls body \<equiv> sequence' (List.map body ls)\<close>

subsection\<open>Bounded while loops\<close>

text\<open>A fuel-based while-loop combinator. Terminates by structural recursion on the fuel @{typ nat}.
When fuel reaches 0 the loop returns @{term skip} (unit). The WP invariant rules force the user to
prove fuel sufficiency, so the fuel=0 case is unreachable in verified code.\<close>
fun bounded_while :: \<open>nat \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>bounded_while 0 cond body = skip\<close>
| \<open>bounded_while (Suc n) cond body =
     bind cond (\<lambda>c. if c then sequence body (bounded_while n cond body)
                     else skip)\<close>

definition for_loop_core :: \<open>('s, 'a, 'abort, 'i, 'o) iterator \<Rightarrow> ('a \<Rightarrow> ('s,'v,'r, 'abort, 'i, 'o) expression) \<Rightarrow>
    ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>for_loop_core iter body \<equiv>
     raw_for_loop [0..<(length (iterator_ethunks iter :: (_, _, 'r, 'abort, 'i, 'o) expression list))]
       (\<lambda>i. bind ((iterator_ethunks iter :: (_, _, 'r, 'abort, 'i, 'o) expression list) ! i) body)\<close>

lemma for_loop_core_alt [code]:
  fixes iter :: \<open>('s, 'a, 'abort, 'i, 'o) iterator\<close>
    and body :: \<open>('a \<Rightarrow> ('s,'v,'r, 'abort, 'i, 'o) expression)\<close>
  shows \<open>for_loop_core iter body = (
           let t = iterator_ethunks iter :: (_, _, 'r, 'abort, 'i, 'o) expression list in
             raw_for_loop [0..<(length t)] (\<lambda>i. bind (t ! i) body))\<close>
by (simp add: Let_def for_loop_core_def)

definition for_loop :: \<open>('s, ('s, 'a, 'abort, 'i, 'o) iterator, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('a \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>for_loop iter body \<equiv> bind iter (\<lambda>it. for_loop_core it body)\<close>

(*<*)
end
(*>*)
