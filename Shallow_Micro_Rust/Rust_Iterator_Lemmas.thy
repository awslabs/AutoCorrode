(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Rust_Iterator_Lemmas
  imports Rust_Iterator Core_Expression Core_Expression_Lemmas Core_Syntax Range_Type
begin
(*>*)

section \<open>Inductive definition of loop constructs\<close>

lemma gather'_nil [micro_rust_simps]:
  shows \<open>gather' [] acc = literal acc\<close>
  by (auto simp add: gather'_def foldM_def)

lemma gather'_cons [micro_rust_simps]: 
  shows \<open>gather' (t0 # thunks) acc = bind t0 (\<lambda>v0. gather' thunks (acc @ [v0]))\<close>
  by (auto simp add: gather'_def foldM_def) 

lemma sequence'_nil [micro_rust_simps]:
  shows \<open>sequence' [] = skip\<close>
  by (auto simp add: sequence'_def)

lemma sequence'_cons [micro_rust_simps]: 
  shows \<open>sequence' (e # es) = sequence e (sequence' es)\<close>
  by (auto simp add: sequence'_def) 

lemma raw_for_loop_nil [micro_rust_simps]:
  shows \<open>raw_for_loop [] body = skip\<close>
  by (auto simp add: raw_for_loop_def micro_rust_simps)

lemma raw_for_loop_cons [micro_rust_simps]:
  shows \<open>raw_for_loop (x#xs) body = (body x; raw_for_loop xs body)\<close>
  by (auto simp add: raw_for_loop_def micro_rust_simps)

\<comment>\<open>Use this to unroll one loop iteration at a time when dealing with a loop with a large
   number of iterations.\<close>
lemma raw_for_loop_standard_unroll_once_simp:
  shows \<open>raw_for_loop (list.map word64_of_nat [n..<m]) body =
         (if n < m then
                   (body (word64_of_nat n); raw_for_loop (list.map word64_of_nat [(Suc n)..<m]) body)
                else
                   skip)\<close> 
  by (simp add: raw_for_loop_cons raw_for_loop_nil upt_rec)

lemma urust_sequence_cong:
  assumes \<open>e = e'\<close>
  shows \<open>(e; f) = (e'; f)\<close>
  using assms by simp

lemmas raw_for_loop_unroll_once_cong = urust_sequence_cong[where f=\<open>raw_for_loop _ _\<close>]

section\<open>Simplification rules for static loops\<close>

lemma iterator_make_iterator_from_list [simp]:
  shows \<open>iterator_ethunks (make_iterator_from_list ls) = List.map literal ls\<close> 
  by (simp add: iterator_ethunks_def make_iterator_from_list_def micro_rust_simps)

lemma iterator_make_iterator_from_range [simp]:
  shows \<open>iterator_ethunks (make_iterator_from_range r) = List.map literal (range_into_list r)\<close> 
  by (simp add: make_iterator_from_range_def)

lemma bind_literal_compose [micro_rust_simps]:
  shows \<open>(\<lambda>e. bind e f) \<circ> literal = f\<close> 
  by (intro ext, simp add:micro_rust_simps)

lemma map_nth' [simp]:
  shows \<open>List.map (\<lambda>i. f (ls ! i)) [0..<length ls] = List.map f ls\<close> 
  apply (induction ls rule: List.rev_induct)
  apply force
  apply clarsimp
  apply (rule map_upt_eqI, force)
  apply (clarsimp simp add: nth_append)
  done

lemma bind_map [micro_rust_simps]:
  shows \<open>list.map (\<lambda>xa. bind (ls ! xa) body) [0..<length ls] = list.map (\<lambda>e. bind e body) ls\<close>
  using map_nth' by fastforce

lemma for_loop_list [micro_rust_simps]:
  shows \<open>for_loop (\<up>(make_iterator_from_list ls)) body = raw_for_loop ls body\<close>
  by (clarsimp simp add: for_loop_def for_loop_core_def raw_for_loop_def micro_rust_simps)

(*<*)
end
(*>*)
