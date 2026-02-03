(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Array
  imports "HOL-Library.Word" Data_Structures.BraunTreeAdditional ListAdditional
begin
(*>*)

section\<open>A fixed-length array type\<close>

subsection\<open>The type itself\<close>

definition is_array :: \<open>'a tree \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>is_array t n \<equiv> braun t \<and> size t = n\<close>

typedef (overloaded) ('a, 'b::\<open>{len}\<close>) array = \<open>{ t::'a tree . is_array t LENGTH('b) }\<close>
proof -
  have \<open>braun_of undefined LENGTH('b) \<in> {t. is_array t LENGTH('b)}\<close>
    by (metis braun_braun_of is_array_def length_replicate list_braun_of mem_Collect_eq size_list)
  from this show ?thesis
    by blast
qed

(*<*)
setup_lifting array.type_definition_array

text\<open>This is needed to explain to the code-generator how equalities at type \<^verbatim>\<open>array\<close> should be
handled (basically, use the underlying equality on trees):\<close>
instantiation array :: (equal, len) equal
begin

lift_definition equal_array :: \<open>('a, 'b::len) array \<Rightarrow> ('a, 'b) array \<Rightarrow> bool\<close> is \<open>(=)\<close> .

instance
  by standard (simp add: equal_array_def Rep_array_inject)

end
(*>*)

subsection \<open>Lifted operations on the type\<close>

abbreviation array_len :: \<open>('a,'l::{len}) array \<Rightarrow> nat\<close> where
  \<open>array_len xs \<equiv> LENGTH('l)\<close>

lift_definition array_map :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a, 'b::{len}) array \<Rightarrow> ('c, 'b::{len}) array\<close>
  is \<open>tree_map\<close> by (simp add: is_array_def tree_map_braun)

lift_definition array_nth :: \<open>('a, 'b::{len}) array \<Rightarrow> nat \<Rightarrow> 'a\<close>
  is \<open>\<lambda>t i. lookup1 t (i+1)\<close> .

lift_definition array_update :: \<open>('a, 'b::{len}) array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a, 'b::{len}) array\<close>
  is \<open>\<lambda>t i v. if i < LENGTH('b) then update1 (i+1) v t else t\<close>
  by (auto simp add: is_array_def braun_update1 size_update1)

lift_definition array_constant :: \<open>'a \<Rightarrow> ('a, 'l::{len}) array\<close>
  is \<open>\<lambda>v. braun_of v LENGTH('l)\<close>
proof -
  fix a :: \<open>'a\<close>
  have \<open>size (braun_of a LENGTH('l)) = LENGTH('l)\<close>
    using length_replicate size_list list_braun_of by metis
  from this show \<open>is_array (braun_of a LENGTH('l)) LENGTH('l)\<close>
    by (clarsimp simp add: is_array_def braun_braun_of)
qed

lift_definition array_of_list :: \<open>'a list \<Rightarrow> ('a, 'b::len) Array.array\<close>
  is \<open>\<lambda>ls. let a = brauns1 ls;
               n = size_fast a
            in if n = LENGTH('b) then a else braun_of undefined LENGTH('b)\<close>
proof -
  fix list :: \<open>'a list\<close>
  {
    assume \<open>size (brauns1 list) \<noteq> LENGTH('b)\<close>
    from this have \<open>size (braun_of undefined LENGTH('b)) = LENGTH('b)\<close>
      using length_replicate size_list list_braun_of by metis
  }
  from this show \<open>?thesis list\<close>
    by (clarsimp simp add: is_array_def brauns1_correct braun_braun_of size_fast Let_def)
qed

lift_definition array_to_list :: \<open>('a, 'b::len) array \<Rightarrow> 'a list\<close>
  is \<open>list_fast\<close> .

definition array_splice :: \<open>nat \<Rightarrow> ('a, 'l0::{len}) array \<Rightarrow> ('a, 'l1::{len}) array \<Rightarrow> ('a, 'l1) array\<close> where
  \<open>array_splice n xs ys \<equiv> foldl (\<lambda>a i. array_update a i (array_nth xs i)) ys [0..<n]\<close>

lift_definition array_resize :: \<open>('a, 'l0::{len}) array \<Rightarrow> 'a \<Rightarrow> ('a, 'l1::len) array\<close>
  is \<open>\<lambda>xs default. if LENGTH('l0) < LENGTH('l1) then
             adds (replicate (LENGTH('l1) - LENGTH('l0)) default) (LENGTH('l0)) xs
           else
             braun_take xs LENGTH('l1)\<close>
by (auto simp add: is_array_def size_braun_adds braun_braun_take size_braun_take)

lemma array_to_list_nth [simp]:
  assumes \<open>i < array_len xs\<close>
    shows \<open>array_to_list xs ! i = array_nth xs i\<close>
using assms by (transfer, clarsimp simp add: is_array_def list_fast_correct nth_list_lookup1)

lemma array_to_list_length [simp]:
  shows \<open>length (array_to_list xs) = array_len xs\<close>
by (transfer, clarsimp simp add: is_array_def list_fast_correct size_list)

lemma array_to_list_update [simp]:
  shows \<open>array_to_list (array_update l i v) = list_update (array_to_list l) i v\<close>
by transfer (auto simp add: is_array_def list_fast_correct braun_update1 list_update1 size_list list_update_beyond)

lemma array_map_nth [simp]:
  assumes \<open>i < array_len xs\<close>
    shows \<open>array_nth (array_map f xs) i = f (array_nth xs i)\<close>
using assms by transfer (auto simp add: is_array_def tree_map_lookup1)

lemma list_to_array_nth [simp]:
  assumes \<open>length ls = LENGTH('l::{len})\<close>
      and \<open>i < LENGTH('l)\<close>
    shows \<open>array_nth (array_of_list ls :: ('a, 'l) array) i = ls ! i\<close>
using assms proof transfer
     fix ls :: \<open>'a list\<close>
     and i
  assume \<open>length ls = LENGTH('l)\<close>
     and \<open>i < LENGTH('l)\<close>
  moreover {
    assume \<open>size_fast (brauns1 ls) = LENGTH('l)\<close>
    from this calculation have \<open>lookup1 (brauns1 ls) (Suc i) = ls ! i\<close>
      by (metis add.commute brauns1_correct nth_list_lookup1 plus_1_eq_Suc size_fast)
  } moreover {
    assume \<open>size_fast (brauns1 ls) \<noteq> LENGTH('l)\<close>
    from this calculation have \<open>lookup1 (braun_of undefined LENGTH('l)) (Suc i) = ls ! i\<close>
      by (metis brauns1_correct size_fast size_list)
  }
  ultimately show \<open>lookup1 (
    let a = brauns1 ls;
        n = size_fast a
     in if n = LENGTH('l) then a else braun_of undefined LENGTH('l)) (i + 1) = ls ! i\<close>
    by (clarsimp simp add: Let_def)
qed

lemma array_nth_update [simp]:
  assumes \<open>j < array_len l\<close>
    shows \<open>array_nth (array_update l i v) j = (if i = j then v else array_nth l j)\<close>
using assms by transfer (auto simp add: is_array_def lookup1_update1)

lemma array_splice_nth [simp]:
  assumes \<open>i < array_len ys\<close>
    shows \<open>array_nth (array_splice n xs ys) i = (if i < n then array_nth xs i else array_nth ys i)\<close>
using assms by (induction n, auto simp add: array_splice_def)

lemma array_extI:
    fixes xs ys :: \<open>('a, 'l::{len}) array\<close>
  assumes \<open>\<And>i. i < LENGTH('l) \<Longrightarrow> array_nth xs i = array_nth ys i\<close>
    shows \<open>xs = ys\<close>
using assms by transfer (auto simp add: is_array_def intro: braun_tree_ext)

lemma array_to_list_extI:
    fixes bs cs :: \<open>('a, 'b::{len}) array\<close>
  assumes \<open>array_to_list bs = array_to_list cs\<close>
    shows \<open>bs = cs\<close>
using assms by transfer (metis braun_tree_ext is_array_def list_fast_correct nth_list_lookup1
  semiring_norm(174))

lemma array_update_nth [simp]:
  shows \<open>array_update arr j (array_nth arr j) = arr\<close>
by (simp add: array_extI)

lemma resize_array_nth:
    fixes xs :: \<open>('a, 'l0::{len}) array\<close>
      and ys :: \<open>('a, 'l1::{len}) array\<close>
  assumes \<open>array_resize xs d = ys\<close>
      and \<open>i < LENGTH('l1)\<close>
    shows \<open>array_nth ys i = (if i < LENGTH('l0) then array_nth xs i else d)\<close>
using assms by transfer (auto simp add: is_array_def braun_take_lookup1 lookup1_adds
  nth_list_lookup1 size_list nth_append split: if_splits)

lemma list_to_array_to_list:
    fixes a :: \<open>('a, 'b::{len}) array\<close>
  assumes \<open>a = array_of_list l\<close>
      and \<open>length l = LENGTH('b)\<close>
    shows \<open>array_to_list a = l\<close>
using assms proof transfer
     fix a
     and l :: \<open>'a list\<close>
  assume \<open>is_array a LENGTH('b)\<close>
     and \<open>a = (let a = brauns1 l; n = size_fast a in if n = LENGTH('b) then a else braun_of undefined LENGTH('b))\<close>
     and \<open>length l = LENGTH('b)\<close>
  moreover {
      note calculation_thus_far = calculation
    assume \<open>size_fast (brauns1 l) = LENGTH('b)\<close>
    moreover from this calculation_thus_far have \<open>a = brauns1 l\<close> and \<open>length l = LENGTH('b)\<close>
      by (auto simp add: Let_def)
    moreover from calculation calculation_thus_far have \<open>size_fast (brauns1 l) = LENGTH('b)\<close>
      by (auto simp add: is_array_def)
    moreover from calculation have \<open>list_fast (brauns1 l) = l\<close>
      by (simp add: brauns1_correct list_fast_correct)
    ultimately have \<open>list_fast a = l\<close>
      by (clarsimp simp add: list_fast_correct)
  } moreover {
    assume \<open>size_fast (brauns1 l) \<noteq> LENGTH('b)\<close>
    from this calculation have \<open>list_fast a = l\<close>
      by (clarsimp simp add: Let_def) (metis brauns1_correct size_fast size_list)
  }
  ultimately show \<open>list_fast a = l\<close>
    by blast
qed

lemma array_splice_Suc:
  shows \<open>array_splice (Suc n) xs ys = array_update (array_splice n xs ys) n (array_nth xs n)\<close>
by (clarsimp intro!: array_extI simp add: array_splice_def)

lemma array_splice_0 [simp]:
  shows \<open>array_splice 0 xs = id\<close>
    and \<open>array_splice 0 xs ys = ys\<close>
by (auto intro!: array_extI simp add: array_splice_def)

lemma array_constant_nth [simp]:
  assumes \<open>i < LENGTH('l::{len})\<close>
    shows \<open>array_nth (array_constant v :: ('a, 'l :: {len}) array) i = v\<close>
using assms proof transfer
     fix i
     and v :: \<open>'a\<close>
  assume \<open>i < LENGTH('l)\<close>
  from this show \<open>lookup1 (braun_of v LENGTH('l)) (i + 1) = v\<close>
    using list_braun_of length_replicate nth_list_lookup1 nth_replicate by (metis Suc_eq_plus1
      braun_braun_of size_list)
qed

lemma array_update_overwrite [simp]:
  shows \<open>array_update (array_update ls i v) i w = array_update ls i w\<close>
by (intro array_extI) auto

lemma array_update_swap:
  assumes \<open>i \<noteq> j\<close>
    shows \<open>array_update (array_update ls i v) j w = array_update (array_update ls j w) i v\<close>
using assms by (intro array_extI) auto

lemma array_splice_update0:
    fixes xs :: \<open>('a, 'l0::{len}) array\<close>
      and ys :: \<open>('a, 'l1::{len}) array\<close>
  assumes \<open>n \<le> LENGTH('l0)\<close>
      and \<open>n \<le> LENGTH('l1)\<close>
      and \<open>i < n\<close>
    shows \<open>array_update (array_splice n xs ys) i v = array_splice n (array_update xs i v) ys\<close>
using assms by (auto intro: array_extI)

lemma array_splice_update1:
    fixes xs :: \<open>('a, 'l0::{len}) array\<close>
      and ys :: \<open>('a, 'l1::{len}) array\<close>
  assumes \<open>n \<le> LENGTH('l0)\<close>
      and \<open>n \<le> LENGTH('l1)\<close>
      and \<open>i < LENGTH('l1)\<close>
      and \<open>i \<ge> n\<close>
    shows \<open>array_update (array_splice n xs ys) i v = array_splice n xs (array_update ys i v)\<close>
using assms by (auto intro: array_extI)

definition array_over_nth :: \<open>nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'l::{len}) array \<Rightarrow> ('a, 'l) array\<close> where
  \<open>array_over_nth i f v \<equiv> if i < LENGTH('l) then array_update v i (f (array_nth v i)) else v\<close>

lemma array_over_nth_list_update:
  fixes xs :: \<open>('a, 'l::{len}) array\<close>
  shows \<open>array_over_nth n f xs = (if n < array_len xs then array_update xs n (f (array_nth xs n)) else xs)\<close>
by (auto simp add: array_over_nth_def)

lemma array_over_nth_list_update':
  fixes xs :: \<open>('a, 'l::{len}) array\<close>
  shows \<open>array_over_nth = (\<lambda>n f xs. if n < array_len xs then array_update xs n (f (array_nth xs n)) else xs)\<close>
by (auto simp add: array_over_nth_def intro!: ext)

lemma array_of_list_to_array [simp]:
  shows \<open>array_of_list (array_to_list a) = a\<close>
proof transfer
     fix a :: \<open>'a tree\<close>
  assume \<open>is_array a LENGTH('b::{len})\<close>
  moreover {
      note calculation_thus_far = calculation
    assume \<open>size_fast (brauns1 (list_fast a)) = LENGTH('b)\<close>
    moreover from this calculation_thus_far have \<open>braun a\<close> and \<open>size a = LENGTH('b)\<close>
      by (auto simp add: is_array_def)
    moreover from calculation have \<open>brauns1 (braun_list a) = a\<close>
      by (metis Suc_eq_plus1 braun_tree_ext brauns1_correct list_fast_correct nth_list_lookup1 size_fast)
    ultimately have \<open>brauns1 (list_fast a) = a\<close>
      by (clarsimp simp add: list_fast_correct)
  } moreover {
    assume \<open>size_fast (brauns1 (list_fast a)) \<noteq> LENGTH('b)\<close>
    from this calculation have \<open>braun_of undefined LENGTH('b) = a\<close>
      by (metis brauns1_correct is_array_def list_fast_correct size_fast size_list)
  }
  ultimately show \<open>(let a = brauns1 (list_fast a); n = size_fast a in if n = LENGTH('b) then a else braun_of undefined LENGTH('b)) = a\<close>
    by (clarsimp simp add: Let_def)
qed

lemma array_of_list_list_update [simp]:
  assumes \<open>LENGTH('b::{len}) = length xs\<close>
    shows \<open>(array_of_list (xs[i := e])::('a, 'b) array) = array_update (array_of_list xs) i e\<close>
using assms by (metis array_of_list_to_array array_to_list_update list_to_array_to_list)

(*<*)
end
(*>*)