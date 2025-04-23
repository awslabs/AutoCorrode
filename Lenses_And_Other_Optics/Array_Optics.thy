(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Array_Optics
  imports Misc.Array Focus
begin
(*>*)

section\<open>Optics for arrays\<close>

definition nth_lens_array :: \<open>nat \<Rightarrow> (('v, 'l::len) array, 'v) lens\<close> where
  \<open>nth_lens_array idx \<equiv> make_lens (\<lambda>arr. array_nth arr idx) (\<lambda>v arr. array_update arr idx v)\<close>

lemma nth_lens_array_is_valid [focus_intros, intro]:
  assumes \<open>n < LENGTH('l :: len)\<close>
    shows \<open>is_valid_lens ((nth_lens_array::nat \<Rightarrow> (('a, 'l) array, 'a) lens) n)\<close>
using assms by (clarsimp simp add: is_valid_lens_def nth_lens_array_def array_extI lens_update_def)

lift_definition nth_focus_array :: \<open>nat \<Rightarrow> (('v, 'l::{len}) array, 'v) focus\<close> is
   \<open>\<lambda>idx. if idx < LENGTH('l) then \<integral>'\<^sub>l (nth_lens_array idx) else dummy_focus\<close>
by (case_tac \<open>nat < LENGTH('l)\<close>) (auto simp add: nth_lens_array_is_valid
  lens_to_focus_raw_valid dummy_focus_is_valid)

lemma nth_focus_array_components [focus_components]:
    fixes idx :: nat
      and arr :: \<open>('v, 'l::len) array\<close>
  assumes \<open>idx < LENGTH('l :: len)\<close>
    shows \<open>focus_view (nth_focus_array idx) arr = Some (array_nth arr idx)\<close>
      and \<open>focus_update (nth_focus_array idx) v arr = array_update arr idx v\<close>
      and \<open>focus_modify (nth_focus_array idx) f arr = array_update arr idx (f (array_nth arr idx))\<close>
using assms by (transfer; clarsimp simp add: nth_lens_array_def lens_to_focus_raw_components lens_modify_def)+

lemma nth_focus_array_view [focus_intros]:
    fixes ls :: \<open>('a, 'l::{len}) array\<close>
  assumes \<open>n < LENGTH('l)\<close>
      and \<open>x = array_nth ls n\<close>
    shows \<open>\<down>{nth_focus_array n} ls \<doteq> x\<close>
using assms by (simp add: focus_components)

text\<open>The prism/subtype of lists of a fixed length.\<close>

definition list_fixlen_project :: \<open>'a list \<Rightarrow> ('a, 'l::{len}) array option\<close> where
  \<open>list_fixlen_project l \<equiv> if length l = LENGTH('l) then Some (array_of_list l) else None\<close>

definition list_fixlen_embed :: \<open>('a, 'l::{len}) array \<Rightarrow> 'a list\<close> where
  \<open>list_fixlen_embed a \<equiv> array_to_list a\<close>

lemma list_fixlen_project_embed:
  shows \<open>\<And>t. list_fixlen_project (list_fixlen_embed t) = Some t\<close>
    and \<open>\<And>t. list_fixlen_project x = Some y \<Longrightarrow> list_fixlen_embed y = x\<close>
by (auto split: if_splits simp add: list_to_array_to_list list_fixlen_project_def list_fixlen_embed_def)

definition list_fixlen_prism :: \<open>('a list, ('a, 'l::{len}) array) prism\<close> where
  \<open>list_fixlen_prism \<equiv> make_prism list_fixlen_embed list_fixlen_project\<close>

lemma list_fixlen_prism_valid [focus_intros]:
  shows \<open>is_valid_prism list_fixlen_prism\<close> 
by (simp add: is_valid_prism_def list_fixlen_prism_def list_fixlen_project_embed)

lift_definition list_fixlen_focus :: \<open>('a list, ('a, 'l::len) array) focus\<close> is \<open>\<integral>'\<^sub>p list_fixlen_prism\<close>
using list_fixlen_prism_valid prism_to_focus_raw_valid by blast

lemmas list_fixlen_focus_components [focus_components] =
  prism_to_focus_components[OF list_fixlen_prism_valid, folded list_fixlen_focus_def,
    simplified list_fixlen_prism_def, simplified prism_dom_def, simplified]

text\<open>The prism/subtype of lists of a minimum length\<close>

definition list_minlen_project :: \<open>'a list \<Rightarrow> (('a, 'l::{len}) array \<times> 'a list) option\<close> where
  \<open>list_minlen_project l \<equiv>
     if length l \<ge> LENGTH('l) then 
       Some (array_of_list (take LENGTH('l) l), drop LENGTH('l) l) 
     else
       None\<close>

definition list_minlen_embed :: \<open>('a, 'l::{len}) array \<times> 'a list \<Rightarrow> 'a list\<close> where
  \<open>list_minlen_embed x \<equiv> (array_to_list (fst x)) @ (snd x)\<close>

lemma list_minlen_project_embed:
  shows \<open>list_minlen_project (list_minlen_embed t) = Some t\<close>
    and \<open>list_minlen_project x = Some y \<Longrightarrow> list_minlen_embed y = x\<close>
by (auto split: if_splits simp add: list_to_array_to_list list_minlen_project_def list_minlen_embed_def)

definition list_minlen_prism :: \<open>('a list, ('a, 'l::{len}) array \<times> 'a list) prism\<close> where
  \<open>list_minlen_prism \<equiv> make_prism list_minlen_embed list_minlen_project\<close>

lemma list_minlen_prism_dom:
  shows \<open>prism_dom (list_minlen_prism :: ('a list, ('a, 'l::{len}) array \<times> 'a list) prism) = 
           { xs :: 'a list . length xs \<ge> LENGTH('l) }\<close>
by (clarsimp simp add: prism_dom_def dom_def list_minlen_project_def list_minlen_prism_def)

lemma list_minlen_prism_valid [focus_intros]:
shows \<open>is_valid_prism list_minlen_prism\<close> 
  by (simp add: is_valid_prism_def list_minlen_prism_def list_minlen_project_embed)

lift_definition list_minlen_focus :: \<open>('a list, ('a, 'l::len) array \<times> 'a list) focus\<close> is \<open>\<integral>'\<^sub>p list_minlen_prism\<close> 
using list_minlen_prism_valid prism_to_focus_raw_valid by blast

lemmas list_minlen_focus_components[focus_components] =
  prism_to_focus_components[OF list_minlen_prism_valid, folded list_minlen_focus_def,
    simplified list_minlen_prism_dom, simplified list_minlen_prism_def, simplified]

(*<*)
end
(*>*)