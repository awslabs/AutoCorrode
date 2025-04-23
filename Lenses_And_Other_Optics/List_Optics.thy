(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory List_Optics
  imports Prism Lens Focus Misc.ListAdditional
begin
(*>*)

section\<open>Optics for lists\<close>

text\<open>The special case of the prism/subtype of empty lists\<close>

definition list_empty_prism_project :: \<open>'a list \<Rightarrow> unit option\<close> where
  \<open>list_empty_prism_project ls \<equiv> case ls of [] \<Rightarrow> Some () | _ \<Rightarrow> None\<close>

definition list_empty_prism_embed :: \<open>unit \<Rightarrow> 'a list\<close> where
  \<open>list_empty_prism_embed _ \<equiv> []\<close>

definition list_empty_prism where
  \<open>list_empty_prism \<equiv> make_prism list_empty_prism_embed list_empty_prism_project\<close>

lemma list_empty_prism_dom:
  shows \<open>prism_dom list_empty_prism = { [] }\<close>
by (auto simp add: prism_dom_def dom_def neq_Nil_conv list_empty_prism_def
  list_empty_prism_project_def) (metis list.case_eq_if option.distinct(1))

lemma list_empty_prism_valid [focus_intros]:
  shows \<open>is_valid_prism list_empty_prism\<close>
by (auto simp add: list_empty_prism_def list_empty_prism_project_def list_empty_prism_embed_def
  is_valid_prism_def split!: list.splits)

lift_definition list_empty_focus :: \<open>('a list, unit) focus\<close> is
  \<open>\<integral>'\<^sub>p list_empty_prism\<close>
using list_empty_prism_valid prism_to_focus_raw_valid by blast

text\<open>Use eta expansion during code generation to avoid ML value restriction\<close>
definition list_empty_focus_lazy :: \<open>unit \<Rightarrow> ('a list, unit) focus\<close> where
  \<open>list_empty_focus_lazy _ = list_empty_focus\<close>

declare list_empty_focus_lazy_def[of \<open>()\<close>, symmetric, code_unfold]
declare list_empty_focus_lazy_def[THEN  arg_cong[where f="Rep_focus"], simplified list_empty_focus.rep_eq, code]

lemmas list_empty_focus_components [focus_components] =
  prism_to_focus_components[OF list_empty_prism_valid, folded list_empty_focus_def,
    simplified list_empty_prism_dom, simplified prism_to_focus_raw_def, simplified]

text\<open>The special case of the prism/subtype of singleton lists\<close>

definition list_singleton_prism_project :: \<open>'a list \<Rightarrow> 'a option\<close> where
  \<open>list_singleton_prism_project ls \<equiv> if length ls = 1 then Some (hd ls) else None\<close>

definition list_singleton_prism_embed :: \<open>'a \<Rightarrow> 'a list\<close> where
  \<open>list_singleton_prism_embed x \<equiv> [x]\<close>

definition list_singleton_prism :: \<open>('a list, 'a) prism\<close> where
  \<open>list_singleton_prism \<equiv> make_prism list_singleton_prism_embed list_singleton_prism_project\<close>

lemma list_singleton_prism_dom:
  shows \<open>prism_dom list_singleton_prism = { xs . length xs = 1 }\<close>
by (clarsimp simp add: prism_dom_def dom_def list_singleton_prism_def list_singleton_prism_project_def)

lemma list_singleton_prism_valid [focus_intros]:
  shows \<open>is_valid_prism list_singleton_prism\<close>
by (clarsimp simp add: list_singleton_prism_def list_singleton_prism_project_def
  list_singleton_prism_embed_def is_valid_prism_def) (metis length_0_conv length_Suc_conv list.sel(1))

lift_definition list_singleton_focus :: \<open>('a list, 'a) focus\<close> is
  \<open>\<integral>'\<^sub>p list_singleton_prism\<close>
using list_singleton_prism_valid prism_to_focus_raw_valid by blast

text\<open>Use eta expansion during code generation to avoid ML value restriction:\<close>

definition list_singleton_focus_lazy :: \<open>unit \<Rightarrow> ('a list, 'a) focus\<close> where
  \<open>list_singleton_focus_lazy _ = list_singleton_focus\<close>

declare list_singleton_focus_lazy_def [symmetric, of \<open>()\<close>, code_unfold]
declare list_singleton_focus_lazy_def [THEN arg_cong[where f="Rep_focus"], simplified list_singleton_focus.rep_eq, code]

lemmas list_singleton_focus_components [focus_components] =
  prism_to_focus_components[OF list_singleton_prism_valid, folded list_singleton_focus_def,
    simplified list_singleton_prism_dom, simplified prism_to_focus_raw_def, simplified]

text\<open>The special case of non-empty lists\<close>

definition list_nonempty_prism_project :: \<open>'a list \<Rightarrow> ('a \<times> 'a list) option\<close> where
  \<open>list_nonempty_prism_project ls \<equiv> case ls of x # xs \<Rightarrow> Some (x, xs) | _ \<Rightarrow> None\<close>

definition list_nonempty_prism_embed :: \<open>'a \<times> 'a list \<Rightarrow> 'a list\<close> where
  \<open>list_nonempty_prism_embed t \<equiv> fst t#snd t\<close>

definition list_nonempty_prism :: \<open>('a list, 'a \<times> 'a list) prism\<close> where
  \<open>list_nonempty_prism \<equiv> make_prism list_nonempty_prism_embed list_nonempty_prism_project\<close>

lemma list_nonempty_prism_dom:
  shows \<open>prism_dom list_nonempty_prism = { ls . ls \<noteq> [] }\<close>
by (auto simp add: prism_dom_def list_nonempty_prism_def list_nonempty_prism_project_def dom_def list.case_eq_if)

lemma list_nonempty_prism_valid [focus_intros]:
  shows \<open>is_valid_prism list_nonempty_prism\<close>
by (auto simp add: list_nonempty_prism_def list_nonempty_prism_project_def list_nonempty_prism_embed_def
  is_valid_prism_def split!: list.splits)

lift_definition list_nonempty_focus :: \<open>('a list, 'a \<times> 'a list) focus\<close> is
  \<open>\<integral>'\<^sub>p list_nonempty_prism\<close>
using list_nonempty_prism_valid prism_to_focus_raw_valid by blast

text\<open>Use eta expansion during code generation to avoid ML value restriction:\<close>
definition list_nonempty_focus_lazy :: \<open>unit \<Rightarrow> ('a list, 'a \<times> 'a list) focus\<close> where
  \<open>list_nonempty_focus_lazy _ = list_nonempty_focus\<close>

declare list_nonempty_focus_lazy_def [symmetric, of \<open>()\<close>, code_unfold]
declare list_nonempty_focus_lazy_def [THEN arg_cong[where f="Rep_focus"], simplified list_nonempty_focus.rep_eq, code]

lemmas list_nonempty_focus_components[focus_components] =
  prism_to_focus_components[OF list_nonempty_prism_valid, folded list_nonempty_focus_def,
    simplified list_nonempty_prism_dom, simplified prism_to_focus_raw_def, simplified]

lemma nth_focus_valid_core:
  shows \<open>is_valid_view_modify (nth_opt idx) (over_nth idx)\<close>
by (clarsimp simp add: is_valid_view_modify_def over_nth_is_valid)

lift_definition nth_focus :: \<open>nat \<Rightarrow> ('v list, 'v) focus\<close> ("_\<^sub>t\<^sub>h") is
  \<open>\<lambda>idx. make_focus_raw_via_view_modify (nth_opt idx) (over_nth idx)\<close>
by (intro is_valid_focus_via_modifyI) (auto simp add: over_nth_is_valid)

lemma nth_focus_components[focus_components]:
  shows \<open>focus_view (nth_focus idx) = nth_opt idx\<close>
    and \<open>focus_update (nth_focus idx) v arr = list_update arr idx v\<close>
    and \<open>focus_modify n \<^sub>t\<^sub>h f x = x [n := f (x ! n)]\<close>
  apply (transfer; clarsimp simp add: make_focus_raw_via_view_modify_def)
  apply (transfer; clarsimp simp add: make_focus_raw_via_view_modify_def over_nth_list_update)
  apply (transfer; clarsimp simp add: make_focus_raw_via_view_modify_components nth_focus_valid_core
    over_nth_list_update)
  done

lemma nth_focus_view[focus_intros]:
  assumes \<open>n < length ls\<close>
      and \<open>x = ls ! n\<close>
    shows \<open>\<down>{n \<^sub>t\<^sub>h} ls \<doteq> x\<close>
using assms by (simp add: focus_components nth_opt_spec)

(*<*)
end
(*>*)