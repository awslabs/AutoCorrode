(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Stack
  imports
    Micro_Rust_Examples.Linked_List
begin

section\<open>Stack\<close>

text\<open>Linked-list backed uRust stack type.\<close>

locale stack =
    ll_example _ _ _ _ _ _ _ reference_types ref_gref_opt_prism \<open>iso_prism id id\<close> ll_focus
  + ref_ll_node: reference_allocatable reference_types _ _ _ _ _ _ _ node_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
    ref_gref_opt_prism :: \<open>('gv, ('addr, 'gv) gref option) prism\<close> and
    ll_focus :: \<open>('gv, ('addr, 'gv, 't) ll_node_raw) focus\<close> and
    node_prism :: \<open>('gv, ('addr, 'gv, 't) ll_node_raw) prism\<close>
  + assumes ll_focus_node_prism: \<open>ll_focus = prism_to_focus node_prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_ll_node.new

lemma prism_embed_iso_prism_id [simp]: \<open>prism_embed (iso_prism id id) = id\<close>
  by (auto simp: iso_prism_def)

lemma gref_map_id [simp]: \<open>gref_map id = id\<close>
  by (auto simp: gref_map_def)

abbreviation gref_of_ref ::
  \<open>('addr, 'gv, ('addr, 'gv, 't) ll_node_raw) Global_Store.ref \<Rightarrow> ('addr, 'gv) gref\<close> where
  \<open>gref_of_ref r \<equiv> unwrap_focused r\<close>

\<comment> \<open>Separation logic predicate relating a stack reference and a list\<close>

definition stack_points_to :: \<open>'t list \<Rightarrow> ('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow> 's assert\<close>
  where \<open>stack_points_to ts s \<equiv> (\<Squnion>b h. s \<mapsto>\<langle>\<top>\<rangle> b\<down>h \<star> ll_points_to ts h None)\<close>

lemma ucincl_stack_points_to [ucincl_intros]:
  shows \<open>ucincl (stack_points_to ts s)\<close>
  unfolding stack_points_to_def by (auto intro!: ucincl_intros)

lemma ll_ptr_as_ref'_gref_of_ref:
  assumes \<open>\<integral> xa = \<integral>\<^sub>p node_prism\<close>
  shows \<open>ll_ptr_as_ref' (gref_of_ref xa) = xa\<close>
  using assms by (simp add: ll_focus_node_prism focused.expand)

subsection\<open>Empty\<close>

definition empty ::
  \<open>('s, ('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>empty \<equiv> FunctionBody \<lbrakk>
     let mut s = \<llangle>None :: ('addr, 'gv) gref option\<rrangle>;
     s
   \<rbrakk>\<close>

definition empty_contract ::
  \<open>('s, ('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>empty_contract \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> stack_points_to [] r in
     make_function_contract pre post\<close>
ucincl_auto empty_contract

lemma empty_spec [crush_specs]:
  shows \<open>\<Gamma>; empty \<Turnstile>\<^sub>F empty_contract\<close>
  apply (crush_boot f: empty_def contract: empty_contract_def)
  apply (clarsimp simp add: stack_points_to_def ll_points_to_None asepconj_simp)
  apply crush_base
  done

subsection\<open>Push\<close>

definition push :: \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow> 't \<Rightarrow>
     ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>push s x \<equiv> FunctionBody \<lbrakk>
     let h = *s;
     let mut node = \<llangle>make_ll_node_raw x\<rrangle>\<^sub>1(h);
     s = Some(\<llangle>gref_of_ref\<rrangle>\<^sub>1(node))
   \<rbrakk>\<close>

definition push_contract ::
  \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow> 't \<Rightarrow> 't list \<Rightarrow>
   ('s, unit, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>push_contract s x ts \<equiv>
     let pre = can_alloc_reference \<star> stack_points_to ts s in
     let post = \<lambda>_. can_alloc_reference \<star> stack_points_to (x # ts) s in
     make_function_contract pre post\<close>
ucincl_auto push_contract

lemma push_spec [crush_specs]:
  shows \<open>\<Gamma>; push s x \<Turnstile>\<^sub>F push_contract s x ts\<close>
  apply (crush_boot f: push_def contract: push_contract_def)
  apply (clarsimp simp add: stack_points_to_def)
  apply crush_base
  apply (simp_all add: ll_focus_node_prism aentails_refl is_valid_ref_for_def)
  done

subsection\<open>Pop\<close>

definition pop :: \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow>
     ('s, 't option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>pop s \<equiv> FunctionBody \<lbrakk>
     match *s {
       None \<Rightarrow> None,
       Some(r) \<Rightarrow> {
         let node = *\<llangle>ll_ptr_as_ref'\<rrangle>\<^sub>1(r);
         s = \<llangle>ll_node_raw.next\<rrangle>\<^sub>1(node);
         Some(\<llangle>ll_node_raw.data\<rrangle>\<^sub>1(node))
       }
     }
   \<rbrakk>\<close>

definition pop_contract ::
  \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow> 't list \<Rightarrow>
   ('s, 't option, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>pop_contract s ts \<equiv>
     let pre = stack_points_to ts s in
     let post = \<lambda>r. (case ts of
          []    \<Rightarrow> stack_points_to [] s \<star> \<langle>r = None\<rangle>
        | x#xs  \<Rightarrow> stack_points_to xs s \<star> \<langle>r = Some x\<rangle>) in
     make_function_contract pre post\<close>
ucincl_proof pop_contract
  by (auto split: list.splits intro: ucincl_intros)

lemma pop_spec [crush_specs]:
  shows \<open>\<Gamma>; pop s \<Turnstile>\<^sub>F pop_contract s ts\<close>
  apply (crush_boot f: pop_def contract: pop_contract_def)
  apply (cases ts; clarsimp simp add: stack_points_to_def ll_points_to_None asepconj_simp)
   apply (crush_base split!: option.splits)+
  done

subsection\<open>Is-empty\<close>

definition is_empty :: \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow>
     ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>is_empty s \<equiv> FunctionBody \<lbrakk>
     match *s { None \<Rightarrow> True, Some(_) \<Rightarrow> False }
   \<rbrakk>\<close>

definition is_empty_contract ::
  \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow> 't list \<Rightarrow>
   ('s, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>is_empty_contract s ts \<equiv>
     let pre = stack_points_to ts s in
     let post = \<lambda>r. stack_points_to ts s \<star> \<langle>r \<longleftrightarrow> ts = []\<rangle> in
     make_function_contract pre post\<close>
ucincl_auto is_empty_contract

lemma is_empty_spec [crush_specs]:
  shows \<open>\<Gamma>; is_empty s \<Turnstile>\<^sub>F is_empty_contract s ts\<close>
  apply (crush_boot f: is_empty_def contract: is_empty_contract_def)
  apply (cases ts; clarsimp simp add: stack_points_to_def ll_points_to_None asepconj_simp)
   apply (crush_base split!: option.splits)+
  done

subsection\<open>Push-all\<close>

definition push_all :: \<open>('addr, 'gv, ('addr, 'gv) gref option) Global_Store.ref \<Rightarrow> 't list \<Rightarrow>
     ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>push_all s xs \<equiv> FunctionBody \<lbrakk>
     for w in \<llangle>xs\<rrangle> {
       push(s, w);
     }
   \<rbrakk>\<close>

definition push_all_contract where
  [crush_contracts]: \<open>push_all_contract s xs ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star> stack_points_to ts s)
       (\<lambda>_. can_alloc_reference \<star> stack_points_to (rev xs @ ts) s)\<close>
ucincl_auto push_all_contract

lemma push_all_spec [crush_specs]:
  shows \<open>\<Gamma>; push_all s xs \<Turnstile>\<^sub>F push_all_contract s xs ts\<close>
  apply (crush_boot f: push_all_def contract: push_all_contract_def)
  apply (crush_base simp add: list_into_iter_def)
  apply (ucincl_discharge\<open>
    rule_tac
      INV = \<open>\<lambda>_ i. can_alloc_reference \<star> stack_points_to (rev (take i xs) @ ts) s\<close> and
      \<tau>   = \<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>   = \<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'
  \<close>)
  subgoal by crush_base
  subgoal by (crush_base simp add: take_Suc_conv_app_nth)
  done

end

end
