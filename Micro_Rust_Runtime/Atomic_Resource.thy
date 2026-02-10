(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Atomic_Resource
imports
  Separation_Lenses.SLens_Examples
  Separation_Lenses.SLens_Pullback
begin

section\<open>Reading/Writing non-spittable values\<close>

definition read_atomic_value_core :: \<open>('v option, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>read_atomic_value_core \<equiv> Expression (\<lambda>r.
     case r of 
        None \<Rightarrow> Abort DanglingPointer r
      | Some val \<Rightarrow> Success val r
  )\<close>

definition atomic_value_is :: \<open>'v \<Rightarrow> 'v option assert\<close> where
  \<open>atomic_value_is v \<equiv> { Some v }\<close>

lemma derived_order_option:
  shows \<open>Some x \<preceq> y \<longleftrightarrow> y = Some x\<close>
  by (auto simp add: derived_order_def disjoint_option_def plus_option_def
    split!: option.splits)

lemma ucincl_atomic_value_is [ucincl_intros]: \<open>ucincl (atomic_value_is v)\<close>
  unfolding atomic_value_is_def ucincl_def ucpred_def using derived_order_option 
  by force

lemma eval_read_atomic_value_core:
  shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>y,read_atomic_value_core\<rangle> (a, \<sigma>') \<longleftrightarrow> (\<sigma> = None \<and> a = DanglingPointer \<and> \<sigma> = \<sigma>')\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>y,read_atomic_value_core\<rangle> (v, \<sigma>') \<longleftrightarrow> (\<sigma>' = \<sigma> \<and> (case \<sigma> of None \<Rightarrow> False | Some v' \<Rightarrow> v = v'))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>y,read_atomic_value_core\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
  by (auto simp add: read_atomic_value_core_def evaluates_to_abort_def evaluates_to_value_def
    evaluates_to_return_def deep_evaluates_nondet_basic.simps evaluate_def split!: option.splits)

corollary eval_read_atomic_value_core_local:
  shows \<open>is_local (eval_value y read_atomic_value_core) (atomic_value_is v)\<close>
    and \<open>is_local (eval_return y read_atomic_value_core) (atomic_value_is v)\<close>
    and \<open>is_local (eval_abort y read_atomic_value_core) (atomic_value_is v)\<close>
  apply (intro is_localI; clarsimp simp add: asat_def uc_state_def
      eval_read_atomic_value_core eval_value_def atomic_value_is_def plus_option_def)
  apply (intro is_localI; clarsimp simp add: eval_return_def asat_def uc_state_def
      eval_read_atomic_value_core atomic_value_is_def plus_option_def)
  apply (intro is_localI; clarsimp simp add: asat_def uc_state_def
      eval_read_atomic_value_core eval_abort_def atomic_value_is_def plus_option_def)
  done

definition read_atomic_value :: \<open>('v option, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>read_atomic_value \<equiv> FunctionBody read_atomic_value_core\<close>

definition read_atomic_value_contract :: \<open>'v \<Rightarrow> ('v option, 'v, 'abort) function_contract\<close>
  where \<open>read_atomic_value_contract \<equiv> \<lambda>v.
     let pre = atomic_value_is v in
     let post = \<lambda>r. atomic_value_is v \<star> \<langle>r = v\<rangle> in
     make_function_contract pre post\<close>

lemma read_atomic_value_contract_no_abort:
  shows \<open>function_contract_abort (read_atomic_value_contract b) = \<bottom>\<close>
  by (simp add: read_atomic_value_contract_def pull_back_contract_def)

lemma read_atomic_value_spec:
  shows \<open>\<Gamma>; read_atomic_value \<Turnstile>\<^sub>F read_atomic_value_contract v\<close>
  apply (intro satisfies_function_contractI;
    clarsimp intro!: ucincl_intros simp add: read_atomic_value_contract_def)
  apply (intro sstripleI; clarsimp simp add: read_atomic_value_def atriple_rel_def
    asat_apure_distrib2 ucincl_intros asepconj_simp eval_read_atomic_value_core_local; safe?)
  apply (auto simp add: eval_read_atomic_value_core eval_return_def eval_abort_def eval_value_def
    asat_def atomic_value_is_def)
  done

definition write_atomic_value_core :: \<open>'v \<Rightarrow> ('v option, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>write_atomic_value_core val \<equiv> Expression (\<lambda>r.
     case r of  
        Some _ \<Rightarrow> Success () (Some val)
      | _ \<Rightarrow> Abort DanglingPointer r
  )\<close>

definition atomic_value_is_writable :: \<open>'v option assert\<close> where
  \<open>atomic_value_is_writable \<equiv> { \<sigma>. case \<sigma> of None \<Rightarrow> False | Some _ \<Rightarrow> True }\<close>

lemma atomic_value_is_writableE:
  assumes \<open>\<sigma> \<Turnstile> atomic_value_is_writable\<close>
  and \<open>\<And>v. \<sigma> = Some v \<Longrightarrow> R\<close>
  shows R
  using assms by (auto simp add: asat_def atomic_value_is_writable_def split!: option.splits)

lemma atomic_value_is_writable_alt:
  shows \<open>(\<Squnion>v0. atomic_value_is v0) = atomic_value_is_writable\<close> 
  apply (intro asat_semequivI;
    clarsimp simp add: atomic_value_is_def atomic_value_is_writable_def 
    split!: option.splits elim!: atomic_value_is_writableE; 
    clarsimp simp add: asat_def atomic_value_is_def)
  done

lemma atomic_value_is_writable_ucincl[ucincl_intros]:
  shows \<open>ucincl atomic_value_is_writable\<close>
  by (clarsimp intro!: ucincl_intros simp flip: atomic_value_is_writable_alt)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma atomic_value_is_writable_basic:
  shows \<open>Some v \<Turnstile> atomic_value_is_writable\<close>
  by (simp add: asat_def atomic_value_is_writable_def)

lemma eval_write_atomic_value_core:
  shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>y,write_atomic_value_core val\<rangle> (a, \<sigma>') \<longleftrightarrow> ( \<not>(\<sigma> \<Turnstile> atomic_value_is_writable) \<and> a = DanglingPointer \<and> \<sigma> = \<sigma>')\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>y,write_atomic_value_core val\<rangle> (v, \<sigma>') \<longleftrightarrow> (\<sigma> \<Turnstile> atomic_value_is_writable \<and> \<sigma>' = Some val)\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>y,write_atomic_value_core val\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
  by (auto simp add: write_atomic_value_core_def evaluates_to_abort_def evaluates_to_value_def
    asat_def atomic_value_is_writable_def evaluates_to_return_def deep_evaluates_nondet_basic.simps evaluate_def 
    split!: option.splits if_splits)

corollary eval_write_atomic_value_core_local:
  shows \<open>is_local (eval_value y (write_atomic_value_core val)) atomic_value_is_writable\<close>
    and \<open>is_local (eval_return y (write_atomic_value_core val)) atomic_value_is_writable\<close>
    and \<open>is_local (eval_abort y (write_atomic_value_core val)) atomic_value_is_writable\<close>
  apply (intro is_localI; auto simp add: eval_value_def eval_write_atomic_value_core
    disjoint_option_def asat_def plus_option_def atomic_value_is_writable_def split!: option.splits)
  apply (intro is_localI; simp add: eval_return_def eval_write_atomic_value_core)
  apply (intro is_localI; simp add: eval_abort_def eval_write_atomic_value_core)
  using asat_weaken atomic_value_is_writable_ucincl apply blast
  done

definition write_atomic_value :: \<open>'v \<Rightarrow> ('v option, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>write_atomic_value val \<equiv> FunctionBody (write_atomic_value_core val)\<close>

definition write_atomic_value_contract :: \<open>'v \<Rightarrow> ('v option, unit, 'abort) function_contract\<close>
  where \<open>write_atomic_value_contract \<equiv> \<lambda>v.
     let pre = \<Squnion>v0. atomic_value_is v0 in
     let post = \<lambda>r. atomic_value_is v in
     make_function_contract pre post\<close>

lemma write_atomic_value_contract_no_abort:
  shows \<open>function_contract_abort (write_atomic_value_contract a) = \<bottom>\<close>
  by (simp add: write_atomic_value_contract_def pull_back_contract_def)

lemma write_atomic_value_spec:
  shows \<open>\<Gamma>; write_atomic_value v \<Turnstile>\<^sub>F write_atomic_value_contract v\<close>
  apply (intro satisfies_function_contractI;
    clarsimp intro!: ucincl_intros simp add: write_atomic_value_contract_def)
  apply (intro sstripleI; clarsimp simp add: atomic_value_is_writable_alt write_atomic_value_def 
    asat_apure_distrib2 ucincl_intros asepconj_simp eval_write_atomic_value_core_local atriple_rel_def; safe?)
  apply (auto simp add: eval_write_atomic_value_core atomic_value_is_def zero_share_def
    eval_return_def eval_value_def eval_abort_def asat_def) 
  done

text\<open>In any interesting application, the underlying separation algebra will not be equal to 
\<^verbatim>\<open>atomic_value\<close>, but contain it via a separation lens. In this case, we can use the pullback
mechanism to obtain read/write functions on the larger separation algebra:\<close>

type_synonym ('s, 'v) atomic_resource = \<open>('s, 'v option) lens\<close>

definition atomic_resource_is :: \<open>('s, 'v) atomic_resource \<Rightarrow> 'v \<Rightarrow> 's assert\<close>
  where \<open>atomic_resource_is l v \<equiv> l\<inverse> (atomic_value_is v)\<close>

definition read_atomic_resource :: \<open>('s, 'v) atomic_resource \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>
  where \<open>read_atomic_resource l \<equiv> l\<inverse> read_atomic_value\<close>

definition write_atomic_resource :: \<open>('s, 'v) atomic_resource\<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  where \<open>write_atomic_resource l v \<equiv> l\<inverse> (write_atomic_value v)\<close>

definition read_atomic_resource_contract :: \<open>('s::sepalg, 'v) atomic_resource \<Rightarrow> 'v \<Rightarrow> ('s, 'v, 'abort) function_contract\<close>
  where \<open>read_atomic_resource_contract l v \<equiv> l\<inverse> (read_atomic_value_contract v)\<close>

lemma read_atomic_resource_contract_no_abort:
  shows \<open>function_contract_abort (read_atomic_resource_contract a b) = \<bottom>\<close>
  by (simp add: read_atomic_value_contract_no_abort read_atomic_resource_contract_def pull_back_contract_def
    pull_back_assertion_def bot_fun_def)

definition write_atomic_resource_contract :: \<open>('s::sepalg, 'v) atomic_resource \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close>
  where \<open>write_atomic_resource_contract l v \<equiv> l\<inverse> (write_atomic_value_contract v)\<close>

lemma write_atomic_resource_contract_no_abort:
  shows \<open>function_contract_abort (write_atomic_resource_contract a b) = \<bottom>\<close>
  by (simp add: write_atomic_value_contract_no_abort write_atomic_resource_contract_def pull_back_contract_def
    pull_back_assertion_def bot_fun_def)

lemma read_atomic_resource_spec:
  assumes \<open>is_valid_slens l\<close>
  shows \<open>\<Gamma>; read_atomic_resource l \<Turnstile>\<^sub>F read_atomic_resource_contract l v\<close>
  by (simp add: assms slens.pull_back_spec_universal read_atomic_resource_contract_def read_atomic_resource_def
    read_atomic_value_spec read_atomic_value_contract_no_abort)

lemma write_atomic_resource_spec:
  assumes \<open>is_valid_slens l\<close>
  shows \<open>\<Gamma>; write_atomic_resource l v \<Turnstile>\<^sub>F write_atomic_resource_contract l v\<close>
  by (simp add: assms slens.pull_back_spec_universal write_atomic_resource_contract_def write_atomic_resource_def
    write_atomic_value_spec write_atomic_value_contract_no_abort)

end