(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Global_Perm_Store
  imports Micro_Rust_Interfaces_Core.References Shallow_Micro_Rust.Global_Store
begin
(*>*)

locale global_perm_store = store: global_store store_read_reference store_write_reference
                              store_allocate_reference
      for store_read_reference :: \<open>'s::{sepalg} \<Rightarrow> 'a \<rightharpoonup> 'b\<close>
      and store_write_reference :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 'b \<rightharpoonup> 's\<close>
      and store_allocate_reference :: \<open>'s \<rightharpoonup> ('a \<times> 's)\<close> +
    fixes store_perm_map :: \<open>'s \<Rightarrow> 'a \<Rightarrow> share\<close>
      and store_alloc_pool :: \<open>'s \<Rightarrow> 'a set\<close>
      and store_has_valid_allocator :: \<open>'s \<Rightarrow> bool\<close>
  assumes store_pool_inf: \<open>\<And>s. store_alloc_pool s = {} \<or> infinite (store_alloc_pool s)\<close>
      and store_alloc_unique: \<open>\<And>s1 s2. s1\<sharp>s2 \<Longrightarrow> store_alloc_pool s1 = {} \<or> store_alloc_pool s2 = {}\<close>
      and read_perm_succeeds: \<open>\<And>s a. store_perm_map s a > 0 \<longleftrightarrow> (\<exists>v. store_read_reference s a = Some v)\<close>
      and write_perm_succeeds: \<open>\<And>s a v. store_perm_map s a = \<top> \<longleftrightarrow> (\<exists>s'. store_write_reference s a v = Some s')\<close>
      and allocate_succeeds : \<open>\<And>s. store_alloc_pool s \<noteq> {} \<longleftrightarrow> (\<exists>a s'. store_allocate_reference s = Some (a,s'))\<close>
      and store_disjoint_perm: \<open>\<And>s1 s2. s1 \<sharp> s2 \<Longrightarrow> (\<forall>a. store_perm_map s1 a \<sharp> store_perm_map s2 a)\<close>
      and store_disjoint_pool: \<open>\<And>s1 s2. s1 \<sharp> s2 \<Longrightarrow> store_alloc_pool s1 \<sharp> store_alloc_pool s2\<close>
      and store_add_perm: \<open>\<And>s1 s2 a. s1 \<sharp> s2 \<Longrightarrow>
            store_perm_map (s1+s2) a = store_perm_map s1 a \<squnion> store_perm_map s2 a\<close>
      and store_add_pool: \<open>\<And>s1 s2. s1 \<sharp> s2 \<Longrightarrow>
            store_alloc_pool (s1 + s2) = store_alloc_pool s1 \<union> store_alloc_pool s2\<close>
      and store_add_read: \<open>\<And>s1 s2 a v. store_read_reference s1 a = Some v \<Longrightarrow> s1 \<sharp> s2 \<Longrightarrow> 
            store_read_reference (s1+s2) a = Some v\<close>
      and store_add_write: \<open>\<And>s1 s1' s2 a v. store_write_reference s1 a v = Some s1' \<Longrightarrow> s1 \<sharp> s2 \<Longrightarrow> 
            store_write_reference (s1+s2) a v = Some (s1'+s2) \<and> s1'\<sharp>s2\<close>
      and store_add_alloc: \<open>\<And>s1 s1' s2 a. s1 \<sharp> s2 \<Longrightarrow> store_allocate_reference s1 = Some (a, s1') \<Longrightarrow>
            store_allocate_reference (s1 + s2) = Some (a, s1' + s2) \<and> s1' \<sharp> s2\<close>
      and store_add_valid_allocator: \<open>\<And>s1 s2. s1\<sharp>s2 \<Longrightarrow> store_has_valid_allocator s1 \<Longrightarrow>
            store_has_valid_allocator (s1 + s2)\<close>
      and store_write_valid_allocator: \<open>\<And>s a v s'. store_has_valid_allocator s \<Longrightarrow>
            store_write_reference s a v = Some s' \<Longrightarrow> store_has_valid_allocator s'\<close>
      and store_alloc_valid_allocator: \<open>\<And>s a s'. store_has_valid_allocator s \<Longrightarrow>
            store_allocate_reference s = Some (a, s') \<Longrightarrow> store_has_valid_allocator s'\<close>
      and store_write_pool: \<open>\<And>s a v s'. store_write_reference s a v = Some s' \<Longrightarrow>
            store_alloc_pool s = store_alloc_pool s'\<close>
      and allocate_full_share: \<open>\<And>s a s'. store_allocate_reference s = Some (a, s') \<Longrightarrow>
            a \<in> store_alloc_pool s \<and> store_alloc_pool s' = store_alloc_pool s - {a} \<and>
              store_perm_map s' a = \<top>\<close>
      and store_split_allocator: \<open>\<And>s. store_has_valid_allocator s \<Longrightarrow> \<exists>s1 s2. s = s1 + s2 \<and>
            s1 \<sharp> s2 \<and> store_has_valid_allocator s1 \<and> store_alloc_pool s1 = store_alloc_pool s \<and>
            store_alloc_pool s2 = {} \<and> (\<forall>a. store_perm_map s1 a = \<bottom>) \<and>
              (\<forall>a. store_perm_map s2 a = store_perm_map s a)\<close>
      and store_split_perm: \<open>\<And>s p1 p2. p1 \<sharp> p2 \<Longrightarrow> store_perm_map s = p1 + p2 \<Longrightarrow>
           \<exists>s1 s2. s1 \<sharp> s2 \<and> s = s1 + s2 \<and> store_perm_map s1 = p1 \<and> store_perm_map s2 = p2\<close>
begin

definition points_to_raw' :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 's assert\<close> where
  \<open>points_to_raw' r sh b \<equiv> {s. 0 < sh \<and> sh \<le> store_perm_map s (address r) \<and>
            store_read_reference s (address r) = Some b}\<close>

notation points_to_raw' ("(_) \<mapsto> \<langle>_\<rangle> (_)" [69,0,69]70)

lemma ucincl_points_to_raw'I [ucincl_intros]:
  shows \<open>ucincl (points_to_raw' r sh v)\<close>
by (simp add: ucincl_def ucpred_def points_to_raw'_def) (metis derived_order_def le_supI1
  store_add_perm store_add_read)

lemma points_to_aentails_rawI [intro]:
  assumes \<open>sh1 \<ge> sh2\<close>
      and \<open>0 < sh2\<close>
      and \<open>g1 = g2\<close>
    shows \<open>r \<mapsto> \<langle>sh1\<rangle> g1 \<longlongrightarrow> r \<mapsto>\<langle>sh2\<rangle> g2\<close>
using assms by (auto simp add: aentails_def points_to_raw'_def asat_def)

lemma points_to_raw'I [intro]:
  assumes \<open>0 < sh\<close>
      and \<open>sh \<le> store_perm_map s (address r)\<close>
      and \<open>store_read_reference s (address r) = Some b\<close>
    shows \<open>s \<Turnstile> r \<mapsto>\<langle>sh\<rangle> b\<close>
using assms by (auto simp add: asat_def points_to_raw'_def)

lemma points_to_raw'E [elim]:
  assumes \<open>s \<Turnstile> r \<mapsto>\<langle>sh\<rangle> b\<close>
      and \<open>0 < sh \<Longrightarrow> sh \<le> store_perm_map s (address r) \<Longrightarrow>
              store_read_reference s (address r) = Some b \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: asat_def points_to_raw'_def)

lemma points_to_raw_combine':
  shows \<open>r \<mapsto>\<langle>sh1\<rangle> v1 \<star> r \<mapsto>\<langle>sh2\<rangle> v2 \<longlongrightarrow> r \<mapsto>\<langle>sh1+sh2\<rangle> v1 \<star> \<langle>v1 = v2\<rangle>\<close>
proof (rule aentailsI)
  fix x
  assume \<open>x \<Turnstile> r \<mapsto> \<langle>sh1\<rangle> v1 \<star> r \<mapsto> \<langle>sh2\<rangle> v2\<close>
  moreover from this obtain y z where \<open>x = y + z\<close> and \<open>y \<sharp> z\<close> and \<open>y \<Turnstile> r \<mapsto> \<langle>sh1\<rangle> v1\<close> and \<open>z \<Turnstile> r \<mapsto> \<langle>sh2\<rangle> v2\<close>
    by (elim asepconjE)
  moreover from this have \<open>0 < sh1\<close> and \<open>sh1 \<le> store_perm_map y (address r)\<close> and
      \<open>store_read_reference y (address r) = Some v1\<close> and \<open>0 < sh2\<close> and
      \<open>sh2 \<le> store_perm_map z (address r)\<close> and \<open>store_read_reference z (address r) = Some v2\<close>
    by auto
  moreover from calculation have \<open>0 < sh1 + sh2\<close>
    using less_supI2 plus_share_def by auto
  moreover from calculation have \<open>sh1 + sh2 \<le> store_perm_map x (address r)\<close>
    by (metis plus_share_def store_add_perm sup_mono)
  moreover from calculation have \<open>store_read_reference x (address r) = Some v1\<close>
    using store_add_read by blast
  moreover from calculation have \<open>x \<Turnstile> r \<mapsto> \<langle>sh1 + sh2\<rangle> v1\<close>
    by auto
  moreover from calculation have \<open>v1 = v2\<close>
    by (metis disjoint_sym option.inject sepalg_comm store_add_read)
  ultimately show \<open>x \<Turnstile> r \<mapsto> \<langle>sh1 + sh2\<rangle> v1 \<star> \<langle>v1 = v2\<rangle>\<close>
    by (simp add: asat_apure_precise_distrib2)
qed

lemma points_to_raw_split1:
  assumes \<open>x \<Turnstile> r \<mapsto>\<langle>sh\<rangle> v\<close>
      and \<open>sh = sh1 + sh2\<close>
      and \<open>sh1 \<sharp> sh2\<close>
      and \<open>0 < sh1\<close>
      and \<open>0 < sh2\<close>
    shows \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
proof -
  let ?shr = \<open>store_perm_map x (address r)\<close>
  let ?shr' = \<open>?shr - sh1\<close>
  let ?p1 = \<open>0( address r := sh1)\<close>
  let ?p2 = \<open>(store_perm_map x)( address r := ?shr' )\<close>
  from assms have \<open>0 < sh\<close> and \<open>sh \<le> ?shr\<close> and
    \<open>store_read_reference x (address r) = Some v\<close> by auto
  moreover from this and assms have \<open>sh2 \<le> ?shr'\<close>
    by (clarsimp simp add: plus_share_def disjoint_share_def) (metis diff_eq inf_shunt
      inf_sup_aci(1) le_infI)
  moreover from assms have \<open>sh1 \<sharp> ?shr'\<close>
    by (simp add: diff_eq disjoint_share_def)
  moreover from calculation assms have \<open>?shr = sh1 \<squnion> ?shr'\<close>
    by (metis (no_types, lifting) diff_eq inf.absorb1 inf.cobounded2 le_iff_sup le_supE
      plus_share_def shunt2 sup_inf_distrib1)
  moreover from calculation have \<open>?p1 \<sharp> ?p2\<close>
    by (metis (mono_tags, lifting) disjoint_fun_def fun_upd_apply zero_disjoint2)
  moreover from calculation and assms  have \<open>store_perm_map x = ?p1 + ?p2\<close>
    by (intro ext) (auto simp add: diff_eq zero_fun_def plus_share_def plus_fun_def zero_share_def)
  moreover from calculation and assms obtain x1 x2 where \<open>x1 \<sharp> x2\<close> and \<open>x = x1 + x2\<close> and
        \<open>store_perm_map x1 = ?p1\<close> and \<open>store_perm_map x2 = ?p2\<close>
    using store_split_perm[of ?p1 ?p2 x] by fast
  moreover from assms and calculation have \<open>store_read_reference x1 (address r) = Some v\<close>
    using read_perm_succeeds store_add_read by (metis fun_upd_same)
  moreover from assms and calculation have \<open>store_read_reference x2 (address r) = Some v\<close>
    using read_perm_succeeds store_add_read by (metis disjoint_sym fun_upd_same inf.absorb_iff2
        less_supI2 sepalg_comm sup_inf_absorb)
  moreover from calculation and assms have \<open>x1 \<Turnstile> r\<mapsto>\<langle>sh1\<rangle> v\<close>
    by (intro points_to_raw'I) auto
  moreover from calculation and assms have \<open>x2 \<Turnstile> r\<mapsto>\<langle>sh2\<rangle> v\<close>
    by (intro points_to_raw'I) auto
  ultimately show \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r\<mapsto>\<langle>sh2\<rangle> v\<close>
    by (intro asepconjI) auto
qed

definition can_alloc_reference :: \<open>'s assert\<close> where
  \<open>can_alloc_reference \<equiv> {s. store_alloc_pool s \<noteq> {} \<and> store_has_valid_allocator s}\<close>

lemma ucincl_can_alloc_referenceI [ucincl_intros]:
  shows \<open>ucincl can_alloc_reference\<close>
by (auto simp add: ucincl_def ucpred_def derived_order_def can_alloc_reference_def
  store_add_pool store_add_valid_allocator)

lemma points_to_raw_split'':
  assumes \<open>sh = sh1+sh2\<close>
      and \<open>sh1 \<sharp> sh2\<close>
      and \<open>0 < sh1\<close>
      and \<open>0 < sh2\<close>
    shows \<open>r \<mapsto>\<langle>sh\<rangle> v \<longlongrightarrow> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
proof (unfold aentails_def, intro allI impI)
  fix x
  assume \<open>x \<Turnstile> r \<mapsto>\<langle>sh\<rangle> v\<close>
  moreover from assms and calculation have \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
    by (intro points_to_raw_split1) auto
  ultimately show \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
    by (auto intro: asepconjI)
qed

lemma alloc_and_write_spec_raw:
  assumes \<open>s \<Turnstile> can_alloc_reference\<close>
      and \<open>store_write_reference s a v = Some s'\<close>
    shows \<open>s' \<Turnstile> (make_untyped_ref a) \<mapsto>\<langle>\<top>\<rangle> v \<star> can_alloc_reference\<close>
proof -
  from assms obtain s1 s2 where \<open>s'=s1 + s2\<close> and \<open>s1 \<sharp> s2\<close> and
        \<open>store_alloc_pool s1 = store_alloc_pool s'\<close> and \<open>store_alloc_pool s2 = {}\<close> and
        \<open>store_has_valid_allocator s1\<close> and \<open>\<And>a. store_perm_map s1 a = \<bottom>\<close> and
        \<open>\<And>a. store_perm_map s2 a = store_perm_map s' a\<close>
    using store_split_allocator store_write_valid_allocator by (clarsimp simp add:
      can_alloc_reference_def asat_def) blast
  moreover from assms and calculation have \<open>s1 \<Turnstile> can_alloc_reference\<close>
    by (clarsimp simp add: can_alloc_reference_def asat_def) (metis store_write_pool)
  moreover from assms and calculation have \<open>store_perm_map s2 a = \<top>\<close>
    by (metis store.write_store_write_store write_perm_succeeds)
  moreover from this obtain b where \<open>store_read_reference s2 a = Some b\<close>
    by (metis read_perm_succeeds shares_nontrivial zero_share_def)
  moreover from assms and calculation have \<open>store_read_reference s2 a = Some v\<close>
    by (metis disjoint_sym sepalg_comm store.write_store_read_store store_add_read)
  moreover from assms and calculation have \<open>s2 \<Turnstile> (make_untyped_ref a) \<mapsto>\<langle>\<top>\<rangle> v\<close>
    by (clarsimp simp add: points_to_raw'_def asat_def make_untyped_ref_def zero_share_def)
  ultimately show \<open>s' \<Turnstile>(make_untyped_ref a) \<mapsto> \<langle>\<top>\<rangle> v \<star> can_alloc_reference\<close>
    by (simp add: asepconjI asepconj_comm)
qed

subsection\<open>Reference allocation\<close>

lemma urust_eval_predicate_reference_raw:
  shows \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>, store.reference_raw g\<rangle> (a, \<sigma>')) \<longleftrightarrow> (
             (store_allocate_reference \<sigma> = None \<and> AssertionFailed = a \<and> \<sigma> = \<sigma>') \<or>
             (\<exists>\<sigma>'' addr. store_allocate_reference \<sigma> = Some (addr, \<sigma>'') \<and>
                  store_write_reference \<sigma>'' addr g = None \<and>
                  a = AssertionFailed \<and> \<sigma>' = \<sigma>''))\<close> (is ?abort)
    and \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>, store.reference_raw g\<rangle> (v,\<sigma>'')) \<longleftrightarrow> (
         \<exists>\<sigma>' addr. store_allocate_reference \<sigma> = Some (addr, \<sigma>') \<and>
                   store_write_reference \<sigma>' addr g = Some \<sigma>'' \<and>
                   make_untyped_ref addr = v)\<close> (is ?value)
    and \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>, store.reference_raw g\<rangle> (r,\<sigma>')) \<longleftrightarrow> False\<close> (is ?return)
proof
  assume \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, store.reference_raw g\<rangle> (a, \<sigma>')\<close>
  from this show \<open>store_allocate_reference \<sigma> = None \<and> AssertionFailed = a \<and> \<sigma> = \<sigma>' \<or>
        (\<exists>\<sigma>'' addr. store_allocate_reference \<sigma> = Some (addr, \<sigma>'') \<and>
          store_write_reference \<sigma>'' addr g = None \<and> a = AssertionFailed \<and> \<sigma>' = \<sigma>'')\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps
      store.reference_raw_def evaluate_def call_def call_function_body.simps
      split!: option.splits expression.splits continuation.splits)
next
  assume \<open>store_allocate_reference \<sigma> = None \<and> AssertionFailed = a \<and> \<sigma> = \<sigma>' \<or> (\<exists>\<sigma>'' addr.
            store_allocate_reference \<sigma> = Some (addr, \<sigma>'') \<and>
            store_write_reference \<sigma>'' addr g = None \<and> a = AssertionFailed \<and> \<sigma>' = \<sigma>'')\<close>
  from this show \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>,store.reference_raw g\<rangle> (a, \<sigma>')\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps
      store.reference_raw_def evaluate_def call_def call_function_body.simps
      split!: option.splits expression.splits continuation.splits)
next
  show \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, store.reference_raw g\<rangle> (v,\<sigma>'') = (\<exists>\<sigma>' addr.
          store_allocate_reference \<sigma> = Some (addr, \<sigma>') \<and>
            store_write_reference \<sigma>' addr g = Some \<sigma>'' \<and> make_untyped_ref addr = v)\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps make_untyped_ref_def
      store.reference_raw_def evaluate_def call_def call_function_body.simps
      split!: option.splits expression.splits continuation.splits)
next
  show \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>,store.reference_raw g\<rangle> (r,\<sigma>') = False\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps
      store.reference_raw_def evaluate_def split!: option.splits)
qed

corollary urust_eval_predicate_reference_raw_local:
  shows \<open>urust_is_local \<Gamma> (store.reference_raw g) can_alloc_reference\<close>
proof (intro conjI)
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>')) can_alloc_reference\<close>
  proof (clarsimp simp add: urust_eval_predicate_reference_raw is_local_def
    can_alloc_reference_def asat_def, safe, goal_cases)
    case (1 \<sigma>_0 \<sigma>_1 x \<sigma>_0' \<sigma>' addr)
    then show ?case 
      by (meson disjoint_sym global_perm_store.store_add_alloc global_perm_store_axioms store_add_write)
  next
    case (2 \<sigma>_0 \<sigma>_1 x \<sigma>' v \<sigma>'' addr) note assms = this
    obtain \<sigma>_0' addr' where \<open>store_allocate_reference \<sigma>_0 = Some (addr', \<sigma>_0')\<close>
      using allocate_succeeds assms by blast
    moreover from this and assms have \<open>addr' = addr\<close> and \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close> and \<open>\<sigma>'' = \<sigma>_0' + \<sigma>_1\<close>
      using store_add_alloc by force+
    ultimately show ?case using assms
      by (metis option.inject store.allocate_write_succeeds store_add_write)
  next
    case (3 \<sigma>_0 \<sigma>_1 x \<sigma>' v \<sigma>_0' \<sigma>'' addr)
    then show ?case using store_add_alloc store_add_write by blast
  qed
next
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>')) can_alloc_reference\<close>
    by (clarsimp simp add: is_local_def asat_def urust_eval_predicate_reference_raw)
next
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>')) can_alloc_reference\<close>
    apply (clarsimp simp add: urust_eval_predicate_reference_raw is_local_def allocate_succeeds 
      can_alloc_reference_def asat_def )
    by (metis option.distinct(1) store.allocate_write_succeeds store_add_alloc)
qed

lemma asat_hoist_pure_precise:
  shows \<open>\<phi> \<Turnstile> \<langle>P\<rangle> \<star> \<xi> \<longleftrightarrow> (P \<and> (\<phi> \<Turnstile> \<xi>))\<close> (is ?g1)
    and \<open>\<phi> \<Turnstile> \<xi> \<star> \<langle>P\<rangle> \<longleftrightarrow> ((\<phi> \<Turnstile> \<xi>) \<and> P)\<close> (is ?g2)
proof -
  show ?g1
    by (rule asat_apure_precise_distrib)
  show ?g2
    by (rule asat_apure_precise_distrib2)
qed

lemma is_local_store_reference_raw:
    shows \<open>is_local (\<lambda>\<sigma> (va, \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>,store.reference_raw g\<rangle> (va,\<sigma>')) can_alloc_reference\<close>
      and \<open>is_local (\<lambda>\<sigma> (va, \<sigma>'). \<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>,store.reference_raw g\<rangle> (va,\<sigma>')) can_alloc_reference\<close>
      and \<open>is_local (\<lambda>\<sigma> (va, \<sigma>'). \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>,store.reference_raw g\<rangle> (va,\<sigma>')) can_alloc_reference\<close>
  using urust_eval_predicate_reference_raw_local 
  by fastforce+

lemma striple_ref_raw:
    notes asepconj_simp [simp]
    shows \<open>\<Gamma>; can_alloc_reference \<turnstile> store.reference_raw g \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
              (\<lambda>r. r \<mapsto>\<langle>\<top>\<rangle> g \<star> can_alloc_reference) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof (intro striple_localI)
  fix \<sigma> \<sigma>' v
  assume \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>')\<close> \<open>\<sigma> \<Turnstile> can_alloc_reference\<close>
  then obtain \<sigma>'' addr where \<sigma>'': \<open>store_allocate_reference \<sigma> = Some (addr, \<sigma>'')\<close>
    using urust_eval_predicate_reference_raw(2) by blast
  then have \<open>store_alloc_pool \<sigma>'' \<noteq> {}\<close>
    by (metis allocate_full_share empty_iff finite.emptyI infinite_remove store_pool_inf)
  with \<sigma> \<sigma>'' have \<open>\<sigma>'' \<Turnstile> can_alloc_reference\<close>
    by (force simp: asat_def can_alloc_reference_def store_alloc_valid_allocator)
  with \<sigma> \<sigma>'' show \<open>\<sigma>' \<Turnstile> v \<mapsto> \<langle>\<top>\<rangle> g \<star> can_alloc_reference\<close>
    by (metis alloc_and_write_spec_raw option.inject prod.inject
        urust_eval_predicate_reference_raw(2))
next
  fix \<sigma> \<sigma>' :: 's and r :: 'f
  assume \<open>\<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,store.reference_raw g\<rangle> (r,\<sigma>')\<close>
    and \<open>\<sigma> \<Turnstile> can_alloc_reference\<close>
  then show \<open>\<sigma>' \<Turnstile> \<rho> r\<close>
        by (auto simp add: urust_eval_predicate_reference_raw)
    next
      fix \<sigma> \<sigma>' :: 's
        and a :: \<open>'c abort\<close>
      assume \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,store.reference_raw g\<rangle> (a,\<sigma>')\<close> \<open>\<sigma> \<Turnstile> can_alloc_reference\<close>
      have \<open>store_write_reference \<sigma>' addr g \<noteq> None\<close>
        if \<open>store_allocate_reference \<sigma> = Some (addr, \<sigma>')\<close> for addr
        by (metis that option.discI store.allocate_write_succeeds) 
      with \<sigma> show \<open>\<sigma>' \<Turnstile> \<theta> a\<close>
        by (auto simp: urust_eval_predicate_reference_raw allocate_succeeds asat_def can_alloc_reference_def)
qed (use urust_eval_predicate_reference_raw_local in fastforce)+

lemma sstriple_ref_raw:
    shows \<open>\<Gamma>; can_alloc_reference \<turnstile> store.reference_raw g \<stileturn>
              (\<lambda>r. r \<mapsto>\<langle>\<top>\<rangle> g \<star> can_alloc_reference) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro sstriple_from_stripleI striple_ref_raw)
   (auto simp add: eval_abort_def eval_value_def eval_return_def is_local_store_reference_raw)

definition reference_raw_contract' :: \<open>'b \<Rightarrow> ('s, ('a, 'b) gref, 'abort) function_contract\<close> where
  \<open>reference_raw_contract' g \<equiv>
      let pre = can_alloc_reference in
     let post = \<lambda>r. r \<mapsto>\<langle>\<top>\<rangle> g \<star> can_alloc_reference in
     make_function_contract pre post\<close>

corollary ref_raw_spec':
  shows \<open>\<Gamma> ; store.reference_raw_fun g \<Turnstile>\<^sub>F reference_raw_contract' g\<close>
  unfolding store.reference_raw_fun_def
  by (intro satisfies_function_contractI; simp add: reference_raw_contract'_def
    ucincl_intros ucincl_asepconjR sstriple_ref_raw)

subsection\<open>Dereferencing\<close>

lemma urust_eval_predicate_dereference_raw:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,store.dereference_by_value_raw r\<rangle> (v,\<sigma>') \<longleftrightarrow>
          (\<sigma>' = \<sigma> \<and> store_read_reference \<sigma> (address r) = Some v)\<close> (is ?value)
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,store.dereference_by_value_raw r\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>  (is ?return)
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,store.dereference_by_value_raw r\<rangle> (a, \<sigma>') \<longleftrightarrow>
          (a = DanglingPointer \<and> \<sigma> = \<sigma>' \<and> store_read_reference \<sigma> (address r) = None)\<close> (is ?abort)
by (cases \<open>store_read_reference \<sigma> (address r)\<close>, auto simp add: store.dereference_by_value_raw_def
  urust_eval_predicate_bind urust_eval_predicate_get urust_eval_predicate_abort
  urust_eval_predicate_literal)+

lemma urust_eval_predicate_dereference_raw_local:
  shows \<open>urust_is_local \<Gamma> (store.dereference_by_value_raw r) (r \<mapsto>\<langle>sh\<rangle> v)\<close>
by (auto simp add: is_local_def urust_eval_predicate_dereference_raw points_to_raw'_def
  asat_def store_add_read)

lemma striple_dereference_raw:
  shows \<open>\<Gamma>; r \<mapsto>\<langle>sh\<rangle> v \<turnstile> store.dereference_by_value_raw r \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v'. r\<mapsto>\<langle>sh\<rangle> v \<star> \<langle>v = v'\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  apply (intro striple_localI)
  using urust_eval_predicate_dereference_raw_local
  apply (auto simp: urust_eval_predicate_dereference_raw asat_apure_precise_distrib2
     simp add: asepconj_simp)
  done

lemma sstriple_dereference_raw:
  notes asepconj_simp [simp]
  shows \<open>\<Gamma>; r \<mapsto>\<langle>sh\<rangle> v \<turnstile> store.dereference_by_value_raw r \<stileturn> (\<lambda>v'. r\<mapsto>\<langle>sh\<rangle> v \<star> \<langle>v = v'\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro sstriple_from_stripleI, intro striple_dereference_raw) (auto simp add: eval_value_def
  eval_abort_def eval_return_def urust_eval_predicate_dereference_raw_local)

lemma wp_dereference_raw:
    notes asat_simp [simp]
      and aentails_intro [intro]
    shows \<open>r\<mapsto>\<langle>sh\<rangle> g \<star> (r\<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g) \<longlongrightarrow> \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) \<psi> \<rho> \<theta>\<close>
proof -
  have \<open>r \<mapsto>\<langle>sh\<rangle> g \<star> (\<Sqinter>g'. (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<Zsurj> \<psi> g') \<longlongrightarrow>
                      \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) \<psi> \<rho> \<theta>\<close>
    by (intro sstriple_straightline_to_wp sstriple_dereference_raw)
  moreover have \<open>r \<mapsto>\<langle>sh\<rangle> g \<star> (r \<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g) \<longlongrightarrow>
      r \<mapsto>\<langle>sh\<rangle> g \<star> (\<Sqinter>g'. (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<Zsurj> \<psi> g')\<close>
  proof (intro asepconj_mono4 aentails_refl aforall_entailsR)
    fix g'
    show \<open>r \<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g \<longlongrightarrow> (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<Zsurj> \<psi> g'\<close>
    proof (cases \<open>g = g'\<close>)
      \<comment>\<open>A precise-pure factor is a unit when true and an annihilator when false.\<close>
      case True
      then show ?thesis
        by (simp add: asepconj_simp aentails_refl)
    next
      case False
      then show ?thesis
        by (simp add: asepconj_simp awand_bot aentails_true)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma wp_dereference_rawI:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> (r\<mapsto>\<langle>sh\<rangle> g \<star> (r\<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g))\<close>
    shows \<open>\<phi> \<longlongrightarrow>  \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) \<psi> \<rho> \<theta>\<close>
by (rule aentails_trans', rule wp_dereference_raw) (auto intro: assms)

definition dereference_by_value_raw_contract'
  :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> ('s, 'b, 'abort) function_contract\<close> where
  \<open>dereference_by_value_raw_contract' r sh g \<equiv>
     let pre = r \<mapsto>\<langle>sh\<rangle> g in
     let post = \<lambda>g'. (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g=g'\<rangle>) in
     make_function_contract pre post\<close>

corollary dereference_by_value_raw_spec':
  shows \<open>\<Gamma> ; store.dereference_by_value_raw_fun r \<Turnstile>\<^sub>F dereference_by_value_raw_contract' r sh g\<close>
proof -
  have \<open>r \<mapsto> \<langle>sh\<rangle> g \<longlongrightarrow>
    \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) (\<lambda>g'. r \<mapsto> \<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) (\<lambda>g'. r \<mapsto> \<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<bottom>\<close>
    using sstriple_dereference_raw wp_sstriple_iff by blast
  then show ?thesis
    by (simp add: store.dereference_by_value_raw_fun_def satisfies_function_contract_def dereference_by_value_raw_contract'_def
        wp_sstriple_iff)
qed

subsection\<open>Modifications behind a reference\<close>

lemma urust_eval_predicate_modify_raw:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>') \<longleftrightarrow>
          (\<exists>g. store_read_reference \<sigma> (address r) = Some g \<and>
               store_write_reference \<sigma> (address r) (f g) = Some \<sigma>')\<close> (is ?value)
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,store.modify_raw r f\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>  (is ?return)
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,store.modify_raw r f\<rangle> (a, \<sigma>') \<longleftrightarrow>
          (a = DanglingPointer \<and> \<sigma>' = \<sigma> \<and> (
              (store_read_reference \<sigma> (address r) = None)
            \<or> (\<exists>g. store_read_reference \<sigma> (address r) = Some g \<and>
                   store_write_reference \<sigma> (address r) (f g) = None)))\<close> (is ?abort)
by (auto simp add: store.modify_raw_def urust_eval_predicate_bind urust_eval_predicate_get
  urust_eval_predicate_abort urust_eval_predicate_literal urust_eval_predicate_put_assert split:
  option.splits)

lemma urust_eval_predicate_modify_raw_local:
  shows \<open>urust_is_local \<Gamma> (store.modify_raw r f) (r \<mapsto>\<langle>\<top>\<rangle> v)\<close>
proof (intro conjI)
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>')) (r \<mapsto> \<langle>\<top>\<rangle> v)\<close>
  proof -
    have \<open>\<exists>\<sigma>_0'. store_write_reference \<sigma>_0 (address r) (f v) = Some \<sigma>_0' \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
      if \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
        and \<open>\<top> \<le> store_perm_map \<sigma>_0 (address r)\<close>
        and \<open>store_write_reference (\<sigma>_0 + \<sigma>_1) (address r) (f v) = Some \<sigma>'\<close>
      for \<sigma>_0 \<sigma>_1 \<sigma>' :: 's
      using that
      by (metis option.inject store_add_write top.extremum_uniqueI write_perm_succeeds)
    then show ?thesis
      by (auto simp add: is_local_def urust_eval_predicate_modify_raw points_to_raw'_def asat_def
          dest: store_add_read store_add_write)
  qed
next
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>')) (r \<mapsto> \<langle>\<top>\<rangle> v)\<close>
    by (clarsimp simp add: is_local_def urust_eval_predicate_modify_raw)
next
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>')) (r \<mapsto> \<langle>\<top>\<rangle> v)\<close>
    apply (clarsimp simp add: is_local_def urust_eval_predicate_modify_raw
      points_to_raw'_def asat_def store_add_read top.extremum_unique)
    apply (metis option.distinct(1) store_add_write write_perm_succeeds)
    done
qed

lemma striple_modify_raw:
  notes global_store_simps [simp]
  shows \<open>\<Gamma>; r \<mapsto>\<langle>\<top>\<rangle> v \<turnstile> store.modify_raw r f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> (f v)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof (intro striple_localI)
  fix \<sigma> \<sigma>' :: 's and va
  assume \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,store.modify_raw r f\<rangle> (va,\<sigma>')\<close> \<open>\<sigma> \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> v\<close>
  then have \<open>store_read_reference \<sigma>' (address r) = Some (f v)\<close>
    by (metis option.inject points_to_raw'E store.write_store_read_store urust_eval_predicate_modify_raw(1))
  moreover have \<open>\<top> \<le> store_perm_map \<sigma>' (address r)\<close>
    by (metis \<sigma> points_to_raw'E urust_eval_predicate_modify_raw(1) store.write_store_write_store write_perm_succeeds)
  ultimately show \<open>\<sigma>' \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> f v\<close>       
    using \<sigma> by (simp add: points_to_raw'_def asat_def)
next
  fix \<sigma> \<sigma>' :: 's and ra :: 'f
  assume \<open>\<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,store.modify_raw r f\<rangle> (ra,\<sigma>')\<close>
    and \<open>\<sigma> \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> v\<close>
  then show \<open>\<sigma>' \<Turnstile> \<rho> ra\<close>
    by (simp add: urust_eval_predicate_modify_raw(2))
next
  fix \<sigma> \<sigma>' :: 's and a :: \<open>'c abort\<close>
  assume \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,store.modify_raw r f\<rangle> (a,\<sigma>')\<close> \<open>\<sigma> \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> v\<close>
  then have \<open>\<sigma> \<in> \<theta> DanglingPointer\<close>
    by (metis option.distinct(1) points_to_raw'E top.extremum_unique urust_eval_predicate_modify_raw(3)
        write_perm_succeeds)
  with \<sigma> show \<open>\<sigma>' \<Turnstile> \<theta> a\<close>
    by (simp add: urust_eval_predicate_modify_raw asat_hoist_pure_precise ucincl_intros points_to_raw'_def asat_def)
qed (use urust_eval_predicate_modify_raw_local in fastforce)+

lemma sstriple_modify_raw:
  shows \<open>\<Gamma>; r \<mapsto>\<langle>\<top>\<rangle> v \<turnstile> store.modify_raw r f \<stileturn> (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> (f v)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro sstriple_from_stripleI, intro striple_modify_raw) (auto simp add: eval_value_def
  eval_return_def eval_abort_def urust_eval_predicate_modify_raw_local)

lemma wp_modify_raw:
    notes asat_simp [simp]
      and aentails_intro [intro]
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> ()) \<longlongrightarrow> \<W>\<P> \<Gamma> (store.modify_raw r f) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>r\<mapsto>\<langle>\<top>\<rangle> g \<star> (\<Sqinter>u. r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> u) \<longlongrightarrow>
                      \<W>\<P> \<Gamma> (store.modify_raw r f) \<psi> \<rho> \<theta>\<close>
    by (intro sstriple_straightline_to_wp sstriple_modify_raw)
  moreover have \<open>r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> ()) \<longlongrightarrow> r\<mapsto>\<langle>\<top>\<rangle> g \<star> (\<Sqinter>u. r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> u)\<close>
    by (auto elim!: asepconjE awandE intro!: asepconjI awandI simp add: asat_weaken
      aentails_def)
  ultimately show ?thesis
    by blast
qed

lemma wp_modify_rawI:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> ())\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (store.modify_raw r f) \<psi> \<rho> \<theta>\<close>
  by (rule aentails_trans', rule wp_modify_raw) (auto intro: assms)

definition modify_raw_contract' :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>modify_raw_contract' r g f \<equiv>
     let pre = r \<mapsto>\<langle>\<top>\<rangle> g in
     let post = \<lambda>_. (r \<mapsto>\<langle>\<top>\<rangle> (f g)) in
     make_function_contract pre post\<close>

corollary modify_raw_spec':
  shows \<open>\<Gamma> ; store.modify_raw_fun r f \<Turnstile>\<^sub>F modify_raw_contract' r g f\<close>
proof -
  have \<open>r \<mapsto> \<langle>\<top>\<rangle> g \<longlongrightarrow> \<W>\<P> \<Gamma> (store.modify_raw r f) (\<lambda>_. r \<mapsto> \<langle>\<top>\<rangle> f g) (\<lambda>_. r \<mapsto> \<langle>\<top>\<rangle> f g) \<bottom>\<close>
    using sstriple_modify_raw wp_sstriple_iff by blast
  then show ?thesis
  unfolding store.modify_raw_fun_def
  by (simp add: modify_raw_contract'_def satisfies_function_contractI sstriple_modify_raw
      ucincl_points_to_raw'I)
qed

subsection\<open>Updating a reference\<close>

lemma striple_update_raw:
  shows \<open>\<And>\<rho>. \<Gamma>; r \<mapsto>\<langle>\<top>\<rangle> g \<turnstile> store.update_raw r g' \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> g') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using striple_modify_raw by (force simp add: store.update_raw_def)

lemma wp_update_raw:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>r \<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> g' \<Zsurj> \<psi> ()) \<longlongrightarrow> \<W>\<P> \<Gamma> (store.update_raw r g') \<psi> \<rho> \<theta>\<close>
using assms by (metis wp_modify_raw store.update_raw_def)

lemma wp_update_rawI:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> g' \<Zsurj> \<psi> ())\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (store.update_raw r g') \<psi> \<rho> \<theta>\<close>
  by (rule aentails_trans', rule wp_update_raw) (auto intro: assms)

definition update_raw_contract' :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>update_raw_contract' r g0 g \<equiv>
     let pre = r \<mapsto>\<langle>\<top>\<rangle> g0 in
     let post = \<lambda>_. (r \<mapsto>\<langle>\<top>\<rangle> g) in
     make_function_contract pre post\<close>

corollary update_raw_spec':
  shows \<open>\<Gamma> ; store.update_raw_fun r g \<Turnstile>\<^sub>F update_raw_contract' r g0 g\<close>
  unfolding store.update_raw_fun_def
  by (metis modify_raw_contract'_def modify_raw_spec' store.modify_raw_fun_def store.update_raw_def
      update_raw_contract'_def)

no_notation points_to_raw' ("(_) \<mapsto> \<langle>_\<rangle> (_)" [69,0,69]70)

(*<*)
end
(*>*)

\<comment>\<open>Conceptually, we want a sublocale declaration here. Indeed, the proof below as-is
proves that

\<^verbatim>\<open>sublocale global_perm_store \<subseteq> reference \<open>\<lambda> (_ :: 's) (_ :: 'a) (_ :: 'b). ()\<close>
   store.update_raw_fun store.dereference_by_value_raw_fun store.reference_raw_fun
   points_to_raw' can_alloc_reference\<close>

Unfortunately, code generation does not seem to like the combination of nested locales
and sublocales (see code generation tutorial). We circumvent the problem by proving the
logical content of the \<^verbatim>\<open>sublocale\<close> command here, and explicitly rather than automatically
instantiating \<^verbatim>\<open>reference\<close> when we interpret \<^verbatim>\<open>global_perm_store\<close>.\<close>

context global_perm_store
begin
lemma reference_sublocale: \<open>reference
   store.update_raw_fun store.dereference_by_value_raw_fun store.reference_raw_fun
   points_to_raw' (\<lambda>_. UNIV) UNIV can_alloc_reference\<close>
proof 
  show \<open>\<And>\<Gamma> r g g0. \<Gamma> ; store.update_raw_fun  r g \<Turnstile>\<^sub>F
     reference_defs.update_raw_contract points_to_raw' (\<lambda>_. UNIV) r g0 g\<close>
    using update_raw_spec' by (simp add: update_raw_contract'_def
      reference_defs.update_raw_contract_def reference_defs.points_to_raw_def
        ucincl_points_to_raw'I asepconj_simp)
next
  show \<open>\<And>\<Gamma> r sh g.
       \<Gamma> ; store.dereference_by_value_raw_fun
             r \<Turnstile>\<^sub>F reference_defs.dereference_raw_contract points_to_raw' r sh g\<close>
    using dereference_by_value_raw_spec' by (simp add: reference_defs.dereference_raw_contract_def
      reference_defs.points_to_raw_def dereference_by_value_raw_contract'_def)
next
  show \<open>\<And>\<Gamma> g. \<Gamma> ; store.reference_raw_fun
                g \<Turnstile>\<^sub>F reference_defs.reference_raw_contract points_to_raw' (\<lambda>_. UNIV) UNIV can_alloc_reference g\<close>
    using ref_raw_spec' by (simp add: reference_defs.reference_raw_contract_def
      reference_defs.points_to_raw_def reference_raw_contract'_def ucincl_can_alloc_referenceI
      asepconj_simp)
next
  show \<open>ucincl can_alloc_reference\<close>
    by (simp add: ucincl_can_alloc_referenceI)
next
  show \<open>\<And>r sh1 sh2 v1 v2.
       reference_defs.points_to_raw points_to_raw' r sh1 v1 \<star>
       reference_defs.points_to_raw points_to_raw' r sh2 v2 \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r (sh1 + sh2) v1 \<star> \<langle>v1 = v2\<rangle>\<close>
    by (simp add: points_to_raw_combine' reference_defs.points_to_raw_def)
next
  show \<open>\<And>sh sh1 sh2 r v.
       sh = sh1 + sh2 \<Longrightarrow>
       sh1 \<sharp> sh2 \<Longrightarrow>
       0 < sh1 \<Longrightarrow>
       0 < sh2 \<Longrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh v \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh1 v \<star>
       reference_defs.points_to_raw points_to_raw' r sh2 v\<close>
    by (simp add: points_to_raw_split'' reference_defs.points_to_raw_def)
qed

end

(*<*)
end
(*>*)
