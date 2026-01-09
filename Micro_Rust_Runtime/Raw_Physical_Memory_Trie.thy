(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Raw_Physical_Memory_Trie
  imports 
    Raw_Physical_Memory_Trie_Core
    Micro_Rust_Interfaces_Core.Raw_Physical_Memory
begin
(*>*)

section\<open>Derived material around trie-based physical memory\<close>

text\<open>This theory derives an interpretation of the \<^locale>\<open>raw_tagged_physical_memory\<close> locale from
the core material on trie-based physical memory in \<^verbatim>\<open>Physical_Memory_Trie_Core\<close>.\<close>

named_theorems raw_tagged_pmem_spec_specs

subsection\<open>Definitions\<close>

text\<open>First, we establish the parameters of the \<^locale>\<open>raw_tagged_physical_memory\<close> locale.\<close>

definition points_to_tagged_phys_byte :: \<open>64 word \<Rightarrow> share \<Rightarrow> 'tag \<Rightarrow> 8 word \<Rightarrow> 'tag tagged_physical_memory assert\<close>
  where \<open>points_to_tagged_phys_byte pa sh tag b \<equiv>
     { \<sigma>. \<exists>actual_sh.
            physical_memory_lookup \<sigma> pa = Tagged actual_sh tag b \<and>
            0 < sh \<and> sh \<le> Rep_nonempty_share actual_sh }\<close>

definition load_tagged_phys_byte :: \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> memory_fault + (8 word \<times> 'tag tagged_physical_memory)\<close> where
  \<open>load_tagged_phys_byte m pa \<equiv>
     case physical_memory_lookup m pa of
       No_Value \<Rightarrow> Inl Unmapped_Address
     | Shared_Value sh (_, b) \<Rightarrow> Inr (b, m)\<close>

definition store_tagged_phys_byte :: \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow>
      memory_fault + 'tag tagged_physical_memory\<close> where
  \<open>store_tagged_phys_byte m pa b \<equiv> physical_memory_memset_block m pa 0 b\<close>

definition load_tagged_physical_address_core :: \<open>64 word \<Rightarrow> ('tag tagged_physical_memory, 8 word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>load_tagged_physical_address_core pa \<equiv>
     bind (get id) (\<lambda>mem.
       case load_tagged_phys_byte mem pa of
         Inl _     \<Rightarrow> abort DanglingPointer
       | Inr (b,m) \<Rightarrow> sequence (put (\<lambda>_. m)) (literal b))\<close>

definition load_tagged_physical_address :: \<open>64 word \<Rightarrow> ('tag tagged_physical_memory, 8 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>load_tagged_physical_address pa \<equiv> FunctionBody (load_tagged_physical_address_core pa)\<close>

definition store_tagged_physical_address_core :: \<open>64 word \<Rightarrow> 8 word \<Rightarrow> ('tag tagged_physical_memory, unit,'r, 'abort, 'i, 'o) expression\<close> where
  \<open>store_tagged_physical_address_core pa b \<equiv>
     bind (get id) (\<lambda>mem.
       case store_tagged_phys_byte mem pa b of
         Inl _ \<Rightarrow> abort DanglingPointer
       | Inr m  \<Rightarrow> put (\<lambda>_. m))\<close>

definition store_tagged_physical_address :: \<open>64 word \<Rightarrow> 8 word \<Rightarrow> ('tag tagged_physical_memory,unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>store_tagged_physical_address pa b \<equiv> FunctionBody (store_tagged_physical_address_core pa b)\<close>

definition memset_tagged_phys_block_core :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow>
    ('tag tagged_physical_memory, unit, unit, 'abort, 'i, 'o) expression\<close> where
  \<open>memset_tagged_phys_block_core pa n b \<equiv>
     bind (get id) (\<lambda>mem.
       case physical_memory_memset_block mem pa n b of
         Inl e \<Rightarrow> abort DanglingPointer
       | Inr m \<Rightarrow> put (\<lambda>_. m))\<close>

definition memset_tagged_phys_block :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow>
    ('tag tagged_physical_memory, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>memset_tagged_phys_block pa n b \<equiv> FunctionBody (memset_tagged_phys_block_core pa n b)\<close>

definition memset_tagged_phys :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow>
    ('tag tagged_physical_memory, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>memset_tagged_phys pa l b \<equiv> FunctionBody \<lbrakk>
    for blk in \<llangle>range_to_aligned_blocks pa l\<rrangle> {
      let addr = \<llangle>fst blk\<rrangle>;
      let n = \<llangle>snd blk\<rrangle>;
      memset_tagged_phys_block(addr, n, b)
    }
  \<rbrakk>\<close>

definition tag_physical_page_core :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> ('tag tagged_physical_memory, unit, unit, 'abort, 'i, 'o) expression\<close> where
  \<open>tag_physical_page_core pa n tag \<equiv>
     bind (get id) (\<lambda>mem.
       case physical_memory_tag_page mem pa n tag of
         Inl _ \<Rightarrow> abort DanglingPointer
       | Inr m \<Rightarrow> put (\<lambda>_. m))\<close>

definition tag_physical_page :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> ('tag tagged_physical_memory, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>tag_physical_page pa n tag \<equiv> FunctionBody (tag_physical_page_core pa n tag)\<close>

interpretation raw_tagged_pmem_defs: raw_tagged_physical_memory_defs \<open>\<lambda>(_ :: 'tag tagged_physical_memory) (_ :: 'tag) _ _ _. ()\<close>
  memset_tagged_phys memset_tagged_phys_block
  points_to_tagged_phys_byte store_tagged_physical_address
  load_tagged_physical_address tag_physical_page .

subsection\<open>Properties\<close>

text\<open>Next, we work towards establishing the axioms for the \<^locale>\<open>raw_tagged_physical_memory\<close> locale.\<close>

lemma points_to_tagged_phys_byte_ucincl' [ucincl_intros, raw_tagged_pmem_spec_specs]:
  shows \<open>ucincl (points_to_tagged_phys_byte adr sh tag b)\<close>
proof -
  {
       fix x y adr sh b
    assume \<open>physical_memory_lookup x adr = Tagged sh tag b\<close>
       and \<open>x \<sharp> y\<close>
    from this have \<open>\<exists>sh'. physical_memory_lookup (x+y) adr = Tagged sh' tag b \<and> sh \<le> sh'\<close>
      using physical_memory_lookup_local[of x adr \<open>Tagged sh tag b\<close> y] less_eq_nonempty_share.rep_eq 
        plus_nonempty_share.rep_eq by (auto split!: shareable_value.splits)
  }
  then show ?thesis
    unfolding points_to_tagged_phys_byte_def ucincl_def ucpred_def derived_order_def
    using less_eq_nonempty_share.rep_eq by fastforce
qed

corollary points_to_tagged_phys_byte_ucincl'':
  shows \<open>points_to_tagged_phys_byte pa \<pi> tag b \<star> UNIV = points_to_tagged_phys_byte pa \<pi> tag b\<close>
    and \<open>UNIV \<star> points_to_tagged_phys_byte pa \<pi> tag b = points_to_tagged_phys_byte pa \<pi> tag b\<close>
    and \<open>points_to_tagged_phys_byte pa \<pi> tag b \<star> \<langle>P\<rangle> = points_to_tagged_phys_byte pa \<pi> tag b \<sqinter> \<langle>P\<rangle>\<close>
by (auto simp add: asepconj_comm asepconj_ident points_to_tagged_phys_byte_ucincl'
  asepconj_pure')

lemma points_to_tagged_phys_byteE [elim]:
  assumes \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa sh tag b\<close>
      and \<open>\<And>actual_sh. physical_memory_lookup \<sigma> pa = Tagged actual_sh tag b \<Longrightarrow>
            0 < sh \<Longrightarrow> sh \<le> Rep_nonempty_share actual_sh \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms unfolding points_to_tagged_phys_byte_def asat_def by blast

lemma points_to_tagged_phys_byteI [intro]:
  assumes \<open>physical_memory_lookup \<sigma> pa = Tagged actual_sh tag b\<close>
      and \<open>0 < sh\<close>
      and \<open>sh \<le> Rep_nonempty_share actual_sh\<close>
    shows \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa sh tag b\<close>
using assms unfolding points_to_tagged_phys_byte_def asat_def by blast

lemma urust_eval_predicate_load_tagged_physical_address_core [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (a, \<sigma>') \<longleftrightarrow>
            ((a = DanglingPointer \<and> \<sigma> = \<sigma>' \<and> (\<exists>e. load_tagged_phys_byte \<sigma> pa = Inl e)))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>') \<longleftrightarrow>
    (\<exists>b m. load_tagged_phys_byte \<sigma> pa = Inr (b,m) \<and> \<sigma>' = m \<and> v = b)\<close>
by (auto simp add: load_tagged_physical_address_core_def urust_eval_predicate_simps split: sum.splits)

lemma physical_memory_lookup_not_tagged:
  assumes \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> \<open>load_tagged_phys_byte (\<sigma>_0 + \<sigma>_1) pa = Inl e\<close>
  shows \<open>physical_memory_lookup \<sigma>_0 pa \<noteq> Tagged actual_sh tag b\<close>
proof -
  have \<open>physical_memory_lookup (\<sigma>_0 + \<sigma>_1) pa = No_Value\<close>
    using assms
    by (auto simp: load_tagged_phys_byte_def split: shareable_value.splits)
  with assms show ?thesis
    using physical_memory_plus_eq by fastforce
qed

lemma points_to_tagged_phys_byte_not_core:
  assumes \<open>\<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close> and \<open>\<sigma>_0 \<leadsto>\<^sub>a \<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>_0')\<close>
  shows False
  using assms
  by (auto simp: load_tagged_phys_byte_def urust_eval_predicate_load_tagged_physical_address_core(1))

lemma load_tagged_physical_address_core_is_local:
  notes asepconj_simp [simp]
    and points_to_tagged_phys_byte_ucincl'' [simp]
    and points_to_tagged_phys_byte_ucincl' [simp]
  shows \<open>urust_is_local \<Gamma> (load_tagged_physical_address_core pa) (points_to_tagged_phys_byte pa \<pi> tag b)\<close>
proof (intro conjI is_localI; safe)
     fix \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<sigma>\<^sub>0' v
  assume \<open>\<sigma>\<^sub>0 \<sharp> \<sigma>\<^sub>1\<close>
     and \<open>\<sigma>\<^sub>0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close>
     and \<open>\<sigma>\<^sub>0 \<leadsto>\<^sub>v \<langle>\<Gamma>, load_tagged_physical_address_core pa\<rangle> (v, \<sigma>\<^sub>0')\<close>
  from this show \<open>\<sigma>\<^sub>0' \<sharp> \<sigma>\<^sub>1\<close> 
    by (clarsimp simp add: urust_eval_predicate_simps physical_memory_disjoint_eq
      load_tagged_phys_byte_def elim!: points_to_tagged_phys_byteE)
next
    fix \<sigma>_0 \<sigma>_1 \<sigma>' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
     and \<sigma>_0: \<open>\<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close>
              \<open>\<sigma>_0 + \<sigma>_1 \<leadsto>\<^sub>v \<langle>\<Gamma>, load_tagged_physical_address_core pa\<rangle> (v, \<sigma>')\<close>
  then obtain b' m where b': \<open>load_tagged_phys_byte (\<sigma>_0 + \<sigma>_1) pa = Inr (b', m)\<close> and \<open>\<sigma>' = m\<close> and \<open>v = b'\<close>
    by (simp add: urust_eval_predicate_load_tagged_physical_address_core(3))
  then obtain actual_sh 
      where actual_sh: \<open>physical_memory_lookup \<sigma>_0 pa = Tagged actual_sh tag b\<close> \<open>\<pi> \<le> Rep_nonempty_share actual_sh\<close> and \<open>0 < \<pi>\<close>
    using \<open>\<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close> by auto 
  moreover 
  have \<open>physical_memory_lookup (\<sigma>_0 + \<sigma>_1) pa \<noteq> No_Value\<close>
    by (metis b' load_tagged_phys_byte_def shareable_value.simps(5) sum.simps(4))
  moreover               note calculation_thus_far = calculation
  have \<open>\<exists>\<sigma>_0'. \<sigma>_0 \<leadsto>\<^sub>v \<langle>\<Gamma>, load_tagged_physical_address_core pa\<rangle> (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
    if \<open>physical_memory_lookup (\<sigma>_0 + \<sigma>_1) pa = Tagged other_sh tag' b'\<close> for other_sh tag'
  proof -
    have \<open>m = \<sigma>_0 + \<sigma>_1\<close>
      using that b' by (simp add: load_tagged_phys_byte_def)
    moreover have \<open>b = b'\<close> and \<open>tag = tag'\<close>
      using \<sigma>_0 \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
      by (metis  that asat_weaken points_to_tagged_phys_byteE points_to_tagged_phys_byte_ucincl' 
        shareable_value.simps(1) prod.inject)+
    ultimately show ?thesis
      using b' \<sigma>_0 actual_sh by (simp add: load_tagged_phys_byte_def urust_eval_predicate_load_tagged_physical_address_core(3))
  qed
  ultimately show \<open>\<exists>\<sigma>_0'. \<sigma>_0 \<leadsto>\<^sub>v \<langle>\<Gamma>, load_tagged_physical_address_core pa\<rangle> (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
    using b' by (auto simp add: load_tagged_phys_byte_def split: shareable_value.splits)
next
     fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v \<sigma>'
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
     and \<open>\<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close>
     and \<open>\<sigma>_0 \<leadsto>\<^sub>v \<langle>\<Gamma>, load_tagged_physical_address_core pa\<rangle> (v, \<sigma>_0')\<close>
  moreover from this obtain actual_sh tag where \<open>physical_memory_lookup \<sigma>_0 pa = Tagged actual_sh tag b\<close> and \<open>\<pi> \<le> Rep_nonempty_share actual_sh\<close>
    by (clarsimp elim!: points_to_tagged_phys_byteE)
  moreover from calculation have \<open>load_tagged_phys_byte \<sigma>_0 pa = Inr (v, \<sigma>_0')\<close>
    by (clarsimp simp add: urust_eval_predicate_load_tagged_physical_address_core)
  moreover 
  have \<open>physical_memory_lookup (\<sigma>_0' + \<sigma>_1) pa \<noteq> Unmapped\<close>
    using calculation by (auto simp add: load_tagged_phys_byte_def physical_memory_plus_eq)
  moreover 
  have \<open>v' = v\<close> and \<open>tag = tag'\<close> 
    if \<open>physical_memory_lookup (\<sigma>_0' + \<sigma>_1) pa = Tagged other_sh tag' v'\<close>
      for other_sh v' tag'
    using that calculation 
      by (force simp: physical_memory_plus_eq load_tagged_phys_byte_def elim!: plus_shareable_value.elims)+
  moreover from calculation have \<open>load_tagged_phys_byte (\<sigma>_0 + \<sigma>_1) pa = Inr (v, \<sigma>_0' + \<sigma>_1)\<close>
    by (clarsimp simp add: load_tagged_phys_byte_def split!: shareable_value.splits)
  ultimately show \<open>\<sigma>_0 + \<sigma>_1 \<leadsto>\<^sub>v \<langle>\<Gamma>, load_tagged_physical_address_core pa\<rangle> (v, \<sigma>_0' + \<sigma>_1)\<close>
    by (clarsimp simp add: urust_eval_predicate_load_tagged_physical_address_core)
next
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close>
    and \<open>\<sigma>_0 \<leadsto>\<^sub>a \<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>_0')\<close>
  then show \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
    by (simp add: urust_eval_predicate_load_tagged_physical_address_core)
next
  show \<open>\<And>\<sigma>_0 \<sigma>_1 \<sigma>' v.
       \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow>
       \<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b \<Longrightarrow>
       \<sigma>_0 + \<sigma>_1 \<leadsto>\<^sub>a \<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>') \<Longrightarrow>
       \<exists>\<sigma>_0'. \<sigma>_0 \<leadsto>\<^sub>a \<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
    by (meson asat_weaken points_to_tagged_phys_byte_not_core points_to_tagged_phys_byte_ucincl')
next
  fix \<sigma>_0 \<sigma>_1 \<sigma>_0' v \<sigma>'
  assume \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close> and \<open>\<sigma>_0 \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b\<close>
    and \<open>\<sigma>_0 \<leadsto>\<^sub>a \<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>_0')\<close>
  then show \<open>\<sigma>_0 + \<sigma>_1 \<leadsto>\<^sub>a \<langle>\<Gamma>,load_tagged_physical_address_core pa\<rangle> (v,\<sigma>_0' + \<sigma>_1)\<close>
    by (metis points_to_tagged_phys_byte_not_core)
qed (auto simp add: urust_eval_predicate_load_tagged_physical_address_core)

lemma load_tagged_physical_address_spec [raw_tagged_pmem_spec_specs]:
  notes asepconj_simp [simp]
    and points_to_tagged_phys_byte_ucincl'' [simp]
  shows \<open>\<Gamma>; load_tagged_physical_address pa \<Turnstile>\<^sub>F make_function_contract (points_to_tagged_phys_byte pa \<pi> tag b)
          (\<lambda>r. points_to_tagged_phys_byte pa \<pi> tag b \<star> \<langle>r = b\<rangle>)\<close>
proof (ucincl_discharge \<open>intro satisfies_function_contractI\<close>; clarsimp)
  have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,function_body (load_tagged_physical_address pa)\<rangle> (x,y)) (points_to_tagged_phys_byte pa \<pi> tag b)\<close>
    by (simp add: load_tagged_physical_address_core_is_local load_tagged_physical_address_def)
  moreover have \<open>is_local (eval_return (yh \<Gamma>) (function_body (load_tagged_physical_address pa))) (points_to_tagged_phys_byte pa \<pi> tag b)\<close>
    by (simp add: eval_return_def is_local_def load_tagged_physical_address_def urust_eval_predicate_load_tagged_physical_address_core(2))
  moreover have \<open>is_local (eval_abort (yh \<Gamma>) (function_body (load_tagged_physical_address pa))) (points_to_tagged_phys_byte pa \<pi> tag b)\<close>
    by (auto simp add: load_tagged_physical_address_core_is_local load_tagged_physical_address_def eval_abort_def)
  moreover from calculation have \<open>points_to_tagged_phys_byte pa \<pi> tag b \<turnstile>
      eval_value (yh \<Gamma>) (function_body (load_tagged_physical_address pa)) \<stileturn>\<^sub>R
          (\<lambda>r. points_to_tagged_phys_byte pa \<pi> tag b \<inter> \<langle>r = b\<rangle>)\<close>
    by (force simp add: atriple_rel_def eval_value_def load_tagged_physical_address_def
      asepconj_False_True load_tagged_phys_byte_def urust_eval_predicate_load_tagged_physical_address_core)
  moreover from calculation have \<open>points_to_tagged_phys_byte pa \<pi> tag b \<turnstile> eval_return (yh \<Gamma>) (function_body (load_tagged_physical_address pa)) \<stileturn>\<^sub>R
      (\<lambda>r. points_to_tagged_phys_byte pa \<pi> tag b \<inter> \<langle>r = b\<rangle>)\<close>
    by (clarsimp simp add: atriple_rel_def eval_return_def eval_value_def load_tagged_physical_address_def
      urust_eval_predicate_load_tagged_physical_address_core)
  moreover 
  have \<open>\<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>, function_body (load_tagged_physical_address pa)\<rangle> (a, \<sigma>') = False\<close>
    if \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa \<pi> tag b \<star> \<top>\<close> for \<sigma> a \<sigma>'
    using that
    by (metis function_body.sel load_tagged_physical_address_def points_to_tagged_phys_byte_not_core 
        points_to_tagged_phys_byte_ucincl''(1)) 
  moreover from calculation have \<open>points_to_tagged_phys_byte pa \<pi> tag b \<turnstile>
      eval_abort (yh \<Gamma>) (function_body (load_tagged_physical_address pa)) \<stileturn>\<^sub>R \<bottom>\<close>
    by (clarsimp simp add: eval_abort_def atriple_rel_def)
  ultimately show \<open>\<Gamma> ; points_to_tagged_phys_byte pa \<pi> tag b \<turnstile> function_body (load_tagged_physical_address pa) \<stileturn>
    (\<lambda>r. points_to_tagged_phys_byte pa \<pi> tag b \<inter> \<langle>r = b\<rangle>) \<bowtie> (\<lambda>r. points_to_tagged_phys_byte pa \<pi> tag b \<inter> \<langle>r = b\<rangle>) \<bowtie> \<bottom>\<close>
    by (intro sstripleI; clarsimp)
qed

lemma urust_eval_predicate_store_tagged_physical_address_core [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,store_tagged_physical_address_core pa b\<rangle> (a, \<sigma>') \<longleftrightarrow> ((a = DanglingPointer \<and> (\<sigma> = \<sigma>') \<and> (\<exists>e. store_tagged_phys_byte \<sigma> pa b = Inl e)))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,store_tagged_physical_address_core pa b\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,store_tagged_physical_address_core pa b\<rangle> (v,\<sigma>') \<longleftrightarrow> (\<exists>m. store_tagged_phys_byte \<sigma> pa b = Inr m \<and> \<sigma>' = m)\<close>
by (auto simp add: store_tagged_physical_address_core_def urust_eval_predicate_simps split: sum.splits)

lemma store_tagged_physical_address_core_is_local:
  notes asepconj_simp [simp]
    and points_to_tagged_phys_byte_ucincl'' [simp]
    and points_to_tagged_phys_byte_ucincl' [simp]
    and Rep_nonempty_share_inject [simp]
    and top.extremum_uniqueI [simp]
    and top_nonempty_share.rep_eq [simp]
  shows \<open>urust_is_local \<Gamma> (store_tagged_physical_address_core pa b) (points_to_tagged_phys_byte pa \<top> tag b0)\<close>
proof -
  have \<open>\<exists>m. physical_memory_memset_block \<sigma>0 pa 0 b = Inr m\<close>
    if \<open>physical_memory_lookup \<sigma>0 pa = Tagged sh tag b0\<close> \<open>\<top> \<le> Rep_nonempty_share sh\<close> 
    for \<sigma>0 sh m tag
    using that nonempty_share_top_eq physical_memory_memset_block_succeeds
    by fastforce
  moreover 
  have \<open>m \<sharp> \<sigma>1\<close> and \<open>physical_memory_memset_block (\<sigma>0 + \<sigma>1) pa 0 b = Inr (m + \<sigma>1)\<close>
    if \<open>\<sigma>0 \<sharp> \<sigma>1\<close>
      and \<open>physical_memory_lookup \<sigma>0 pa = Tagged sh tag b0\<close>
      and \<open>\<top> \<le> Rep_nonempty_share sh\<close>
      and \<open>physical_memory_memset_block \<sigma>0 pa 0 b = Inr m\<close>
    for  \<sigma>0 \<sigma>1 sh m and tag
      using that physical_memory_memset_block_local by blast+
  ultimately show ?thesis
    by (fastforce simp add: is_local_def urust_eval_predicate_store_tagged_physical_address_core
      store_tagged_phys_byte_def block_range_def elim!: points_to_tagged_phys_byteE)
qed

lemma store_physical_address_spec [raw_tagged_pmem_spec_specs]:
  shows \<open>\<Gamma>; store_tagged_physical_address pa b \<Turnstile>\<^sub>F make_function_contract (points_to_tagged_phys_byte pa \<top> tag b0)
            (\<lambda>_. points_to_tagged_phys_byte pa \<top> tag b)\<close>
proof(ucincl_discharge \<open>rule satisfies_function_contractI\<close>; clarsimp)
  have \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,function_body (store_tagged_physical_address pa b)\<rangle> (v,\<sigma>'))
      (points_to_tagged_phys_byte pa \<top> tag b0)\<close>
    by (simp add: store_tagged_physical_address_core_is_local store_tagged_physical_address_def)
  moreover have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,function_body (store_tagged_physical_address pa b)\<rangle> (x,y))
      (points_to_tagged_phys_byte pa \<top> tag b0)\<close>
    by (simp add: store_tagged_physical_address_core_is_local store_tagged_physical_address_def)
  moreover {
       fix \<sigma> \<sigma>'
    assume \<open>\<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,function_body (store_tagged_physical_address pa b)\<rangle> ((), \<sigma>')\<close>
       and \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa \<top> tag b0\<close>
    from this have \<open>\<sigma>' \<Turnstile> points_to_tagged_phys_byte pa \<top> tag b\<close>
      apply (elim points_to_tagged_phys_byteE; intro points_to_tagged_phys_byteI; clarsimp)
      apply (simp add: store_tagged_physical_address_def physical_memory_memset_block_result
        set_byte_state_def store_tagged_phys_byte_def map_shareable_value_def
        urust_eval_predicate_store_tagged_physical_address_core)+
      done
  } moreover {
       fix \<sigma> \<sigma>'
    assume \<open>\<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,function_body (store_tagged_physical_address pa b)\<rangle> ((), \<sigma>')\<close>
       and \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa \<top> tag b0\<close>
    from this have \<open>\<sigma>' \<Turnstile> points_to_tagged_phys_byte pa \<top> tag b\<close>
      by (simp add: store_tagged_physical_address_def urust_eval_predicate_store_tagged_physical_address_core)
  } moreover {
       fix \<sigma> a \<sigma>'
    assume \<sigma>: \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa \<top> tag b0 \<star> \<top>\<close>
              \<open>\<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,function_body (store_tagged_physical_address pa b)\<rangle> (a, \<sigma>')\<close>
    then have \<open>\<exists>m. physical_memory_memset_block \<sigma> pa 0 b = Inr m\<close>
      by (clarsimp simp flip: physical_memory_memset_block_succeeds; 
          clarsimp simp add: ucincl_intros points_to_tagged_phys_byte_ucincl'' nonempty_share_top_eq top_unique 
          elim!: points_to_tagged_phys_byteE)
    with \<sigma> have \<open>False\<close>
      by (metis Inr_Inl_False function_body.sel store_tagged_phys_byte_def store_tagged_physical_address_def 
          urust_eval_predicate_store_tagged_physical_address_core(1))
  }
  moreover from calculation have
     \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,function_body (store_tagged_physical_address pa b)\<rangle> (x,y))
      (points_to_tagged_phys_byte pa \<top> tag b0)\<close>
    by (simp add: store_tagged_physical_address_core_is_local store_tagged_physical_address_def)
  ultimately have \<open>\<Gamma> ; points_to_tagged_phys_byte pa \<top> tag b0 \<turnstile> function_body (store_tagged_physical_address pa b) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
        (\<lambda>_. points_to_tagged_phys_byte pa \<top> tag b) \<bowtie> (\<lambda>_. points_to_tagged_phys_byte pa \<top> tag b) \<bowtie> \<bottom>\<close>
    apply (intro striple_localI; clarsimp)
    apply (metis points_to_tagged_phys_byte_ucincl' ucincl_alt)
    done
  then show \<open>\<Gamma> ; points_to_tagged_phys_byte pa \<top> tag b0 \<turnstile> function_body (store_tagged_physical_address pa b) \<stileturn>
          (\<lambda>_. points_to_tagged_phys_byte pa \<top> tag b) \<bowtie> (\<lambda>_. points_to_tagged_phys_byte pa \<top> tag b) \<bowtie> \<bottom>\<close>
    by (simp add: sstriple_striple' store_tagged_physical_address_core_is_local store_tagged_physical_address_def)
qed

lemma urust_eval_predicate_memset_phys_block_core [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,memset_tagged_phys_block_core pa n b\<rangle> (a, \<sigma>') \<longleftrightarrow>
           ((a = DanglingPointer \<and> \<sigma> = \<sigma>' \<and> (\<exists>e. physical_memory_memset_block \<sigma> pa n b = Inl e)))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,memset_tagged_phys_block_core pa n b\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,memset_tagged_phys_block_core pa n b\<rangle> (v,\<sigma>') \<longleftrightarrow>
          (\<exists>m. physical_memory_memset_block \<sigma> pa n b = Inr m \<and> \<sigma>' = m)\<close>
by (auto simp add: memset_tagged_phys_block_core_def urust_eval_predicate_simps split: sum.splits)

lemma memset_tagged_block_pre_tagged:
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag\<close>
      and \<open>x \<in> block_range pa n\<close>
    shows \<open>\<exists>b. physical_memory_lookup \<sigma> x = Tagged \<top> tag b\<close>
proof -
  have \<open>finite (block_range pa n)\<close>
    by (auto intro: finite_block_range)
  moreover from calculation assms have \<open>mset_set (block_range pa n) = add_mset x (mset_set (block_range pa n - {x}))\<close>
    using mset_set.remove by metis
  moreover from calculation assms have \<open>\<sigma> \<Turnstile> \<star>\<star>{# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)). a \<leftarrow> add_mset x (mset_set (block_range pa n - {x})) #}\<close>
    by (simp add: block_range_def block_range_def)
  moreover from calculation have \<open>\<sigma> \<Turnstile> \<Union> (range (points_to_tagged_phys_byte x \<top> tag)) \<star> 
     \<star>\<star>{# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)). a \<leftarrow> mset_set (block_range pa n - {x}) #}\<close>
    by clarsimp
  moreover from calculation obtain \<sigma>\<^sub>1 \<sigma>\<^sub>2 where \<open>\<sigma>\<^sub>1 \<sharp> \<sigma>\<^sub>2\<close> and \<open>\<sigma> = \<sigma>\<^sub>1 + \<sigma>\<^sub>2\<close> and \<open>\<sigma>\<^sub>1 \<Turnstile> \<Union> (range (points_to_tagged_phys_byte x \<top> tag))\<close> and
        \<open>\<sigma>\<^sub>2 \<Turnstile> \<star>\<star>{# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)). a \<leftarrow> mset_set (block_range pa n - {x}) #}\<close>
    by (auto elim!: asepconjE)
  moreover from calculation obtain y where \<open>\<sigma>\<^sub>1 \<Turnstile> points_to_tagged_phys_byte x \<top> tag y\<close>
    by blast
  moreover from calculation obtain actual_sh where \<open>physical_memory_lookup \<sigma>\<^sub>1 x = Tagged actual_sh tag y\<close> and \<open>(0::share) < \<top>\<close> and
        \<open>\<top> \<le> Rep_nonempty_share actual_sh\<close>
    by blast
  moreover from calculation have \<open>actual_sh = \<top>\<close>
    by (metis Rep_nonempty_share_inject top_le top_nonempty_share.rep_eq)
  moreover from calculation have \<open>physical_memory_lookup \<sigma>\<^sub>2 x = Unmapped\<close>
    by (metis Rep_nonempty_share_inject tagged_disjoint_lemma' physical_memory_disjoint_eq top.extremum_uniqueI top_nonempty_share.rep_eq)
  moreover from calculation have \<open>physical_memory_lookup (\<sigma>\<^sub>1 + \<sigma>\<^sub>2) x = Tagged \<top> tag y + Unmapped\<close>
    by (auto simp add: physical_memory_plus_eq)
  ultimately show ?thesis
    by clarsimp
qed

lemma memset_tagged_block_pre_writable_states:
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag\<close>
      and \<open>x \<in> block_range pa n\<close>
    shows \<open>writeable_byte_state (physical_memory_lookup \<sigma> x)\<close>
  using assms memset_tagged_block_pre_tagged by fastforce

lemma tagged_block_via_lookup:
  assumes \<open>\<And>x. x \<in> block_range pa n \<Longrightarrow> physical_memory_lookup \<sigma> x = Tagged \<top> tag (f x) \<close>
     and \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
     and \<open>is_aligned pa n\<close>
     and \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
   shows \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f\<close>
using assms proof (induction n arbitrary: \<sigma> pa)
     fix \<sigma> pa
  assume \<open>\<And>x. x \<in> block_range pa 0 \<Longrightarrow> physical_memory_lookup \<sigma> x = Tagged \<top> tag (f x)\<close>
     and \<open>0 \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
     and \<open>is_aligned pa 0\<close>
     and \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
  moreover have \<open>ucincl (points_to_tagged_phys_byte pa \<top> tag (f pa))\<close>
    by ucincl_solve
  moreover have \<open>(0::share) < \<top>\<close>
    by (simp add: zero_share_def)
  moreover have \<open>\<top> \<le> Rep_nonempty_share \<top>\<close>
    by (simp add: top_nonempty_share.rep_eq)
  moreover from calculation have \<open>physical_memory_lookup \<sigma> pa = Tagged \<top> tag (f pa)\<close>
    by force
  moreover from calculation have \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa \<top> tag (f pa)\<close>
    by (force intro: points_to_tagged_phys_byteI)
  moreover from calculation have \<open>\<sigma> \<Turnstile> points_to_tagged_phys_byte pa \<top> tag (f pa) \<star> \<top>\<close>
    by (subst asepconj_ident2) auto
  ultimately show \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa 0 tag f\<close>
    by (clarsimp simp add: asepconj_simp)
next
     fix n \<sigma> pa
  assume \<open>is_aligned pa (Suc n)\<close>
     and \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
     and \<open>Suc n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
     and \<open>\<And>x. x \<in> block_range pa (Suc n) \<Longrightarrow> physical_memory_lookup \<sigma> x = Tagged \<top> tag (f x)\<close>
     and \<open>\<And>\<sigma> pa. (\<And>x. x \<in> block_range pa n \<Longrightarrow> physical_memory_lookup \<sigma> x = Tagged \<top> tag (f x)) \<Longrightarrow>
            n \<le> PMEM_TRIE_ADDRESS_WIDTH \<Longrightarrow> is_aligned pa n \<Longrightarrow>
            pa < PMEM_TRIE_ADDRESS_LIMIT \<Longrightarrow> \<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f\<close>
  moreover from this have \<open>is_aligned pa n\<close>
    by (meson is_aligned_weaken lessI nless_le)
  moreover from calculation have \<open>is_aligned (pa + 2 ^ n) n\<close>
    using is_aligned_add is_aligned_triv by blast
  moreover from \<open>Suc n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close> have \<open>2 ^ n < (2::64 word) ^ Suc n\<close> 
    by (subst word_less_nat_alt unat_2tp_if)+
      (clarsimp simp add: PMEM_TRIE_ADDRESS_WIDTH_def)
  moreover from \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close> have \<open>pa < 2 ^ PMEM_TRIE_ADDRESS_WIDTH\<close>
    by (clarsimp simp add: PMEM_TRIE_ADDRESS_LIMIT_def)
  moreover from calculation have \<open>pa + 2 ^ n < 2 ^ PMEM_TRIE_ADDRESS_WIDTH\<close>
    by (auto intro: is_aligned_add_less_t2n)
  moreover from calculation have \<open>pa + 2 ^ n < PMEM_TRIE_ADDRESS_LIMIT\<close>
    by (clarsimp simp add: PMEM_TRIE_ADDRESS_LIMIT_def)
  moreover have \<open>x \<notin> block_range pa n\<close> if \<open>x \<in> block_range (pa + 2 ^ n) n\<close> for x
    using block_range_split_disjoint calculation that 
    by (force simp add: PMEM_TRIE_ADDRESS_WIDTH_def)
  moreover from calculation have \<open>\<sigma> = physical_memory_delete_block \<sigma> pa n + physical_memory_take_block \<sigma> pa n\<close>
    using physical_memory_take_delete_eq physical_memory_take_delete_disjoint
    by (metis sepalg_comm)
  moreover from calculation have \<open>physical_memory_take_block \<sigma> pa n \<sharp> physical_memory_delete_block \<sigma> pa n\<close>
    using physical_memory_take_delete_disjoint by (clarsimp simp add: comp_def)
  moreover from calculation have \<open>physical_memory_take_block \<sigma> pa n \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f\<close>
    by (clarsimp simp add: physical_memory_take_lookup block_range_split)
  moreover from calculation have \<open>physical_memory_delete_block \<sigma> pa n \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block (pa + 2 ^ n) n tag f\<close>
    by (clarsimp simp add: physical_memory_delete_lookup block_range_split block_range_split_disjoint)
  moreover from calculation have \<open>block_range pa n \<inter> block_range (pa + 2 ^ n) n = {}\<close>
    by blast
  moreover from calculation have \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f \<star> raw_tagged_pmem_defs.tagged_physical_block (pa + 2 ^ n) n tag f\<close>
    by (metis (mono_tags, lifting) asepconjI physical_memory_take_delete_eq)
  moreover from calculation have \<open>\<sigma> \<Turnstile> \<star>\<star> {# points_to_tagged_phys_byte a \<top> tag (f a) . a \<leftarrow> mset_set (block_range pa n \<union> block_range (pa + 2 ^ n) n) #}\<close>
    by (subst mset_set_Union; simp add: finite_block_range asepconj_simp block_range_split_disjoint)
  ultimately show \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa (Suc n) tag f\<close>
    by (clarsimp simp add: block_range_split)
qed

corollary memset_tagged_block_post_via_lookup:
  assumes \<open>\<And>x. x \<in> block_range pa n \<Longrightarrow> physical_memory_lookup \<sigma> x = Tagged \<top> tag b\<close>
      and \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
      and \<open>is_aligned pa n\<close>
      and \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_post pa n tag b\<close>
using assms by (simp add: tagged_block_via_lookup)

lemma memset_phys_block_core_is_local:
    notes asepconj_simp [simp]
      and points_to_tagged_phys_byte_ucincl'' [simp]
      and points_to_tagged_phys_byte_ucincl' [simp]
      and Rep_nonempty_share_inject [simp]
      and top.extremum_uniqueI [simp]
      and top_nonempty_share.rep_eq [simp]
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
    shows \<open>urust_is_local \<Gamma> (memset_tagged_phys_block_core pa n b) (raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag)\<close>
proof -
  have \<open>\<exists>m. physical_memory_memset_block \<sigma>0 pa n b = Inr m\<close>
    if \<open>\<sigma>0 \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag\<close> for \<sigma>0
    using that assms memset_tagged_block_pre_writable_states physical_memory_memset_block_succeeds by fastforce
  moreover 
  have \<open>physical_memory_memset_block (\<sigma>0 + \<sigma>1) pa n b = Inr (m + \<sigma>1) \<and> m\<sharp>\<sigma>1\<close>
    if \<open>\<sigma>0 \<sharp> \<sigma>1\<close> and \<open>physical_memory_memset_block \<sigma>0 pa n b = Inr m\<close> for \<sigma>0 \<sigma>1 m:: "'a tagged_physical_memory"
      using that assms physical_memory_memset_block_local by blast
  ultimately show ?thesis
    by (fastforce simp add: is_local_def urust_eval_predicate_memset_phys_block_core)
qed

lemma memset_phys_block_spec [raw_tagged_pmem_spec_specs]:
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
      and \<open>is_aligned pa n\<close>
      and \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>\<Gamma>; memset_tagged_phys_block pa n b \<Turnstile>\<^sub>F
              make_function_contract (raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag) (\<lambda>_. raw_tagged_pmem_defs.memset_tagged_block_post pa n tag b)\<close>
proof -
  have \<open>m \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_post pa n tag b\<close>
    if \<sigma>: \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag\<close>
          \<open>physical_memory_memset_block \<sigma> pa n b = Inr m\<close>      for \<sigma> m
  proof -
    have \<open>physical_memory_lookup m x = Tagged \<top> tag b\<close> 
        if \<open>x \<in> block_range pa n\<close> for x
        using \<sigma> that
        by (auto simp add: map_shareable_value_def set_byte_state_def 
            dest!: physical_memory_memset_block_result[of \<sigma> pa n b m x] memset_tagged_block_pre_tagged)
    from this assms show ?thesis
      by (simp add: memset_tagged_block_post_via_lookup)
  qed 
  moreover  {
       fix \<sigma> e
    assume \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag \<star> UNIV\<close>
       and \<open>physical_memory_memset_block \<sigma> pa n b = Inl e\<close>
    moreover from this have \<open>ucincl (raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag)\<close>
      by ucincl_solve
    moreover from calculation have \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.memset_tagged_block_pre pa n tag\<close>
      by (auto simp add: asepconj_ident2)
    moreover from calculation have \<open>\<sigma> \<Turnstile> \<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #}\<close>
      by meson
    moreover from calculation have \<open>writeable_byte_state (physical_memory_lookup \<sigma> pa)\<close>
      using block_range_includes memset_tagged_block_pre_writable_states by metis
    moreover from assms calculation obtain m where \<open>physical_memory_memset_block \<sigma> pa n b = Inr m\<close>
      using memset_tagged_block_pre_writable_states physical_memory_memset_block_succeeds by metis
    ultimately have \<open>False\<close>
      by clarsimp
  }
  moreover have \<open>ucincl (\<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #})\<close>
    by ucincl_solve
  moreover have \<open>ucincl (raw_tagged_pmem_defs.memset_tagged_block_post pa n tag b)\<close>
    by ucincl_solve
  moreover from calculation assms have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>, function_body (memset_tagged_phys_block pa n b)\<rangle> (x,y)) (\<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #})\<close>
    by (simp add: memset_phys_block_core_is_local memset_tagged_phys_block_def)
  moreover from calculation assms have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,function_body (memset_tagged_phys_block pa n b)\<rangle> (x,y)) (\<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #})\<close>
    by (simp add: memset_phys_block_core_is_local memset_tagged_phys_block_def)
  moreover from calculation assms have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,function_body (memset_tagged_phys_block pa n b)\<rangle> (x,y)) (\<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #})\<close>
    by (simp add: memset_phys_block_core_is_local memset_tagged_phys_block_def)
  moreover from calculation have
    \<open>\<Gamma> ; \<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #}
        \<turnstile> function_body (memset_tagged_phys_block pa n b)
        \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. raw_tagged_pmem_defs.memset_tagged_block_post pa n tag b) \<bowtie> (\<lambda>_. raw_tagged_pmem_defs.memset_tagged_block_post pa n tag b) \<bowtie> \<bottom>\<close>
    by (intro striple_localI, auto simp add: asepconj_ident2 memset_tagged_phys_block_def
      urust_eval_predicate_memset_phys_block_core)
  ultimately show ?thesis
    by (intro satisfies_function_contractI sstriple_from_stripleI) (auto simp add:
      ucincl_intros eval_value_def eval_return_def eval_abort_def)
qed

named_theorems asat_elims

lemma asat_multiE:
  assumes \<open>\<sigma> \<Turnstile> \<star>\<star> \<Phi>\<close>
     and \<open>\<And>x. x \<in># \<Phi> \<Longrightarrow> ucincl x\<close>
     and \<open>(\<And>\<phi>. \<phi> \<in># \<Phi> \<Longrightarrow> \<sigma> \<Turnstile> \<phi>) \<Longrightarrow> R\<close>
   shows R 
  by (metis aentailsE aentails_cancel_r asepconj_add_mset assms multi_member_split)

corollary asat_multiE2[asat_elims]:
  assumes \<open>\<sigma> \<Turnstile> \<star>\<star>{# \<xi> x . x \<leftarrow> ms #}\<close>
     and \<open>\<And>x. x \<in># ms \<Longrightarrow> ucincl (\<xi> x)\<close>
     and \<open>(\<And>x. x \<in># ms \<Longrightarrow> \<sigma> \<Turnstile> \<xi> x) \<Longrightarrow> R\<close>
   shows R
  using assms by (elim asat_multiE; clarsimp)

lemma asat_asepconjE[asat_elims]:
  assumes \<open>\<sigma> \<Turnstile> \<alpha> \<star> \<beta>\<close>
     and \<open>ucincl \<alpha>\<close>
     and \<open>ucincl \<beta>\<close>
     and \<open>\<sigma> \<Turnstile> \<alpha> \<Longrightarrow> \<sigma> \<Turnstile> \<beta> \<Longrightarrow> R\<close>
   shows R
  using assms by (meson asepconj_strengthenE asepconj_strengthenE2)

declare apureE[asat_elims]
  and asat_existsE[asat_elims]
  and asat_existsE'[asat_elims]
  and asat_forallE[asat_elims]

lemma tagged_physical_block_byte_state:
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f\<close>
      and \<open>x \<in> block_range pa n\<close>
    shows \<open>physical_memory_lookup \<sigma> x = Tagged \<top> tag (f x)\<close>
proof -
  have \<open>\<And>a. a \<in> block_range pa n \<Longrightarrow> \<sigma> \<Turnstile> points_to_tagged_phys_byte a \<top> tag (f a)\<close>
    using assms by (auto simp: ucincl_intros elim!: asat_elims)
  with \<open>x \<in> block_range pa n\<close> show ?thesis
    using nonempty_share_top_eq top.extremum_unique by fastforce
qed

lemma taggable_physical_block_byte_state:
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
      and \<open>x \<in> block_range pa n\<close>
    shows \<open>\<exists>tag'. tag \<noteq> tag' \<and> physical_memory_lookup \<sigma> x = Tagged \<top> tag' (f x)\<close>
proof -
  obtain tag' where \<open>\<sigma> \<Turnstile> \<langle>tag' \<noteq> tag\<rangle> \<star> points_to_tagged_phys_byte x \<top> tag' (f x)\<close>
    using assms by (force simp: ucincl_IntE ucincl_Un ucincl_apure ucincl_asepconjL elim!: asat_elims)
  with \<open>x \<in> block_range pa n\<close> show ?thesis
    by (auto simp: ucincl_apure nonempty_share_top_eq top.extremum_unique points_to_tagged_phys_byte_ucincl' elim!: asat_elims)
qed

lemma taggable_physical_block_byte_stateE:
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
      and \<open>(\<And>x. x \<in> block_range pa n \<Longrightarrow> (\<exists>tag'. tag \<noteq> tag' \<and>
               physical_memory_lookup \<sigma> x = Tagged \<top> tag' (f x))) \<Longrightarrow> R\<close>
    shows R
  by (meson assms block_range_includes taggable_physical_block_byte_state)


lemma taggable_physical_block_byte_state':
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
  shows \<open>\<forall>x\<in>block_range pa n. is_owned_with_other_tag tag (state_to_class (physical_memory_lookup \<sigma> x))\<close>
  using assms by (auto elim!: taggable_physical_block_byte_stateE simp add: is_owned_with_other_tag_def
    nonempty_share_top_eq split!: shareable_value.splits)

lemma taggable_physical_block_byte_stateE':
  assumes \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
      and \<open>(\<forall>x\<in>block_range pa n. is_owned_with_other_tag tag (state_to_class (physical_memory_lookup \<sigma> x))) \<Longrightarrow> R\<close>
    shows R
  using assms by (simp add: taggable_physical_block_byte_state')

lemma urust_eval_predicate_tag_physical_page_core [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,tag_physical_page_core pa n tag\<rangle> (a, \<sigma>') \<longleftrightarrow>
            ((a = DanglingPointer \<and> \<sigma> = \<sigma>' \<and> (\<exists>e. physical_memory_tag_page \<sigma> pa n tag = Inl e)))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,tag_physical_page_core pa n tag\<rangle> (r,\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,tag_physical_page_core pa n tag\<rangle> (v,\<sigma>') \<longleftrightarrow>
            (\<exists>m. physical_memory_tag_page \<sigma> pa n tag = Inr m \<and> \<sigma>' = m)\<close>
by (auto simp add: tag_physical_page_core_def urust_eval_predicate_simps split: sum.splits)

lemma tag_physical_page_core_is_local:
    notes asepconj_simp [simp]
      and points_to_tagged_phys_byte_ucincl'' [simp]
      and points_to_tagged_phys_byte_ucincl' [simp]
      and Rep_nonempty_share_inject [simp]
      and top.extremum_uniqueI [simp]
      and top_nonempty_share.rep_eq [simp]
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
    shows \<open>urust_is_local \<Gamma> (tag_physical_page_core pa n tag) (raw_tagged_pmem_defs.taggable_physical_block pa n tag f)\<close>
proof -
  have \<open>\<exists>m. physical_memory_tag_page \<sigma>0 pa n tag = Inr m\<close>
    if \<open>\<sigma>0 \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close> for \<sigma>0
    using that assms
    by (force elim!: asat_elims taggable_physical_block_byte_stateE
        simp flip: physical_memory_tag_page_succeeds simp add: is_owned_with_other_tag_def)
  moreover 
  have \<open>physical_memory_tag_page (\<sigma>0 + \<sigma>1) pa n tag = Inr (m + \<sigma>1) \<and> m\<sharp>\<sigma>1\<close>
    if \<open>\<sigma>0 \<sharp> \<sigma>1\<close> and \<open>physical_memory_tag_page \<sigma>0 pa n tag  = Inr m\<close> for \<sigma>0 \<sigma>1 m
      using assms that physical_memory_tag_page_local by metis
  ultimately show ?thesis
    by (fastforce simp add: is_local_def urust_eval_predicate_tag_physical_page_core)
qed

lemma tag_physical_page_spec[raw_tagged_pmem_spec_specs]:
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
      and \<open>is_aligned pa n\<close>
      and \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>\<Gamma>; tag_physical_page pa n tag \<Turnstile>\<^sub>F
              make_function_contract (raw_tagged_pmem_defs.taggable_physical_block pa n tag f) (\<lambda>_. raw_tagged_pmem_defs.tagged_physical_block pa n tag f)\<close>
proof (intro satisfies_function_contractI; clarsimp;  ucincl_solve?)
  from assms have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,function_body (tag_physical_page pa n tag)\<rangle> (x,y)) (raw_tagged_pmem_defs.taggable_physical_block pa n tag f)\<close>
    by (simp add: tag_physical_page_core_is_local tag_physical_page_def)
  moreover from assms have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,function_body (tag_physical_page pa n tag)\<rangle> (x,y)) (raw_tagged_pmem_defs.taggable_physical_block pa n tag f)\<close>
    by (simp add: tag_physical_page_core_is_local tag_physical_page_def)
  moreover from assms have \<open>is_local (\<lambda>\<sigma> (x, y). \<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,function_body (tag_physical_page pa n tag)\<rangle> (x,y)) (raw_tagged_pmem_defs.taggable_physical_block pa n tag f)\<close>
    by (simp add: tag_physical_page_core_is_local tag_physical_page_def)
  moreover 
  have \<open>\<sigma>' \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f\<close>
    if \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,function_body (tag_physical_page pa n tag)\<rangle> ((),\<sigma>')\<close>
          \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
    for \<sigma> \<sigma>'
  proof -
    have \<open>physical_memory_lookup \<sigma>' x = Tagged \<top> tag (f x)\<close>
      if \<open>x \<in> block_range pa n\<close> for x
    proof -
      from that \<sigma> obtain tag' where \<open>tag' \<noteq> tag\<close> and \<open>physical_memory_lookup \<sigma> x = Tagged \<top> tag' (f x)\<close>
        by (force elim!: taggable_physical_block_byte_stateE)
      with that show ?thesis
        using \<sigma> by (clarsimp simp add: tag_physical_page_def 
            physical_memory_tag_block_result urust_eval_predicate_tag_physical_page_core(3))
    qed
    with \<sigma> show ?thesis
      using assms by (intro tagged_block_via_lookup) auto
  qed
  moreover 
  have \<open>\<sigma>' \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block pa n tag f\<close>
    if \<open>\<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,function_body (tag_physical_page pa n tag)\<rangle> ((),\<sigma>')\<close>
       \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
     for \<sigma> \<sigma>'
      using that
      by (simp add: tag_physical_page_def urust_eval_predicate_tag_physical_page_core(2))
  moreover {
      note calculation_thus_far = this
       fix \<sigma> a \<sigma>'
    assume \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f \<star> \<top>\<close>
       and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,function_body (tag_physical_page pa n tag)\<rangle> (a, \<sigma>')\<close>
    moreover have \<open>ucincl (raw_tagged_pmem_defs.taggable_physical_block pa n tag f)\<close>
      by ucincl_solve
    moreover from calculation have \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.taggable_physical_block pa n tag f\<close>
      using asepconj_strengthenE ucincl_UNIV by blast
    ultimately have \<open>False\<close>
      using calculation_thus_far assms
      by (clarsimp elim!: taggable_physical_block_byte_stateE' simp add: physical_memory_tag_page_succeeds
        tag_physical_page_def urust_eval_predicate_tag_physical_page_core)
  }
  moreover from calculation have \<open>\<Gamma> ; raw_tagged_pmem_defs.taggable_physical_block pa n tag f
      \<turnstile> function_body (tag_physical_page pa n tag)
      \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. raw_tagged_pmem_defs.tagged_physical_block pa n tag f) \<bowtie> (\<lambda>_. raw_tagged_pmem_defs.tagged_physical_block pa n tag f) \<bowtie> \<bottom>\<close>
    apply (intro striple_localI; clarsimp)
    by (meson asat_connectives_characterisation(1) asepconj_weakenI)
  ultimately show \<open>\<Gamma> ; raw_tagged_pmem_defs.taggable_physical_block pa n tag f
     \<turnstile> function_body (tag_physical_page pa n tag)
     \<stileturn> (\<lambda>_. raw_tagged_pmem_defs.tagged_physical_block pa n tag f) \<bowtie> (\<lambda>_. raw_tagged_pmem_defs.tagged_physical_block pa n tag f) \<bowtie> \<bottom>\<close>
    by (intro sstriple_from_stripleI) (auto simp add: eval_value_def eval_return_def eval_abort_def)
qed

lemma memset_phys_contract_ucincl:
  shows [ucincl_intros]: \<open>ucincl (function_contract_pre (raw_tagged_pmem_defs.memset_tagged_phys_contract pa l tag b))\<close>
     and [ucincl_intros]: \<open>ucincl (function_contract_post (raw_tagged_pmem_defs.memset_tagged_phys_contract pa l tag b) r)\<close>
     and [ucincl_intros]: \<open>ucincl (function_contract_abort (raw_tagged_pmem_defs.memset_tagged_phys_contract pa l tag b) r')\<close> 
  by (ucincl_solve simp: raw_tagged_pmem_defs.memset_tagged_phys_contract_def)

lemma block_range_to_page_range:
  assumes \<open>is_aligned adr l\<close>
  shows \<open>block_range adr l = page_range_word adr l\<close>
  using assms aligned_word_range range_to_aligned_blocks_aligned
  by (auto simp add: is_aligned_neg_mask_eq block_range_def)

lemma page_range_word_to_block_range:
  assumes \<open>0 < l\<close>
  shows \<open>\<Union>( (\<lambda>an. page_range_word (fst an) (snd an)) ` set (range_to_aligned_blocks adr l)) =
         \<Union>( (\<lambda>an. block_range (fst an) (snd an)) ` set (range_to_aligned_blocks adr l))\<close>
  using block_range_to_page_range range_to_aligned_blocks_aligned by auto

lemma range_to_aligned_blocks_block_range:
  assumes \<open>0 < l\<close> and \<open>adr \<le> adr + (l - 1)\<close>
  shows \<open>{ adr .. (adr + (l - 1)) } =
         \<Union>( (\<lambda>an. block_range (fst an) (snd an)) ` set (range_to_aligned_blocks adr l))\<close>
  using assms range_to_aligned_blocks_page_range[of l adr]
  by (clarsimp simp add: page_range_word_to_block_range[of l adr, symmetric]
    image_comp add_diff_eq)

lemma range_to_aligned_blocks_disjoint:
  assumes \<open>range_to_aligned_blocks adr l ! i = (xi,ni)\<close>
  and \<open>range_to_aligned_blocks adr l ! j = (xj,nj)\<close>
  and \<open>i < length (range_to_aligned_blocks adr l)\<close>
  and \<open>j < length (range_to_aligned_blocks adr l)\<close>
  and \<open>i < j\<close>
  and \<open>adr \<le> adr + (l-1)\<close>
  and \<open>adr < 2^N\<close>
  and \<open>adr+(l-1) < 2^N\<close>
  and \<open>x \<in> block_range xi ni\<close>
  and \<open>x \<in> block_range xj nj\<close>
  shows \<open>R\<close>
  using assms 
proof (induction adr l arbitrary: i j rule: range_to_aligned_blocks_induct)
  case (1 addr l)
  then show ?case by clarsimp
next
  case (2 addr l xs)
  moreover from calculation have \<open>l \<le> 2^N\<close>
    by (metis add_diff_cancel_left' word_less_imp_diff_less word_minus_one_le_leq)
  moreover from calculation have \<open>2^next_aligned_block_size x l \<le> (2^N :: 64 word)\<close>
    using next_aligned_block_size_le order_trans by blast
  moreover from calculation have \<open>next_aligned_block_size x l \<le> N\<close>
    by (metis next_aligned_block_size_gt0 p2_gt_0 power_le_mono word_gt_a_gt_0)
  moreover from calculation have \<open>0 < l - 2 ^ next_aligned_block_size addr l\<close>
    by clarsimp (metis bot_nat_0.extremum le_less_Suc_eq length_0_conv less_zeroE range_to_aligned_blocks.simps)
  moreover from calculation have \<open>addr + 2 ^ next_aligned_block_size addr l \<le> addr + (l - 1)\<close>
    by (metis diff_self le_step_down_word_2 next_aligned_block_size_le word_coorder.not_eq_extremum word_plus_mono_right)
  moreover have \<open>is_aligned xj nj\<close>
   using range_to_aligned_blocks_aligned assms by (metis nth_mem)
  moreover from calculation have \<open>is_aligned ((2::64 word) ^ N) ni\<close>
    by (metis is_aligned_power2 range_to_aligned_blocks.elims range_to_aligned_blocks_bounds)
  note facts = this calculation
  show ?case
  proof (cases i)
    case 0
    moreover from this and facts
    have \<open>xi + 2 ^ next_aligned_block_size xi l \<le> xj \<and> xj \<le> xi + (l - 1) \<and> nj \<le> N\<close>
      using range_to_aligned_blocks_bounds[of
        \<open>(xi + 2 ^ next_aligned_block_size xi l)\<close>
        \<open>(l - 2 ^ next_aligned_block_size xi l)\<close> \<open>j-1\<close> xj nj N]
      by auto
    ultimately show ?thesis
      using facts apply (auto simp add: next_aligned_block_is_aligned block_range_to_page_range
                              range_to_aligned_blocks_aligned page_range_word_def)
      by (meson next_aligned_block_is_aligned not_greatest_aligned order_trans word_must_wrap)
  next
    case (Suc nat)
    from facts and this show ?thesis by auto
  qed
qed

lemma memset_phys_spec[raw_tagged_pmem_spec_specs]:
  notes wp_cong[crush_cong del]
    and wp_cong'[crush_cong del]
  shows \<open>\<Gamma>; memset_tagged_phys pa l b \<Turnstile>\<^sub>F raw_tagged_pmem_defs.memset_tagged_phys_contract pa l tag b\<close>
  apply (crush_boot f: memset_tagged_phys_def contract: raw_tagged_pmem_defs.memset_tagged_phys_contract_def)
  apply (clarsimp simp add: range_to_aligned_blocks_block_range)
  apply (crush_base simp add: list_into_iter_def)
  apply (rule_tac \<tau>=\<open>\<bottom>\<close> and
          INV=\<open>\<lambda>ls i.
            \<star>\<star> {# \<Union> (range
                 (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (\<Union>an\<in>set (List.drop i ls). block_range (fst an) (snd an)) #} \<star>
            \<star>\<star> {# points_to_tagged_phys_byte a \<top> tag b . a \<leftarrow> mset_set (\<Union>an\<in>set (List.take i ls). block_range (fst an) (snd an)) #}\<close>
      in wp_raw_for_loop_framedI', ucincl_solve)
   apply (fastcrush_base split: prod.splits simp add: take_Suc_conv_app_nth drop_Suc_nth)
  subgoal for i
    apply (rule wp_callI[OF memset_phys_block_spec]; (simp add: PMEM_TRIE_ADDRESS_WIDTH_def)?)
    using range_to_aligned_blocks_bounds
       apply (metis prod.collapse raw_tagged_physical_memory_bitwidth_def raw_tagged_pmem_defs.is_within_bounds_def)
      apply (metis nth_mem range_to_aligned_blocks_aligned surjective_pairing)
    using range_to_aligned_blocks_bounds
     apply (metis PMEM_TRIE_ADDRESS_LIMIT_def PMEM_TRIE_ADDRESS_WIDTH_def prod.collapse 
        raw_tagged_physical_memory_bitwidth_def raw_tagged_pmem_defs.is_within_bounds_def)
    apply (subst mset_set_Union; (simp add: finite_block_range)?)
     apply (safe; clarsimp simp add: raw_tagged_pmem_defs.is_within_bounds_def in_set_conv_nth)
     apply (cases \<open>range_to_aligned_blocks pa l ! i\<close>; clarsimp)
    using range_to_aligned_blocks_disjoint [where i=i] apply force
    apply fastcrush_base
    apply (subst mset_set_Union; (simp add: finite_block_range)?) 
     apply (safe; clarsimp simp add: raw_tagged_pmem_defs.is_within_bounds_def in_set_conv_nth)
     apply (case_tac \<open>range_to_aligned_blocks pa l ! i\<close>; clarsimp)
     apply (meson order_less_trans range_to_aligned_blocks_disjoint)
    apply fastcrush_base
    done
  done

text\<open>Finally, we establish share splitting for the \<^verbatim>\<open>points_to\<close> predicate.

The following section provides the definition for a singleton memory owning a single
claimed physical byte with a given share. The details of the construction are not relevant
and hence marked \<^verbatim>\<open>private\<close>.\<close>
context begin

text\<open>We construct the desired singleton-memory as a restriction of the 'all claimed' memory.\<close>

definition physical_memory_singleton_tagged :: \<open>64 word \<Rightarrow> 8 word \<Rightarrow> nonempty_share \<Rightarrow> 'tag \<Rightarrow> 'tag tagged_physical_memory\<close> where
  \<open>physical_memory_singleton_tagged pa v sh tag \<equiv>
     physical_memory_take_block (physical_memory_tag_all_bytes v sh tag) pa 0\<close>

text\<open>This is the defining property for the singleton memory:\<close>
lemma physical_memory_singleton_tagged_decl:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>(m = physical_memory_singleton_tagged pa v sh tag) \<longleftrightarrow>
              (physical_memory_lookup m pa = Tagged sh tag v \<and>
                  (\<forall>pa'. pa \<noteq> pa' \<longrightarrow> physical_memory_lookup m pa' = Unmapped))\<close>
using assms by (auto simp add: physical_memory_singleton_tagged_def
  physical_memory_tag_all_bytes_lookup physical_memory_take_lookup intro!: physical_memory_ext)

end

\<comment> \<open>Local notation only\<close>
notation physical_memory_singleton_tagged ("PSINGLE")
notation points_to_tagged_phys_byte ("P'(_:_:_:_')")
notation physical_memory_lookup ("LOOKUP")
notation Rep_nonempty_share ("\<epsilon>")

corollary physical_memory_singleton_tagged_lookup:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>LOOKUP (PSINGLE pa v sh tag) pa' = (if pa = pa' then Tagged sh tag v else Unmapped)\<close>
by (metis assms physical_memory_singleton_tagged_decl)

text\<open>The strategy for proving share-splitting for \<^verbatim>\<open>points_to\<close> is to split off a singleton
memory for the byte to split, and then split that singleton memory.

First, we prove that singleton memories can be split as expected:\<close>

lemma physical_memory_singleton_tagged_split:
    fixes sh1 sh2 :: nonempty_share
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>\<epsilon> sh1 \<sharp> \<epsilon> sh2\<close>
    shows \<open>PSINGLE pa v sh1 tag \<sharp> PSINGLE pa v sh2 tag\<close>
      and \<open>PSINGLE pa v sh1 tag + PSINGLE pa v sh2 tag = PSINGLE pa v (sh1 + sh2) tag\<close>
proof -
  from assms show \<open>PSINGLE pa v sh1 tag \<sharp> PSINGLE pa v sh2 tag\<close>
    by (auto simp add: physical_memory_disjoint_eq physical_memory_singleton_tagged_lookup)
  moreover from this assms show \<open>PSINGLE pa v sh1 tag + PSINGLE pa v sh2 tag = PSINGLE pa v (sh1 + sh2) tag\<close>
    by (clarsimp simp add: physical_memory_singleton_tagged_decl
       physical_memory_plus_eq physical_memory_singleton_tagged_lookup)
qed

lemma physical_memory_singleton_tagged_split_alt:
    fixes sh1 sh2 :: nonempty_share
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>\<epsilon> sh1 \<sharp> \<epsilon> sh2\<close>
    shows \<open>{PSINGLE pa v (sh1 + sh2) tag} = {PSINGLE pa v sh1 tag} \<star> {PSINGLE pa v sh2 tag}\<close>
using assms physical_memory_singleton_tagged_split asepconj_singleton by metis

lemma physical_memory_singleton_tagged_split_rev:
    fixes sh1 sh2 :: nonempty_share
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>PSINGLE pa v sh1 tag1 \<sharp> PSINGLE pa v' sh2 tag2\<close>
    shows \<open>v = v'\<close>
      and \<open>tag1 = tag2\<close>
      and \<open>\<epsilon> sh1 \<sharp> \<epsilon> sh2\<close>
proof -
  let ?\<sigma> = \<open>PSINGLE pa v sh1 tag1 + PSINGLE pa v' sh2 tag2\<close>
  from assms have \<open>Tagged sh1 tag1 v \<sharp> Tagged sh2 tag2 v'\<close>
    by (metis assms physical_memory_disjoint_eq physical_memory_singleton_tagged_lookup)
  from this show \<open>v = v'\<close> and \<open>tag1 = tag2\<close> and \<open>Rep_nonempty_share sh1 \<sharp> Rep_nonempty_share sh2\<close>
    using tagged_disjoint_lemma by blast+
qed

lemma physical_memory_singleton_tagged_split_alt':
    fixes sh1 sh2 :: nonempty_share
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>{PSINGLE pa v sh1 tag} \<star> {PSINGLE pa v' sh2 tag'} =
             (if v = v' \<and> tag = tag' \<and> \<epsilon> sh1 \<sharp> \<epsilon> sh2 then
                {PSINGLE pa v (sh1 + sh2) tag}
              else {})\<close>
using assms by (cases \<open>v = v'\<close>; cases \<open>\<epsilon> sh1 \<sharp> \<epsilon> sh2\<close>) (auto simp add:
  physical_memory_singleton_tagged_split_alt asepconj_def asat_def
  physical_memory_singleton_tagged_split_rev)

lemma physical_memory_singleton_tagged_split_alt'':
    fixes sh1 sh2 :: nonempty_share
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>{PSINGLE pa v sh1 tag} \<star> {PSINGLE pa v' sh2 tag'} \<star> \<top> =
             {PSINGLE pa v (sh1 + sh2) tag} \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>v = v'\<rangle> \<star> \<langle>\<epsilon> sh1 \<sharp> \<epsilon> sh2\<rangle>\<close>
  using assms by (cases \<open>v = v'\<close>; cases \<open>tag = tag'\<close>; cases \<open>\<epsilon> sh1 \<sharp> \<epsilon> sh2\<close>)
  (auto simp flip: asepconj_assoc simp add:
    physical_memory_singleton_tagged_split_alt' simp add: asepconj_simp apure_def)

lemma physical_memory_take_byte:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>LOOKUP \<sigma> pa = Tagged sh tag b\<close>
    shows \<open>physical_memory_take_block \<sigma> pa 0 = PSINGLE pa b sh tag\<close>
using assms by (clarsimp simp add: physical_memory_singleton_tagged_decl physical_memory_take_lookup)

lemma physical_memory_split_byte:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>LOOKUP \<sigma> pa = Tagged sh tag b\<close>
    shows \<open>\<sigma> = PSINGLE pa b sh tag + physical_memory_delete_block \<sigma> pa 0\<close>
      and \<open>PSINGLE pa b sh tag \<sharp> physical_memory_delete_block \<sigma> pa 0\<close>
using assms by (metis physical_memory_take_byte physical_memory_take_delete_eq) (metis assms
  physical_memory_take_byte physical_memory_take_delete_disjoint)

lemma share_leq_split:
    fixes sh sh' :: share
  assumes \<open>sh' \<le> sh\<close>
    shows \<open>sh' \<preceq> sh\<close>
proof -
  let ?sh'' = \<open>sh - sh'\<close>
  from assms have \<open>sh = sh' + ?sh''\<close>
    by (metis diff_eq inf_sup_ord(1) leD le_supI order_le_less plus_share_def shunt2)
  moreover have \<open>sh' \<sharp> ?sh''\<close>
    by (simp add: diff_eq disjoint_share_def)
  ultimately show ?thesis
    by fastforce
qed

text\<open>Next, we describe the \<^verbatim>\<open>points_to\<close> predicate as the upwards closure of the singleton memory:\<close>
lemma points_to_tagged_phys_byte_singleton:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    shows \<open>P(pa:(\<epsilon> sh):tag:b) = {PSINGLE pa b sh tag} \<star> \<top>\<close>
proof safe
     fix \<sigma>
  assume \<open>\<sigma> \<in> P(pa:(\<epsilon> sh):tag:b)\<close>
  then obtain sh' where sh': \<open>\<epsilon> sh \<le> \<epsilon> sh'\<close>   \<open>LOOKUP \<sigma> pa = Tagged sh' tag b\<close>
    by (auto simp add: points_to_tagged_phys_byte_def)
  with assms obtain \<sigma>' where \<sigma>': \<open>\<sigma> = PSINGLE pa b sh' tag + \<sigma>'\<close> \<open>PSINGLE pa b sh' tag \<sharp> \<sigma>'\<close>
    using physical_memory_split_byte by metis
  then obtain sh'' where sh'': \<open>\<epsilon> sh \<sharp> sh''\<close>  \<open>\<epsilon> sh + sh'' = \<epsilon> sh'\<close>
    using share_leq_split sh' by blast
  show \<open>\<sigma> \<in> {PSINGLE pa b sh tag} \<star> \<top>\<close>
  proof (cases \<open>sh'' = 0\<close>)
    case True
    then have \<open>sh = sh'\<close>
      using Rep_nonempty_share_inject
      using sh'' by auto 
    with \<sigma>' show ?thesis
      by (metis asat_connectives_characterisation(1) asat_def asepconjI insert_iff)
  next
    case False
    then obtain sh''' where sh''': \<open>sh'' = \<epsilon> sh'''\<close>
      using Rep_nonempty_share_cases by (auto simp: bot.not_eq_extremum zero_share_def)
    moreover 
    obtain *: \<open>PSINGLE pa b sh' tag = PSINGLE pa b sh tag + PSINGLE pa b sh''' tag\<close>  
              \<open>PSINGLE pa b sh tag \<sharp> PSINGLE pa b sh''' tag\<close>
      by (metis Rep_nonempty_share_inverse assms plus_nonempty_share.rep_eq plus_share_def
        physical_memory_singleton_tagged_split sh''' sh'')
    have \<open>\<sigma> = PSINGLE pa b sh tag + (PSINGLE pa b sh''' tag + \<sigma>')\<close>
      by (metis \<sigma>' * sepalg_assoc sepalg_pairwise)
    moreover have \<open>PSINGLE pa b sh tag \<sharp> (PSINGLE pa b sh''' tag + \<sigma>')\<close>
      by (metis \<sigma>'(2) * sepalg_apart_assoc)
    moreover have \<open>PSINGLE pa b sh''' tag \<sharp> \<sigma>'\<close>
      by (metis \<sigma>'(2) * sepalg_apart_plus)
    ultimately show ?thesis
      by (meson asat_connectives_characterisation(1) asat_def asepconjI insert_iff)
  qed
next
     fix \<sigma>
  assume \<open>\<sigma> \<in> {PSINGLE pa b sh tag} \<star> \<top>\<close>
  then obtain \<sigma>'' and \<sigma>0 where \<open>\<sigma> = \<sigma>'' + \<sigma>0\<close> and \<open>\<sigma>'' \<sharp> \<sigma>0\<close> and \<open>\<sigma>'' \<Turnstile> {PSINGLE pa b sh tag}\<close>
    by (meson asat_def asepconjE)
  then obtain \<sigma>' where \<sigma>': \<open>PSINGLE pa b sh tag \<sharp> \<sigma>'\<close> \<open>\<sigma> = PSINGLE pa b sh tag + \<sigma>'\<close>
    by (simp add: asat_def)
  moreover obtain \<open>LOOKUP \<sigma> pa = Tagged sh tag b + LOOKUP \<sigma>' pa\<close> and \<open>Tagged sh tag b \<sharp> LOOKUP \<sigma>' pa\<close>
    by (metis assms \<sigma>' physical_memory_disjoint_eq physical_memory_plus_eq physical_memory_singleton_tagged_decl)
  ultimately show \<open>\<sigma> \<in> P(pa:(\<epsilon> sh):tag:b)\<close>
    using assms
    by (metis CollectD Rep_nonempty_share asat_def asat_weaken order.eq_iff 
      physical_memory_singleton_tagged_lookup points_to_tagged_phys_byteI points_to_tagged_phys_byte_ucincl' 
      zero_share_def)
qed

lemma points_to_tagged_phys_byte_empty_share [raw_tagged_pmem_spec_specs]:
  shows \<open>P(pa:0:tag:b) = {}\<close>
by (clarsimp simp add: points_to_tagged_phys_byte_def)


text\<open>Finally, the desired share splitting for the \<^verbatim>\<open>points_to\<close> predicate:\<close>
lemma points_to_tagged_phys_byte_split_core:
  shows \<open>P(pa:shA:tag:b) \<star> P(pa:shB:tag':b') = P(pa:(shA + shB):tag:b) \<star> \<langle>0 < shA\<rangle> \<star> \<langle>0 < shB\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle> \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>b = b'\<rangle>\<close>
proof (cases \<open>pa \<ge> PMEM_TRIE_ADDRESS_LIMIT\<close>)
  case True
  then have \<open>P(pa:(shA + shB):tag:b) = {}\<close> and \<open>P(pa:shA:tag:b) = {}\<close> and \<open>P(pa:shB:tag:b) = {}\<close>
    by (auto simp add: points_to_tagged_phys_byte_def physical_memory_lookup_out_of_range)
  then show ?thesis
    by (simp add: asepconj_simp)
next
  case False
  then have less: \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
    by auto
  show ?thesis
   proof (cases \<open>shA = 0 \<or> shB = 0\<close>)
     case True
     then show ?thesis
       by (auto simp: points_to_tagged_phys_byte_empty_share asepconj_simp asepconj_False_True)
   next
     case False
     then have \<open>0 \<noteq> shA\<close> and \<open>0 \<noteq> shB\<close> 
       by auto
    moreover from this have \<open>0 < shA\<close> and \<open>0 < shB\<close> and \<open>0 < shA + shB\<close>
      by (metis bot.not_eq_extremum zero_share_def less_supI1 plus_share_def)+
    moreover from calculation obtain shA' shB' :: nonempty_share where \<open>shA = \<epsilon> shA'\<close> \<open>shB = \<epsilon> shB'\<close>
      by (metis Abs_nonempty_share_inverse less_supI1 mem_Collect_eq plus_share_def zero_share_def)
    moreover from this have \<open>shA + shB = \<epsilon> (shA' + shB')\<close>
      by (simp add: plus_nonempty_share.rep_eq plus_share_def)
    moreover from calculation and points_to_tagged_phys_byte_singleton have
        \<open>P(pa:(shA + shB):tag:b)  = {PSINGLE pa b (shA' + shB') tag } \<star> \<top>\<close> and
        \<open>P(pa:shA:tag:b) = {PSINGLE pa b shA' tag} \<star> \<top>\<close> and \<open>P(pa:shB:tag':b') = {PSINGLE pa b' shB' tag'} \<star> \<top>\<close>
      by (metis less)+
    ultimately show ?thesis
      using less
      apply (simp add: points_to_tagged_phys_byte_singleton)
      apply (intro aentails_eq; clarsimp simp add: asepconj_simp)
      apply (aentails_pick_assm 2, clarsimp simp add: asepconj_simp)
      apply (aentails_pick_assm 1, clarsimp simp add: physical_memory_singleton_tagged_split_alt'')
      apply (aentails_cancel, clarsimp simp add: asepconj_simp ucincl_intros aentails_simp is_sat_pure 
        intro!: apure_entailsR0)
      apply (aentails_pick_concl 2, clarsimp simp add: asepconj_simp)
      apply (aentails_pick_concl 1, clarsimp simp add: physical_memory_singleton_tagged_split_alt'')
      apply (aentails_cancel, clarsimp simp add: asepconj_simp ucincl_intros aentails_simp is_sat_pure 
        intro!: apure_entailsR0)
      done
   qed
 qed

lemma points_to_tagged_phys_byte_split [raw_tagged_pmem_spec_specs]:
    fixes pa sh shA shB b
  assumes \<open>sh = shA + shB\<close>
      and \<open>shA \<sharp> shB\<close>
      and \<open>0 < shA\<close>
      and \<open>0 < shB\<close>
    shows \<open>P(pa:sh:tag:b) \<longlongrightarrow> P(pa:shA:tag:b) \<star> P(pa:shB:tag:b)\<close>
using assms by (fastcrush_base simp add: points_to_tagged_phys_byte_split_core)

lemma points_to_tagged_phys_byte_combine [raw_tagged_pmem_spec_specs]:
  fixes pa shA shB b b'
  shows \<open>P(pa:shA:tag:b) \<star> P(pa:shB:tag':b') \<longlongrightarrow> P(pa:(shA + shB):tag:b) \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>b = b'\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle>\<close>
by (clarsimp simp add: points_to_tagged_phys_byte_split_core) fastcrush_base

no_notation physical_memory_singleton_tagged ("PSINGLE")
no_notation points_to_tagged_phys_byte ("P'(_:_:_')")
no_notation physical_memory_lookup ("LOOKUP")
no_notation Rep_nonempty_share ("\<epsilon>")

declare memset_tagged_phys_def [code]
declare memset_tagged_phys_block_def [code]
declare memset_tagged_phys_block_core_def [code]

declare load_tagged_physical_address_def [code]
declare load_tagged_physical_address_core_def [code]

declare store_tagged_physical_address_def [code]
declare store_tagged_physical_address_core_def [code]

declare store_tagged_phys_byte_def [code]
declare load_tagged_phys_byte_def [code]

declare tag_physical_page_def [code]
declare tag_physical_page_core_def [code]

interpretation Raw_Tagged_Physical_Memory_Trie: raw_tagged_physical_memory 
  \<open>\<lambda>(_ :: 'tag tagged_physical_memory) (_ :: 'tag) (_::'abort) (_ :: 'i prompt) (_::'o prompt_output). ()\<close>
  memset_tagged_phys memset_tagged_phys_block points_to_tagged_phys_byte
  store_tagged_physical_address
  load_tagged_physical_address tag_physical_page
proof
  fix \<Gamma> :: \<open>('tag tagged_physical_memory, 'abort, 'i, 'o) striple_context\<close> and pa tag \<pi> b
  show \<open>\<Gamma> ; load_tagged_physical_address
             pa \<Turnstile>\<^sub>F raw_tagged_pmem_defs.load_tagged_physical_address_contract pa \<pi> tag b\<close>
    by (simp add: raw_tagged_physical_memory_defs.all_physical_memory_defs(2) raw_tagged_pmem_spec_specs(2))
next
  fix \<Gamma> :: \<open>('tag tagged_physical_memory, 'abort, 'i, 'o) striple_context\<close> and pa b tag b0
  show \<open>\<Gamma> ; store_tagged_physical_address pa
             b \<Turnstile>\<^sub>F raw_tagged_pmem_defs.store_tagged_physical_address_contract pa b b0 tag\<close>
    by (simp add: raw_tagged_pmem_defs.all_physical_memory_defs(3) raw_tagged_pmem_spec_specs(3))
next
  fix n and pa :: \<open>64 word\<close> and \<Gamma> :: \<open>('tag tagged_physical_memory, 'abort, 'i, 'o) striple_context\<close> and f and tag tag' :: 'tag
  assume \<open>n \<le> raw_tagged_physical_memory_bitwidth\<close>
     and \<open>raw_tagged_pmem_defs.is_within_bounds pa\<close>
     and \<open>is_aligned pa n\<close>
  then show \<open>\<Gamma> ; tag_physical_page pa n tag \<Turnstile>\<^sub>F 
              make_function_contract (raw_tagged_pmem_defs.taggable_physical_block  pa n tag f)
                     (\<lambda>_. raw_tagged_pmem_defs.tagged_physical_block pa n tag f)\<close>
    by (simp add: PMEM_TRIE_ADDRESS_LIMIT_def PMEM_TRIE_ADDRESS_WIDTH_def raw_tagged_physical_memory_bitwidth_def 
      raw_tagged_pmem_defs.is_within_bounds_def tag_physical_page_spec)
next
  fix n and pa :: \<open>64 word\<close> and \<Gamma> :: \<open>('tag tagged_physical_memory, 'abort, 'i, 'o) striple_context\<close> and b and tag
  assume \<open>n \<le> raw_tagged_physical_memory_bitwidth\<close>
     and \<open>is_aligned pa n\<close>
     and \<open>raw_tagged_pmem_defs.is_within_bounds pa\<close>
  from this show \<open>\<Gamma> ; memset_tagged_phys_block pa n
             b \<Turnstile>\<^sub>F make_function_contract
                     (\<star>\<star> {# \<Union> (range (points_to_tagged_phys_byte a \<top> tag)) . a \<leftarrow> mset_set (block_range pa n) #})
                     (\<lambda>_. \<star>\<star> {# points_to_tagged_phys_byte a \<top> tag b . a \<leftarrow> mset_set (block_range pa n) #})\<close>
    using memset_phys_block_spec
    by (metis PMEM_TRIE_ADDRESS_LIMIT_def PMEM_TRIE_ADDRESS_WIDTH_def raw_tagged_physical_memory_bitwidth_def 
      raw_tagged_pmem_defs.is_within_bounds_def)
next
  show \<open>\<And>pa shA shB b b' tag tag'. P(pa:shA:tag:b) \<star> P(pa:shB:tag':b')
       \<longlongrightarrow> P(pa:shA + shB:tag:b) \<star> \<langle>b = b'\<rangle> \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle>\<close>
    by (metis asepconj_swap_top points_to_tagged_phys_byte_combine)
qed (auto simp add: raw_tagged_pmem_spec_specs)

lemma physical_memory_tag_all_bytes_tagged_block:
  assumes \<open>\<sigma> = physical_memory_tag_all_bytes b \<top> tag\<close>
    shows \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block 0 PMEM_TRIE_ADDRESS_WIDTH tag (\<lambda>_. b)\<close>
proof(intro tagged_block_via_lookup)
     fix x
  assume \<open>x \<in> block_range 0 PMEM_TRIE_ADDRESS_WIDTH\<close>
  with assms have \<open>x < PMEM_TRIE_ADDRESS_LIMIT\<close>
    by (clarsimp simp add: PMEM_TRIE_ADDRESS_LIMIT_def PMEM_TRIE_ADDRESS_WIDTH_def
      block_range_to_page_range page_range_word_def) unat_arith
  with assms show \<open>physical_memory_lookup \<sigma> x = Tagged \<top> tag b\<close>
    by (clarsimp simp add: physical_memory_tag_all_bytes_lookup) 
qed (auto simp add: PMEM_TRIE_ADDRESS_LIMIT_def PMEM_TRIE_ADDRESS_WIDTH_def)

lemma physical_memory_tag_all_bytes_correct:
  assumes \<open>\<sigma> = physical_memory_tag_all_bytes b \<top> tag\<close>
  shows \<open>\<sigma> \<Turnstile> \<star>\<star>{# points_to_tagged_phys_byte addr \<top> tag b .
                   addr \<leftarrow> mset_set { pa . pa < PMEM_TRIE_ADDRESS_LIMIT } #}\<close>
proof -
  from assms have \<open>\<sigma> \<Turnstile> raw_tagged_pmem_defs.tagged_physical_block 0 PMEM_TRIE_ADDRESS_WIDTH tag (\<lambda>_. b)\<close>
    using physical_memory_tag_all_bytes_tagged_block by metis
  moreover have \<open>{pa:: 64 word. pa < 2 ^ PMEM_TRIE_ADDRESS_WIDTH} =
      {0..(2 ^ PMEM_TRIE_ADDRESS_WIDTH) - 1}\<close>
    by (auto simp add: PMEM_TRIE_ADDRESS_WIDTH_def; unat_arith)
  ultimately show ?thesis
    by (clarsimp simp add: block_range_to_page_range page_range_word_def PMEM_TRIE_ADDRESS_WIDTH_def
      PMEM_TRIE_ADDRESS_LIMIT_def)
qed

(*<*)
end
(*>*)
