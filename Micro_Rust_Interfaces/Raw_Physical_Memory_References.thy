(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Raw_Physical_Memory_References
  imports 
    Micro_Rust_Std_Lib.StdLib_All
    Micro_Rust_Interfaces_Core.References
    Micro_Rust_Interfaces_Core.Raw_Physical_Memory
    Crush.Crush
begin

section\<open>References backed in physical memory\<close>

text\<open>In this section, we demonstrate how the \<^locale>\<open>reference\<close> locale can be interpreted in the
context of the physical memory interface.\<close>

context raw_tagged_physical_memory
begin

lemma points_to_tagged_phys_byte_combinesplit:
     \<open>points_to_tagged_phys_byte pa shA tag b \<star> points_to_tagged_phys_byte pa shB tag' b'
        = points_to_tagged_phys_byte pa (shA + shB) tag b \<star> \<langle>0 < shA\<rangle> \<star> \<langle>0 < shB\<rangle> \<star> \<langle>b = b'\<rangle> \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle>\<close>
proof -
  { assume \<open>shA = 0\<close>
    from this have ?thesis
      by (auto simp add: points_to_tagged_phys_byte_empty_share asepconj_simp
        asepconj_False_True) }
  moreover { assume \<open>shB = 0\<close>
    from this have ?thesis
      by (auto simp add: points_to_tagged_phys_byte_empty_share asepconj_simp
        asepconj_False_True) }
  moreover { assume \<open>0 < shA\<close> and \<open>0 < shB\<close>
    then have ?thesis
      by (fastcrush_base intro!: aentails_eq seplog drule add: points_to_tagged_phys_byte_combine
    seplog rule add: points_to_tagged_phys_byte_split) }
  ultimately show ?thesis
    by (metis bot.not_eq_extremum zero_share_def)
qed

ucincl_auto memset_tagged_phys_contract
  load_tagged_physical_address_contract
  store_tagged_physical_address_contract

end

datatype_record raw_pmem_region =
  raw_pmem_region_base :: \<open>64 word\<close>
  raw_pmem_region_size :: \<open>nat\<close>

definition raw_pmem_region_end :: \<open>raw_pmem_region \<Rightarrow> 64 word\<close> where
  \<open>raw_pmem_region_end rg \<equiv> raw_pmem_region_base rg + (of_nat (raw_pmem_region_size rg))\<close>

\<comment>\<open>TODO: Should the region not be allowed to reach up to the address boundary?\<close>
definition is_valid_raw_pmem_region :: \<open>raw_pmem_region \<Rightarrow> bool\<close> where
  \<open>is_valid_raw_pmem_region pr \<equiv> (unat (raw_pmem_region_base pr) + (raw_pmem_region_size pr)
                                   < 2^raw_tagged_physical_memory_bitwidth)\<close>

lemma is_valid_raw_pmem_region_sz_bound:
  assumes \<open>is_valid_raw_pmem_region pr\<close>
  shows \<open>raw_pmem_region_size pr < 2^raw_tagged_physical_memory_bitwidth\<close>
  using assms is_valid_raw_pmem_region_def by force

lemma is_valid_raw_pmem_region_nat_word_conv:
  assumes \<open>is_valid_raw_pmem_region pr\<close>
  shows \<open>unat (word64_of_nat (raw_pmem_region_size pr)) = raw_pmem_region_size pr\<close>
  using assms
  apply (intro unat_of_nat_eq)
  apply (drule is_valid_raw_pmem_region_sz_bound)
  apply (clarsimp simp add: raw_tagged_physical_memory_bitwidth_def)
  done

lemma is_valid_raw_pmem_region_nat_word_conv':
  assumes \<open>is_valid_raw_pmem_region pr\<close>
    and \<open>i < raw_pmem_region_size pr\<close>
  shows \<open>unat (word64_of_nat i) = i\<close>
  using assms
  apply (intro unat_of_nat_eq)
  apply (drule is_valid_raw_pmem_region_sz_bound)
  apply (clarsimp simp add: raw_tagged_physical_memory_bitwidth_def)
  done

text\<open>Here we define address in a range from a lower bound (inclusive) to an upper bound (exclusive).
Note, this is likely not the definition you would first think of, but this formulation is convenient
because it behaves better with respect to ranges that overflow. We rarely (or never) need to actually
have such ranges, but it is convenient to not have to prove the non-overflow conditions that otherwise
arise. Below, we show how this definition relates to the one that most readers probably have in mind.\<close>
definition word_range :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word set\<close> where
  \<open>word_range from to \<equiv> { a :: 64 word. a - from < a - to}\<close>

type_synonym raw_pref = raw_pmem_region

locale raw_tagged_physical_memory_references = 
  raw_tagged_physical_memory \<open>\<lambda>(_::'s::{sepalg}) (_ :: 'tag) (_ :: 'abort) (_ :: 'i prompt) (_::'o prompt_output). ()\<close>
begin

definition points_to_tagged_phys_bytes :: \<open>64 word \<Rightarrow> share \<Rightarrow> 'tag \<Rightarrow> 8 word list \<Rightarrow> 's assert\<close> where
  \<open>points_to_tagged_phys_bytes addr sh tag bs \<equiv>
    let idxs = [0..<length bs] in
    \<star>\<star>{# points_to_tagged_phys_byte (addr + (word_of_nat idx)) sh tag (bs!idx) \<Colon> idx \<leftarrow> idxs #}\<close>
ucincl_auto points_to_tagged_phys_bytes

definition points_to_raw' :: \<open>(raw_pref,8 word list) gref \<Rightarrow> share \<Rightarrow> 8 word list \<Rightarrow> 's assert\<close>
  where \<open>points_to_raw' r sh bs \<equiv> (let pr = Global_Store.address r in
    \<langle>is_valid_raw_pmem_region pr\<rangle> \<star>
    \<langle>length bs = raw_pmem_region_size pr\<rangle> \<star>
    (\<Squnion>tag. points_to_tagged_phys_bytes (raw_pmem_region_base pr) sh tag bs))\<close>
ucincl_auto points_to_raw'

definition update_raw_fun :: \<open>(raw_pref, 8 word list) gref \<Rightarrow> 8 word list \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>update_raw_fun r bs \<equiv>
     let pr = Global_Store.address r in
       FunctionBody \<lbrakk>
         trace!(l\<llangle>"Raw_Tagged_Physical_Memory.update_raw_fun"\<rrangle>);

         if \<llangle>length\<rrangle>\<^sub>1(bs) != \<llangle>raw_pmem_region_size\<rrangle>\<^sub>1(pr) {
           panic!("Size-mismatch for physical memory store")
         };

         for i in 0..\<llangle>word64_of_nat (raw_pmem_region_size pr)\<rrangle> {
           let cur_addr = \<llangle>raw_pmem_region_base pr + i\<rrangle>;
           let cur_byte = bs[i];
           store_tagged_physical_address (cur_addr, cur_byte);
         };
       \<rbrakk>\<close>

definition dereference_raw_fun :: \<open>(raw_pref, 8 word list) gref \<Rightarrow> ('s, 8 word list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>dereference_raw_fun r \<equiv>
     let pr = Global_Store.address r in
       FunctionBody \<lbrakk>
         trace!(l\<llangle>"Raw_Tagged_Physical_Memory.dereference_raw_fun"\<rrangle>);

         (0..\<llangle>word64_of_nat (raw_pmem_region_size pr)\<rrangle>).into_iter().map( |i| {
           load_tagged_physical_address (\<llangle>raw_pmem_region_base pr + i\<rrangle>)
         }).collect()
       \<rbrakk>\<close>

definition reference_raw_fun :: \<open>8 word list \<Rightarrow> ('s, (raw_pref, 8 word list) gref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>reference_raw_fun bs \<equiv> FunctionBody \<lbrakk>
     trace!(l\<llangle>"Raw_Tagged_Physical_Memory.reference_raw_fun"\<rrangle>);

     panic!("Memory allocation unsupported for physical memory")
   \<rbrakk>\<close>

definition gref_can_store :: \<open>(raw_pref, 8 word list) gref \<Rightarrow> 8 word list set\<close>
  where \<open>gref_can_store r \<equiv> { bs. (length bs = raw_pmem_region_size (Global_Store.address r)) }\<close>

definition new_gref_can_store :: \<open>8 word list set\<close> where \<open>new_gref_can_store \<equiv> {}\<close>

definition can_alloc_reference :: \<open>'s assert\<close> where \<open>can_alloc_reference \<equiv> {}\<close>
ucincl_auto can_alloc_reference

lemma [ucincl_intros]:
  shows \<open>ucincl (function_contract_pre (
            reference_defs.update_raw_contract points_to_raw' gref_can_store a b c))\<close>
    and \<open>ucincl (function_contract_post (
            reference_defs.update_raw_contract points_to_raw' gref_can_store a b c) r)\<close>
    and \<open>ucincl (function_contract_abort (
            reference_defs.update_raw_contract points_to_raw' gref_can_store a b c) ab)\<close>
    and \<open>ucincl (function_contract_pre (
            reference_defs.dereference_raw_contract points_to_raw' x y z))\<close>
    and \<open>ucincl (function_contract_post (
            reference_defs.dereference_raw_contract points_to_raw' x y z) r')\<close>
    and \<open>ucincl (function_contract_abort (
            reference_defs.dereference_raw_contract points_to_raw' x y z) ab)\<close>
    and \<open>ucincl (function_contract_pre (
            reference_defs.reference_raw_contract points_to_raw' gref_can_store new_gref_can_store can_alloc_reference g))\<close>
    and \<open>ucincl (function_contract_post (
            reference_defs.reference_raw_contract points_to_raw' gref_can_store new_gref_can_store can_alloc_reference g) r'')\<close>
    and \<open>ucincl (function_contract_abort (
            reference_defs.reference_raw_contract points_to_raw' gref_can_store new_gref_can_store can_alloc_reference g) ab)\<close>
  by (auto intro!: ucincl_intros simp: reference_defs.update_raw_contract_def
    reference_defs.reference_raw_contract_def
    reference_defs.dereference_raw_contract_def reference_defs.points_to_raw_def)

lemma update_raw_fun_spec:
  notes mset_upt [simp del]
    wp_cong[crush_cong del]
    wp_cong'[crush_cong del]
  shows \<open>\<Gamma> ; update_raw_fun r g \<Turnstile>\<^sub>F reference_defs.update_raw_contract points_to_raw' gref_can_store r g0 g\<close>
proof -
  let ?pr = \<open>Global_Store.address r\<close>
  let ?base = \<open>raw_pmem_region_base ?pr\<close>
  let ?n = \<open>raw_pmem_region_size ?pr\<close>
  show ?thesis
  apply (crush_boot f: update_raw_fun_def contract: reference_defs.update_raw_contract_def)
  apply (crush_base simp add: for_loop_def range_new_def for_loop_core_def
    reference_defs.points_to_raw_def points_to_raw'_def Let_def is_valid_raw_pmem_region_nat_word_conv)
   apply (rule_tac INV=\<open>\<lambda>ls i.
      \<star>\<star>{# points_to_tagged_phys_byte (?base + (word_of_nat idx)) \<top> tag (g!idx) \<Colon> idx \<leftarrow> [0..<i] #} \<star>
      \<star>\<star>{# points_to_tagged_phys_byte (?base + (word_of_nat idx)) \<top> tag (g0!idx) \<Colon> idx \<leftarrow> [i..<?n] #}
  \<close> and \<tau>=\<open>\<lambda>_. {}\<close> in wp_raw_for_loop_framedI')
  apply (crush_base simp add: gref_can_store_def points_to_tagged_phys_bytes_def
    specs add: store_physical_address_spec
    contracts add: store_tagged_physical_address_contract_def)
  apply (aentails_float_multi_assms', rule_tac i=0 in aentails_multi_mapped_pick,
    fastcrush_base simp add: is_valid_raw_pmem_region_nat_word_conv')
  done
qed

lemma dereference_raw_fun_spec:
  notes mset_upt [simp del]
    reference_defs.points_to_raw_def[simp add]
    and wp_cong[crush_cong del]
    and wp_cong'[crush_cong del]
  shows \<open>\<Gamma> ; dereference_raw_fun r \<Turnstile>\<^sub>F reference_defs.dereference_raw_contract points_to_raw' r sh g\<close>
proof -
  let ?pr = \<open>Global_Store.address r\<close>
  let ?base = \<open>raw_pmem_region_base ?pr\<close>
  let ?n = \<open>raw_pmem_region_size ?pr\<close>
  show ?thesis
  apply (crush_boot f: dereference_raw_fun_def contract: reference_defs.dereference_raw_contract_def)
  apply (crush_base simp add: Rust_Iterator.map_def collect_def reference_defs.points_to_raw_def
    points_to_raw'_def Let_def)
  apply (ucincl_discharge\<open>rule_tac \<tau>=\<open>\<lambda>_. {}\<close> and INV=\<open>\<lambda>i ls.
     \<langle>ls = List.take i g\<rangle> \<star> (points_to_tagged_phys_bytes (raw_pmem_region_base (gref_address r)) sh tag g)
  \<close> in wp_gather_framedI'\<close>)
  apply (fastcrush_base simp add: iterator_ethunks_def iterator_thunks_def make_iterator_from_list_def
    is_valid_raw_pmem_region_nat_word_conv specs add: load_physical_address_spec
    contracts add: load_tagged_physical_address_contract_def)
  apply (fastcrush_base simp prems add: points_to_tagged_phys_bytes_def)
  apply (aentails_float_multi_assms', rule_tac i=i in aentails_multi_mapped_pick_0L, simp,
    fastcrush_base simp add: take_Suc_conv_app_nth simp concls add: points_to_tagged_phys_bytes_def)
  apply (simp add: aentails_def asepconj_comm asepconj_multi_mapped_pick)
  done
qed

lemma reference_raw_fun_spec:
  shows \<open>\<And>\<Gamma> g. \<Gamma> ; reference_raw_fun
                g \<Turnstile>\<^sub>F reference_defs.reference_raw_contract points_to_raw' gref_can_store new_gref_can_store
                        can_alloc_reference g\<close>
  \<comment>\<open>Trivial, since \<^verbatim>\<open>can_alloc_reference = {}\<close>.\<close>
  apply (crush_boot f: reference_raw_fun_def contract: reference_defs.reference_raw_contract_def)
  apply (fastcrush_base simp add: can_alloc_reference_def)
  done

lemma is_sat_splitD[is_sat_destruct]:
  shows \<open>is_sat (\<phi> \<star> \<psi>) \<Longrightarrow> (is_sat \<phi> \<and> is_sat \<psi>)\<close>
  by is_sat_destruct

lemma points_to_tagged_bytes_join:
  shows \<open>\<And>r sh1 sh2 v1 v2.
       reference_defs.points_to_raw points_to_raw' r sh1 v1 \<star>
       reference_defs.points_to_raw points_to_raw' r sh2 v2
     \<longlongrightarrow> reference_defs.points_to_raw points_to_raw' r (sh1 + sh2) v1 \<star> \<langle>v1 = v2\<rangle>\<close>
  apply (clarsimp simp add: reference_defs.points_to_raw_def points_to_raw'_def Let_def
       points_to_tagged_phys_bytes_def asepconj_simp)
  apply crush_base
  apply (simp flip: asepconj_multi_split_body add: points_to_tagged_phys_byte_combinesplit
    asepconj_multi_split_body asepconj_multi_pure)
  apply fastcrush_base
  apply (intro nth_equalityI; simp)
  apply (simp flip: asepconj_multi_split_body add: points_to_tagged_phys_byte_combinesplit)
  apply is_sat_destruct
  apply (erule_tac x=i in meta_allE)
  apply is_sat_destruct
  done

lemma points_to_tagged_bytes_split:
  notes mset_upt[simp del]
  shows \<open>\<And>sh sh1 sh2 r v.
       sh = sh1 + sh2 \<Longrightarrow>
       sh1 \<sharp> sh2 \<Longrightarrow>
       0 < sh1 \<Longrightarrow>
       0 < sh2 \<Longrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh v \<longlongrightarrow>
         reference_defs.points_to_raw points_to_raw' r sh1 v \<star>
         reference_defs.points_to_raw points_to_raw' r sh2 v\<close>
  by (fastcrush_base simp add: reference_defs.points_to_raw_def points_to_raw'_def
       points_to_tagged_phys_bytes_def seplog drule add: points_to_tagged_phys_byte_split
    simp flip: asepconj_multi_split_body intro add: aentails_multi_list_pointwise)

lemma reference_sublocale:
  shows \<open>reference update_raw_fun dereference_raw_fun
            reference_raw_fun points_to_raw' gref_can_store new_gref_can_store can_alloc_reference\<close>
proof standard
  show \<open>\<And>\<Gamma> r g g0.
       \<Gamma> ; update_raw_fun r g \<Turnstile>\<^sub>F reference_defs.update_raw_contract points_to_raw' gref_can_store r g0 g\<close>
    by (rule update_raw_fun_spec)
next
  show \<open>\<And>\<Gamma> r sh g. \<Gamma> ; dereference_raw_fun r \<Turnstile>\<^sub>F reference_defs.dereference_raw_contract points_to_raw' r sh g\<close>
    by (rule dereference_raw_fun_spec)
next
  show \<open>\<And>\<Gamma> g. \<Gamma> ; reference_raw_fun
                g \<Turnstile>\<^sub>F reference_defs.reference_raw_contract points_to_raw' gref_can_store new_gref_can_store
                        can_alloc_reference g\<close>
    by (rule reference_raw_fun_spec)
next
  show \<open>\<And>r sh g. ucincl (reference_defs.points_to_raw points_to_raw' r sh g)\<close>
    unfolding reference_defs.points_to_raw_def by ucincl_solve
next
  show \<open>ucincl can_alloc_reference\<close>
    unfolding can_alloc_reference_def by ucincl_solve
next
  show \<open>\<And>r sh1 sh2 v1 v2.
       reference_defs.points_to_raw points_to_raw' r sh1 v1 \<star> reference_defs.points_to_raw points_to_raw' r sh2 v2 \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r (sh1 + sh2) v1 \<star> \<langle>v1 = v2\<rangle>\<close>
    by (rule points_to_tagged_bytes_join)
next
  show \<open>\<And>sh sh1 sh2 r v.
       sh = sh1 + sh2 \<Longrightarrow>
       sh1 \<sharp> sh2 \<Longrightarrow>
       0 < sh1 \<Longrightarrow>
       0 < sh2 \<Longrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh v \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh1 v \<star> reference_defs.points_to_raw points_to_raw' r sh2 v\<close>
    by (rule points_to_tagged_bytes_split)
qed

end

end