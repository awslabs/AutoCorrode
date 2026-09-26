(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Transfer_Raw_Physical_Memory
  imports Micro_Rust_Interfaces_Core.Raw_Physical_Memory
    Separation_Lenses.SLens
    Separation_Lenses.SLens_Pullback
begin

section\<open>Extending implementing of \<^locale>\<open>raw_tagged_physical_memory\<close> to larger separation algebras\<close>

text\<open>This theory uses the general pull back machinery to show that interpretations of the
\<^locale>\<open>raw_tagged_physical_memory\<close> locale can be extended along separation lenses.\<close>
locale raw_tagged_physical_memory_transfer =
   M: raw_tagged_physical_memory physical_memory_types_lo
  memset_phys_lo memset_phys_block_lo  points_to_tagged_phys_byte_lo store_physical_address_lo load_physical_address_lo
   tag_physical_page_lo + slens l
   for  l :: \<open>('s::sepalg, 't::sepalg) lens\<close> and
        physical_memory_types_lo :: \<open>'t \<Rightarrow> 'tag \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
        memset_phys_lo memset_phys_block_lo points_to_tagged_phys_byte_lo
        store_physical_address_lo load_physical_address_lo tag_physical_page_lo
begin

named_theorems lifted_defs
definition [lifted_defs]: \<open>memset_phys a b c \<equiv> l\<inverse> (memset_phys_lo a b c)\<close>
definition [lifted_defs]: \<open>memset_phys_block x y z \<equiv> l\<inverse> (memset_phys_block_lo x y z)\<close>
\<comment>\<open>A byte accounts exactly for its resource, so every operation in this locale transfers
through the precise pullback.\<close>
definition [lifted_defs]: \<open>points_to_tagged_phys_byte x y z t \<equiv>
  l\<inverse> (points_to_tagged_phys_byte_lo x y z t)\<close>
definition [lifted_defs]: \<open>store_physical_address x y \<equiv> l\<inverse> (store_physical_address_lo x y)\<close>
definition [lifted_defs]: \<open>load_physical_address x \<equiv> l\<inverse> (load_physical_address_lo x)\<close>
definition [lifted_defs]: \<open>tag_physical_page x y tag \<equiv> l\<inverse> (tag_physical_page_lo x y tag)\<close>

interpretation Defs: raw_tagged_physical_memory_defs \<open>\<lambda>(_::'s) (_::'tag) (_::'abort) (_ :: 'i prompt) (_::'o prompt_output). ()\<close>
  memset_phys memset_phys_block points_to_tagged_phys_byte
  store_physical_address load_physical_address tag_physical_page .

lemma raw_tagged_physical_memory_contracts_no_abort:
  shows \<open>\<And>a b c d. function_contract_abort (M.memset_tagged_phys_contract a b c d) = \<bottom>\<close>
    and \<open>\<And>a b c d. function_contract_abort (M.load_tagged_physical_address_contract a b c d) = \<bottom>\<close>
    and \<open>\<And>a b c d. function_contract_abort (M.store_tagged_physical_address_contract a b c d) = \<bottom>\<close>
  by (simp add: M.all_physical_memory_defs)+

text\<open>Precise pullbacks commute with the exact spatial constructions used by these contracts,
including iterated separating conjunction over address ranges.\<close>
lemma raw_tagged_physical_memory_transfer_def_simps:
  shows \<open>\<And>a b c d. Defs.memset_tagged_phys_contract a b c d =
      l\<inverse> (M.memset_tagged_phys_contract a b c d)\<close>
    and \<open>\<And>a b c d. Defs.load_tagged_physical_address_contract a b c d =
      l\<inverse> (M.load_tagged_physical_address_contract a b c d)\<close>
    and \<open>\<And>a b c d. Defs.store_tagged_physical_address_contract a b c d =
      l\<inverse> (M.store_tagged_physical_address_contract a b c d)\<close>
  \<comment>\<open>\<^verbatim>\<open>multiset.map_comp\<close> and \<^verbatim>\<open>comp_def\<close> fuse the composed pullback left by
  \<^verbatim>\<open>pull_back_asepconj_multi\<close> into the mapped body used by these definitions.\<close>
  by (clarsimp simp add: lifted_defs slens_pull_back_precise_simps
    raw_tagged_physical_memory_defs.all_physical_memory_defs
    raw_tagged_physical_memory_contracts_no_abort bot_fun_def
    multiset.map_comp comp_def)+

lemma memset_phys_lifted:
  shows \<open>\<Gamma>; memset_phys pa sz b \<Turnstile>\<^sub>F Defs.memset_tagged_phys_contract pa sz tag b\<close>
  unfolding memset_phys_def
  by (subst raw_tagged_physical_memory_transfer_def_simps(1))
     (auto simp add: raw_tagged_physical_memory_contracts_no_abort
       intro!: pull_back_spec_universal_precise M.memset_phys_spec)

text\<open>Byte-level obligations transfer because precise pullback preserves \<^term>\<open>(\<star>)\<close> and
\<^term>\<open>\<langle>P\<rangle>\<close>.\<close>
lemma points_to_tagged_phys_byte_combine_lifted:
  shows \<open>points_to_tagged_phys_byte pa shA tag b \<star> points_to_tagged_phys_byte pa shB tag' b'
    \<longlongrightarrow> points_to_tagged_phys_byte pa (shA + shB) tag b \<star>
      \<langle>b = b'\<rangle> \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle>\<close>
proof -
  have \<open>l\<inverse> (points_to_tagged_phys_byte_lo pa shA tag b \<star>
        points_to_tagged_phys_byte_lo pa shB tag' b')
      \<longlongrightarrow> l\<inverse> (points_to_tagged_phys_byte_lo pa (shA + shB) tag b \<star>
        \<langle>b = b'\<rangle> \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle>)\<close>
    by (intro pull_back_aentailsI M.points_to_tagged_phys_byte_combine)
  then show ?thesis
    by (simp only: lifted_defs pull_back_asepconj pull_back_assertion_apure_precise)
qed

lemma points_to_tagged_phys_byte_split_lifted:
  assumes \<open>sh = shA + shB\<close>
      and \<open>shA \<sharp> shB\<close>
      and \<open>0 < shA\<close>
      and \<open>0 < shB\<close>
    shows \<open>points_to_tagged_phys_byte pa sh tag b \<longlongrightarrow>
      points_to_tagged_phys_byte pa shA tag b \<star> points_to_tagged_phys_byte pa shB tag b\<close>
proof -
  from assms have \<open>points_to_tagged_phys_byte_lo pa sh tag b \<longlongrightarrow>
      points_to_tagged_phys_byte_lo pa shA tag b \<star> points_to_tagged_phys_byte_lo pa shB tag b\<close>
    by (rule M.points_to_tagged_phys_byte_split)
  then show ?thesis
    by (simp only: lifted_defs pull_back_asepconj[symmetric] pull_back_aentails)
qed

lemma points_to_tagged_phys_byte_empty_share_lifted:
  shows \<open>points_to_tagged_phys_byte pa 0 tag b = {}\<close>
  by (simp add: lifted_defs M.points_to_tagged_phys_byte_empty_share
    pull_back_assertion_false)

text\<open>The partially applied byte under \<^term>\<open>range\<close> needs a dedicated pullback equation.\<close>
lemma pull_back_byte_range:
  shows \<open>\<Union> (range (points_to_tagged_phys_byte pa sh tag)) =
      l\<inverse> (\<Union> (range (points_to_tagged_phys_byte_lo pa sh tag)))\<close>
  by (auto simp add: lifted_defs pull_back_assertion_def)

lemma raw_tagged_physical_memory_block_contract_transfer:
  shows \<open>make_function_contract (Defs.memset_tagged_block_pre pa n tag)
        (\<lambda>_. Defs.memset_tagged_block_post pa n tag b) =
      l\<inverse> (make_function_contract (M.memset_tagged_block_pre pa n tag)
        (\<lambda>_. M.memset_tagged_block_post pa n tag b))\<close>
    and \<open>make_function_contract (Defs.taggable_physical_block pa n tag f)
        (\<lambda>_. Defs.tagged_physical_block pa n tag f) =
      l\<inverse> (make_function_contract (M.taggable_physical_block pa n tag f)
        (\<lambda>_. M.tagged_physical_block pa n tag f))\<close>
  by (clarsimp simp add: lifted_defs pull_back_byte_range slens_pull_back_precise_simps
    multiset.map_comp comp_def bot_fun_def)+

lemma memset_phys_block_lifted:
  assumes \<open>n \<le> raw_tagged_physical_memory_bitwidth\<close>
      and \<open>Defs.is_within_bounds pa\<close>
      and \<open>is_aligned pa n\<close>
    shows \<open>\<Gamma>; memset_phys_block pa n b \<Turnstile>\<^sub>F
      make_function_contract (Defs.memset_tagged_block_pre pa n tag)
        (\<lambda>_. Defs.memset_tagged_block_post pa n tag b)\<close>
  unfolding memset_phys_block_def
  by (subst raw_tagged_physical_memory_block_contract_transfer(1))
     (auto simp add: assms intro!: pull_back_spec_universal_precise M.memset_phys_block_spec)

lemma tag_physical_page_lifted:
  assumes \<open>n \<le> raw_tagged_physical_memory_bitwidth\<close>
      and \<open>Defs.is_within_bounds pa\<close>
      and \<open>is_aligned pa n\<close>
    shows \<open>\<Gamma>; tag_physical_page pa n tag \<Turnstile>\<^sub>F
      make_function_contract (Defs.taggable_physical_block pa n tag f)
        (\<lambda>_. Defs.tagged_physical_block pa n tag f)\<close>
  unfolding tag_physical_page_def
  by (subst raw_tagged_physical_memory_block_contract_transfer(2))
     (auto simp add: assms intro!: pull_back_spec_universal_precise M.tag_physical_page_spec)

lemma raw_tagged_physical_memory_lifted:
  shows \<open>raw_tagged_physical_memory memset_phys memset_phys_block
    points_to_tagged_phys_byte store_physical_address
    load_physical_address tag_physical_page\<close>
using M.all_raw_tagged_physical_memory_specs
  apply -
  apply (standard; (simp add: memset_phys_lifted points_to_tagged_phys_byte_combine_lifted
    points_to_tagged_phys_byte_split_lifted points_to_tagged_phys_byte_empty_share_lifted
    memset_phys_block_lifted tag_physical_page_lifted)?)
  \<comment>\<open>The remaining load and store contracts contain no iterated conjunction and transport
  directly.\<close>
  apply (clarsimp simp add: raw_tagged_physical_memory_transfer_def_simps
    raw_tagged_physical_memory_contracts_no_abort lifted_defs pull_back_spec_universal_precise)+
  done

end

end
