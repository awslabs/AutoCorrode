(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Raw_Physical_Memory
  imports Shallow_Separation_Logic.Shallow_Separation_Logic
begin

section\<open>Physical memory abstraction\<close>

text\<open>This theory defines an abstraction for access to physical memory.\<close>

subsection\<open>Raw tagged physical memory\<close>

text\<open>This section contains an abstraction for raw physical memory where bytes can additionally
be tagged with an abstract type of tags. We also include \<^verbatim>\<open>memset\<close> operations in the locale to
allow for more efficient implementations than a simple loop over \<^verbatim>\<open>store_physical_address\<close>.\<close>

\<comment>\<open>This should morally be a parameter in the \<^verbatim>\<open>raw_tagged_physical_memory\<close> locale, but that
complicates things by adding a dependency from pmem region validity to the locale.\<close>
definition raw_tagged_physical_memory_bitwidth :: nat where \<open>raw_tagged_physical_memory_bitwidth \<equiv> 48\<close>

locale raw_tagged_physical_memory_defs =
  fixes raw_tagged_physical_memory_types :: \<open>'s::{sepalg} \<Rightarrow> 'tag \<Rightarrow> 'abort \<Rightarrow> 'i \<Rightarrow> 'o \<Rightarrow> unit\<close>
    and memset_tagged_phys :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
    and memset_tagged_phys_block :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
    and points_to_tagged_phys_byte :: \<open>64 word \<Rightarrow> share \<Rightarrow>  'tag \<Rightarrow> 8 word \<Rightarrow> 's assert\<close>
    and store_tagged_physical_address :: \<open>64 word \<Rightarrow> 8 word \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
    and load_tagged_physical_address :: \<open>64 word \<Rightarrow> ('s, 8 word, 'abort, 'i, 'o) function_body\<close>
    and tag_physical_page :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
begin

named_theorems raw_tagged_physical_memory_defs'

definition is_within_bounds :: \<open>64 word \<Rightarrow> bool\<close> where
  \<open>is_within_bounds addr \<equiv> addr < 2^raw_tagged_physical_memory_bitwidth\<close>

definition memset_tagged_phys_contract where [raw_tagged_physical_memory_defs']:
  \<open>memset_tagged_phys_contract pa l tag b \<equiv>
    let pre = \<langle>l > 0\<rangle> \<star> \<langle>pa \<le> pa+(l-1)\<rangle> \<star> \<langle>is_within_bounds pa\<rangle> \<star>  \<langle>is_within_bounds (pa+(l-1))\<rangle> \<star>
              \<star>\<star>{# (\<Squnion>b0. points_to_tagged_phys_byte a \<top> tag b0) . a \<leftarrow> mset_set { pa .. pa+(l-1) } #} in
    let post = \<lambda>_.  \<star>\<star>{# points_to_tagged_phys_byte a \<top> tag b . a \<leftarrow> mset_set { pa .. pa+(l-1) } #}
    in make_function_contract pre post\<close>

definition load_tagged_physical_address_contract where [raw_tagged_physical_memory_defs']:
  \<open>load_tagged_physical_address_contract pa \<pi> tag b \<equiv>
    let pre = (points_to_tagged_phys_byte pa \<pi> tag b) in
    let post = (\<lambda>r. points_to_tagged_phys_byte pa \<pi> tag b \<star> \<langle>r = b\<rangle>) in
      make_function_contract pre post\<close>

definition store_tagged_physical_address_contract where [raw_tagged_physical_memory_defs']:
  \<open>store_tagged_physical_address_contract pa b tag b0 \<equiv>
    let pre = (points_to_tagged_phys_byte pa \<top> tag b0) in
    let post = (\<lambda>_. points_to_tagged_phys_byte pa \<top> tag b) in
      make_function_contract pre post\<close>

abbreviation taggable_physical_block :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> (64 word \<Rightarrow> 8 word) \<Rightarrow> 's assert\<close> where
  \<open>taggable_physical_block pa n tag f \<equiv> \<star>\<star>{# (\<Squnion>tag'. \<langle>tag' \<noteq> tag\<rangle> \<star> (points_to_tagged_phys_byte a \<top> tag' (f a))) . a \<leftarrow> mset_set (block_range pa n) #}\<close>

abbreviation tagged_physical_block :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> (64 word \<Rightarrow> 8 word) \<Rightarrow> 's assert\<close> where
  \<open>tagged_physical_block pa n tag f \<equiv> \<star>\<star>{# (points_to_tagged_phys_byte a \<top> tag (f a)) . a \<leftarrow> mset_set (block_range pa n) #}\<close>

abbreviation memset_tagged_block_pre :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> 's assert\<close> where
  \<open>memset_tagged_block_pre pa n tag \<equiv> \<star>\<star>{# (\<Squnion>b0. points_to_tagged_phys_byte a \<top> tag b0) . a \<leftarrow> mset_set (block_range pa n) #}\<close>

abbreviation memset_tagged_block_post :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> 8 word \<Rightarrow> 's assert\<close> where
  \<open>memset_tagged_block_post pa n tag b \<equiv> \<star>\<star>{# (points_to_tagged_phys_byte a \<top> tag b) . a \<leftarrow> mset_set (block_range pa n) #}\<close>

lemmas all_physical_memory_defs = raw_tagged_physical_memory_defs'
named_theorems all_raw_tagged_physical_memory_specs

end

locale raw_tagged_physical_memory = raw_tagged_physical_memory_defs raw_tagged_physical_memory_types
  memset_tagged_phys
  memset_tagged_phys_block
  points_to_tagged_phys_byte
  store_tagged_physical_address
  load_tagged_physical_address
  tag_physical_page for
  raw_tagged_physical_memory_types :: \<open>'s::sepalg \<Rightarrow> 'tag \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
  memset_tagged_phys memset_tagged_phys_block points_to_tagged_phys_byte
  store_tagged_physical_address load_tagged_physical_address tag_physical_page +

assumes load_physical_address_spec [all_raw_tagged_physical_memory_specs]:
       \<open>\<Gamma>; load_tagged_physical_address pa \<Turnstile>\<^sub>F load_tagged_physical_address_contract pa \<pi> tag b\<close>

   and store_physical_address_spec [all_raw_tagged_physical_memory_specs]:
        \<open>\<Gamma>; store_tagged_physical_address pa b \<Turnstile>\<^sub>F store_tagged_physical_address_contract pa b tag b0\<close>

   \<comment>\<open>TODO! this should be stronger and use taggable in the precondition?\<close>
   and tag_physical_page_spec [all_raw_tagged_physical_memory_specs]: \<open>
       n \<le> raw_tagged_physical_memory_bitwidth
       \<Longrightarrow> is_within_bounds pa
       \<Longrightarrow> is_aligned pa n
       \<Longrightarrow> \<Gamma>; tag_physical_page pa n tag \<Turnstile>\<^sub>F
       make_function_contract (taggable_physical_block pa n tag f) (\<lambda>_. tagged_physical_block pa n tag f)\<close>

   and memset_phys_spec [all_raw_tagged_physical_memory_specs]:
     \<open>\<Gamma>; memset_tagged_phys pa l b \<Turnstile>\<^sub>F memset_tagged_phys_contract pa l tag b\<close>

   and memset_phys_block_spec [all_raw_tagged_physical_memory_specs]:
     \<open>n \<le> raw_tagged_physical_memory_bitwidth
      \<Longrightarrow> is_within_bounds pa
      \<Longrightarrow> is_aligned pa n
      \<Longrightarrow> \<Gamma>; memset_tagged_phys_block pa n b \<Turnstile>\<^sub>F make_function_contract (memset_tagged_block_pre pa n tag) (\<lambda>_. memset_tagged_block_post pa n tag b)\<close>

   \<comment>\<open>Byte assertions describe concrete resource and carry no upwards-closure requirement.
   A model may still provide closure when it is inherent in the representation.\<close>

   and points_to_tagged_phys_byte_empty_share[all_raw_tagged_physical_memory_specs]:
     \<open>\<And>pa b tag. points_to_tagged_phys_byte pa 0 tag b = {}\<close>

   and points_to_tagged_phys_byte_split[all_raw_tagged_physical_memory_specs]:
     \<open>\<And>pa sh shA shB b tag. sh = shA + shB \<Longrightarrow> shA \<sharp> shB \<Longrightarrow> 0 < shA \<Longrightarrow> 0 < shB \<Longrightarrow>
        points_to_tagged_phys_byte pa sh tag b \<longlongrightarrow>
           points_to_tagged_phys_byte pa shA tag b \<star> points_to_tagged_phys_byte pa shB tag b\<close>

   and points_to_tagged_phys_byte_combine[all_raw_tagged_physical_memory_specs]:
     \<open>\<And>pa shA shB b b' tag tag'.
           points_to_tagged_phys_byte pa shA tag b \<star> points_to_tagged_phys_byte pa shB tag' b'
               \<longlongrightarrow> points_to_tagged_phys_byte pa (shA + shB) tag b \<star> \<langle>b = b'\<rangle> \<star> \<langle>tag = tag'\<rangle> \<star> \<langle>shA \<sharp> shB\<rangle>\<close>

end
