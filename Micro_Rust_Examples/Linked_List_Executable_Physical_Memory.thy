(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Linked_List_Executable_Physical_Memory
  imports
    Separation_Lenses.SLens
    Byte_Level_Encoding.Niche_Encoding_Option_NonNull
    Micro_Rust_Std_Lib.StdLib_All
    Linked_List
    Micro_Rust_Runtime.Raw_Physical_Memory_Trie_PP
    Micro_Rust_Runtime.Raw_Physical_References
begin

section\<open>Linked List reversal via physical references\<close>

type_synonym phys = \<open>unit tagged_physical_memory\<close>

text\<open>First, we instantiate the linked list reversal with data-free linked list nodes.\<close>

definition gref_iso_prism :: \<open>(NonNullRaw option, (NonNullRaw, byte list) gref option) prism\<close> where
  \<open>gref_iso_prism \<equiv> iso_prism (map_option Global_Store.make_gref) (map_option Global_Store.gref_address)\<close>

lemma gref_iso_prism_is_valid: \<open>is_valid_prism gref_iso_prism\<close>
  by (auto simp add: gref_iso_prism_def iso_prism_valid is_valid_prism_def iso_prism_def
     option.expand option.map_sel)

definition ref_gref_opt_prism :: \<open>(byte list, (NonNullRaw, byte list) gref option) prism\<close>
  where \<open>ref_gref_opt_prism \<equiv> prism_compose niche_encoding_list_prism_le gref_iso_prism\<close>

lemma ref_gref_opt_prism_valid:
  shows \<open>is_valid_prism ref_gref_opt_prism\<close>
  by (simp add: gref_iso_prism_is_valid ref_gref_opt_prism_def prism_compose_valid
    niche_encoding_array_prism_validity)

definition \<open>ref_gref_opt_focus \<equiv> \<integral>\<^sub>p ref_gref_opt_prism\<close>

declare ref_gref_opt_focus_def[symmetric, code_unfold]
declare prism_to_focus.rep_eq[OF ref_gref_opt_prism_valid, folded ref_gref_opt_focus_def, code]

lift_definition (code_dt) caddr_prism_project :: \<open>raw_pmem_region \<Rightarrow> NonNullRaw option\<close>
  is \<open>\<lambda>(pr :: raw_pmem_region).
     if raw_pmem_region_size pr = 8 \<and> raw_pmem_region_base pr \<noteq> 0 then
       Some (raw_pmem_region_base pr)
     else
       None\<close>
  by auto

definition caddr_prism_embed :: \<open>NonNullRaw \<Rightarrow> raw_pmem_region\<close>
  where \<open>caddr_prism_embed nn \<equiv> make_raw_pmem_region (as_raw_ptr nn) 8\<close>

definition caddr_prism :: \<open>(raw_pmem_region, NonNullRaw) prism\<close> where
  \<open>caddr_prism \<equiv> make_prism caddr_prism_embed caddr_prism_project\<close>

lemma caddr_prism_valid: \<open>is_valid_prism caddr_prism\<close>
  apply (auto simp add: is_valid_prism_def caddr_prism_def caddr_prism_embed_def caddr_prism_project_def)
  using Rep_NonNullRaw_inverse as_raw_ptr.rep_eq apply force
  apply (metis (mono_tags, lifting) as_raw_ptr.rep_eq mem_Collect_eq type_definition_NonNullRaw
    type_definition_def)
  by (metis (mono_tags, lifting) Abs_NonNullRaw_inverse as_raw_ptr.rep_eq
    mem_Collect_eq raw_pmem_region.collapse)

definition ll_node_raw_unit_isoprism
  :: \<open>((NonNullRaw, byte list) gref option, (NonNullRaw, byte list, unit) ll_node_raw) prism\<close>
  where \<open>ll_node_raw_unit_isoprism \<equiv> iso_prism (make_ll_node_raw ()) ll_node_raw.next\<close>

lemma ll_node_raw_unit_isoprism_valid:
  shows \<open>is_valid_prism ll_node_raw_unit_isoprism\<close>
  unfolding ll_node_raw_unit_isoprism_def apply (intro iso_prism_valid)
  by (auto simp add: ll_node_raw.exhaust) (metis ll_node_raw.exhaust_sel unit.exhaust)

definition ll_prism :: \<open>(byte list, (NonNullRaw, byte list, unit) ll_node_raw) prism\<close> where
  \<open>ll_prism \<equiv> prism_compose ref_gref_opt_prism ll_node_raw_unit_isoprism\<close>

lemma ll_prism_valid: \<open>is_valid_prism ll_prism\<close>
  unfolding ll_prism_def by (auto intro!: prism_compose_valid
    simp add: ref_gref_opt_prism_valid ll_node_raw_unit_isoprism_valid)

definition \<open>ll_focus \<equiv> \<integral>\<^sub>p ll_prism\<close>

\<comment>\<open>The following is necessary to avoid code generation failing for \<^verbatim>\<open>\<integral>\<^sub>p gref_opt_prism\<close>.\<close>
declare ll_focus_def[symmetric, code_unfold]
declare prism_to_focus.rep_eq[OF ll_prism_valid, folded ll_focus_def, code]

print_locale ll_example_basic
global_interpretation ll_basic_pmem: ll_example_basic raw_pmem_trie_memrefs.update_raw_fun
  raw_pmem_trie_memrefs.dereference_raw_fun
  raw_pmem_trie_memrefs.reference_raw_fun
  raw_pmem_trie_memrefs.points_to_raw'
  raw_pmem_trie_memrefs.gref_can_store
  raw_pmem_trie_memrefs.new_gref_can_store
  raw_pmem_trie_memrefs.can_alloc_reference
  \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  caddr_prism ll_focus
  defines
    reverse_unlink = \<open>ll_basic_pmem.reverse_unlink\<close>
  apply standard
  apply (simp add: caddr_prism_valid)
  done

definition physical_memory_read :: \<open>phys \<Rightarrow> 64 word \<Rightarrow> byte\<close>
  where \<open>physical_memory_read s addr \<equiv>
     case physical_memory_lookup s addr of
        Tagged _ _ b \<Rightarrow> b | _ \<Rightarrow> undefined\<close>

definition physical_memory_read_many :: \<open>phys \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> byte list\<close>
  where \<open>physical_memory_read_many s addr n \<equiv>
    List.map (\<lambda>i. physical_memory_read s (addr + (word64_of_nat i))) [0..<n]\<close>

definition physical_memory_write :: \<open>phys \<Rightarrow> 64 word \<Rightarrow> byte \<Rightarrow> phys\<close>
  where \<open>physical_memory_write s addr v \<equiv> projr (physical_memory_memset_block s addr 0 v)\<close>

definition physical_memory_write_many :: \<open>phys \<Rightarrow> 64 word \<Rightarrow> byte list \<Rightarrow> phys\<close>
  where \<open>physical_memory_write_many s addr vs \<equiv>
    List.foldr (\<lambda>(i,b) s. physical_memory_write s (addr + (word64_of_nat i)) b) (List.enumerate 0 vs) s\<close>

context
begin

private definition test_page :: \<open>64 word\<close> where \<open>test_page \<equiv> 0xdeadbeef000\<close>

private definition \<open>read_at s a n \<equiv> physical_memory_read_many s a n\<close>
private definition \<open>write_at s a vs \<equiv> physical_memory_write_many s a vs\<close>

text\<open>Initial memory has test page claimed and zeroed\<close>
private definition \<sigma>\<^sub>0 where \<open>\<sigma>\<^sub>0 \<equiv> physical_memory_tag_all_bytes 0 \<top> ()\<close>
value\<open>\<sigma>\<^sub>0\<close>

private definition map_continuation :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'v, 'r, unit, unit prompt, unit prompt_output) continuation \<Rightarrow> ('b, 'v, 'r, unit, unit prompt, unit prompt_output) continuation\<close>
  where \<open>map_continuation f c \<equiv> case c of
    Abort a \<sigma> \<Rightarrow> Abort a (f \<sigma>)
  | Core_Expression.Success v \<sigma> \<Rightarrow> Core_Expression.Success v (f \<sigma>)
  | Return r s \<Rightarrow> Return r (f s)
  | _ \<Rightarrow> undefined\<close>

private definition run_it where
  \<open>run_it st f \<equiv> map_continuation (\<lambda>s. read_at s test_page 0x48)
                     (deep_evaluate_det yield_handler_det_no_yield (call f) st :: (_, _, unit, unit, unit prompt, unit prompt_output) continuation)\<close>

\<comment>\<open>Little endian word encoding\<close>
abbreviation \<open>enc64le \<equiv> word64_to_byte_list_le\<close>

text\<open>Prepare initial linked list in raw memory\<close>
definition \<open>\<sigma>\<^sub>1 \<equiv> write_at \<sigma>\<^sub>0 test_page (List.concat [
               \<comment>\<open>Linked list nodes are just pointers to other nodes here (no data)\<close>
               enc64le (test_page + 0x08),
               enc64le (test_page + 0x10),
               enc64le (test_page + 0x18),
               enc64le (test_page + 0x20),
               enc64le (test_page + 0x28),
               enc64le (test_page + 0x30),
               enc64le 0, \<comment>\<open>Last node stores null pointer\<close>
               enc64le 0x1234, \<comment>\<open>Scratch word\<close>
               enc64le 0x4321  \<comment>\<open>Scratch word\<close>
           ])\<close>
value\<open>\<sigma>\<^sub>1\<close>

value\<open>read_at \<sigma>\<^sub>1 test_page 0x48\<close>
(* [0x08, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x10, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x18, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x20, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x28, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x30, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
       0,    0,    0,    0,    0,   0, 0, 0,
    0x34, 0x12,    0,    0,    0,   0, 0, 0,
    0x21, 0x43,    0,    0,    0,   0, 0, 0]" *)

private lift_definition (code_dt) test_page_ptr :: \<open>NonNullRaw\<close> is \<open>test_page\<close>
  by (auto simp add: test_page_def)

text\<open>Pointer to head of linked list\<close>
definition ll_head :: \<open>(NonNullRaw, byte list) gref option\<close> where
  \<open>ll_head \<equiv> Some (make_gref test_page_ptr)\<close>
text\<open>Pointer to scratch memory needed by linked list reversal\<close>
private definition tmp0_ref :: \<open>(raw_pmem_region, byte list, (NonNullRaw, byte list) gref option) Global_Store.ref\<close> where
  \<open>tmp0_ref \<equiv> make_focused (make_gref (make_raw_pmem_region (test_page + 0x38) 8)) ref_gref_opt_focus\<close>
private definition tmp1_ref :: \<open>(raw_pmem_region, byte list, (NonNullRaw, byte list) gref option) Global_Store.ref\<close> where
  \<open>tmp1_ref \<equiv> make_focused (make_gref (make_raw_pmem_region (test_page + 0x40) 8)) ref_gref_opt_focus\<close>

\<comment>\<open>\<^verbatim>\<open>
definition reverse_unlink :: \<open>64 word \<Rightarrow> ('caddr, 'gv) gref option
  \<Rightarrow> ('addr, 'gv, ('caddr, 'gv) gref option) Global_Store.ref
  \<Rightarrow> ('addr, 'gv, ('caddr, 'gv) gref option) Global_Store.ref
  \<Rightarrow> ('s, ('caddr, 'gv) gref option \<times> ('caddr, 'gv) gref option) function_body\<close> where
  \<open>reverse_unlink n orig cur_raw last_raw \<equiv> FunctionBody \<lbrakk>
      last_raw = None;
      cur_raw = orig;
      for i in 0..n {
         \<comment>\<open>Akin to casting a raw Rust pointer into a reference\<close>
         let cur = \<llangle>ll_ptr_as_ref\<rrangle>\<^sub>1(*cur_raw);
         let Some(cur_ref) = cur else {
            panic!("Unexpectedly short linked list")
         };
         let next_raw = (*cur_ref).next;
         cur_ref.next = *last_raw;
         last_raw = *cur_raw;
         cur_raw = next_raw;
      };
      let last = *last_raw;
      let cur = *cur_raw;
      \<llangle>(last, cur)\<rrangle> \<comment>\<open>Unfortunately, we don't yet have tuple notation in uRust\<close>
  \<rbrakk>\<close>
\<close>\<close>
value[code] \<open>run_it \<sigma>\<^sub>1 (reverse_unlink 4 ll_head tmp0_ref tmp1_ref)\<close>

(* continuation.Success (Some (make_gref (Abs_NonNullRaw 0xDEADBEEF018)), Some (make_gref (Abs_NonNullRaw 0xDEADBEEF020)))
  [   0,    0,    0,    0,    0,   0, 0, 0,
   0x00, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x08, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x10, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x28, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x30, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
      0,    0,    0,    0,    0,   0, 0, 0,
   0x20, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x18, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0]" *)

end

end
