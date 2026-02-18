(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Linked_List_Executable_Hybrid
  imports
    Byte_Level_Encoding.Niche_Encoding_Option_NonNull
    Micro_Rust_Std_Lib.StdLib_All
    Linked_List
    Micro_Rust_Runtime.Raw_Physical_Memory_Trie_PP
    Micro_Rust_Runtime.Hybrid_References
begin

section\<open>Linked List reversal via hybrid heap+physical references\<close>

text\<open>This theory develops a 'hybrid' instantiation of the reference context in which the linked
list reversal example from \<^verbatim>\<open>Linked_List.thy\<close> can be run: On the one hand, we use the uRust heap
for the allocation of mutable local variables. On the other hand, we use physical memory backed
references for the pointers of the linked list itself.

This example shows how to combine different reference types in a single example. In particular, it
demonstrates how one can gradually move from abstract heap references to concrete physical references.\<close>

subsection\<open>Concrete address type\<close>

text\<open>The concrete address type stored in the linked list is \<^verbatim>\<open>NonNull\<close>:\<close>

type_synonym caddr = NonNullRaw

subsection\<open>Abstract address type\<close>

text\<open>The abstract address type is the disjoint union of the abstract address types for the
heap-based and the memory-based reference implementations:\<close>

type_synonym addr = \<open>nat + raw_pmem_region\<close>

text\<open>The prism from the abstract to the concrete address type is essentially constructed
as in \<^file>\<open>Linked_List_Executable_Physical_Memory.thy\<close>:\<close>

lift_definition (code_dt) caddr_prism_project' :: \<open>raw_pmem_region \<Rightarrow> NonNullRaw option\<close>
  is \<open>\<lambda>(pr :: raw_pmem_region).
     if raw_pmem_region_size pr = 8 \<and> raw_pmem_region_base pr \<noteq> 0 then
       Some (raw_pmem_region_base pr)
     else
       None\<close>
  by auto

definition caddr_prism_embed' :: \<open>NonNullRaw \<Rightarrow> raw_pmem_region\<close>
  where \<open>caddr_prism_embed' nn \<equiv> make_raw_pmem_region (as_raw_ptr nn) 8\<close>

definition caddr_prism' :: \<open>(raw_pmem_region, NonNullRaw) prism\<close> where
  \<open>caddr_prism' \<equiv> make_prism caddr_prism_embed' caddr_prism_project'\<close>

lemma caddr_prism_valid': \<open>is_valid_prism caddr_prism'\<close>
  apply (auto simp add: is_valid_prism_def caddr_prism'_def caddr_prism_embed'_def
    caddr_prism_project'_def)
  using Rep_NonNullRaw_inverse as_raw_ptr.rep_eq apply force
  apply (metis (mono_tags, lifting) as_raw_ptr.rep_eq mem_Collect_eq type_definition_NonNullRaw
    type_definition_def)
  by (metis (mono_tags, lifting) Abs_NonNullRaw_inverse as_raw_ptr.rep_eq
    mem_Collect_eq raw_pmem_region.collapse)

definition addr_raw_pmem_region_prism :: \<open>(addr, raw_pmem_region) prism\<close> where
  \<open>addr_raw_pmem_region_prism \<equiv> make_prism Inr (case_sum (\<lambda>_. None) Some)\<close>

lemma addr_raw_pmem_region_prism_valid: \<open>is_valid_prism addr_raw_pmem_region_prism\<close>
  unfolding addr_raw_pmem_region_prism_def is_valid_prism_def by (auto split!: sum.splits)

definition caddr_prism :: \<open>(addr, caddr) prism\<close> where
  \<open>caddr_prism \<equiv> prism_compose addr_raw_pmem_region_prism caddr_prism'\<close>

lemma caddr_prism_valid: \<open>is_valid_prism caddr_prism\<close>
  by (simp add: addr_raw_pmem_region_prism_valid caddr_prism_def caddr_prism_valid' prism_compose_valid)

subsection\<open>Global value type\<close>

text\<open>The global value type for the hybrid interpretation is the disjoint union of the global
value type of the heap and the global value type of the physical memory backed references. The
latter is fixed to \<^typ>\<open>byte list\<close> while the former is flexible.

Since we use the heap for mutable locals only, and those have type \<^verbatim>\<open>('caddr, 'gv) gref option\<close>,
we can set the heap's global value type to \<^verbatim>\<open>'caddr option\<close>.\<close>

datatype heap_gv = Heap_Gv (heap_gv: \<open>caddr option\<close>)

instantiation heap_gv :: default
begin
definition \<open>default_heap_gv \<equiv> Heap_Gv None\<close>
instance ..
end

text\<open>The global value type for the hybrid implementation is therefore as follows:\<close>
type_synonym gv = \<open>heap_gv + byte list\<close>

definition heap_gv_caddr_opt_prism :: \<open>(heap_gv, (caddr, gv) gref option) prism\<close> where
  \<open>heap_gv_caddr_opt_prism \<equiv> iso_prism
      ((map_option make_gref) \<circ> heap_gv) (Heap_Gv \<circ> (map_option gref_address))\<close>

lemma heap_gv_caddr_opt_prism_valid: \<open>is_valid_prism heap_gv_caddr_opt_prism\<close>
  unfolding heap_gv_caddr_opt_prism_def by (auto intro!: iso_prism_valid
    simp add: map_option.compositionality map_option_idI)

definition gv_heap_gv_prism  :: \<open>(gv, heap_gv) prism\<close> where
  \<open>gv_heap_gv_prism \<equiv> make_prism Inl (case_sum Some (\<lambda>_. None))\<close>

lemma gv_heap_gv_prism_valid: \<open>is_valid_prism gv_heap_gv_prism\<close>
  unfolding gv_heap_gv_prism_def is_valid_prism_def by (auto split!: sum.splits)

definition gv_addr_opt_prism :: \<open>(gv, (caddr, gv) gref option) prism\<close> where
  \<open>gv_addr_opt_prism \<equiv> prism_compose gv_heap_gv_prism heap_gv_caddr_opt_prism\<close>

lemma gv_addr_opt_prism_valid: \<open>is_valid_prism gv_addr_opt_prism\<close>
  by (simp add: gv_addr_opt_prism_def gv_heap_gv_prism_valid heap_gv_caddr_opt_prism_valid
    prism_compose_valid)

\<comment>\<open>The following is necessary to avoid code generation failing for \<^verbatim>\<open>\<integral>\<^sub>p ll_example_gv_prism_ll_node\<close>.\<close>
definition \<open>gv_addr_opt_focus = \<integral>\<^sub>p gv_addr_opt_prism\<close>
declare gv_addr_opt_focus_def[symmetric, code_unfold]
declare prism_to_focus.rep_eq[OF gv_addr_opt_prism_valid,
                              folded gv_addr_opt_focus_def, code]

subsection\<open>Focus from global value type to linked list nodes\<close>

text\<open>The focus from the global value type to the linked list nodes is as in
\<^file>\<open>Linked_List_Executable_Physical_Memory.thy\<close>. We only need to compose it with the
embedding of \<^verbatim>\<open>byte list\<close> into \<^verbatim>\<open>gv\<close>.\<close>

definition gv_byte_list_prism  :: \<open>(gv, byte list) prism\<close> where
  \<open>gv_byte_list_prism \<equiv> make_prism Inr (case_sum (\<lambda>_. None) Some)\<close>

lemma gv_byte_list_prism_valid: \<open>is_valid_prism gv_byte_list_prism\<close>
  unfolding gv_byte_list_prism_def is_valid_prism_def by (auto split!: sum.splits)

definition ll_node_raw_unit_isoprism
  :: \<open>((NonNullRaw, gv) gref option, (NonNullRaw, gv, unit) ll_node_raw) prism\<close>
  where \<open>ll_node_raw_unit_isoprism \<equiv> iso_prism (make_ll_node_raw ()) ll_node_raw.next\<close>

lemma ll_node_raw_unit_isoprism_valid:
  shows \<open>is_valid_prism ll_node_raw_unit_isoprism\<close>
  unfolding ll_node_raw_unit_isoprism_def apply (intro iso_prism_valid)
  by (auto simp add: ll_node_raw.exhaust) (metis ll_node_raw.exhaust_sel unit.exhaust)

definition gref_iso_prism :: \<open>(NonNullRaw option, (NonNullRaw, gv) gref option) prism\<close> where
  \<open>gref_iso_prism \<equiv> iso_prism (map_option Global_Store.make_gref) (map_option Global_Store.gref_address)\<close>

lemma gref_iso_prism_is_valid: \<open>is_valid_prism gref_iso_prism\<close>
  by (auto simp add: gref_iso_prism_def iso_prism_valid is_valid_prism_def iso_prism_def
     option.expand option.map_sel)

definition ref_gref_opt_prism :: \<open>(byte list, (NonNullRaw, gv) gref option) prism\<close>
  where \<open>ref_gref_opt_prism \<equiv> prism_compose niche_encoding_list_prism_le gref_iso_prism\<close>

lemma ref_gref_opt_prism_valid:
  shows \<open>is_valid_prism ref_gref_opt_prism\<close>
  by (simp add: gref_iso_prism_is_valid ref_gref_opt_prism_def prism_compose_valid
    niche_encoding_array_prism_validity)

definition ll_prism' :: \<open>(byte list, (NonNullRaw, gv, unit) ll_node_raw) prism\<close> where
  \<open>ll_prism' \<equiv> prism_compose ref_gref_opt_prism ll_node_raw_unit_isoprism\<close>

lemma ll_prism'_valid: \<open>is_valid_prism ll_prism'\<close>
  by (simp add: ll_node_raw_unit_isoprism_valid ll_prism'_def
    prism_compose_valid ref_gref_opt_prism_valid)

definition ll_prism :: \<open>(gv, (NonNullRaw, gv, unit) ll_node_raw) prism\<close> where
  \<open>ll_prism \<equiv> prism_compose gv_byte_list_prism ll_prism'\<close>

lemma ll_prism_valid: \<open>is_valid_prism ll_prism\<close>
  by (simp add: gv_byte_list_prism_valid ll_prism'_valid ll_prism_def prism_compose_valid)

definition \<open>ll_focus \<equiv> \<integral>\<^sub>p ll_prism\<close>

\<comment>\<open>The following is necessary to avoid code generation failing for \<^verbatim>\<open>\<integral>\<^sub>p gref_opt_prism\<close>.\<close>
declare ll_focus_def[symmetric, code_unfold]
declare prism_to_focus.rep_eq[OF ll_prism_valid, folded ll_focus_def, code]

subsection\<open>Interpretation of Linked List Example context\<close>

global_interpretation ll_example_hybrid: ll_example
   hybrid_update_raw_fun
   hybrid_dereference_raw_fun
   hybrid_reference_raw_fun
   RefPair.points_to_raw'
   RefPair.gref_can_store
   RefPair.new_gref_can_store
   RefPair.can_alloc_reference
   \<open>\<lambda>_ _ (_ :: heap_gv + byte list) (_ :: unit) (_::unit prompt) (_::unit prompt_output). ()\<close>
   gv_addr_opt_prism caddr_prism ll_focus
  rewrites \<open>reference_defs.dereference_fun hybrid_dereference_raw_fun = hybrid_dereference_fun\<close>
    and \<open>reference_defs.update_fun hybrid_update_raw_fun hybrid_dereference_raw_fun = hybrid_update_fun\<close>
    and \<open>reference_defs.reference_fun hybrid_reference_raw_fun = hybrid_reference_fun\<close>
  defines
    reverse_unlink = \<open>ll_example_hybrid.reverse_unlink\<close>
    and reverse_unlink' = \<open>ll_example_hybrid.reverse_unlink'\<close>
    and ref_gref_opt_new = \<open>ll_example_hybrid.ref_gref_opt.new\<close>
    and ref_gref_opt_focus = \<open>ll_example_hybrid.ref_gref_opt.focus\<close>
  apply (clarsimp simp add: ll_example_def ll_example_basic_def reference_allocatable_def
    reference_allocatable_axioms_def; safe)
  using Hybrid_Refs.reference_axioms apply blast
  using caddr_prism_valid ll_example_basic_axioms.intro apply blast
  using Hybrid_Refs.reference_axioms apply blast
      apply (rule gv_addr_opt_prism_valid)

  apply (clarsimp simp add: Hybrid_Refs.can_create_gref_for_prism_def)
  apply (clarsimp simp add: RefPair.new_gref_can_store_def gv_addr_opt_prism_def
    gv_heap_gv_prism_def prism_compose_def prism_dom_def split!: sum.splits option.splits)
  apply (simp add: hybrid_dereference_fun_def hybrid_update_fun_def hybrid_reference_fun_def)+
  done

subsection\<open>Running an example\<close>

text\<open>The state setup code here combines those from \<^file>\<open>Linked_List_Executable_Heap.thy\<close> and
\<^file>\<open>Linked_List_Executable_Physical_Memory.thy\<close>.\<close>

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

private lift_definition mem_to_alist :: \<open>heap_gv Permissioned_Heap.mem \<Rightarrow> (nat \<times> heap_gv) list\<close>
  is \<open>\<lambda>m. List.map (\<lambda> (k, v, _). (k, v)) (rbt_share_map_entries (memory_rbt m))\<close> .

private definition \<open>read_at s a n \<equiv> physical_memory_read_many s a n\<close>
private definition \<open>write_at s a vs \<equiv> physical_memory_write_many s a vs\<close>

private definition simplify :: \<open>heap_gv Permissioned_Heap.mem \<times> phys \<Rightarrow> _\<close>
  where \<open>simplify \<equiv> (\<lambda>(a,b). (mem_to_alist a, read_at b test_page 0x48))\<close>

private lift_definition empty_heap :: \<open>heap_gv Permissioned_Heap.mem\<close>
  is \<open>make_mem_raw 0 (Some 0)\<close> by (clarsimp simp add: mem_is_valid_def zero_fun_def)

text\<open>Initial memory has test page claimed and zeroed\<close>
private definition \<sigma>\<^sub>0 :: \<open>heap_gv Permissioned_Heap.mem \<times> phys\<close>
  where  \<open>\<sigma>\<^sub>0 \<equiv> (empty_heap, physical_memory_tag_all_bytes 0 \<top> ())\<close>

value[code] \<open>\<sigma>\<^sub>0\<close>

private definition map_continuation :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'v, 'r, unit, unit prompt, unit prompt_output) continuation \<Rightarrow> ('b, 'v, 'r, unit, unit prompt, unit prompt_output) continuation\<close>
  where \<open>map_continuation f c \<equiv> case c of
    Abort a \<sigma> \<Rightarrow> Abort a (f \<sigma>)
  | Core_Expression.Success v \<sigma> \<Rightarrow> Core_Expression.Success v (f \<sigma>)
  | Return r s \<Rightarrow> Return r (f s)
  | _ \<Rightarrow> undefined\<close>

private definition run_it where
  \<open>run_it st f \<equiv> map_continuation snd
                     (deep_evaluate_det yield_handler_det_no_yield (call f) st :: (_, _, unit, unit, unit prompt, unit prompt_output) continuation)\<close>

\<comment>\<open>Little endian word encoding\<close>
abbreviation \<open>enc64le \<equiv> word64_to_byte_list_le\<close>

text\<open>Prepare initial linked list in raw memory\<close>
definition \<open>\<sigma>\<^sub>1 \<equiv> apsnd (\<lambda>\<sigma>. write_at \<sigma> test_page (List.concat [
               \<comment>\<open>Linked list nodes are just pointers to other nodes here (no data)\<close>
               enc64le (test_page + 0x08),
               enc64le (test_page + 0x10),
               enc64le (test_page + 0x18),
               enc64le (test_page + 0x20),
               enc64le (test_page + 0x28),
               enc64le (test_page + 0x30),
               enc64le 0 \<comment>\<open>Last node stores null pointer\<close>
           ])) \<sigma>\<^sub>0\<close>

value\<open>snd \<sigma>\<^sub>1\<close>
(* ([],
    [0x08, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x10, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x18, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x20, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x28, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
    0x30, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
       0,    0,    0,    0,    0,   0, 0, 0,
    0x34, 0x12,    0,    0,    0,   0, 0, 0,
    0x21, 0x43,    0,    0,    0,   0, 0, 0])" *)

private lift_definition (code_dt) test_page_ptr :: \<open>NonNullRaw\<close> is \<open>test_page\<close>
  by (auto simp add: test_page_def)

text\<open>Pointer to head of linked list\<close>
definition ll_head :: \<open>(NonNullRaw, gv) gref option\<close> where
  \<open>ll_head \<equiv> Some (make_gref test_page_ptr)\<close>

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
value[code] \<open>run_it \<sigma>\<^sub>1 (reverse_unlink' 4 ll_head)\<close>

(* continuation.Success
  (Some (make_gref (Abs_NonNullRaw 0xDEADBEEF018)),
   Some (make_gref (Abs_NonNullRaw 0xDEADBEEF020)))
  ([(0, Heap_Gv (Some (Abs_NonNullRaw 0xDEADBEEF020))),
    (1, Heap_Gv (Some (Abs_NonNullRaw 0xDEADBEEF018)))],
   [   0,    0,    0,    0,    0,   0, 0, 0,
   0x00, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x08, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x10, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x28, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
   0x30, 0xF0, 0xEE, 0xDB, 0xEA, 0xD, 0, 0,
      0,    0,    0,    0,    0,   0, 0, 0,
      0,    0,    0,    0,    0,   0, 0, 0,
      0,    0,    0,    0,    0,   0, 0, 0])" *)

(*  *)
end

end
