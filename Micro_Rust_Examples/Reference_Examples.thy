(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Reference_Examples
  imports
    Micro_Rust_Runtime.Runtime_Heap
    Micro_Rust_Runtime.Raw_Physical_References
    Micro_Rust_Runtime.Raw_Physical_Memory_Trie_PP
    Misc.WordAdditional
    Byte_Level_Encoding.Byte_Parser
    Byte_Level_Encoding.Byte_Encoding_Word_Nat
begin

section\<open>References\<close>

text\<open>References in uRust are specified axiomatically through the \<^verbatim>\<open>reference\<close> locale. Typically,
when you need to reason about a uRust program that involves references, you will want to define
and reason about the program in the axiomatic context of the \<^verbatim>\<open>reference\<close> locale
(likely extended with other assumptions). You can then interpret, run and inherit proofs about
the program in any concrete implementation of the \<^verbatim>\<open>reference\<close> locale.\<close>

subsection\<open>Running example\<close>

text\<open>Let's look at a simple example, a function taking two references and swapping the values therein.
We define this function in a dedicated context capturing what is needed to make sense of it -- in this
case, merely the \<^verbatim>\<open>Reference\<close> locale:\<close>

locale SwapRefContext = reference reference_types
  for
    \<comment>\<open>The \<^verbatim>\<open>reference\<close> locale has multiple parameters which in particular determine the types
    it operates on. Here, we merely specify the dummy parameter \<^verbatim>\<open>reference_types\<close> whose purpose
    is to fix all type names without having to spell out all other parameters. You can still see
    the other parameters in the Output window:

    \<^verbatim>\<open>
locale SwapRefContext
  fixes
    update_raw_fun ::
      "('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body"
    and
    dereference_raw_fun ::
      "('addr, 'gv) gref \<Rightarrow> ('s, 'gv, 'abort, 'i prompt, 'o prompt_output) function_body"
    and
    reference_raw_fun ::
      "'gv \<Rightarrow> ('s, ('addr, 'gv) gref, 'abort, 'i prompt, 'o prompt_output) function_body"
    and points_to_raw' :: "('addr, 'gv) gref \<Rightarrow> share \<Rightarrow> 'gv \<Rightarrow> 's set"
    and gref_can_store :: "('addr, 'gv) gref \<Rightarrow> 'gv set"
    and new_gref_can_store :: "'gv set"
    and can_alloc_reference :: "'s set"
    and reference_types :: "'s \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit"
     ...
    \<close>\<close>
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
begin

\<comment>\<open>Map the (a priori uninterpreted) update syntax in uRust to the reference update.
TODO: It should be possible to do this in the reference locale itself -- revisit in Isabelle 2025\<close>
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text\<open>Unpacking this, there are three main abstractions in the \<^verbatim>\<open>reference\<close> locale: First, the underlying
separation algebra, here denoted \<^verbatim>\<open>'s\<close>. Second, the type \<^verbatim>\<open>'addr\<close> of 'untyped' references -- in the context
of memory-based \<^verbatim>\<open>reference\<close> implementations, for example, this could be \<^typ>\<open>64 word\<close>. Third, and perhaps
surprisingly, a notion of 'global value' type, here denoted \<^verbatim>\<open>'gv\<close>: The reference locale assumes that every
untyped reference points to an 'untyped' value of the fixed type \<^verbatim>\<open>'gv\<close>. A 'typed' reference is then a
pair of an untyped reference together with a means to convert between the global value type \<^verbatim>\<open>'gv\<close>
and the desired type of the reference. For example, in memory-based example, \<^verbatim>\<open>'gv\<close> could be byte strings,
and typing would consist of encoding/decoding byte strings as as concrete types.\<close>

text\<open>Before going into further details, here is the example of the \<^verbatim>\<open>swap\<close> function:\<close>

definition swap_ref :: \<open>('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> ('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>swap_ref rA rB \<equiv> FunctionBody \<lbrakk>
     let oldA = *rA;
     let oldB = *rB;
     rA = oldB;
     rB = oldA;
  \<rbrakk>\<close>
thm swap_ref_def

end

subsection\<open>Heap-based references\<close>

text\<open>Before we reason about \<^verbatim>\<open>swap_ref\<close>, let's make sure we can actually run it. For that,
we need concrete interpretations of the \<^verbatim>\<open>SwapRefContext\<close> locale, hence the \<^verbatim>\<open>reference\<close>
locale.

This repository comes with two implementations for the \<^verbatim>\<open>Reference\<close> locale: First, an abstract
heap. Here, references are just addresses into a monomorphic heap whose global value type \<^verbatim>\<open>'gv\<close>
is a big disjoint union of all concrete value types we may want to store in it. Second, a reference
implementation based on physical memory: Here, addresses are memory regions and global values are byte streams.\<close>

text\<open>The abstract heap-based implementation of the \<^verbatim>\<open>reference\<close> locale is provided by
\<^file>\<open>../Micro_Rust_Runtime/Runtime_Heap.thy\<close>: At the heart, it provides a polymorphic type \<^typ>\<open>'gv mem\<close> of an
\<^verbatim>\<open>'gv\<close>-valued monomorphic store. Here, let's instantiate it \<^verbatim>\<open>'gv = 64 word\<close> for concreteness.
The global value type needs to provide default values for uninitialized values; to keep things
simple, we use \<^verbatim>\<open>0\<close>; a more complicated example will want a dedicated variant.\<close>

datatype_record heap_ex_gv = heap_ex_gv :: \<open>64 word\<close>
(*type_synonym heap_ex_gv = \<open>64 word\<close> *)
type_synonym heap_ex_ty = \<open>heap_ex_gv mem\<close>

instantiation heap_ex_gv :: default
begin
definition default_heap_ex_gv :: \<open>heap_ex_gv\<close> where \<open>default_heap_ex_gv \<equiv> make_heap_ex_gv 0\<close>
instance ..
end

print_locale SwapRefContext
global_interpretation SwapRefContext_Heap: SwapRefContext
  urust_heap_update_raw_fun
  urust_heap_dereference_raw_fun
  urust_heap_reference_raw_fun
  urust_heap_points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  urust_heap_can_alloc_reference
  (* reference_types :: "'s \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit" *)
  \<open>\<lambda>(_ :: heap_ex_gv mem) (_ :: nat) (_ :: heap_ex_gv) (_ :: unit) (_ :: unit prompt) (_ :: unit prompt_output). ()\<close>
  \<comment>\<open>Normally, \<^verbatim>\<open>global_interpretation\<close> offers the \<^verbatim>\<open>defines\<close> clause as a convenient way to
  establish code equations for definitions exported from the locale that is being interpreted.
  Unfortunately, there appears to be a hiccup regarding the polymorphism of the abstract heap
  here, and the following is needed:\<close>
  rewrites \<open>reference_defs.dereference_fun urust_heap_dereference_raw_fun = urust_heap_dereference_fun\<close>
    and \<open>reference_defs.update_fun urust_heap_update_raw_fun urust_heap_dereference_raw_fun = urust_heap_update_fun\<close>
  defines heap_ex_swap_ref = \<open>SwapRefContext_Heap.swap_ref\<close>
  by (auto simp add: Global_Perm_Store.reference_sublocale SwapRefContext_def
     urust_heap_dereference_fun_def urust_heap_update_fun_def urust_heap_reference_fun_def)

text\<open>We are now in a position to (code-)evaluate the \<^verbatim>\<open>swap_ref\<close> function, as witnessed by the
ability to code-extract it:\<close>
term heap_ex_swap_ref
export_code heap_ex_swap_ref in OCaml

text\<open>Let's start with an empty heap and two invalid references, and see what happens.

First, the empty heap:\<close>
definition h\<^sub>0 :: heap_ex_ty where \<open>h\<^sub>0 \<equiv> mem_from_alist []\<close>
value[code] h\<^sub>0

text\<open>Next, we need two typed references in \<^typ>\<open>(nat, heap_ex_gv, 'a) Global_Store.ref\<close>, which is
essentially a combination of a raw reference in \<^typ>\<open>(nat, heap_ex_gv) gref\<close>, and a 'focus'. In general,
a focus is a means to go from the fixed global value type to varying 'local' value types, but in our
case, we just use the global value type directly, and hence resort to the identity focus.\<close>

definition ref0 :: \<open>(nat, heap_ex_gv, heap_ex_gv) Global_Store.ref\<close> where
  \<open>ref0 \<equiv> make_focused (make_gref 0) focus_id\<close>

definition ref1 :: \<open>(nat, heap_ex_gv, heap_ex_gv) Global_Store.ref\<close> where
  \<open>ref1 \<equiv> make_focused (make_gref 1) focus_id\<close>

text\<open>Let's try to run the function. This functions are essentially uRust \<^verbatim>\<open>expression\<close>s, we
need to explicitly evaluate them to get a pure function:\<close>
definition eval' :: \<open>('s, 'a, unit, unit prompt, unit prompt_output) function_body
  \<Rightarrow> 's \<Rightarrow> ('s, 'a, 'a, unit, unit prompt, unit prompt_output) continuation\<close> where
  \<open>eval' f \<sigma> \<equiv> (deep_evaluate_det yield_handler_det_no_yield (call f) \<sigma>)\<close>
value[code] \<open>eval' (heap_ex_swap_ref ref0 ref1) h\<^sub>0\<close>
(* "Abort DanglingPointer (Abs_mem (make_mem_raw (RmShareMap (abs_rbt_ext (RBT rbt.Empty))) (Some 0)))"
  :: "(64 word mem, unit, unit, unit, unit prompt, unit prompt_output) continuation" *)

text\<open>This didn't work since \<^verbatim>\<open>ref0\<close> and \<^verbatim>\<open>ref1\<close> were dangling, so let's actually allocate
some slots at addresses \<^verbatim>\<open>0\<close> and \<^verbatim>\<open>1\<close>:\<close>

definition h\<^sub>1 :: heap_ex_ty where \<open>h\<^sub>1 \<equiv> mem_from_alist [(0, make_heap_ex_gv 12), (1, make_heap_ex_gv 42)]\<close>
value h\<^sub>1
(* "Abs_mem
  (make_mem_raw
    (RmShareMap
      (abs_rbt_ext
        (RBT (Branch color.B
               (Branch color.R rbt.Empty 0
                 (make_heap_ex_gv 0xC, Abs_nonempty_share (Abs_share (Tree_Shares.tree.Leaf True))) rbt.Empty)
               1 (make_heap_ex_gv 0x2A, Abs_nonempty_share (Abs_share (Tree_Shares.tree.Leaf True))) rbt.Empty))))
    (Some 2))"
  :: "heap_ex_gv mem" *)
(* TODO: not very pallettable... write a pretty-printer for RBT *)
value \<open>mem_to_alist h\<^sub>1\<close> (* [(0, make_heap_ex_gv 0xC), (1, make_heap_ex_gv 0x2A)] *)

text\<open>Let's try again, with another convenience evaluator which picks out the final state:\<close>

definition eval :: \<open>('s, 'a, unit, unit prompt, unit prompt_output) function_body
  \<Rightarrow> 's \<Rightarrow> 'a \<times> 's\<close> where
  \<open>eval f \<sigma> \<equiv>
    let cont = (deep_evaluate_det yield_handler_det_no_yield (call f) \<sigma>)
       :: ('s, 'a, 'a, unit, unit prompt, unit prompt_output) continuation
    in
    case cont of
      continuation.Success v \<sigma>' \<Rightarrow> (v, \<sigma>')
    | _ \<Rightarrow> undefined
  \<close>
definition h\<^sub>2 where \<open>h\<^sub>2 \<equiv> snd (eval (heap_ex_swap_ref ref0 ref1) h\<^sub>1)\<close>
value[code] \<open>mem_to_alist h\<^sub>2\<close> (* "[(0, make_heap_ex_gv 0x2A), (1, make_heap_ex_gv 0xC)]" *)

subsection\<open>Memory-based feferences\<close>

text\<open>As demonstrated in \<^file>\<open>../Micro_Rust_Runtime/Raw_Physical_References.thy\<close>, our physical memory
implementation gives rise to another interpretation of the \<^verbatim>\<open>reference\<close> locale: In this interpretation,
references are address regions, global values are byte strings, and foci are essentially pairs
of decoders/encoders from byte strings to concrete 'local' value types.

We demonstrate how all this work in the \<^verbatim>\<open>swap_ref\<close> example. First, we need another interpretation
of the \<^locale>\<open>SwapRefContext\<close> locale. This is essentially the \<^verbatim>\<open>reference\<close> implementation from
\<^file>\<open>../Micro_Rust_Runtime/Raw_Physical_References.thy\<close>:\<close>

type_synonym pmem_ex_gv = \<open>byte list\<close>
type_synonym pmem_ex_ty = \<open>unit tagged_physical_memory\<close>

global_interpretation SwapRefContext_PMem: SwapRefContext
  raw_pmem_trie_update_raw_fun
  raw_pmem_trie_dereference_raw_fun
  raw_pmem_trie_reference_raw_fun
  raw_pmem_trie_memrefs.points_to_raw'
  raw_pmem_trie_memrefs.gref_can_store
  raw_pmem_trie_memrefs.new_gref_can_store
  raw_pmem_trie_memrefs.can_alloc_reference
  (* reference_types :: "'s \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit" *)
  \<open>\<lambda>(_ :: pmem_ex_ty) (_ :: raw_pmem_region) (_ :: byte list) (_ :: unit) (_ :: unit prompt) (_ :: unit prompt_output). ()\<close>
  rewrites \<open>reference_defs.dereference_fun raw_pmem_trie_dereference_raw_fun = raw_pmem_trie_dereference_fun\<close>
    and \<open>reference_defs.update_fun raw_pmem_trie_update_raw_fun raw_pmem_trie_dereference_raw_fun = raw_pmem_trie_update_fun\<close>
  defines pmem_ex_swap_ref = \<open>SwapRefContext_PMem.swap_ref\<close>
  by (simp add: SwapRefContext_def raw_pmem_trie_memrefs.reference_sublocale
    raw_pmem_trie_dereference_fun_def raw_pmem_trie_update_fun_def)+

text\<open>We are now in a position to (code-)evaluate the \<^verbatim>\<open>swap_ref\<close> function, as witnessed by the
ability to code-extract it:\<close>

term pmem_ex_swap_ref
export_code pmem_ex_swap_ref in OCaml

text\<open>As for the heap-based example, we need to setup a concrete memory and two references.

First, we setup the references. As before, they are a combination of a raw address and a 'focus'
relating the global and local value type. While in the abstract-heap example, the focus was trivial,
here we use a focus representing little/big endian decoder/encoders of \<^verbatim>\<open>32 word\<close> as \<^verbatim>\<open>byte list\<close>.
The theory \<^file>\<open>../Byte_Level_Encoding/Byte_Encoding_Word_Nat.thy\<close> provides foci for standard little/big-endian encoding
of words and nats.\<close>
definition pref_le :: \<open>(raw_pmem_region, 8 word list, 32 word) Global_Store.ref\<close>
    where \<open>pref_le \<equiv> make_focused (make_gref (make_raw_pmem_region 0x0000000FF1C8 4))
                                              word32_byte_list_focus_le\<close>

definition pref_be :: \<open>(raw_pmem_region, 8 word list, 32 word) Global_Store.ref\<close>
   where \<open>pref_be \<equiv> make_focused (make_gref (make_raw_pmem_region 0xDEADBEEF0 4))
                                              word32_byte_list_focus_be\<close>

text\<open>Let's see the foci in action by writing two \<^verbatim>\<open>64 word\<close>s into memory through the references:\<close>
definition \<sigma>\<^sub>0 where \<open>\<sigma>\<^sub>0 \<equiv> physical_memory_tag_all_bytes 0 \<top> ()\<close>
value \<sigma>\<^sub>0

definition \<sigma>\<^sub>1 :: pmem_ex_ty where \<open>\<sigma>\<^sub>1 \<equiv> snd (eval (raw_pmem_trie_update_fun pref_le 0x01020304) \<sigma>\<^sub>0)\<close>
value \<open>\<sigma>\<^sub>1\<close>
text\<open>We can see the little-endian encoding in action here:\<close>
(* "MEMORY \<lparr>\<lbrakk>0x0-0xFF1C0\<rbrakk>: 0, \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 2, 1, 0, 0, 0, 0], \<lbrakk>0xFF1D0-0x1000000000000\<rbrakk>: 0\<rparr>" *)

definition \<sigma>\<^sub>2 :: pmem_ex_ty where \<open>\<sigma>\<^sub>2 \<equiv> snd (eval (raw_pmem_trie_update_fun pref_be 0x0A0B0C0D) \<sigma>\<^sub>1)\<close>
text\<open>Likewise, the big-endian encoding:\<close>
value \<open>\<sigma>\<^sub>2\<close>
(* "MEMORY \<lparr>\<lbrakk>0x0-0xFF1C0\<rbrakk>: 0,
       \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 2, 1, 0, 0, 0, 0],
       \<lbrakk>0xFF1D0-0xDEADBEEF0\<rbrakk>: 0,
       \<lbrakk>0xDEADBEEF0-0xDEADBEF00\<rbrakk>: [0xA, 0xB, 0xC, 0xD, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       \<lbrakk>0xDEADBEF00-0x1000000000000\<rbrakk>: 0\<rparr>" *)

text\<open>Finally, let's run the swap function:\<close>
value \<open>snd (eval (pmem_ex_swap_ref pref_le pref_be) \<sigma>\<^sub>2)\<close>
(* "MEMORY \<lparr>
   \<lbrakk>0x0-0xFF1C0\<rbrakk>: 0,
   \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 0xD, 0xC, 0xB, 0xA, 0, 0, 0, 0],
   \<lbrakk>0xFF1D0-0xDEADBEEF0\<rbrakk>: 0,
   \<lbrakk>0xDEADBEEF0-0xDEADBEF00\<rbrakk>: [1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   \<lbrakk>0xDEADBEF00-0x1000000000000\<rbrakk>: 0\<rparr>"
*)

subsection\<open>Avoiding locales\<close>

text\<open>It is generally useful to define and reason about uRust source code in a generic context
axiomatizing the contextual assumptions. For example, by building on the \<^verbatim>\<open>reference\<close> axioms
alone, you can be sure that the correctness of your code does not depend on specifics of the
\<^verbatim>\<open>reference\<close> implementation.

However, if you want to do a quick evaluation experiment, it is cumbersome to define a locale
first. Here we briefly describe how to directly define and evaluate uRust.\<close>

text\<open>Outside of the \<^verbatim>\<open>reference\<close> locale, the constants for (a) allocating, (b) updating, and
(c) dereferencing references are uninterpreted. If you want to define a 'freestanding' piece
of uRust dealing with references, you therefore need to say ahead of time what the meaning of
those constants should be.

Assuming we want to work with physical memory references again, that would be:\<close>

adhoc_overloading store_update_const \<rightleftharpoons> raw_pmem_trie_update_fun
adhoc_overloading store_dereference_const \<rightleftharpoons> raw_pmem_trie_dereference_fun

text\<open>With this, we can make sense of the \<^verbatim>\<open>swap_ref\<close> function outside of any locale:\<close>

definition swap_ref :: \<open>(raw_pmem_region, byte list, 'v) Global_Store.ref \<Rightarrow> (raw_pmem_region, byte list, 'v) Global_Store.ref
   \<Rightarrow> (unit tagged_physical_memory, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>swap_ref rA rB \<equiv> FunctionBody \<lbrakk>
     let oldA = *rA;
     let oldB = *rB;
     rA = oldB;
     rB = oldA;
  \<rbrakk>\<close>

text\<open>Let's look at the definition:\<close>
declare [[show_variants]]
thm swap_ref_def
(* swap_ref ?rA ?rB \<equiv>
FunctionBody
 (let oldA = bind (\<up>?rA) (call_deep1 raw_pmem_trie_dereference_fun);
  let oldB = bind (\<up>?rB) (call_deep1 raw_pmem_trie_dereference_fun);
   bind2 (call_deep2 raw_pmem_trie_update_fun) (\<up>?rA) (\<up>oldB) ;  bind2 (call_deep2 raw_pmem_trie_update_fun) (\<up>?rB) (\<up>oldA) ; \<up>()  ) *)

text\<open>This looks right!

Let's try to re-evaluate this with the same references and physical memory as above:\<close>

value \<open>snd (eval (swap_ref pref_le pref_be) \<sigma>\<^sub>2)\<close>
(* "MEMORY \<lparr>\<lbrakk>0x0-0xFF1C0\<rbrakk>: 0, \<lbrakk>0xFF1C0-0xFF1D0\<rbrakk>: [0, 0, 0, 0, 0, 0, 0, 0, 0xD, 0xC, 0xB, 0xA, 0, 0, 0, 0], \<lbrakk>0xFF1D0-0xDEADBEEF0\<rbrakk>: 0, \<lbrakk>0xDEADBEEF0-0xDEADBEF00\<rbrakk>: [1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0,
 0, 0, 0, 0, 0], \<lbrakk>0xDEADBEF00-0x1000000000000\<rbrakk>: 0\<rparr>"
  :: "unit tagged_physical_memory"*)

text\<open>To avoid clashes, you may want to undo the adhoc overloading when you're doing with
the expriment:\<close>
no_adhoc_overloading store_update_const \<rightleftharpoons> raw_pmem_trie_update_fun
no_adhoc_overloading store_dereference_const \<rightleftharpoons> raw_pmem_trie_dereference_fun

subsection\<open>Conclusion\<close>

text\<open>This theory has demonstrated how to instantiate generic uRust using references with different
models of references, one backed by an abstract heap and another by physical memory.

For a more involved example along the same lines, see \<^file>\<open>Linked_List.thy\<close>,  \<^file>\<open>Linked_List_Executable_Heap.thy\<close>,
 \<^file>\<open>Linked_List_Executable_Physical_Memory.thy\<close>, \<^file>\<open>Linked_List_Executable_Hybrid.thy\<close>. The first
theory \<^file>\<open>Linked_List.thy\<close> establishes a generic context in which a linked list reversal can be
implemented, and generically reasons about its correctness. The remaining theories instantiates
the context using the abstract heap and/or physical memory. It also constructs a 'hybrid' where
mutable locals are backed by an abstract heap, and otherwise references a memory-based.\<close>

end
