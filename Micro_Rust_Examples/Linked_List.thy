(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Linked_List
  imports
    Word_Lib.Many_More
    Crush.Crush
    Micro_Rust_Std_Lib.StdLib_All
begin
(*>*)

section\<open>Example: Linked List reversal in uRust\<close>

text\<open>The following is a toy-example of how to reason about recursive structures in uRust.
We study how to implement, specify and prove a linked list reversal in uRust. Ultimately,
one may want to instantiate such implementation at models of references that are backed by
raw memory. Care is therefore taken to stay generic in the reference interface.\<close>

datatype_record ('addr, 'fv, 't) ll_node_raw =
  data   :: 't
  "next" :: \<open>('addr, 'fv) gref option\<close>
micro_rust_record ll_node_raw

locale ll_example_basic = reference reference_types
      for \<comment> \<open>We need reference support\<close>
         reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> +

      \<comment> \<open>In addition to the type of 'global' addresses (think: union of logical heap addresses
          and physical addresses), specify 'local' address type used in linked list nodes\<close>
    fixes caddr_prism :: \<open>('addr, 'caddr) prism\<close>

      \<comment> \<open>We also need a way to view a global value as a linked list node.
          For example, if references are memory-backed, the conversion between linkedd list nodes
          and byte lists would be captured here. This can include things like niche encodings.\<close>
      and ll_focus :: \<open>('gv, ('caddr, 'gv, 't) ll_node_raw) focus\<close>
  assumes caddr_prism_valid: \<open>is_valid_prism caddr_prism\<close>
begin

adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

definition gref_map :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'v) gref \<Rightarrow> ('b, 'v) gref\<close>
  where \<open>gref_map f r \<equiv> make_gref (f (gref_address r))\<close>

abbreviation ll_ptr_as_ref' ::
  \<open>('caddr, 'gv) gref \<Rightarrow> ('addr, 'gv, ('caddr, 'gv, 't) ll_node_raw) Global_Store.ref\<close> where
  \<open>ll_ptr_as_ref' r \<equiv> make_focused (gref_map (prism_embed caddr_prism) r) ll_focus\<close>

abbreviation \<open>ll_ptr_as_ref \<equiv> Option.map_option ll_ptr_as_ref'\<close>

\<comment>\<open>Bounded reversal of linked lists of uRust references\<close>
definition reverse_unlink :: \<open>64 word \<Rightarrow> ('caddr, 'gv) gref option \<Rightarrow>
      ('addr, 'gv, ('caddr, 'gv) gref option) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, ('caddr, 'gv) gref option) Global_Store.ref \<Rightarrow>
      ('s, ('caddr, 'gv) gref option \<times> ('caddr, 'gv) gref option \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
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
      (last, cur)
  \<rbrakk>\<close>

\<comment>\<open>Recursive predicate capturing the abstract content of a linked list of uRust references\<close>
fun ll_points_to :: \<open>'t list         \<comment> \<open>abstracted prefix of linked list\<close>
      \<Rightarrow> ('caddr, 'gv) gref option   \<comment> \<open>concrete linked list\<close>
      \<Rightarrow> ('caddr, 'gv) gref option   \<comment> \<open>remainder of linked list\<close>
      \<Rightarrow> 's assert\<close> where
  \<open>ll_points_to [] x y     = \<langle>x=y\<rangle>\<close>
| \<open>ll_points_to (d # ds) None _ = \<langle>False\<rangle>\<close>
| \<open>ll_points_to (d # ds) (Some ref) remainder =
     (\<Squnion>r g. let typed_ref = ll_ptr_as_ref' ref in
             let next_ref_opt = ll_node_raw.next r in
           typed_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>r
         \<star> \<langle>ll_node_raw.data r = d\<rangle>
         \<star> (ll_points_to ds next_ref_opt remainder))\<close>

lemma ll_points_to_None:
  shows \<open>ll_points_to ds None rem = \<langle>ds = []\<rangle> \<star> \<langle>rem = None\<rangle>\<close>
by (cases ds; clarsimp simp add: asepconj_simp apure_def)

lemma ucincl_ll_points_to [ucincl_intros]:
  shows \<open>ucincl (ll_points_to ds ll rem)\<close>
by (induction ds; cases ll; auto intro: ucincl_intros)

definition reverse_unlink_contract ::
   \<open>64 word
   \<Rightarrow> ('caddr, 'gv) gref option
   \<Rightarrow> ('addr, 'gv, ('caddr, 'gv) gref option) Global_Store.ref
   \<Rightarrow> ('addr, 'gv, ('caddr, 'gv) gref option) Global_Store.ref
   \<Rightarrow> 't list
   \<Rightarrow> ('caddr, 'gv) gref option
   \<Rightarrow> ('s, ('caddr, 'gv) gref option \<times> ('caddr, 'gv) gref option \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>reverse_unlink_contract n ll tmp0 tmp1 ts rem \<equiv>
     let pre = can_alloc_reference
       \<star> (\<Squnion>g v. tmp0 \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<comment>\<open>The temporaries are valid references\<close>
       \<star> (\<Squnion>g v. tmp1 \<mapsto>\<langle>\<top>\<rangle> g\<down>v)
       \<star> ll_points_to ts ll rem \<star> \<langle>unat n = length ts\<rangle> in
     let post = (\<lambda>r. let (a,b,_) = r in
         can_alloc_reference
       \<star> (\<Squnion>g v. tmp0 \<mapsto>\<langle>\<top>\<rangle> g\<down>v) \<comment>\<open>The temporaries are still valid\<close>
       \<star> (\<Squnion>g v. tmp1 \<mapsto>\<langle>\<top>\<rangle> g\<down>v)
       \<star> \<langle>b = rem\<rangle> \<comment>\<open>Tail of initial list\<close>
       \<star> ll_points_to (rev ts) a None \<comment>\<open>Reversed head of initial list\<close>
    ) in  make_function_contract pre post\<close>
ucincl_proof reverse_unlink_contract
  by (auto split!: prod.splits intro: ucincl_intros)

lemma reverse_unlink_spec [crush_specs]:
  shows \<open>\<Gamma>; reverse_unlink n ll tmp0 tmp1 \<Turnstile>\<^sub>F reverse_unlink_contract n ll tmp0 tmp1 ts rem\<close>
  apply (crush_boot f: reverse_unlink_def contract: reverse_unlink_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i.
       (\<Squnion>g_last g_cur v_last v_cur.
           tmp1\<mapsto>\<langle>\<top>\<rangle> g_last\<down>v_last \<star>
           tmp0\<mapsto>\<langle>\<top>\<rangle> g_cur\<down>v_cur \<star>
           ll_points_to (rev (take i ts)) v_last None \<star>
           ll_points_to (drop i ts) v_cur rem
    )\<close> and \<tau>=\<open>\<lambda>_.\<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (fastcrush_base simp add: Many_More.drop_Suc_nth) 
  apply (fastcrush_base split!: option.splits simp add: take_suc_rev')
  done

end

locale ll_example =
    ll_example_basic _ _ _ _ _ _ _ reference_types caddr_prism ll_focus
  + ref_gref_opt: reference_allocatable reference_types _ _ _ _ _ _ _ ref_gref_opt_prism
  for
    \<comment>\<open>We need reference support\<close>
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
    \<comment>\<open>We need to be able to take references to optional raw references.\<close>
    ref_gref_opt_prism :: \<open>('gv, ('caddr, 'gv) gref option) prism\<close> and
    caddr_prism :: \<open>('addr, 'caddr) prism\<close> and
    ll_focus :: \<open>('gv, ('caddr, 'gv, 't) ll_node_raw) focus\<close>
begin

\<comment>\<open>Unfortunately, adhoc overloading is not inherited across locale hierarchies,
so we always need to repeat overloading for new references.\<close>
adhoc_overloading store_reference_const \<rightleftharpoons> ref_gref_opt.new

\<comment>\<open>Bounded reversal of linked lists of uRust references\<close>
definition reverse_unlink' :: \<open>64 word \<Rightarrow> ('caddr, 'gv) gref option
  \<Rightarrow> ('s, ('caddr, 'gv) gref option \<times> ('caddr, 'gv) gref option \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>reverse_unlink' n ll \<equiv> FunctionBody \<lbrakk>
      let mut last_raw = None;
      let mut cur_raw = None;
      reverse_unlink(n, ll, last_raw, cur_raw)
  \<rbrakk>\<close>

definition reverse_unlink'_contract ::
   \<open>64 word
   \<Rightarrow> ('caddr, 'gv) gref option
   \<Rightarrow> 't list
   \<Rightarrow> ('caddr, 'gv) gref option
   \<Rightarrow> ('s, ('caddr, 'gv) gref option \<times> ('caddr, 'gv) gref option \<times> tnil, 'abort) function_contract\<close> where
  \<open>reverse_unlink'_contract n ll ts rem \<equiv>
     let pre = can_alloc_reference \<star> ll_points_to ts ll rem \<star> \<langle>unat n = length ts\<rangle> in
     let post = (\<lambda>r. let (a,b,_) = r in
         can_alloc_reference
       \<star> \<langle>b = rem\<rangle> \<comment>\<open>Tail of initial list\<close>
       \<star> ll_points_to (rev ts) a None \<comment>\<open>Reversed head of initial list\<close>
    ) in  make_function_contract pre post\<close>
ucincl_proof reverse_unlink'_contract
  by (auto split!: prod.splits intro: ucincl_intros)

lemma reverse_unlink'_spec:
  shows \<open>\<Gamma>; reverse_unlink' n ll \<Turnstile>\<^sub>F reverse_unlink'_contract n ll ts rem\<close>
by (crush_boot f:reverse_unlink'_def contract: reverse_unlink'_contract_def) crush_base

(*<*)
end

end
(*>*)