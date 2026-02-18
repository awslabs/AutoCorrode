(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory References
  imports 
    Shallow_Separation_Logic.Assertion_Language 
    Shallow_Separation_Logic.Tree_Shares
    Shallow_Separation_Logic.Triple 
    Shallow_Separation_Logic.Weakest_Precondition
    Shallow_Micro_Rust.Core_Expression
begin
(*>*)

named_theorems reference_axioms

locale reference_defs = 
  fixes reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i \<Rightarrow> 'o \<Rightarrow> unit\<close>

    and update_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
    and dereference_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
    and reference_raw_fun :: \<open>'b \<Rightarrow> ('s, ('a, 'b) gref, 'abort, 'i, 'o) function_body\<close>

    and points_to_raw' :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 's assert\<close> 

    and gref_can_store :: \<open>('a, 'b) gref \<Rightarrow> 'b set\<close>
    and new_gref_can_store :: \<open>'b set\<close>

    and can_alloc_reference :: \<open>'s assert\<close>
begin

named_theorems all_reference_defs'

definition [all_reference_defs']: \<open>points_to_raw \<equiv> points_to_raw'\<close>
notation points_to_raw ("(_) \<mapsto> \<langle>_\<rangle> (_)" [69,0,69]70)

text\<open>Specifications\<close>

definition update_raw_contract :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>update_raw_contract r g0 g \<equiv>
     let pre = \<langle>g \<in> gref_can_store r\<rangle> \<star> points_to_raw r \<top> g0 in
     let post = \<lambda>_. (points_to_raw r \<top> g) in
     make_function_contract pre post\<close>

definition reference_raw_contract :: \<open>'b \<Rightarrow> ('s, ('a, 'b) gref, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>reference_raw_contract g \<equiv>
      let pre = can_alloc_reference \<star> \<langle>g \<in> new_gref_can_store\<rangle> in
     let post = \<lambda>r. points_to_raw r \<top> g \<star> 
                    \<langle>new_gref_can_store \<subseteq> gref_can_store r\<rangle> \<star> can_alloc_reference in
     make_function_contract pre post\<close>

definition dereference_raw_contract 
  :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> ('s, 'b, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>dereference_raw_contract r sh g \<equiv>
     let pre = points_to_raw r sh g in
     let post = \<lambda>g'. (points_to_raw r sh g \<star> \<langle>g=g'\<rangle>) in
     make_function_contract pre post\<close>

text\<open>Lifting the raw reference operations to typed ones using foci:\<close>

definition reference_fun ::
  \<open>('b, 'v) prism \<Rightarrow>
   'v \<Rightarrow>
   ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i, 'o) function_body\<close> where
  [all_reference_defs']: \<open>reference_fun p e \<equiv> FunctionBody \<lbrakk>
       let r = reference_raw_fun (\<llangle>prism_embed p e\<rrangle>);
       \<llangle>make_ref_typed_from_untyped\<rrangle>\<^sub>2(r, \<llangle>prism_to_focus p\<rrangle>)
   \<rbrakk>\<close>

\<comment>\<open>\<^verbatim>\<open>prism_to_focus p\<close> has no (unconditional) code equations. Instead, specific instances of
for valid \<^verbatim>\<open>p\<close> have to be wrapped as definitions and given code equations by instantiating
\<^verbatim>\<open>prism_to_focus.rep_eq\<close>. However, those specialized code equations will only be recognized 
during code generation if \<^verbatim>\<open>reference_fun\<close> is inlined -- thus the need for \<^verbatim>\<open>code_unfold\<close>.\<close>
declare reference_fun_def[code_unfold]

definition modify_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  [all_reference_defs']: \<open>modify_raw_fun r f \<equiv> FunctionBody \<lbrakk>
     let g = dereference_raw_fun(r);
     update_raw_fun(r, \<llangle>f\<rrangle>\<^sub>1(g))
  \<rbrakk>\<close>

definition modify_fun :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  [all_reference_defs']: \<open>modify_fun ref f \<equiv> FunctionBody \<lbrakk>
     modify_raw_fun (\<llangle>untype_ref\<rrangle>\<^sub>1(ref), \<llangle>focus_modify (get_focus ref) f\<rrangle>)
  \<rbrakk>\<close>

definition update_fun :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  [all_reference_defs']: \<open>update_fun ref v \<equiv> FunctionBody \<lbrakk>
     modify_fun(ref, \<llangle>\<lambda>_. v\<rrangle>)
   \<rbrakk>\<close>

definition dereference_fun :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  [all_reference_defs']: \<open>dereference_fun ref \<equiv> FunctionBody \<lbrakk>
      let b = dereference_raw_fun(\<llangle>untype_ref\<rrangle>\<^sub>1(ref));
      match (\<llangle>focus_view (\<integral> ref) b\<rrangle>) {
         None \<Rightarrow> \<epsilon>\<open>abort TypeError\<close>,
         Some(v) \<Rightarrow> v
      }
  \<rbrakk>\<close>

definition ro_dereference_fun ::
      \<open>('a, 'b, 'v) ro_ref \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  [all_reference_defs']: \<open>ro_dereference_fun r \<equiv> FunctionBody \<lbrakk> dereference_fun(\<llangle>unsafe_ref_from_ro_ref\<rrangle>\<^sub>1(r)) \<rbrakk>\<close>

definition is_valid_ref_for :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b set \<Rightarrow> bool\<close>
  where \<open>is_valid_ref_for r P \<equiv> focus_dom (get_focus r) \<subseteq> P\<close>

lemma is_valid_ref_for_compose[focus_intros]:
  assumes \<open>is_valid_ref_for r P\<close>
  shows \<open>is_valid_ref_for (focus_reference f r) P\<close> 
  using assms by (simp add: is_valid_ref_for_def focus_factors_trans focus_focused_get_focus)

abbreviation points_to_localizes :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> bool\<close> where
  \<open>points_to_localizes r b v \<equiv> is_valid_ref_for r (gref_can_store (unwrap_focused r)) 
                                \<and> focus_view (get_focus r) b = Some v\<close>

definition points_to :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 's assert\<close> where
  [all_reference_defs']: \<open>points_to r sh b v \<equiv> points_to_raw (unwrap_focused r) sh b \<star> \<langle>points_to_localizes r b v\<rangle>\<close>

notation points_to ("(_) \<mapsto> \<langle>_\<rangle>/_/ \<down>/ _" [69,0,69,69]70)

abbreviation points_to_modified :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> share \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 's assert\<close> where
  \<open>points_to_modified r sh op b v \<equiv> points_to r sh (focus_modify (get_focus r) op b) (op v) \<star>
   \<langle>points_to_localizes r b v\<rangle>\<close>

notation points_to_modified ("(_) \<mapsto> \<langle>_\<rangle>/ _\<sqdot> '(_\<down>_')" [69,0,69,69,69]70)

definition modify_raw_contract :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>modify_raw_contract r g f \<equiv>
     let pre = \<langle>f g \<in> gref_can_store r\<rangle> \<star> points_to_raw r \<top> g in
     let post = \<lambda>_. (points_to_raw r \<top> (f g)) in
     make_function_contract pre post\<close>

definition update_contract :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>update_contract r g0 v0 v \<equiv>
     let pre = points_to r \<top> g0 v0 in
     let post = \<lambda>_. points_to_modified r \<top> (\<lambda>_. v) g0 v0 in
     make_function_contract pre post\<close>

definition modify_contract :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('s, unit, 'abort) function_contract\<close> 
  where [all_reference_defs']: \<open>modify_contract r g0 v0 f \<equiv>
     let pre = points_to r \<top> g0 v0 in
     let post = \<lambda>_. (points_to_modified r \<top> f g0 v0) in
     make_function_contract pre post\<close>

definition dereference_contract 
  :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('s, 'v, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>dereference_contract r sh g v \<equiv>
     let pre = points_to r sh g v in
     let post = \<lambda>v'. (points_to r sh g v \<star> \<langle>v=v'\<rangle>) in
     make_function_contract pre post\<close>

definition ro_dereference_contract
  :: \<open>('a, 'b, 'v) ro_ref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('s, 'v, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>ro_dereference_contract r sh g v \<equiv>
     let pre = points_to (unsafe_ref_from_ro_ref r) sh g v in
     let post = \<lambda>v'. points_to (unsafe_ref_from_ro_ref r) sh g v \<star> \<langle>v=v'\<rangle> in
     make_function_contract pre post\<close>

definition reference_contract :: \<open>('b, 'v) prism \<Rightarrow> 'v \<Rightarrow> ('s, ('a, 'b, 'v) Global_Store.ref, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>reference_contract p v \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. points_to r \<top> (prism_embed p v) v \<star> \<langle>\<integral>r = prism_to_focus p\<rangle> \<star> can_alloc_reference in
     make_function_contract pre post\<close>

lemmas all_reference_defs = all_reference_defs'
named_theorems all_reference_specs

end

locale reference = reference_defs reference_types 
    update_raw_fun 
    dereference_raw_fun
    reference_raw_fun
    points_to_raw'
    gref_can_store
    new_gref_can_store
    can_alloc_reference
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> 
    and update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store 
      new_gref_can_store can_alloc_reference +

  assumes update_raw_spec [all_reference_specs]:      \<open>\<Gamma> ; update_raw_fun r g    \<Turnstile>\<^sub>F update_raw_contract r g0 g\<close>
      and dereference_raw_spec[all_reference_specs]: \<open>\<Gamma> ; dereference_raw_fun r \<Turnstile>\<^sub>F dereference_raw_contract r sh g\<close>
      and reference_raw_spec[all_reference_specs]:   \<open>\<Gamma> ; reference_raw_fun g   \<Turnstile>\<^sub>F reference_raw_contract g\<close>

      and ucincl_points_to_raw[ucincl_intros, all_reference_specs]: \<open>\<And>r sh g. ucincl (points_to_raw r sh g)\<close>
      and ucincl_can_alloc_reference[ucincl_intros, all_reference_specs]: \<open>ucincl can_alloc_reference\<close>

      and points_to_raw_combine[all_reference_specs]: 
         \<open>\<And>r sh1 sh2 v1 v2. r \<mapsto>\<langle>sh1\<rangle> v1 \<star> r \<mapsto>\<langle>sh2\<rangle> v2 \<longlongrightarrow> r \<mapsto>\<langle>sh1+sh2\<rangle> v1 \<star> \<langle>v1 = v2\<rangle>\<close>
      and points_to_raw_split[all_reference_specs]: 
         \<open>\<And>sh shA shB r v. sh = shA+shB \<Longrightarrow> shA \<sharp> shB \<Longrightarrow> 0 < shA \<Longrightarrow> 0 < shB \<Longrightarrow> 
            r \<mapsto>\<langle>sh\<rangle> v \<longlongrightarrow> r \<mapsto>\<langle>shA\<rangle> v \<star> r \<mapsto>\<langle>shB\<rangle> v\<close>
begin

lemma points_to_raw'_ucincl[ucincl_intros]:
  shows \<open>\<And>r sh g. ucincl (points_to_raw' r sh g)\<close>
  using ucincl_points_to_raw unfolding points_to_raw_def by simp

lemma points_to_raw_aentails[intro]:
  assumes \<open>g0 = g1\<close>  
    shows \<open>r \<mapsto>\<langle>sh\<rangle> g0 \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> g1\<close>
using assms by (auto intro!: aentails_refl)

lemma points_to_aentails[intro]: 
  assumes \<open>g0 = g1\<close>  
      and \<open>v0 = v1\<close>
    shows \<open>r \<mapsto>\<langle>sh\<rangle> g0\<down>v0 \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> g1\<down>v1\<close>
using assms by (auto intro!: aentails_refl)

lemma aentails_split_single_points_to_assm:
  assumes \<open>points_to_localizes r g v \<Longrightarrow> \<flat> r \<mapsto>\<langle>sh\<rangle> g \<longlongrightarrow> \<phi>\<close>
  shows \<open>r\<mapsto>\<langle>sh\<rangle> g\<down>v \<longlongrightarrow> \<phi>\<close> 
by (metis (full_types) apure_entailsL asepconj_comm assms points_to_def ucincl_points_to_raw)

lemma aentails_split_top_points_to_assm:
  assumes \<open>points_to_localizes r g v \<Longrightarrow> \<flat> r \<mapsto>\<langle>sh\<rangle> g \<star> \<psi> \<longlongrightarrow> \<phi>\<close>
    shows \<open>r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<psi> \<longlongrightarrow> \<phi>\<close> 
by (metis aentails_split_single_points_to_assm assms awand_adjoint)

lemma aentails_cancel_points_to_raw_with_typed:
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>\<psi> \<longlongrightarrow> \<langle>points_to_localizes r g v\<rangle> \<star> \<phi>\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<star> \<psi> \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<phi>\<close> 
using assms points_to_def by (metis (no_types, lifting) asepconj_assoc asepconj_mono)

lemma aentails_cancel_points_to_raw_with_typed_0LR:
    notes asat_simp [simp]
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>points_to_localizes r g v\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v\<close>   
using assms by (simp add: aentails_def points_to_def ucincl_points_to_raw)

lemma aentails_cancel_points_to_raw_with_typed_0L:
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>points_to_localizes r g v\<rangle>\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<star> \<phi> \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v\<close>   
using assms by (simp add: asepconj_mono points_to_def)

lemma aentails_cancel_points_to_raw_with_typed_0R:
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>\<top> \<longlongrightarrow> \<langle>points_to_localizes r g v\<rangle> \<star> \<psi>\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<psi>\<close>   
  using aentails_cancel_points_to_raw_with_typed by (metis asepconj_ident2 assms ucincl_points_to_raw) 

declare reference_axioms [reference_axioms]
end

end
(*>*)
