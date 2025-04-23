(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_References
  imports Crush.Crush
begin
(*>*)

context reference
begin

adhoc_overloading store_dereference_const \<rightleftharpoons>
  dereference_fun
  ro_dereference_fun

lemma points_to_split:
  assumes \<open>sh = sh1+sh2\<close>
      and \<open>sh1 \<sharp> sh2\<close>
      and \<open>0 < sh1\<close>
      and \<open>0 < sh2\<close>
    shows \<open>r \<mapsto>\<langle>sh\<rangle> g\<down>v \<longlongrightarrow> r \<mapsto>\<langle>sh1\<rangle> g\<down>v \<star> r \<mapsto>\<langle>sh2\<rangle> g\<down>v\<close>
using assms
  apply (clarsimp simp add: points_to_def asepconj_simp)
  apply (aentails_drule points_to_raw_split[where shA=sh1 and shB=sh2]; simp?)
  apply crush_base
  done

lemma points_to_combine:
  shows \<open>r \<mapsto>\<langle>sh1\<rangle> g1\<down>v1 \<star> r \<mapsto>\<langle>sh2\<rangle> g2\<down>v2 \<longlongrightarrow> r \<mapsto>\<langle>sh1+sh2\<rangle> g1\<down>v1 \<star> \<langle>g1 = g2\<rangle> \<star> \<langle>v1 = v2\<rangle>\<close>
  by (crush_base simp add: points_to_def seplog drule add: points_to_raw_combine)
    (clarsimp simp add: plus_share_def sup.commute intro!: aentails_refl_eq)

ucincl_auto points_to update_raw_contract dereference_raw_contract reference_raw_contract
 update_contract modify_raw_contract modify_contract dereference_contract
 ro_dereference_contract reference_contract

declare update_raw_spec[crush_specs]
declare dereference_raw_spec[crush_specs]
declare reference_raw_spec[crush_specs]

declare update_raw_contract_def[crush_contracts]
declare modify_raw_contract_def[crush_contracts]
declare reference_raw_contract_def[crush_contracts]
declare dereference_raw_contract_def[crush_contracts]

declare update_contract_def[crush_contracts]
declare modify_contract_def[crush_contracts]
declare reference_contract_def[crush_contracts]
declare dereference_contract_def[crush_contracts]
declare ro_dereference_contract_def[crush_contracts]

corollary modify_raw_spec [crush_specs]:
  shows \<open>\<Gamma> ; modify_raw_fun r f \<Turnstile>\<^sub>F modify_raw_contract r g f\<close>
  by (crush_boot f: modify_raw_fun_def contract: modify_raw_contract_def) crush_base

lemma focus_factors_preservesI[where P=\<open>gref_can_store _\<close>, focus_intros]:
  assumes \<open>focus_factors P f\<close>
      and \<open>x \<in> P\<close>
    shows \<open>focus_modify f g x \<in> P\<close>
  by (simp add: assms focus_factors_modify)

lemma gref_points_to_implies_can_store_general:
  assumes \<open>\<down>{\<integral> r} g \<doteq> v\<close>
      and \<open>is_valid_ref_for r P\<close>
    shows \<open>g \<in> P\<close>
  using assms by (clarsimp simp add: is_valid_ref_for_def focus_dom.rep_eq
    focus_raw_domI focus_view.rep_eq subsetD)

lemma gref_points_to_implies_can_store_specific[focus_elims]:
  assumes \<open>\<down>{\<integral> r} g \<doteq> v\<close>
      and \<open>is_valid_ref_for r (gref_can_store (\<flat> r))\<close>
    shows \<open>g \<in> gref_can_store (\<flat> r)\<close>
  using assms by (intro gref_points_to_implies_can_store_general; simp)

corollary modify_spec [crush_specs]:
  shows \<open>\<Gamma> ; modify_fun r f \<Turnstile>\<^sub>F modify_contract r g0 v0 f\<close>
  apply (crush_boot f: modify_fun_def contract: modify_contract_def simp: points_to_def)
  apply (crush_base simp add: is_valid_ref_for_def)
  done

lemma update_spec [crush_specs]:
  shows \<open>\<Gamma> ; update_fun r v \<Turnstile>\<^sub>F update_contract r g0 v0 v\<close>
  by (crush_boot f: update_fun_def contract: update_contract_def) crush_base

lemma dereference_spec [crush_specs]:
  shows \<open>\<Gamma> ; dereference_fun r \<Turnstile>\<^sub>F dereference_contract r sh g v\<close>
  by (crush_boot f: dereference_fun_def contract: dereference_contract_def simp: points_to_def)
    crush_base

lemma ro_dereference_spec [crush_specs]:
  shows \<open>\<Gamma> ; ro_dereference_fun r \<Turnstile>\<^sub>F ro_dereference_contract r sh g v\<close>
  by (crush_boot f: ro_dereference_fun_def contract: ro_dereference_contract_def)
    crush_base

text\<open>Deliberately don't mark this as \<^verbatim>\<open>crush_specs\<close>. Only specific instances at various
prisms will be registered as specifications.\<close>

definition can_create_gref_for_prism :: \<open>('b, 'v) prism \<Rightarrow> bool\<close>
  where \<open>can_create_gref_for_prism p \<equiv> prism_dom p \<subseteq> new_gref_can_store\<close>

lemma ref_spec:
  assumes \<open>is_valid_prism p\<close>
      and \<open>can_create_gref_for_prism p\<close>
    shows \<open>\<Gamma> ; reference_fun p v \<Turnstile>\<^sub>F reference_contract p v\<close>
using assms
  apply (crush_boot f: reference_fun_def contract: reference_contract_def)
  apply (crush_base simp add: points_to_def can_create_gref_for_prism_def
    is_valid_ref_for_def focus_components)
  apply (auto simp add: prism_dom_alt)
  done

declare update_spec[crush_specs, crush_specs_eager]
declare dereference_spec[crush_specs, crush_specs_eager]
declare ro_dereference_spec[crush_specs, crush_specs_eager]

end

named_theorems ref_prisms_validity

locale reference_allocatable = reference reference_types update_raw_fun dereference_raw_fun
    reference_raw_fun points_to_raw' gref_can_store new_gref_can_store can_alloc_reference
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and update_raw_fun and
    dereference_raw_fun and reference_raw_fun and points_to_raw' and
    gref_can_store new_gref_can_store can_alloc_reference +
    fixes prism :: \<open>('b, 'v) prism\<close>
    assumes prism_valid [ref_prisms_validity, focus_intros]: \<open>is_valid_prism prism\<close>
        and prism_allocatable: \<open>can_create_gref_for_prism prism\<close>
begin

abbreviation project :: \<open>'b \<Rightarrow> 'v option\<close> where
  \<open>project b \<equiv> prism_project prism b\<close>

abbreviation embed :: \<open>'v \<Rightarrow> 'b\<close> where
  \<open>embed b \<equiv> prism_embed prism b\<close>

definition cast :: \<open>('a, 'b) gref \<Rightarrow> ('a, 'b, 'v) ref\<close>
  where \<open>cast gref \<equiv> make_ref_typed_from_untyped gref (prism_to_focus prism)\<close>

definition new :: \<open>'v \<Rightarrow> ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where \<open>new x \<equiv> reference_fun prism x\<close>

definition \<open>focus = prism_to_focus prism\<close>
declare focus_def[symmetric, code_unfold]
declare prism_valid[THEN prism_to_focus.rep_eq, folded focus_def, code]

lemma [focus_simps]:
  shows \<open>\<And>x. project (embed x) = Some x\<close>
    and \<open>\<And>x y. project x = Some y \<Longrightarrow> embed y = x\<close>
  using is_valid_prism_def prism_valid by fastforce+

declare ref_spec[OF prism_valid prism_allocatable, folded new_def, crush_specs]

\<comment>\<open>When you use this locale, unfortunately the following is unlikely to be inherited, so
you will need to adjust and copy it.\<close>
adhoc_overloading store_reference_const \<rightleftharpoons> new

end

\<comment>\<open>TODO: How can one create such a locale experiment that should not be visible outside
of the theory?\<close>
locale "experiment" =
  \<comment> \<open>Reference interface\<close>
    reference reference_types +
    \<comment> \<open>Some assumptions on storability of values... annoying that we have to repeat
    the reference parameters everywhere\<close>
    ref_bool: reference_allocatable reference_types _ _ _ _ _ _ _ bool_prism +
    ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism
  for reference_types :: \<open>'s::sepalg \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  \<comment> \<open>Fixing the types of value projection and injection functions\<close>
  and bool_prism :: \<open>('b, bool) prism\<close>
  and nat_prism :: \<open>('b, nat) prism\<close>

begin

adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

adhoc_overloading store_reference_const \<rightleftharpoons> ref_bool.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new

definition ref_test where \<open>ref_test \<equiv> FunctionBody \<lbrakk>
      let mut nat_ref = \<llangle>0 :: nat\<rrangle>;
      let mut bool_ref = \<llangle>False :: bool\<rrangle>;
      if *bool_ref {
        nat_ref = 42;
      } else {
        nat_ref = 12;
      };
      *nat_ref
  \<rbrakk>\<close>

definition ref_test_contract where
  \<open>ref_test_contract \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = 12\<rangle> in
     make_function_contract pre post\<close>
ucincl_auto ref_test_contract

lemma ref_test_spec:
  shows \<open>\<Gamma>; ref_test \<Turnstile>\<^sub>F ref_test_contract\<close>
  apply (crush_boot f: ref_test_def contract: ref_test_contract_def)
  apply (crush_base simp add: is_valid_ref_for_def)
  done

no_adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

(*<*)
end

end
(*>*)