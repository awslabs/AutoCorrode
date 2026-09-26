(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Transfer_References
  imports
    Separation_Lenses.SLens
    Separation_Lenses.SLens_Pullback
    Micro_Rust_Interfaces_Core.References
begin

section\<open>Extending the domain of a reference implementation\<close>

text\<open>The goal of this section is to show that (standalone) implementation of the \<^verbatim>\<open>Reference\<close>
locale can be extended larger separation algebras.

To begin, the following locale captures an implementation of the reference locale on a 'small'
separation algebra, alongside an embedding into a larger separation algebra by means of
a separation lens.

The goal is to formally derive an implementation of the refrence locale on the large
separation algebra.\<close>
locale reference_transfer =
   R: reference reference_types_lo update_raw_fun_lo dereference_raw_fun_lo
     reference_raw_fun_lo points_to_raw'_lo gref_can_store_lo new_gref_can_store_lo
     can_alloc_reference_lo + slens l
  for
    l :: \<open>('s::{sepalg}, 't::sepalg) lens\<close> and
    reference_types_lo :: \<open>'t::{sepalg} \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
    update_raw_fun_lo dereference_raw_fun_lo reference_raw_fun_lo
    points_to_raw'_lo gref_can_store_lo new_gref_can_store_lo can_alloc_reference_lo
begin
text\<open>Everything is formal nonsense here: We pull back all parameters, constructions and specs
along the separation lens. The real work has been done in \<^verbatim>\<open>SLens.thy\<close> where we established that
pull back commutes with all those constructions.\<close>

named_theorems lifted_defs

definition [lifted_defs]: \<open>update_raw_fun r g \<equiv> l\<inverse> (update_raw_fun_lo r g)\<close>
definition [lifted_defs]: \<open>dereference_raw_fun r \<equiv> l\<inverse> (dereference_raw_fun_lo r)\<close>
definition [lifted_defs]: \<open>reference_raw_fun r \<equiv> l\<inverse> (reference_raw_fun_lo r)\<close>
\<comment>\<open>Points-to assertions transfer precisely, while the upwards-closed allocator assertion
transfers framed.\<close>
definition [lifted_defs]: \<open>points_to_raw' r sh g \<equiv> l\<inverse> (points_to_raw'_lo r sh g)\<close>
definition [lifted_defs]: \<open>can_alloc_reference \<equiv>
  pull_back_assertion_framed l can_alloc_reference_lo\<close>

interpretation Defs: reference_defs \<open>\<lambda>(_::'s) (_::'a) (_::'b) (_ :: 'abort) (_:: 'i prompt) (_::'o prompt_output). ()\<close>
   update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw'
   gref_can_store_lo new_gref_can_store_lo can_alloc_reference .

text\<open>Reference transfer uses precise pullbacks for exact points-to assertions and framed
pullbacks for allocator assertions.\<close>
lemma reference_transfer_def_simps:
  shows \<open>Defs.update_raw_contract rr g0 g = l\<inverse> (R.update_raw_contract rr g0 g)\<close>
    and \<open>Defs.dereference_raw_contract rr sh g = l\<inverse> (R.dereference_raw_contract rr sh g)\<close>
    and \<open>Defs.reference_raw_contract v =
      pull_back_contract_framed l (R.reference_raw_contract v)\<close>
    and \<open>Defs.points_to_raw rr sh g = l\<inverse> (R.points_to_raw rr sh g)\<close>
    and \<open>Defs.points_to r sh g v = l\<inverse> (R.points_to r sh g v)\<close>
  apply (clarsimp simp add: lifted_defs pull_back_contract_framed_def pull_back_contract_def
      comp_def slens_pull_back_precise_simps
      pull_back_assertion_framed_apure_precise_asepconj
      pull_back_assertion_framed_asepconj_apure_precise
      pull_back_assertion_framed_asepconj_apure_precise_asepconj
      pull_back_assertion_framed_false
      pull_back_assertion_mixed_asepconj
      pull_back_assertion_mixed_asepconj'
    (* All definitions in the reference locale *)
      reference_defs.all_reference_defs bot_fun_def)+
  \<comment>\<open>The framed allocator factor absorbs the lens kernel in the mixed contract.\<close>
  apply (simp only: pull_back_assertion_framed_absorbs_precise)
  apply (simp add: lifted_defs reference_defs.points_to_raw_def)
  apply (simp add: lifted_defs reference_defs.points_to_def reference_defs.points_to_raw_def
    slens_pull_back_precise_simps)
  done

text\<open>Applying the various (non-trivial) theorems for transporting specs along pullbacks, we now
formally derive the correctness of the pulled back reference implementation:\<close>

lemma reference_contracts_no_abort:
  shows \<open>\<And>a b c. function_contract_abort (R.update_raw_contract a b c) = \<bottom>\<close>
    and \<open>\<And>a b c. function_contract_abort (R.dereference_raw_contract a b c) = \<bottom>\<close>
    and \<open>\<And>a b c. function_contract_abort (R.reference_raw_contract a) = \<bottom>\<close>
  by (auto simp add: reference_defs.all_reference_defs)

lemma reference_lifted: \<open>reference
   update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw'
   gref_can_store_lo new_gref_can_store_lo can_alloc_reference\<close>
  using R.all_reference_specs apply -
  apply (standard; simp add: reference_transfer_def_simps)
  \<comment>\<open>Framed obligations use only framed rules backwards; precise rules are oriented inward.\<close>
  apply (auto simp add: reference_contracts_no_abort pull_back_spec_universal lifted_defs
    intro!: slens_pull_back_intros
    simp flip: pull_back_assertion_framed_asepconj
      pull_back_assertion_framed_apure_precise_asepconj
      pull_back_assertion_framed_asepconj_apure_precise)
  \<comment>\<open>Exact points-to obligations use precise transport.\<close>
  apply (auto simp add: reference_contracts_no_abort intro!: pull_back_spec_universal_precise)
  apply (metis R.points_to_raw_combine pull_back_aentailsI pull_back_asepconj
    pull_back_assertion_apure_precise)
  apply (metis R.points_to_raw_split pull_back_aentailsI pull_back_asepconj)
  done

end

end
