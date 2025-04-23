(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Focused_Types
  imports Focus
begin

subsection\<open>Focused types\<close>

text\<open>Foci can be used to "type" pointers into a monomorphic global store, by connecting the
fixed store-type to concrete value types. For example, typing physical memory could be achieved
through foci from the fixed type of byte lists to various concrete data types. The foci then encode
the byte-level presentatation of the type.\<close>

datatype_record ('tv, 'vp, 'wp) focused =
  unwrap_focused :: \<open>'tv\<close>
  get_focus :: \<open>('vp, 'wp) focus\<close>

notation get_focus ("\<integral>")
notation unwrap_focused ("\<flat>")

abbreviation map_focus :: \<open>(('v, 'w) focus \<Rightarrow> ('v, 'u) focus) \<Rightarrow> ('t, 'v, 'w) focused \<Rightarrow> ('t, 'v, 'u) focused\<close> where
  \<open>map_focus f \<equiv> update_get_focus f\<close>

definition focus_focused :: \<open>('v, 'w) focus \<Rightarrow> ('a, 'b, 'v) focused \<Rightarrow> ('a, 'b, 'w) focused\<close> where
  \<open>focus_focused foc \<equiv> map_focus (\<lambda>foc'. foc' \<diamondop> foc)\<close>
notation focus_focused ("_/ \<triangleright>/ _")

lemma untype_ref_focus [focus_simps]: \<open>unwrap_focused (focus_focused f r) = unwrap_focused r\<close>
  by (simp add: focus_focused_def)

lemma untype_type_ref[focus_simps]:
  \<open>make_focused (\<flat> r) (\<integral> r) = r\<close>
  by auto

lemma focus_focused_get_focus [focus_simps]:
  \<open>\<integral> (l \<triangleright> r) = (\<integral> r) \<diamondop> l\<close>
  by (simp add: focus_focused_def)

lemma focus_compose [focus_simps]:
  fixes r :: \<open>('a, 'b, 'v) focused\<close>
    and l1 :: \<open>('v, 'w) focus\<close>
    and l2 :: \<open>('w, 'x) focus\<close>
  shows \<open>l2 \<triangleright> (l1 \<triangleright> r) = (l1 \<diamondop> l2) \<triangleright> r\<close>
  by (clarsimp simp add: focus_simps focus_focused_def comp_def)

lemma map_focus_compose [focus_simps]:
  fixes r :: \<open>('x, 'v, 'w) focused\<close>
    and f :: \<open>('v, 'w) focus \<Rightarrow> ('v, 'u) focus\<close>
    and g :: \<open>('v, 'u) focus \<Rightarrow> ('v, 't) focus\<close>
  shows \<open>map_focus g (map_focus f r) = map_focus (g \<circ> f) r\<close>
  by (clarsimp simp add: comp_def apsnd_def map_prod_def split_beta)

end