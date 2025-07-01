(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory MultisetAdditional
  imports Main "HOL-Library.Multiset" ListAdditional WordAdditional
begin
(*>*)

section \<open>Some facts on multiset arithmetic\<close>

subsection\<open>Some notation for multiset mapping\<close>

syntax
  "_mset_from_mapped_list" :: \<open>logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic\<close> ("{# _ \<Colon> _ \<leftarrow> _ #}")
  "_mset_from_mapped_mset" :: \<open>logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic\<close> ("{# _ . _ \<leftarrow> _ #}")
  "_mset_from_anon_mapped_list" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("{# _ \<Colon> _ #}")
  "_mset_from_anon_mapped_mset" :: \<open>logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("{# _ . _ #}")
translations
  "_mset_from_mapped_list entry var lst"      \<rightleftharpoons>
    "(CONST Multiset.image_mset) (\<lambda>var. entry) ((CONST Multiset.mset) lst)"
  "_mset_from_mapped_mset entry var mset"      \<rightleftharpoons>
    "(CONST Multiset.image_mset) (\<lambda>var. entry) mset"
  "_mset_from_anon_mapped_list entryfunc lst" \<rightleftharpoons>
    "(CONST Multiset.image_mset) entryfunc     ((CONST Multiset.mset) lst)"
  "_mset_from_anon_mapped_mset entryfunc ms " \<rightleftharpoons>
    "(CONST Multiset.image_mset) entryfunc ms"

notation image_mset (infixr \<open>`#\<close> 90)

(*<*)
notepad
begin
  fix t :: \<open>nat \<Rightarrow> 'a set\<close>
  have \<open>{# t a \<Colon> (a, b) \<leftarrow> [(0,0),(1,1)] #} = {# \<lambda>(a, b). t a \<Colon> [(0,0), (1,1)] #}\<close>
    by auto
end
(*>*)

subsection\<open>Alternative characterization of injectivity via multisets\<close>

text\<open>Injectivity can be expressed as the equality of multiset-images and set-images:\<close>
lemma inj_on_via_mset:
  assumes \<open>finite A\<close>
      and \<open>image_mset f (mset_set A) = mset_set (f ` A)\<close>
    shows \<open>inj_on f A\<close>
proof -
  {
       fix x y
    assume \<open>x \<in> A\<close>
       and \<open>y \<in> A\<close>
       and \<open>x \<noteq> y\<close>
       and \<open>f x = f y\<close>
    moreover from this have \<open>{# x, y #} \<subseteq># mset_set A\<close>
      by (simp add: assms(1) mset_set.remove)
    moreover from this have \<open>{# f x, f y #} \<subseteq># (image_mset f (mset_set A))\<close>
      using image_mset_subseteq_mono by fastforce
    ultimately have \<open>count (image_mset f (mset_set A)) (f x) \<ge> 2\<close>
      by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right
        cancel_comm_monoid_add_class.diff_cancel count_add_mset count_diff nat_1_add_1
        subseteq_mset_def)
    from this have False
      by (simp add: \<open>x \<in> A\<close> assms)
  }
  from this show ?thesis
    by (auto simp add: inj_on_def)
qed

subsection\<open>Multiset decompositions\<close>

lemma mset_sub_drop:
  shows \<open>mset (drop n ls) \<subseteq># mset ls\<close>
by (induction ls arbitrary: n; clarsimp) (metis append_take_drop_id mset.simps(2) mset_append
    mset_subset_eq_add_right)

lemma mset_nth_decomposition:
  assumes \<open>n < length ls\<close>
    shows \<open>mset ls = mset (take n ls) + {# ls ! n #} + mset (drop (n+1) ls)\<close>
using assms by (subst id_take_nth_drop [where i=n]) auto

lemma mset_drop_nth:
  assumes \<open>n < length ls\<close>
    shows \<open>mset (drop_nth n ls) = mset (take n ls) + mset (drop (n+1) ls)\<close>
using assms drop_nth_def by (metis mset_append)

lemma mset_drop_nth':
  assumes \<open>n < length ls\<close>
    shows \<open>mset (drop_nth n ls) = mset ls - {# ls ! n #}\<close>
using assms mset_nth_decomposition mset_drop_nth by fastforce

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma mset_drop_nth'':
  assumes \<open>n < length ls\<close>
    shows \<open>mset ls = {# ls ! n #} + mset (drop_nth n ls)\<close>
using mset_drop_nth' assms by fastforce

lemma mset_sub_drop_nth [intro]:
  assumes \<open>n < length ls\<close>
    shows \<open>mset (drop_nth n ls) \<subseteq># mset ls\<close>
using assms mset_drop_nth' by fastforce

named_theorems mset_simps

lemma mapped_multiset_eq [mset_simps]:
    fixes ms :: \<open>'a multiset\<close>
      and \<xi> \<tau> :: \<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>x. (x\<in>#ms \<longrightarrow> \<xi> x = \<tau> x)\<close>
    shows \<open>{# \<xi> . ms #} = {# \<tau> . ms #}\<close>
using assms by (metis multiset.map_cong)

lemma mset_set_minus_singletonE [elim]:
  assumes \<open>i \<in># mset_set s - {#i#}\<close>
    shows \<open>R\<close>
proof -
  have \<open>\<And>s j. count (mset_set s) j \<le> 1\<close>
    by (metis count_mset_set order_refl zero_le)
  from this have \<open>\<And>s j. count (mset_set s - {#j#}) j = 0\<close>
    by auto
  from this have False
    using assms by (metis count_eq_zero_iff)
  from this show ?thesis
    by auto
qed

lemma mset_range_minus_singletonE [elim]:
  assumes \<open>i \<in># mset [0..<N] - {#i#}\<close>
    shows \<open>R\<close>
using assms Multiset.mset_upt mset_set_minus_singletonE by auto

lemma mset_minus_drop_nth [mset_simps]:
  assumes \<open>n < length ls\<close>
    shows \<open>mset ls - mset (drop_nth n ls) = {# ls ! n #}\<close>
using assms mset_drop_nth' mset_nth_decomposition by fastforce

lemma mset_set_tagged:
  assumes \<open>finite s\<close>
    shows \<open>mset_set s = (f `# ms') \<longleftrightarrow> (\<exists>s'. (ms' = mset_set s') \<and> s = f ` s' \<and> inj_on f s')\<close>
proof
  {
    assume \<open>mset_set s = (f `# ms')\<close>
    moreover from this [symmetric] and assms have \<open>\<forall>x. count (f `# ms') x \<le> 1\<close>
      by (clarsimp simp add: count_mset_set')
    moreover have \<open>\<forall>x. count ms' x \<le> count (f `# ms') (f x)\<close>
      by (metis count_le_replicate_mset_subset_eq image_mset_subseteq_mono
        image_replicate_mset le_refl)
    moreover from calculation have \<open>\<forall>x. count ms' x \<le> 1\<close>
      using le_trans by blast
    ultimately have \<open>ms' = mset_set (set_mset ms')\<close>
      by (metis count_eq_zero_iff count_greater_eq_one_iff count_mset_set'
       finite_set_mset multi_count_eq nle_le)
  }
  moreover {
       fix r :: \<open>'a \<Rightarrow> 'b\<close>
       and t
    assume F: \<open>finite t\<close>
       and E: \<open>r `# (mset_set t) = mset_set (r ` t)\<close>
    {
         fix x y
      assume \<open>x \<in> t\<close>
         and \<open>y \<in> t\<close>
         and \<open>x \<noteq> y\<close>
         and \<open>r x = r y\<close>
      moreover from this and F have \<open> {# x, y #} \<subseteq>#  mset_set t\<close>
        by (simp add: mset_set.remove)
      moreover from this have \<open>{# r x, r y #} \<subseteq># (r `# mset_set t)\<close>
        using image_mset_subseteq_mono by fastforce
      moreover from calculation have \<open>count (r `# mset_set t) (r x) \<ge> 2\<close>
        by (simp add: count_le_replicate_mset_subset_eq numeral_2_eq_2)
      ultimately have False
        using E by (metis count_mset_set(1) count_mset_set(2) count_mset_set(3) not_numeral_le_zero
          numeral_le_one_iff semiring_norm(69))
    }
    from this have \<open>inj_on r t\<close>
      by (metis inj_on_def)
  }
  ultimately show \<open>mset_set s = (f `# ms') \<Longrightarrow> (\<exists>s'. (ms' = mset_set s') \<and> s = f ` s' \<and> inj_on f s')\<close>
    using assms by (metis finite_set_mset finite_set_mset_mset_set inj_on_via_mset set_image_mset)
  show \<open>(\<exists>s'. (ms' = mset_set s') \<and> s = f ` s' \<and> inj_on f s') \<Longrightarrow> mset_set s = (f `# ms')\<close>
    by (metis image_mset_mset_set)
qed

definition map_from_graph :: \<open>('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b\<close> where
  \<open>map_from_graph g a \<equiv>
    if a \<notin> fst ` g then
      undefined
    else
      snd (SOME t. t \<in> g \<and> fst t = a)\<close>

lemma map_from_graph_eval:
  assumes \<open>(a, b) \<in> g\<close>
      and \<open>inj_on fst g\<close>
    shows \<open>map_from_graph g a = b\<close>
proof -
  from assms have \<open>{t. t \<in> g \<and> fst t = a} = {(a, b)}\<close>
    by (intro equalityI subsetI; clarsimp simp add: inj_on_def)
  moreover from this have \<open>(SOME t. t \<in> g \<and> fst t = a) = (a,b)\<close>
    by blast
  moreover from calculation have \<open>a \<in> fst ` g\<close>
    by auto
  ultimately show ?thesis
    by (clarsimp simp add: map_from_graph_def)
qed

lemma map_from_graph_eval':
  assumes \<open>t \<in> g\<close>
      and \<open>inj_on fst g\<close>
    shows \<open>map_from_graph g (fst t) = snd t\<close>
using assms map_from_graph_eval by (metis prod.collapse)

lemma mset_map_sum_lift_single:
  shows \<open>add_mset x ms0 = (f `# ms') \<longleftrightarrow> (\<exists>x' ms0'. ms' = add_mset x' ms0' \<and> x = f x' \<and> ms0 = (f `# ms0'))\<close>
by (metis (full_types) msed_map_invL msed_map_invR)

lemma mset_sum_count:
  shows \<open>count (\<Sum>x \<in># ms. \<xi> x) t = (\<Sum>x \<in># ms. count (\<xi> x) t)\<close>
by (induction ms; auto)

lemma set_product_sum:
  assumes \<open>finite A\<close>
      and \<open>finite B\<close>
    shows \<open>(\<Sum>x\<in>#mset_set A. {# Pair x . mset_set B #}) = mset_set (A \<times> B)\<close>
proof -
  let ?P = \<open>\<Sum>x\<in>#mset_set A. {# Pair x. mset_set B #}\<close>
  have EQ: \<open>\<And>a b. count ?P (a,b) = (\<Sum>x\<in>#mset_set A. (count {# Pair x . mset_set B #} (a,b)))\<close>
    by (simp add: mset_sum_count)
  moreover {
       fix a b x
    assume \<open>x \<in># mset_set A\<close>
       and \<open>x \<noteq> a\<close>
    then have \<open>count {# Pair x . mset_set B #} (a,b) = 0\<close>
      by (clarsimp simp add: count_image_mset)
  } moreover {
       fix a b x
    assume \<open>x \<in># mset_set A\<close>
       and \<open>a \<notin> A\<close>
    then have \<open>count {# Pair x . mset_set B #} (a,b) = 0\<close>
      using assms calculation by fastforce
  } moreover {
       fix a b x
    assume \<open>x \<in># mset_set A\<close>
       and \<open>b \<notin> B\<close>
    then have \<open>count {# Pair x . mset_set B #} (a,b) = 0\<close>
      using assms calculation by fastforce
  } moreover {
       fix a b
    assume \<open>a \<in> A\<close>
       and B: \<open>b \<in> B\<close>
    {
         fix x
      assume M: \<open>x \<in># mset_set A\<close>
      {
        assume \<open>x = a\<close>
        moreover have \<open>Pair a -` {(a, b)} \<inter> B = {b}\<close>
          using \<open>b \<in> B\<close> by blast
        ultimately have \<open>count {# Pair x . mset_set B #} (a,b) = 1\<close>
          using assms B by (clarsimp simp add: count_image_mset)
      }
      from this and calculation have \<open>count {# Pair x . mset_set B #} (a,b) = (if x = a then 1 else 0)\<close>
        using M by meson
    }
    moreover from calculation have \<open>count ?P (a,b) = (\<Sum>x\<in>#mset_set A. (if x = a then 1 else 0))\<close>
      using image_mset_cong EQ by force
    moreover have \<open>\<And>ms t. (\<Sum> x\<in>#ms. (if x = t then 1 else 0)) = count ms t\<close>
      by (simp add: sum_mset_delta)
    moreover from this have \<open>(\<Sum>x\<in>#mset_set A. (if x = a then 1 else 0)) = count (mset_set A) a\<close>
      by force
    ultimately have \<open>count ?P (a,b) = 1\<close>
      by (simp add: \<open>a \<in> A\<close> assms(1))
  } moreover {
       fix a b
    assume \<open>a \<notin> A\<close>
    then have \<open>count ?P (a,b) = 0\<close>
      using EQ calculation by force
  } moreover {
       fix a b
    assume \<open>b \<notin> B\<close>
    then have \<open>count ?P (a,b) = 0\<close>
      using EQ calculation by auto
  }
  moreover from calculation have \<open>\<And>a b. count ?P (a,b) = (if (a,b) \<in> A \<times> B then 1 else 0)\<close>
    by (meson mem_Sigma_iff)
  moreover from calculation have \<open>\<And> t. count ?P t = count (mset_set (A \<times> B)) t\<close>
    using assms by (clarsimp, simp add: count_mset_set')
  ultimately show ?thesis
    by (meson multi_count_eq)
qed

lemma multiset_map_comp':
  shows \<open>{# \<xi> x . x \<leftarrow> {# f . ms #} #} = {# \<xi> (f y) . y \<leftarrow> ms #}\<close>
using Multiset.Multiset.multiset.map_comp by (auto simp add: comp_def)

lemma multiset_map_comp_retract:
  assumes \<open>\<And>x. x \<in># ms \<Longrightarrow> f (g x) = x\<close>
    shows \<open>{# \<xi> x . x \<leftarrow> ms #} = {# \<xi> (f y) . y \<leftarrow> {# g . ms #} #}\<close>
using assms by (simp add: mapped_multiset_eq multiset_map_comp')

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma multiset_map_comp_word_cast_general:
    fixes ms :: \<open>'a::{len} word multiset\<close>
  assumes \<open>\<And>x. x \<in># ms \<Longrightarrow> unat x < 2^LENGTH('b::{len})\<close>
    shows \<open>{# \<xi> x . x \<leftarrow> ms #} = {# \<xi> (ucast x) . x \<leftarrow> {# ucast::_ \<Rightarrow> 'b word . ms #} #}\<close>
proof -
  let ?g = \<open>ucast :: 'a word \<Rightarrow> 'b word\<close>
  let ?f = \<open>ucast :: 'b word \<Rightarrow> 'a word\<close>
  have \<open>\<And>x. x \<in># ms \<Longrightarrow> ?f (?g x) = x\<close>
    using WordAdditional.ucast_ucast_eq assms by blast
  from this show ?thesis
    using multiset_map_comp_retract[where f=\<open>?f\<close> and g=\<open>?g\<close>] by blast
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma multiset_map_comp_word_up_down:
    fixes ms :: \<open>'a::{len} word multiset\<close>
  assumes \<open>LENGTH('a) \<le> LENGTH('b::{len})\<close>
    shows \<open>{# \<xi> x . x \<leftarrow> ms #} = {# \<xi> ((ucast x) :: 'a word) . x \<leftarrow> {# ucast::'a word \<Rightarrow> 'b word . ms #} #}\<close>
by (simp add: assms eq_ucast_ucast_eq multiset_map_comp')

lemma multiset_map_comp_word_nat_cast:
    fixes ms :: \<open>nat multiset\<close>
  assumes \<open>\<And>x. x \<in># ms \<Longrightarrow> x < 2^LENGTH('a::{len})\<close>
    shows \<open>{# \<xi> x . x \<leftarrow> ms #} = {# \<xi> (unat x) . x \<leftarrow> {# word_of_nat::nat \<Rightarrow> 'a word . ms #} #}\<close>
proof -
  let ?g = \<open>word_of_nat :: nat \<Rightarrow> 'a word\<close>
  let ?f = \<open>unat :: 'a word \<Rightarrow> nat\<close>
  have \<open>\<And>x. x \<in># ms \<Longrightarrow> ?f (?g x) = x\<close>
    using assms unat_of_nat_len by blast
  from this show ?thesis
    using multiset_map_comp_retract[where f=\<open>?f\<close> and g=\<open>?g\<close>] by blast
qed

lemma multiset_map_comp_nat_word_cast:
  shows \<open>{# \<xi> x . x \<leftarrow> ms #} = {# \<xi> (word_of_nat x) . x \<leftarrow> {# unat . ms #} #}\<close>
by (simp add: multiset_map_comp')

lemma mset_reindex_core:
  shows \<open>mset xs = {# xs ! i . i \<leftarrow> mset_set {0..<(length xs)} #}\<close>
proof (induction xs)
  show \<open>mset [] = {# (!) [] . mset_set {0..<length []} #}\<close>
    by clarsimp
next
     fix x
     and xs :: \<open>'a list\<close>
  assume \<open>mset xs = {# (!) xs . mset_set {0..<length xs} #}\<close>
  from this show \<open>mset (x # xs) = {# (!) (x # xs) . mset_set {0..<length (x # xs)} #}\<close>
    by (metis map_nth mset_map mset_upt)
qed

lemma mset_reindex:
  assumes \<open>length xs = hi\<close>
    shows \<open>mset xs = {# xs ! i . i \<leftarrow> mset_set {0..<hi} #}\<close>
using mset_reindex_core assms by blast

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma set_upt_image_word_of_nat:
  assumes \<open>b < 2^LENGTH('l::{len})\<close>
    shows \<open>{0..<(word_of_nat b::'l word)} = word_of_nat ` {0..<b}\<close>
proof (intro set_eqI iffI)
     fix x :: \<open>'l word\<close>
  assume \<open>x \<in> {0..<word_of_nat b}\<close>
  from this show \<open>x \<in> word_of_nat ` {0..<b}\<close>
    by (metis atLeastLessThan_iff imageI le0 unat_less_helper word_unat.Rep_inverse)
next
     fix x :: \<open>'l word\<close>
  assume \<open>x \<in> word_of_nat ` {0..<b}\<close>
  moreover from this obtain y where \<open>x = word_of_nat y\<close>
    by blast
  ultimately show \<open>x \<in> {0..<word_of_nat b}\<close>
    using assms of_nat_mono_maybe by fastforce
qed

lemma set_upt_image_unat:
  shows \<open>unat ` {0..<b} = {0..<unat b}\<close>
by (auto simp add: unat_mono intro: set_eqI) (metis atLeastLessThan_iff image_eqI le_unat_uoi'
  word_coorder.extremum word_of_nat_less)

lemma mset_upt_nat_word_cast:
  fixes b :: \<open>'l::{len} word\<close>
  shows \<open>{# unat . mset_set {0..<b} #} = mset_set {0..<(unat b)}\<close>
proof -
  have \<open>inj_on unat {0..<b}\<close>
    by (simp add: set_upt_image_unat linorder_inj_onI')
  from image_mset_mset_set[OF this] show ?thesis
    by (simp add: set_upt_image_unat)
qed

lemma mset_upt_word_nat_cast:
  fixes b :: \<open>'l::{len} word\<close>
  shows \<open>{# word_of_nat . mset_set {0..<(unat b)} #} = mset_set {0..<b}\<close>
proof -
  have \<open>mset_set {0..<b} = {# x . x \<leftarrow> mset_set {0..<b} #}\<close>
    by auto
  also have \<open>\<dots> = {# word_of_nat x . x \<leftarrow> {# unat . mset_set {0..<b} #} #}\<close>
    using multiset_map_comp_nat_word_cast by blast
  also have \<open>\<dots> = {# word_of_nat x . x \<leftarrow> mset_set {0..<(unat b)} #}\<close>
    using mset_upt_nat_word_cast by metis
  finally show ?thesis
    by simp
qed

lemma mset_reindex_word:
    fixes hi :: \<open>'l::{len} word\<close>
  assumes \<open>length xs = unat hi\<close>
    shows \<open>mset xs = {# xs ! unat i . i \<leftarrow> mset_set {0..<hi} #}\<close>
proof -
  have bound: \<open>\<And>x. x \<in># mset_set {0..<(unat hi)} \<Longrightarrow> x < 2^LENGTH('l)\<close>
    by (meson atLeastLessThan_iff elem_mset_set finite_atLeastLessThan less_Suc_eq less_Suc_unat_less_bound)
  from mset_reindex_core have \<open>mset xs = {# xs ! i . i \<leftarrow> mset_set {0..<(unat hi)} #}\<close>
    using assms by metis
  also have \<open>\<dots> = {# xs ! (unat i) . i \<leftarrow> {# (word_of_nat :: nat \<Rightarrow> 'l word) . mset_set {0..<(unat hi)} #} #}\<close>
    using bound multiset_map_comp_word_nat_cast by blast
  also have \<open>\<dots> = {# xs ! (unat i) . i \<leftarrow> mset_set {0..<hi} #}\<close>
    by (simp add: mset_upt_word_nat_cast)
  finally show ?thesis by simp
qed

(*<*)
end
(*>*)