(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory SetAdditional
  imports Main
begin
(*>*)

lemma set_dependent_union_finite: 
  assumes \<open>finite B\<close>
      and \<open>\<And>y. y \<in> B \<Longrightarrow> finite (A y)\<close>
    shows \<open>finite { (y, x). y \<in> B \<and> x \<in> A y}\<close>
using assms proof (induction rule: Finite_Set.finite_induct)
  show \<open>finite {(y, x). y \<in> {} \<and> x \<in> A y}\<close>
    by auto
next
     fix x F
  assume \<open>finite F\<close>
     and \<open>x \<notin> F\<close>
     and \<open>(\<And>y. y \<in> F \<Longrightarrow> finite (A y)) \<Longrightarrow> finite {(y, x). y \<in> F \<and> x \<in> A y}\<close>
     and \<open>\<And>y. y \<in> insert x F \<Longrightarrow> finite (A y)\<close>
  moreover from this have \<open>{a. case a of (y, xa) \<Rightarrow> (y = x \<or> y \<in> F) \<and> xa \<in> A y} =
      {(y, t). y \<in> F \<and> t \<in> A y} \<union> Pair x ` A x\<close>
    by auto
  moreover from calculation have \<open>finite ({(y, t). y \<in> F \<and> t \<in> A y} \<union> Pair x ` A x)\<close>
    by clarsimp
  ultimately show \<open>finite {(y, xa). y \<in> insert x F \<and> xa \<in> A y}\<close>
    by clarsimp
qed

lemma set_Union_flip:
  shows \<open>(\<Union>a. \<Union>b. \<xi> a b) = (\<Union>b. \<Union>a. \<xi> a b)\<close>
by auto

lemma disjoint_set_helper:
  assumes \<open>A \<subseteq> B\<close>
      and \<open>B \<inter> C = {}\<close>
    shows \<open>A \<inter> C = {}\<close>
using assms by blast

lemma disjoint_set_helper':
  assumes \<open>A \<subseteq> B\<close>
      and \<open>C \<subseteq> D\<close>
      and \<open>B \<inter> D = {}\<close>
    shows \<open>A \<inter> C = {}\<close>
using assms by blast

lemma set_non_membership_after_image:
  assumes \<open>f x \<notin> f ` s\<close>
    shows \<open>x \<notin> s\<close>
using assms by auto

text \<open>This is surprisingly difficult to prove.\<close>
lemma map_set_del:
  assumes \<open>inj_on f A\<close>
      and \<open>x \<in> A\<close>
    shows \<open>f ` (A - {x}) = f ` A - {f x}\<close> (is \<open>?X = ?Y\<close>)
proof -
  from assms have \<open>f x \<notin> ?X\<close> and \<open>f x \<notin> ?Y\<close>
    by (metis inj_on_insert insert_Diff insert_Diff_single, blast)
  moreover from assms have \<open>?X \<union> {f x} = ?Y \<union> {f x}\<close>
    by blast
  ultimately show ?thesis
    by blast
qed

lemma in_set_updateE:
  assumes \<open>x \<in> set (l [ i := v ])\<close>
      and \<open>i < length l\<close>
      and \<open>x \<in> set l \<Longrightarrow> R\<close>
      and \<open>x = v \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: set_conv_nth nth_list_update split: if_splits)

text\<open>Why is this not declared a \<^verbatim>\<open>cong\<close> rule?\<close>
lemma Least_iff_cong:
  assumes \<open>\<And>v. f v = g v\<close>
    shows \<open>(LEAST v. f v) = (LEAST v. g v)\<close>
  using assms by auto

lemma set_disjoint_from_union':
  shows \<open>(b \<union> c) \<inter> a = {} \<longleftrightarrow> (b \<inter> a = {} \<and> c \<inter> a = {})\<close>
by auto

lemma set_disjoint_from_Union':
  shows \<open>((\<Union>x\<in>l. f x) \<inter> a = {}) = (\<forall>x\<in>l. f x \<inter> a = {})\<close>
by auto

subsection\<open>Disjointness and unions\<close>

lemma set_disjoint_from_union:
  shows \<open>a \<inter> (b \<union> c) = {} \<longleftrightarrow> (a \<inter> b = {} \<and> a \<inter> c = {})\<close>
by auto

lemma set_disjoint_from_Union:
  shows \<open>(a \<inter> (\<Union>x\<in>l. f x) = {}) = (\<forall>x\<in>l. a \<inter> f x = {})\<close>
by auto

lemma set_disjoint_from_unionI:
  assumes \<open>a \<inter> b = {}\<close>
      and \<open>a \<inter> c = {}\<close>
    shows \<open>a \<inter> (b \<union> c) = {}\<close>
using assms by auto

lemma set_disjoint_from_UnionI:
  assumes \<open>\<And>x. x\<in>l \<Longrightarrow> a \<inter> f x = {}\<close>
    shows \<open>a \<inter> (\<Union>x\<in>l. f x) = {}\<close>
using assms by auto

subsection\<open>Singletons and distinct lists\<close>

lemma distinct_singleton_list:
  assumes \<open>distinct ls\<close>
      and \<open>set ls = {x}\<close>
    shows \<open>ls = [x]\<close>
by (metis assms distinct.simps(2) distinct_length_2_or_more list.set_cases neq_Nil_conv singleton_iff)

subsection\<open>Let-binding elimination\<close>

lemma LetE:
  assumes \<open>let x = e in P x\<close>
      and \<open>\<And>x. x=e \<Longrightarrow> P x \<Longrightarrow> Q\<close>
    shows \<open>Q\<close>
  using assms by simp

lemma in_set_cons:
  shows \<open>(x \<in> set (Cons y zs)) = (x = y \<or> x \<in> set zs)\<close>
  by auto

(*<*)
end
(*>*)