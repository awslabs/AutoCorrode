(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Prism
  imports Main "HOL-Library.Datatype_Records"
begin
(*>*)

(*<*)
named_theorems focus_rules
named_theorems focus_intros
named_theorems focus_elims
named_theorems focus_simps
named_theorems focus_components
(*>*)

section\<open>Prisms\<close>

text\<open>Prisms are types that describe how one type acts as a subtype of another. They are defined as a
pair of an embedding of the subtype into the larger, compound type, and a partial projection
in the other direction.  If lenses describe the interaction of modifications and reads of deeply-nested
fields within a record or product-like type, then prisms describe the interactions of modifications
and reads of deeply-nested fields within a sum-like type, such as a disjoint union.

Mathematically, one can think of prisms as \<^emph>\<open>subsets/embeddings\<close>.\<close>
datatype_record ('s, 'a) prism =
  prism_embed :: \<open>'a \<Rightarrow> 's\<close>
  prism_project :: \<open>'s \<Rightarrow> 'a option\<close>

text \<open>Like lenses, prisms also have a notion of \<^emph>\<open>validity\<close> that governs how their operations
interact.  Specifically:
\begin{itemize*}
\item
Embedding a field into a sum-like type and then immediately projecting it back out again
successfully returns the embedded field,
\item
If projecting a field out of a sum-like type is successful then embedding that projected-out value
into the sum-like type has no effect.
\end{itemize*}\<close>
definition is_valid_prism :: \<open>('s, 'a) prism \<Rightarrow> bool\<close> where
  \<open>is_valid_prism p \<longleftrightarrow>
     (\<forall>a. prism_project p (prism_embed p a) = Some a) \<and>
     (\<forall>s a. (prism_project p) s = Some a \<longrightarrow> s = (prism_embed p) a)\<close>

lemma prism_laws:
  assumes \<open>is_valid_prism p\<close>
  shows [focus_simps]: \<open>prism_project p (prism_embed p a) = Some a\<close>
    and \<open>prism_project p s = Some a \<longleftrightarrow> s = prism_embed p a\<close>
  using assms unfolding is_valid_prism_def by auto

definition prism_dom :: \<open>('a, 'b) prism \<Rightarrow> 'a set\<close> where
  \<open>prism_dom p \<equiv> dom (prism_project p)\<close>

lemma prism_dom_alt: 
  assumes \<open>is_valid_prism p\<close>
  shows \<open>prism_dom p = prism_embed p ` UNIV\<close>
  using assms by (auto simp add: is_valid_prism_def image_def prism_dom_def)

lemma prism_dom_alt': 
  assumes \<open>is_valid_prism p\<close>
  shows \<open>prism_embed p x \<in> prism_dom p\<close>
  using assms by (simp add: prism_dom_alt)

lemma prism_domI:
  assumes \<open>prism_project p x \<noteq> None\<close>
    shows \<open>x \<in> prism_dom p\<close>
  using assms unfolding prism_dom_def by auto

lemma prism_domI':
  assumes \<open>is_valid_prism p\<close>
     and \<open>x = prism_embed p y\<close>
   shows \<open>x \<in> prism_dom p\<close>
  using assms by (simp add: prism_dom_alt)

lemma prism_domE:
  assumes \<open>x \<in> prism_dom p\<close>
      and \<open>prism_project p x \<noteq> None \<Longrightarrow> R\<close>
    shows R
  using assms prism_dom_def by fastforce

lemma prism_domE':
  assumes \<open>x \<in> prism_dom p\<close>
      and \<open>is_valid_prism p\<close>
      and \<open>\<And>y. x = prism_embed p y \<Longrightarrow> R\<close>
    shows R
  using assms prism_dom_alt by fastforce

definition prism_compose :: \<open>('a, 'b) prism \<Rightarrow> ('b, 'c) prism \<Rightarrow> ('a, 'c) prism\<close> (infixr "\<diamondop>\<^sub>p" 59)
  where \<open>prism_compose pA pB \<equiv>
    make_prism ((prism_embed pA) \<circ> (prism_embed pB))
                (\<lambda>x. Option.bind (prism_project pA x) (prism_project pB))\<close>

lemma prism_compose_valid:
  assumes \<open>is_valid_prism pA\<close>
      and \<open>is_valid_prism pB\<close>
    shows \<open>is_valid_prism (pA \<diamondop>\<^sub>p pB)\<close>
  using assms by (auto simp add: is_valid_prism_def prism_compose_def bind_eq_Some_conv
    split:option.splits)

text\<open>Prisms are preserved under the \<^verbatim>\<open>option\<close> type constructor:\<close>

definition option_prism :: \<open>('c, 'a option) prism \<Rightarrow> ('a, 'b) prism \<Rightarrow> ('c, 'b option) prism\<close>
  where
  \<open>option_prism rawp elp \<equiv>
    make_prism (\<lambda>x. prism_embed rawp (map_option (prism_embed elp) x))
               (\<lambda>g. Option.bind (prism_project rawp g)
                      (\<lambda>x. case x of None \<Rightarrow> Some None | Some v \<Rightarrow> Option.bind (prism_project elp v) (\<lambda>v'. Some (Some v'))))\<close>

lemma option_prism_valid [focus_intros]:
  assumes
    \<open>is_valid_prism rawp\<close>
    \<open>is_valid_prism elp\<close>
  shows
    \<open>is_valid_prism (option_prism rawp elp)\<close>
  using assms unfolding is_valid_prism_def option_prism_def
  by (auto split: option.splits Option.bind_split)

fun list_option_distrib :: \<open>'a option list \<Rightarrow> 'a list option\<close> where
  \<open>list_option_distrib [] = Some []\<close> |
  \<open>list_option_distrib (None#l) = None\<close> |
  \<open>list_option_distrib (Some x#l) = Option.bind (list_option_distrib l) (\<lambda>l'. Some (x#l'))\<close>

text\<open>Prisms are preserved under the \<^verbatim>\<open>option\<close> type constructor:\<close>

definition list_prism :: \<open>('c, 'a list) prism \<Rightarrow> ('a, 'b) prism \<Rightarrow> ('c, 'b list) prism\<close>
  where
  \<open>list_prism lp elp \<equiv>
     make_prism (\<lambda>l. prism_embed lp (List.map (prism_embed elp) l))
                (\<lambda>g. Option.bind (prism_project lp g) (\<lambda>l. list_option_distrib (List.map (prism_project elp) l)))\<close>

lemma list_option_distrib_Some:
  \<open>list_option_distrib xs = Some ys \<longleftrightarrow> xs = list.map Some ys\<close>
  apply (induction xs arbitrary: ys, auto split: Option.bind_split)
  apply (case_tac a; simp?)
  apply (case_tac \<open>list_option_distrib xs\<close>; clarsimp)
  apply fast
  done

corollary list_option_distrib_map_Some:
  \<open>list_option_distrib (list.map Some xs) = Some xs\<close>
  using list_option_distrib_Some by auto

lemma list_option_distrib_None:
  \<open>list_option_distrib xs = None \<longleftrightarrow> None\<in>set xs\<close>
  apply (induction xs, auto)
  apply (case_tac a; simp)
  apply (case_tac a; simp)
  done

lemma list_prism_valid [focus_intros]:
  assumes
    \<open>is_valid_prism lp\<close>
    \<open>is_valid_prism elp\<close>
  shows
    \<open>is_valid_prism (list_prism lp elp)\<close>
proof -
  have \<open>prism_project elp \<circ> prism_embed elp = Some\<close>
    using assms unfolding is_valid_prism_def comp_def by auto
  moreover {
    fix v a
    have \<open>list.map (prism_project elp) v = list.map Some a \<Longrightarrow> v = list.map (prism_embed elp) a\<close>
    using assms unfolding is_valid_prism_def by (induction v arbitrary: a; clarsimp)
  }
  then show ?thesis
    using assms unfolding is_valid_prism_def list_prism_def
    by (auto simp add: list_option_distrib_Some split: Option.bind_split)
qed

text\<open>Isomorphisms are special cases of prisms:\<close>

text\<open>The following builds a prism out of a pair of mutually inverse bijections:\<close>
definition iso_prism :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) prism\<close>
  where \<open>iso_prism f g \<equiv> make_prism g (Some \<circ> f)\<close>

lemma iso_prism_valid:
  assumes \<open>\<And>x. f (g x) = x\<close>
      and \<open>\<And>y. g (f y) = y\<close>
  shows \<open>is_valid_prism (iso_prism f g)\<close>
  using assms by (auto simp add: iso_prism_def is_valid_prism_def)

(*<*)
end
(*>*)
