(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Graph
  imports
    FSet_Ref
    Stack
begin

section\<open>Finite Simple Directed Graphs\<close>

record 'a graph =
  V :: \<open>'a set\<close>
  E :: \<open>('a \<times> 'a) set\<close>

locale finite_directed_graph =
  fixes G :: \<open>'a graph\<close>
  assumes finite_V: \<open>finite (V G)\<close>
      and edges_in_V: \<open>E G \<subseteq> V G \<times> V G\<close>
begin

subsection\<open>Notation and basic definitions\<close>

lemma finite_E: \<open>finite (E G)\<close>
  using finite_V edges_in_V by (auto intro: finite_subset)

abbreviation edge :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<rightarrow>\<^sub>G\<close> 50) where
  \<open>u \<rightarrow>\<^sub>G v \<equiv> (u,v) \<in> E G\<close>

abbreviation reaches :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<rightarrow>\<^sub>G\<^sup>*\<close> 50) where
  \<open>u \<rightarrow>\<^sub>G\<^sup>* v \<equiv> (u,v) \<in> (E G)\<^sup>*\<close>

abbreviation reachable :: \<open>'a \<Rightarrow> 'a set\<close> where
  \<open>reachable v \<equiv> (E G)\<^sup>* `` {v}\<close>

abbreviation neighbours_of :: \<open>'a set \<Rightarrow> 'a set\<close> where
  \<open>neighbours_of Vs \<equiv> E G `` Vs\<close>

definition edges_from_vertex :: \<open>'a \<Rightarrow> ('a \<times> 'a) set\<close> where
  \<open>edges_from_vertex v \<equiv> {(v, w) | w. (v, w) \<in> E G}\<close>

definition edges_from_set :: \<open>'a set \<Rightarrow> ('a \<times> 'a) set\<close> where
  \<open>edges_from_set U \<equiv> (\<Union>v\<in>U. edges_from_vertex v)\<close>

\<comment> \<open>Neighbours of v as a list, so DFS can iterate over them.\<close>
definition neighbours :: \<open>'a \<Rightarrow> 'a list\<close> where
  \<open>neighbours v \<equiv> SOME xs. set xs = {w. v \<rightarrow>\<^sub>G w} \<and> distinct xs\<close>

subsection\<open>Reachability and closed sets\<close>

lemma reachable_subset_V:
  assumes \<open>v \<in> V G\<close>
  shows \<open>reachable v \<subseteq> V G\<close>
  using edges_in_V assms Image_closed_trancl[of \<open>E G\<close> \<open>V G\<close>] by blast

lemma reachable_fixpoint:
  assumes \<open>v \<in> Vs\<close>
      and \<open>Vs \<subseteq> reachable v\<close>
      and \<open>neighbours_of Vs \<subseteq> Vs\<close>
  shows \<open>Vs = reachable v\<close>
proof -
  have \<open>v \<rightarrow>\<^sub>G\<^sup>* x \<Longrightarrow> x \<in> Vs\<close> for x
    by (induction rule: rtrancl_induct) (use assms(1,3) in blast)+
  thus ?thesis using assms(2) by blast
qed

corollary reachable_fixpoint_mem:
  assumes \<open>v \<in> Vs\<close>
      and \<open>Vs \<subseteq> reachable v\<close>
      and \<open>neighbours_of Vs \<subseteq> Vs\<close>
      and \<open>v \<rightarrow>\<^sub>G\<^sup>* x\<close>
  shows \<open>x \<in> Vs\<close>
  using reachable_fixpoint[OF assms(1-3)] assms(4) by simp

subsection\<open>Edge counting\<close>

lemma edges_from_set_subset_E: \<open>edges_from_set U \<subseteq> E G\<close>
  by (auto simp: edges_from_set_def edges_from_vertex_def)

lemma finite_edges_from_set: \<open>finite (edges_from_set U)\<close>
  using edges_from_set_subset_E finite_E by (rule finite_subset)

lemma card_edges_from_vertex:
  \<open>card (edges_from_vertex v) = card {w. v \<rightarrow>\<^sub>G w}\<close>
proof -
  have \<open>edges_from_vertex v = (\<lambda>w. (v,w)) ` {w. v \<rightarrow>\<^sub>G w}\<close>
    by (auto simp: edges_from_vertex_def)
  thus ?thesis by (simp add: card_image inj_on_def)
qed

lemma card_edges_from_set_split:
  assumes \<open>v \<in> U\<close>
  shows \<open>card (edges_from_set U)
       = card (edges_from_set (U - {v})) + card {w. v \<rightarrow>\<^sub>G w}\<close>
proof -
  have split: \<open>edges_from_set U = edges_from_set (U - {v}) \<union> edges_from_vertex v\<close>
    using assms by (auto simp: edges_from_set_def)
  have disj: \<open>edges_from_set (U - {v}) \<inter> edges_from_vertex v = {}\<close>
    by (auto simp: edges_from_set_def edges_from_vertex_def)
  have fin2: \<open>finite (edges_from_vertex v)\<close>
    using finite_E edges_from_set_subset_E[of \<open>{v}\<close>]
    by (auto simp: edges_from_set_def intro: finite_subset)
  show ?thesis
    using split disj finite_edges_from_set fin2
    by (simp add: card_Un_disjoint card_edges_from_vertex)
qed

lemma neighbours_correct:
  shows \<open>set (neighbours v) = {w. v \<rightarrow>\<^sub>G w}\<close>
    and \<open>distinct (neighbours v)\<close>
proof -
  have \<open>{w. v \<rightarrow>\<^sub>G w} = E G `` {v}\<close> by auto
  then have \<open>finite {w. v \<rightarrow>\<^sub>G w}\<close> using finite_E by (auto intro: finite_Image)
  then obtain xs where \<open>set xs = {w. v \<rightarrow>\<^sub>G w} \<and> distinct xs\<close>
    using finite_distinct_list by blast
  thus \<open>set (neighbours v) = {w. v \<rightarrow>\<^sub>G w}\<close> and \<open>distinct (neighbours v)\<close>
    unfolding neighbours_def by (metis (mono_tags, lifting) someI_ex)+
qed

lemma length_neighbours:
  \<open>length (neighbours v) = card {w. v \<rightarrow>\<^sub>G w}\<close>
  using distinct_card[OF neighbours_correct(2)] neighbours_correct(1) by simp

end

section\<open>Depth-First Search\<close>

locale dfs =
    fset_ref _ _ _ _ _ _ _ reference_types fset_prism
  + stack
      where ll_focus = \<open>prism_to_focus node_prism'\<close>
        and node_prism = node_prism'
        and reference_types = reference_types
  + finite_directed_graph G
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
    and fset_prism :: \<open>('gv, 'a fset) prism\<close>
    and node_prism' :: \<open>('gv, ('addr, 'gv, 'a) ll_node_raw) prism\<close>
    and G :: \<open>'a graph\<close>
begin

definition remaining_work :: \<open>'a \<Rightarrow> 'a fset \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>remaining_work s0 Vis Fr \<equiv> length Fr + 2 * card (edges_from_set (reachable s0 - fset Vis))\<close>

definition fuel_bound :: \<open>'a \<Rightarrow> nat\<close> where
  \<open>fuel_bound s0 \<equiv> remaining_work s0 {||} [s0] + 1\<close>

\<comment> \<open>Vertices DFS has seen so far: visited plus pending on the frontier.\<close>
abbreviation seen :: \<open>'a fset \<Rightarrow> 'a list \<Rightarrow> 'a set\<close> where
  \<open>seen Vis Fr \<equiv> fset Vis \<union> set Fr\<close>

definition dfs where
  \<open>dfs (s0::'a) \<equiv> FunctionBody \<lbrakk>
     let mut visited = \<llangle>{||} :: 'a fset\<rrangle>;
     let frontier = empty();
     push(frontier, s0);

     #[fuel(\<epsilon>\<open>fuel_bound s0\<close>)] while let Some(v) = pop(frontier) {
       if !contains(visited, v) {
         fset_insert(visited, v);
         push_all(frontier, \<llangle>neighbours v\<rrangle>);
       }
     };

     *visited
   \<rbrakk>\<close>

definition dfs_contract where
  \<open>dfs_contract s0 \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>s0 \<in> V G\<rangle>)
       (\<lambda>ret. \<langle>fset ret = reachable s0\<rangle> \<star> can_alloc_reference)\<close>
ucincl_auto dfs_contract

abbreviation dfs_inv where
  \<open>dfs_inv s0 visited frontier k \<equiv>
     \<Squnion>Vis Fr.
       fset_points_to Vis visited \<star> stack_points_to Fr frontier
     \<star> can_alloc_reference
     \<star> \<langle>seen Vis Fr \<subseteq> reachable s0\<rangle>
     \<star> \<langle>neighbours_of (fset Vis) \<subseteq> seen Vis Fr\<rangle>
     \<star> \<langle>s0 \<in> seen Vis Fr\<rangle>
     \<star> \<langle>remaining_work s0 Vis Fr \<le> k\<rangle>\<close>

\<comment> \<open>One DFS body iteration strictly decreases \<^verbatim>\<open>remaining_work\<close>.\<close>
lemma remaining_work_decrease:
  shows stale: \<open>remaining_work s0 Vis W < remaining_work s0 Vis (v # W)\<close>
    and fresh: \<open>v \<notin> fset Vis \<Longrightarrow> v \<in> reachable s0
              \<Longrightarrow> remaining_work s0 (finsert v Vis) (rev (neighbours v) @ W)
                  < remaining_work s0 Vis (v # W)\<close>
proof -
  show \<open>remaining_work s0 Vis W < remaining_work s0 Vis (v # W)\<close>
    by (simp add: remaining_work_def)
next
  assume \<open>v \<notin> fset Vis\<close> and \<open>v \<in> reachable s0\<close>
  hence \<open>v \<in> reachable s0 - fset Vis\<close> by simp
  hence \<open>card (edges_from_set (reachable s0 - fset Vis))
       = card (edges_from_set (reachable s0 - fset Vis - {v})) + length (neighbours v)\<close>
    by (simp add: card_edges_from_set_split length_neighbours)
  moreover have \<open>reachable s0 - fset (finsert v Vis) = reachable s0 - fset Vis - {v}\<close>
    by auto
  ultimately show \<open>remaining_work s0 (finsert v Vis) (rev (neighbours v) @ W)
                 < remaining_work s0 Vis (v # W)\<close>
    unfolding remaining_work_def by simp
qed

\<comment> \<open>The invariant is preserved by one DFS iteration.\<close>
lemma dfs_inv_preserved:
  assumes seen_sub:   \<open>seen Vis (v#vs) \<subseteq> reachable s0\<close>
      and closure:    \<open>neighbours_of (fset Vis) \<subseteq> seen Vis (v#vs)\<close>
      and s0_in_seen: \<open>s0 \<in> seen Vis (v#vs)\<close>
      and s0_in_V:    \<open>s0 \<in> V G\<close>
  shows stale_inv: \<open>v \<in> fset Vis \<Longrightarrow>
          seen Vis vs \<subseteq> reachable s0
        \<and> neighbours_of (fset Vis) \<subseteq> seen Vis vs
        \<and> s0 \<in> seen Vis vs\<close>
    and fresh_inv: \<open>v \<notin> fset Vis \<Longrightarrow>
          seen (finsert v Vis) (rev (neighbours v) @ vs) \<subseteq> reachable s0
        \<and> neighbours_of (fset (finsert v Vis)) \<subseteq> seen (finsert v Vis) (rev (neighbours v) @ vs)
        \<and> s0 \<in> seen (finsert v Vis) (rev (neighbours v) @ vs)\<close>
proof -
  show \<open>v \<in> fset Vis \<Longrightarrow>
          seen Vis vs \<subseteq> reachable s0
        \<and> neighbours_of (fset Vis) \<subseteq> seen Vis vs
        \<and> s0 \<in> seen Vis vs\<close>
    using assms by auto
next
  assume \<open>v \<notin> fset Vis\<close>
  have \<open>set (neighbours v) \<subseteq> reachable s0\<close>
    using seen_sub reachable_subset_V[OF s0_in_V] neighbours_correct by force
  thus \<open>seen (finsert v Vis) (rev (neighbours v) @ vs) \<subseteq> reachable s0
      \<and> neighbours_of (fset (finsert v Vis)) \<subseteq> seen (finsert v Vis) (rev (neighbours v) @ vs)
      \<and> s0 \<in> seen (finsert v Vis) (rev (neighbours v) @ vs)\<close>
    using seen_sub closure s0_in_seen neighbours_correct
      reachable_subset_V[OF s0_in_V]
    by auto
qed

\<comment> \<open>Once visited is neighbor-closed, the frontier must be empty.\<close>
lemma remaining_work_exhausted:
  assumes \<open>fset Vis \<subseteq> reachable s0\<close>
      and \<open>neighbours_of (fset Vis) \<subseteq> fset Vis\<close>
      and \<open>s0 \<in> fset Vis\<close>
  shows \<open>remaining_work s0 Vis [] = 0\<close>
proof -
  have \<open>fset Vis = reachable s0\<close>
    using reachable_fixpoint[OF assms(3,1,2)] by simp
  thus ?thesis by (simp add: remaining_work_def edges_from_set_def)
qed

lemma remaining_work_Suc:
  shows stale_Suc: \<open>remaining_work s0 Vis (v # W) \<le> Suc k \<Longrightarrow> remaining_work s0 Vis W \<le> k\<close>
    and fresh_Suc: \<open>v \<notin> fset Vis \<Longrightarrow> v \<in> reachable s0
              \<Longrightarrow> remaining_work s0 Vis (v # W) \<le> Suc k
              \<Longrightarrow> remaining_work s0 (finsert v Vis) (rev (neighbours v) @ W) \<le> k\<close>
proof -
  show \<open>remaining_work s0 Vis (v # W) \<le> Suc k \<Longrightarrow> remaining_work s0 Vis W \<le> k\<close>
    using remaining_work_decrease(1)[of s0 Vis W v] by linarith
  show \<open>v \<notin> fset Vis \<Longrightarrow> v \<in> reachable s0
    \<Longrightarrow> remaining_work s0 Vis (v # W) \<le> Suc k
    \<Longrightarrow> remaining_work s0 (finsert v Vis) (rev (neighbours v) @ W) \<le> k\<close>
    using remaining_work_decrease(2)[of v Vis s0 W] by linarith
qed

lemma dfs_spec:
  shows \<open>\<Gamma>; dfs s0 \<Turnstile>\<^sub>F dfs_contract s0\<close>
  apply (crush_boot f: dfs_def contract: dfs_contract_def)
  apply crush_base
  subgoal for visited_ref frontier_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV  = \<open>\<lambda>k. dfs_inv s0 visited_ref frontier_ref k\<close> and
        INV' = \<open>\<lambda>k. dfs_inv s0 visited_ref frontier_ref k\<close> and
        \<tau>    = \<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>    = \<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI
    \<close>)
    \<comment> \<open>entry: \<^verbatim>\<open>fuel_bound\<close> slots suffice\<close>
    subgoal
      apply (crush_base simp add: fuel_bound_def remaining_work_def)
      by (meson reachable_fixpoint_mem fset_rev_mp)
    \<comment> \<open>loop body: pop, contains, insert and push\<close>
    subgoal
      apply crush_base
      apply (crush_base split!: list.splits option.splits
             simp add: remaining_work_exhausted)
      apply (auto intro: remaining_work_Suc dfs_inv_preserved
                  dest: reachable_subset_V[THEN subsetD]
                  simp add: neighbours_correct)
      done
    \<comment> \<open>*visited\<close>
    subgoal by crush_base
    done
  done

end

end
