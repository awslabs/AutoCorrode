(* Original Copyright (c) 1986-2023,
            University of Cambridge,
            Technische Universitaet Muenchen,
            and contributors
   under the ISABELLE COPYRIGHT LICENSE

   Modifications Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *)

(*
  This theory is mostly a copy of the contents of the Tree, Braun_Tree
  and Array_Braun theories from the Isabelle standard library.

  We have made minor modifications in order to avoid pulling in the
  Main_Complex theory and its attendant dependencies, and have removed
  some aspects that are not useful for our use case. We have also renamed
  some operations and removed some syntax notations that conflict with other
  notions already established in our development.
*)

theory BraunTrees
  imports Main
begin

section\<open>Generic tree material\<close>

datatype 'a tree
  = Leaf
  | Node \<open>'a tree\<close> (tree_value: 'a) \<open>'a tree\<close>

fun tree_left :: \<open>'a tree \<Rightarrow> 'a tree\<close> where
  \<open>tree_left (Node l v r) = l\<close> |
  \<open>tree_left Leaf         = Leaf\<close>

fun tree_right :: \<open>'a tree \<Rightarrow> 'a tree\<close> where
  \<open>tree_right (Node l v r) = r\<close> |
  \<open>tree_right Leaf         = Leaf\<close>

text\<open>Counting the number of leaves rather than nodes:\<close>

fun size1 :: \<open>'a tree \<Rightarrow> nat\<close> where
  \<open>size1 Leaf         = 1\<close> |
  \<open>size1 (Node l x r) = size1 l + size1 r\<close>

fun subtrees :: \<open>'a tree \<Rightarrow> 'a tree set\<close> where
  \<open>subtrees Leaf         = {Leaf}\<close> |
  \<open>subtrees (Node l a r) = {(Node l a r)} \<union> subtrees l \<union> subtrees r\<close>

class height =
fixes height :: \<open>'a \<Rightarrow> nat\<close>

instantiation tree :: (type)height
begin

fun height_tree :: \<open>'a tree \<Rightarrow> nat\<close> where
  \<open>height Leaf         = 0\<close> |
  \<open>height (Node l a r) = 1 + max (height l) (height r)\<close>

instance ..

end

fun min_height :: \<open>'a tree \<Rightarrow> nat\<close> where
  \<open>min_height Leaf         = 0\<close> |
  \<open>min_height (Node l _ r) = 1 + min (min_height l) (min_height r)\<close>

fun complete :: \<open>'a tree \<Rightarrow> bool\<close> where
  \<open>complete Leaf         = True\<close> |
  \<open>complete (Node l x r) = (height l = height r \<and> complete l \<and> complete r)\<close>

text \<open>Almost complete:\<close>
definition acomplete :: \<open>'a tree \<Rightarrow> bool\<close> where
  \<open>acomplete t \<equiv> height t - min_height t \<le> 1\<close>

text \<open>Weight balanced:\<close>
fun wbalanced :: \<open>'a tree \<Rightarrow> bool\<close> where
  \<open>wbalanced Leaf         = True\<close> |
  \<open>wbalanced (Node l x r) = (abs(int(size l) - int(size r)) \<le> 1 \<and> wbalanced l \<and> wbalanced r)\<close>

text \<open>Internal path length:\<close>
fun ipl :: \<open>'a tree \<Rightarrow> nat\<close> where
  \<open>ipl Leaf         = 0\<close> |
  \<open>ipl (Node l _ r) = ipl l + size l + ipl r + size r\<close>

fun preorder :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>preorder Leaf = []\<close> |
  \<open>preorder (Node l x r) = x # preorder l @ preorder r\<close>

fun inorder :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>inorder Leaf         = []\<close> |
  \<open>inorder (Node l x r) = inorder l @ [x] @ inorder r\<close>

text\<open>A linear version avoiding append:\<close>
fun inorder2 :: \<open>'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>inorder2 Leaf xs         = xs\<close> |
  \<open>inorder2 (Node l x r) xs = inorder2 l (x # inorder2 r xs)\<close>

fun postorder :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>postorder Leaf         = []\<close> |
  \<open>postorder (Node l x r) = postorder l @ postorder r @ [x]\<close>

text\<open>Binary Search Tree:\<close>
fun bst_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool\<close> where
  \<open>bst_wrt P Leaf         \<longleftrightarrow> True\<close> |
  \<open>bst_wrt P (Node l a r) \<longleftrightarrow> (\<forall>x\<in>set_tree l. P x a) \<and> (\<forall>x\<in>set_tree r. P a x) \<and> bst_wrt P l \<and> bst_wrt P r\<close>

abbreviation bst :: \<open>'a::{linorder} tree \<Rightarrow> bool\<close> where
  \<open>bst \<equiv> bst_wrt (<)\<close>

fun heap :: \<open>'a::{linorder} tree \<Rightarrow> bool\<close> where
  \<open>heap Leaf         = True\<close> |
  \<open>heap (Node l m r) = ((\<forall>x\<in>set_tree l \<union> set_tree r. m \<le> x) \<and> heap l \<and> heap r)\<close>

subsection \<open>\<^const>\<open>map_tree\<close>\<close>

lemma eq_map_tree_Leaf [simp]:
  shows \<open>map_tree f t = Leaf \<longleftrightarrow> t = Leaf\<close>
by (metis tree.distinct(1) tree.inj_map_strong tree.set_cases tree.simps(8))

lemma eq_Leaf_map_tree [simp]:
  shows \<open>Leaf = map_tree f t \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

subsection \<open>\<^const>\<open>size\<close>\<close>

lemma size1_size:
  shows \<open>size1 t = 1 + size t\<close>
by (induction t) auto

lemma size1_ge0 [simp]:
  \<open>0 < size1 t\<close>
by (simp add: size1_size)

lemma eq_size_0 [simp]:
  shows \<open>size t = 0 \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma eq_0_size [simp]:
  shows \<open>0 = size t \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma neq_Leaf_iff:
  shows \<open>(t \<noteq> Leaf) \<longleftrightarrow> (\<exists>l a r. t = Node l a r)\<close>
by (cases t) auto

lemma size_map_tree [simp]:
  shows \<open>size (map_tree f t) = size t\<close>
by (induction t) auto

lemma size1_map_tree [simp]:
  shows \<open>size1 (map_tree f t) = size1 t\<close>
by (simp add: size1_size)

subsection \<open>\<^const>\<open>set_tree\<close>\<close>

lemma eq_set_tree_empty [simp]:
  shows \<open>set_tree t = {} \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma eq_empty_set_tree [simp]:
  shows \<open>{} = set_tree t \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma finite_set_tree [simp]:
  shows \<open>finite (set_tree t)\<close>
by (induction t) auto

subsection \<open>\<^const>\<open>subtrees\<close>\<close>

lemma neq_subtrees_empty [simp]:
  shows \<open>subtrees t \<noteq> {}\<close>
by (cases t) auto

lemma neq_empty_subtrees [simp]:
  shows \<open>{} \<noteq> subtrees t\<close>
by (cases t) auto

lemma size_subtrees:
  assumes \<open>s \<in> subtrees t\<close>
    shows \<open>size s \<le> size t\<close>
using assms by(induction t) auto

lemma set_treeE:
  assumes \<open>a \<in> set_tree t\<close>
    shows \<open>\<exists>l r. (Node l a r) \<in> subtrees t\<close>
using assms by (induction t) auto

lemma Node_notin_subtrees_if [simp]:
  assumes \<open>a \<notin> set_tree t\<close>
    shows \<open>Node l a r \<notin> subtrees t\<close>
using assms by (induction t) auto

lemma in_set_tree_if:
  assumes \<open>Node l a r \<in> subtrees t\<close>
    shows \<open>a \<in> set_tree t\<close>
using assms by (metis Node_notin_subtrees_if)

subsection \<open>\<^const>\<open>height\<close> and \<^const>\<open>min_height\<close>\<close>

lemma eq_height_0 [simp]:
  assumes \<open>height t = 0\<close>
    shows \<open>t = Leaf\<close>
using assms by (cases t) auto

lemma eq_0_height [simp]:
  shows \<open>0 = height t \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma height_map_tree [simp]:
  shows \<open>height (map_tree f t) = height t\<close>
by (induction t) auto

lemma height_le_size_tree:
  fixes t :: \<open>'a tree\<close>
  shows \<open>height t \<le> size t\<close>
by (induction t) auto

lemma size1_height:
  fixes t :: \<open>'a tree\<close>
  shows \<open>size1 t \<le> 2 ^ height t\<close>
proof (induction t)
  show \<open>size1 Leaf \<le> 2 ^ height Leaf\<close>
    by simp
next case (Node l a r)
  show ?case
  proof (cases \<open>height l \<le> height r\<close>)
    case True
    have \<open>size1(Node l a r) = size1 l + size1 r\<close>
      by simp
    also have \<open>\<dots> \<le> 2 ^ height l + 2 ^ height r\<close>
      using Node.IH by arith
    also have \<open>\<dots> \<le> 2 ^ height r + 2 ^ height r\<close>
      using True by simp
    also have \<open>\<dots> = 2 ^ height (Node l a r)\<close>
      using True by (auto simp: max_def mult_2)
    finally show ?thesis .
  next
    case False
    have \<open>size1(Node l a r) = size1 l + size1 r\<close>
      by simp
    also have \<open>\<dots> \<le> 2 ^ height l + 2 ^ height r\<close>
      using Node.IH by arith
    also have \<open>\<dots> \<le> 2 ^ height l + 2 ^ height l\<close>
      using False by simp
    finally show ?thesis using False
      by (auto simp: max_def mult_2)
  qed
qed

corollary size_height:
  fixes t :: \<open>'a tree\<close>
  shows \<open>size t \<le> 2 ^ height t - 1\<close>
using size1_height[of t, unfolded size1_size] by arith

lemma height_subtrees:
  assumes \<open>s \<in> subtrees t\<close>
    shows \<open>height s \<le> height t\<close>
using assms by (induction t) auto

lemma min_height_le_height:
  shows \<open>min_height t \<le> height t\<close>
by (induction t) auto

lemma min_height_map_tree [simp]:
  shows \<open>min_height (map_tree f t) = min_height t\<close>
by (induction t) auto

lemma min_height_size1:
  shows \<open>2 ^ min_height t \<le> size1 t\<close>
proof (induction t)
  show \<open>2 ^ min_height Leaf \<le> size1 Leaf\<close>
    by simp
next case (Node l a r)
  have \<open>(2::nat) ^ min_height (Node l a r) \<le> 2 ^ min_height l + 2 ^ min_height r\<close>
    by (simp add: min_def)
  also have \<open>\<dots> \<le> size1(Node l a r)\<close>
    using Node.IH by simp
  finally show ?case .
qed

subsection \<open>\<^const>\<open>complete\<close>\<close>

lemma complete_iff_height:
  shows \<open>complete t \<longleftrightarrow> (min_height t = height t)\<close>
proof (induction t)
  show \<open>complete Leaf \<longleftrightarrow> (min_height Leaf = height Leaf)\<close>
    by simp
next case (Node l a r)
  assume \<open>complete l = (min_height l = height l)\<close>
     and \<open>complete r = (min_height r = height r)\<close>
  moreover have \<open>complete (Node l a r) \<longleftrightarrow> (height l = height r \<and> complete l \<and> complete r)\<close>
    by simp
  moreover from calculation have \<open>\<dots> \<longleftrightarrow> (height l = height r) \<and> (min_height l = height l) \<and> (min_height r = height r)\<close>
    by simp
  ultimately show \<open>complete (Node l a r) = (min_height (Node l a r) = height (Node l a r))\<close>
    by (simp add: min_def max_def) (metis le_antisym le_trans min_height_le_height)
qed

lemma size1_if_complete:
  assumes \<open>complete t\<close>
    shows \<open>size1 t = 2 ^ height t\<close>
using assms by (induction t) auto

lemma size_if_complete:
  assumes \<open>complete t\<close>
    shows \<open>size t = 2 ^ height t - 1\<close>
using assms size1_if_complete[simplified size1_size] by fastforce

lemma size1_height_if_incomplete:
  assumes \<open>\<not> complete t\<close>
    shows \<open>size1 t < 2 ^ height t\<close>
using assms proof (induction t)
  assume \<open>\<not> complete Leaf\<close>
  from this have \<open>False\<close>
    by simp
  from this show \<open>size1 Leaf < 2 ^ height Leaf\<close>
    by simp
next case (Node l x r)
  have 1: ?case if h: \<open>height l < height r\<close>
    using h size1_height[of l] size1_height[of r] power_strict_increasing[OF h, of \<open>2::nat\<close>]
    by (auto simp: max_def simp del: power_strict_increasing_iff)
  have 2: ?case if h: \<open>height l > height r\<close>
    using h size1_height[of l] size1_height[of r] power_strict_increasing[OF h, of \<open>2::nat\<close>]
    by (auto simp: max_def simp del: power_strict_increasing_iff)
  have 3: ?case if h: \<open>height l = height r\<close> and c: \<open>\<not> complete l\<close>
    using h size1_height[of r] Node.IH(1)[OF c] by simp
  have 4: ?case if h: \<open>height l = height r\<close> and c: \<open>\<not> complete r\<close>
    using h size1_height[of l] Node.IH(2)[OF c] by simp
  from 1 2 3 4 Node.prems show ?case
    by (simp add: max_def) linarith
qed

lemma complete_iff_min_height:
  shows \<open>complete t \<longleftrightarrow> (height t = min_height t)\<close>
by (auto simp add: complete_iff_height)

lemma min_height_size1_if_incomplete:
  assumes \<open>\<not> complete t\<close>
    shows \<open>2 ^ min_height t < size1 t\<close>
using assms proof(induction t)
  assume \<open>\<not> complete Leaf\<close>
  from this have \<open>False\<close>
    by simp
  from this show \<open>2 ^ min_height Leaf < size1 Leaf\<close>
    by simp
next case (Node l x r)
  have 1: ?case if h: \<open>min_height l < min_height r\<close>
    using h min_height_size1[of l] min_height_size1[of r] power_strict_increasing[OF h, of \<open>2::nat\<close>]
    by (auto simp: max_def simp del: power_strict_increasing_iff)
  have 2: ?case if h: \<open>min_height l > min_height r\<close>
    using h min_height_size1[of l] min_height_size1[of r] power_strict_increasing[OF h, of \<open>2::nat\<close>]
    by (auto simp: max_def simp del: power_strict_increasing_iff)
  have 3: ?case if h: \<open>min_height l = min_height r\<close> and c: \<open>\<not> complete l\<close>
    using h min_height_size1[of r] Node.IH(1)[OF c] by(simp add: complete_iff_min_height)
  have 4: ?case if h: \<open>min_height l = min_height r\<close> and c: \<open>\<not> complete r\<close>
    using h min_height_size1[of l] Node.IH(2)[OF c] by(simp add: complete_iff_min_height)
  from 1 2 3 4 Node.prems show ?case
    by (fastforce simp: complete_iff_min_height[THEN iffD1])
qed

lemma complete_if_size1_height:
  assumes \<open>size1 t = 2 ^ height t\<close>
    shows \<open>complete t\<close>
using assms size1_height_if_incomplete by fastforce

lemma complete_if_size1_min_height:
  assumes \<open>size1 t = 2 ^ min_height t\<close>
    shows \<open>complete t\<close>
using assms min_height_size1_if_incomplete by fastforce

lemma complete_iff_size1:
  shows \<open>complete t \<longleftrightarrow> size1 t = 2 ^ height t\<close>
using complete_if_size1_height size1_if_complete by blast

subsection \<open>\<^const>\<open>acomplete\<close>\<close>

lemma acomplete_subtreeL:
  assumes \<open>acomplete (Node l x r)\<close>
    shows \<open>acomplete l\<close>
using assms by (simp add: acomplete_def)

lemma acomplete_subtreeR:
  assumes \<open>acomplete (Node l x r)\<close>
    shows \<open>acomplete r\<close>
using assms by (simp add: acomplete_def)

lemma acomplete_subtrees:
  assumes \<open>acomplete t\<close>
      and \<open>s \<in> subtrees t\<close>
    shows \<open>acomplete s\<close>
using assms [[simp_depth_limit=1]] by (induction t arbitrary: s) (auto simp add: acomplete_subtreeL
  acomplete_subtreeR)

text\<open>Balanced trees have optimal height:\<close>
lemma acomplete_optimal:
    fixes t :: \<open>'a tree\<close>
      and t' :: \<open>'b tree\<close>
  assumes \<open>acomplete t\<close>
      and \<open>size t \<le> size t'\<close>
    shows \<open>height t \<le> height t'\<close>
proof (cases \<open>complete t\<close>)
  case True
  have \<open>(2::nat) ^ height t \<le> 2 ^ height t'\<close>
  proof -
    have \<open>2 ^ height t = size1 t\<close>
      using True by (simp add: size1_if_complete)
    also have \<open>\<dots> \<le> size1 t'\<close>
      using assms(2) by(simp add: size1_size)
    also have \<open>\<dots> \<le> 2 ^ height t'\<close>
      by (rule size1_height)
    finally show ?thesis .
  qed
  thus ?thesis
    by simp
next case False
  have \<open>(2::nat) ^ min_height t < 2 ^ height t'\<close>
  proof -
    have \<open>(2::nat) ^ min_height t < size1 t\<close>
      by (rule min_height_size1_if_incomplete[OF False])
    also have \<open>\<dots> \<le> size1 t'\<close>
      using assms(2) by (simp add: size1_size)
    also have \<open>\<dots> \<le> 2 ^ height t'\<close>
      by (rule size1_height)
    finally have \<open>(2::nat) ^ min_height t < (2::nat) ^ height t'\<close> .
    thus ?thesis .
  qed
  hence *: \<open>min_height t < height t'\<close>
    by simp
  have \<open>min_height t + 1 = height t\<close>
    using min_height_le_height[of t] assms(1) False by (simp add: complete_iff_height acomplete_def)
  with * show ?thesis
    by arith
qed

subsection \<open>\<^const>\<open>wbalanced\<close>\<close>

lemma wbalanced_subtrees:
  assumes \<open>wbalanced t\<close>
      and \<open>s \<in> subtrees t\<close>
    shows \<open>wbalanced s\<close>
using assms [[simp_depth_limit=1]] by (induction t arbitrary: s) auto

subsection \<open>\<^const>\<open>ipl\<close>\<close>

text \<open>The internal path length of a tree:\<close>

lemma ipl_if_complete_int:
  assumes \<open>complete t\<close>
    shows \<open>int (ipl t) = (int (height t) - 2) * 2^(height t) + 2\<close>
using assms proof(induction t)
  show \<open>int (ipl Leaf) = (int (height Leaf) - 2) * 2 ^ height Leaf + 2\<close>
    by simp
next case (Node l a r)
  assume \<open>complete l \<Longrightarrow> int (ipl l) = (int (height l) - 2) * 2 ^ height l + 2\<close>
     and \<open>complete r \<Longrightarrow> int (ipl r) = (int (height r) - 2) * 2 ^ height r + 2\<close>
     and \<open>complete (Node l a r)\<close>
  moreover from this have \<open>complete l\<close> and \<open>complete r\<close> and \<open>height l = height r\<close>
    by auto
  moreover from calculation have \<open>size l = 2 ^ height l - 1\<close> and \<open>size r = 2 ^ height r - 1\<close>
    using size_if_complete by blast+
  ultimately show \<open>int (ipl (Node l a r)) = (int (height (Node l a r)) - 2) * 2 ^ height (Node l a r) + 2\<close>
    using int_ops by (simp add: algebra_simps size_if_complete of_nat_diff)
qed

subsection \<open>List of entries\<close>

lemma eq_inorder_Nil[simp]:
  shows \<open>inorder t = [] \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma eq_Nil_inorder [simp]:
  shows \<open>[] = inorder t \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma set_inorder [simp]:
  shows \<open>set (inorder t) = set_tree t\<close>
by (induction t) auto

lemma set_preorder [simp]:
  shows \<open>set (preorder t) = set_tree t\<close>
by (induction t) auto

lemma set_postorder [simp]:
  shows \<open>set (postorder t) = set_tree t\<close>
by (induction t) auto

lemma length_preorder [simp]:
  shows \<open>length (preorder t) = size t\<close>
by (induction t) auto

lemma length_inorder [simp]:
  shows \<open>length (inorder t) = size t\<close>
by (induction t) auto

lemma length_postorder [simp]:
  \<open>length (postorder t) = size t\<close>
by (induction t) auto

lemma preorder_map:
  shows \<open>preorder (map_tree f t) = map f (preorder t)\<close>
by (induction t) auto

lemma inorder_map:
  shows \<open>inorder (map_tree f t) = map f (inorder t)\<close>
by (induction t) auto

lemma postorder_map:
  shows \<open>postorder (map_tree f t) = map f (postorder t)\<close>
by (induction t) auto

lemma inorder2_inorder:
  shows \<open>inorder2 t xs = inorder t @ xs\<close>
by (induction t arbitrary: xs) auto

subsection \<open>Binary Search Tree\<close>

lemma bst_wrt_mono:
  assumes \<open>\<And>x y. P x y \<Longrightarrow> Q x y\<close>
      and \<open>bst_wrt P t\<close>
    shows \<open>bst_wrt Q t\<close>
using assms by (induction t) (auto)

lemma bst_wrt_le_if_bst:
  assumes \<open>bst t\<close>
    shows \<open>bst_wrt (\<le>) t\<close>
using assms bst_wrt_mono less_imp_le by blast

lemma bst_wrt_le_iff_sorted:
  shows \<open>bst_wrt (\<le>) t \<longleftrightarrow> sorted (inorder t)\<close>
proof (induction t)
  show \<open>bst_wrt (\<le>) Leaf = sorted (inorder Leaf)\<close>
    by simp
next case (Node l a r)
  assume \<open>bst_wrt (\<le>) l \<longleftrightarrow> sorted (inorder l)\<close>
     and \<open>bst_wrt (\<le>) r \<longleftrightarrow> sorted (inorder r)\<close>
  from this show \<open>bst_wrt (\<le>) (Node l a r) \<longleftrightarrow> sorted (inorder (Node l a r))\<close>
    by (fastforce simp add: sorted_append intro: less_imp_le less_trans)
qed

lemma bst_iff_sorted_wrt_less:
  shows \<open>bst t \<longleftrightarrow> sorted_wrt (<) (inorder t)\<close>
proof (induction t)
  show  \<open>bst Leaf = sorted_wrt (<) (inorder Leaf)\<close>
    by simp
next case (Node l a r)
  assume \<open>bst l \<longleftrightarrow> sorted_wrt (<) (inorder l)\<close>
     and \<open>bst r \<longleftrightarrow> sorted_wrt (<) (inorder r)\<close>
  from this show \<open>bst (Node l a r) = sorted_wrt (<) (inorder (Node l a r))\<close>
    by (fastforce simp: sorted_wrt_append)
qed

section\<open>Braun trees\<close>

text \<open>Braun Trees were studied by Braun and Rem later Hoogerwoord:\<close>

fun braun :: \<open>'a tree \<Rightarrow> bool\<close> where
  \<open>braun Leaf         = True\<close> |
  \<open>braun (Node l x r) = ((size l = size r \<or> size l = size r + 1) \<and> braun l \<and> braun r)\<close>

lemma braun_Node':
  shows \<open>braun (Node l x r) \<longleftrightarrow> (size r \<le> size l \<and> size l \<le> size r + 1 \<and> braun l \<and> braun r)\<close>
by auto

text \<open>The shape of a Braun-tree is uniquely determined by its size:\<close>

lemma braun_unique:
    fixes t1 :: \<open>unit tree\<close>
  assumes \<open>braun t1\<close>
      and \<open>braun t2\<close>
      and \<open>size t1 = size t2\<close>
    shows \<open>t1 = t2\<close>
using assms proof (induction t1 arbitrary: t2)
  case Leaf
  thus ?case by simp
next
  case (Node l1 _ r1)
  from Node.prems(3) have \<open>t2 \<noteq> Leaf\<close>
    by auto
  then obtain l2 x2 r2 where [simp]: \<open>t2 = Node l2 x2 r2\<close>
    by (meson neq_Leaf_iff)
  with Node.prems have \<open>size l1 = size l2 \<and> size r1 = size r2\<close>
    by auto
  thus ?case
    using Node.prems(1,2) Node.IH by auto
qed

subsection \<open>Numbering Nodes\<close>

text \<open>We show that a tree is a Braun tree iff a parity-based
numbering (\<open>braun_indices\<close>) of nodes yields an interval of numbers.\<close>

fun braun_indices :: \<open>'a tree \<Rightarrow> nat set\<close> where
  \<open>braun_indices Leaf         = {}\<close> |
  \<open>braun_indices (Node l _ r) = {1} \<union> (*) 2 ` braun_indices l \<union> Suc ` (*) 2 ` braun_indices r\<close>

lemma braun_indices1:
  shows \<open>0 \<notin> braun_indices t\<close>
by (induction t) auto

lemma finite_braun_indices:
  shows \<open>finite (braun_indices t)\<close>
by (induction t) auto

text\<open>One direction:\<close>
lemma braun_indices_if_braun:
  assumes \<open>braun t\<close>
    shows \<open>braun_indices t = {1..size t}\<close>
using assms proof(induction t)
  case Leaf
  thus ?case
    by simp
next
  have *: \<open>(*) 2 ` {a..b} \<union> Suc ` (*) 2 ` {a..b} = {2*a..2*b+1}\<close> (is \<open>?l = ?r\<close>) for a b
  proof
    show \<open>?l \<subseteq> ?r\<close>
      by auto
  next
    have \<open>\<exists>x2\<in>{a..b}. x \<in> {Suc (2*x2), 2*x2}\<close> if *: \<open>x \<in> {2*a .. 2*b+1}\<close> for x
    proof -
      have \<open>x div 2 \<in> {a..b}\<close>
        using * by auto
      moreover have \<open>x \<in> {2 * (x div 2), Suc(2 * (x div 2))}\<close>
        by auto
      ultimately show ?thesis
        by blast
    qed
    thus \<open>?r \<subseteq> ?l\<close>
      by fastforce
  qed
  case (Node l x r)
  hence \<open>size l = size r \<or> size l = size r + 1\<close> (is \<open>?A \<or> ?B\<close>)
    by auto
  thus ?case
  proof
    assume ?A
    with Node show ?thesis by (auto simp: *)
  next
    assume ?B
    with Node show ?thesis by (auto simp: * atLeastAtMostSuc_conv)
  qed
qed

text \<open>The other direction is more complicated. The following proof is due to Thomas Sewell.\<close>

lemma disj_evens_odds:
  shows \<open>(*) 2 ` A \<inter> Suc ` (*) 2 ` B = {}\<close>
using double_not_eq_Suc_double by auto

lemma card_braun_indices:
  shows \<open>card (braun_indices t) = size t\<close>
proof (induction t)
  case Leaf thus ?case by simp
next
  case Node
  thus ?case
    by (auto simp: UNION_singleton_eq_range finite_braun_indices card_Un_disjoint
      card_insert_if disj_evens_odds card_image inj_on_def braun_indices1)
qed

lemma braun_indices_intvl_base_1:
  assumes bi: \<open>braun_indices t = {m..n}\<close>
    shows \<open>{m..n} = {1..size t}\<close>
proof (cases \<open>t = Leaf\<close>)
  case True
  then show ?thesis
    using bi by simp
next
  case False
  note eqs = eqset_imp_iff[OF bi]
  from eqs[of 0] have 0: \<open>0 < m\<close>
    by (simp add: braun_indices1)
  from eqs[of 1] have 1: \<open>m \<le> 1\<close>
    by (cases t; simp add: False)
  from 0 1 have eq1: \<open>m = 1\<close>
    by simp
  from card_braun_indices[of t] show ?thesis
    by (simp add: bi eq1)
qed

lemma even_of_intvl_intvl:
    fixes S :: \<open>nat set\<close>
  assumes \<open>S = {m..n} \<inter> {i. even i}\<close>
    shows \<open>\<exists>m' n'. S = (\<lambda>i. i * 2) ` {m'..n'}\<close>
proof -
  have \<open>S = (\<lambda>i. i * 2) ` {Suc m div 2..n div 2}\<close>
    by (fastforce simp add: assms mult.commute)
  from this show ?thesis
    by blast
qed

lemma odd_of_intvl_intvl:
    fixes S :: \<open>nat set\<close>
  assumes \<open>S = {m..n} \<inter> {i. odd i}\<close>
    shows \<open>\<exists>m' n'. S = Suc ` (\<lambda>i. i * 2) ` {m'..n'}\<close>
proof -
  have \<open>S = Suc ` ({(if n = 0 then 1 else m - 1)..n - 1} \<inter> {i. even i})\<close>
    by (auto simp: assms image_def elim!: oddE)
  from this have \<open>\<exists>m'. S = Suc ` ({m'..n - 1} \<inter> {i. even i})\<close>
    by blast
  from this show ?thesis
    by (metis even_of_intvl_intvl)
qed

lemma image_int_eq_image:
  shows \<open>(\<forall>i \<in> S. f i \<in> T) \<Longrightarrow> (f ` S) \<inter> T = f ` S\<close>
    and \<open>(\<forall>i \<in> S. f i \<notin> T) \<Longrightarrow> (f ` S) \<inter> T = {}\<close>
by auto

lemma braun_indices1_le:
  assumes \<open>i \<in> braun_indices t\<close>
    shows \<open>Suc 0 \<le> i\<close>
using assms braun_indices1 not_less_eq_eq by blast

lemma braun_if_braun_indices:
  assumes \<open>braun_indices t = {1..size t}\<close>
    shows \<open>braun t\<close>
using assms proof(induction t)
  case Leaf
  then show ?case
    by simp
next case (Node l x r)
  obtain t where t: \<open>t = Node l x r\<close>
    by simp
  from Node.prems have eq: \<open>{2 .. size t} = (\<lambda>i. i * 2) ` braun_indices l \<union> Suc ` (\<lambda>i. i * 2) ` braun_indices r\<close>
    (is \<open>?R = ?S \<union> ?T\<close>)
    apply clarsimp
    apply (drule_tac f=\<open>\<lambda>S. S \<inter> {2..}\<close> in arg_cong)
    apply (simp add: t mult.commute Int_Un_distrib2 image_int_eq_image braun_indices1_le)
    done
  then have ST: \<open>?S = ?R \<inter> {i. even i}\<close> \<open>?T = ?R \<inter> {i. odd i}\<close>
    by (simp_all add: Int_Un_distrib2 image_int_eq_image)
  from ST have l: \<open>braun_indices l = {1 .. size l}\<close>
    by (fastforce dest: braun_indices_intvl_base_1 dest!: even_of_intvl_intvl
      simp: mult.commute inj_image_eq_iff[OF inj_onI])
  from ST have r: \<open>braun_indices r = {1 .. size r}\<close>
    by (fastforce dest: braun_indices_intvl_base_1 dest!: odd_of_intvl_intvl
      simp: mult.commute inj_image_eq_iff[OF inj_onI])
  note STa = ST[THEN eqset_imp_iff, THEN iffD2]
  note STb = STa[of \<open>size t\<close>] STa[of \<open>size t - 1\<close>]
  then have sizes: \<open>size l = size r \<or> size l = size r + 1\<close>
    by (clarsimp simp: t l r inj_image_mem_iff[OF inj_onI]) (cases \<open>even (size l)\<close>;
      cases \<open>even (size r)\<close>; clarsimp elim!: oddE; fastforce)
  from l r sizes show ?case
    by (clarsimp simp: Node.IH)
qed

lemma braun_iff_braun_indices:
  shows \<open>braun t \<longleftrightarrow> braun_indices t = {1..size t}\<close>
using braun_if_braun_indices braun_indices_if_braun by blast

subsection\<open>Array\<close>

fun lookup1 :: \<open>'a tree \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>lookup1 (Node l x r) n =
     (if n=1 then x else lookup1 (if even n then l else r) (n div 2))\<close>

fun update1 :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>update1 n x Leaf         = Node Leaf x Leaf\<close> |
  \<open>update1 n x (Node l a r) =
     (if n = 1 then
        Node l x r
      else if even n then
        Node (update1 (n div 2) x l) a r
      else
        Node l a (update1 (n div 2) x r))\<close>

fun adds :: \<open>'a list \<Rightarrow> nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>adds []     n t = t\<close> |
  \<open>adds (x#xs) n t = adds xs (n+1) (update1 (n+1) x t)\<close>

fun braun_list :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>braun_list Leaf         = []\<close> |
  \<open>braun_list (Node l x r) = x # splice (braun_list l) (braun_list r)\<close>

subsubsection\<open>Functional Correctness\<close>

lemma size_list:
  shows \<open>size (braun_list t) = size t\<close>
by (induction t) auto

lemma minus1_div2:
  shows \<open>(n - Suc 0) div 2 = (if odd n then n div 2 else n div 2 - 1)\<close>
by auto arith

lemma nth_splice:
  assumes \<open>n < size xs + size ys\<close>
      and \<open>size ys \<le> size xs\<close>
      and \<open>size xs \<le> size ys + 1\<close>
    shows \<open>splice xs ys ! n = (if even n then xs else ys) ! (n div 2)\<close>
using assms proof (induction xs ys arbitrary: n rule: splice.induct)
     fix ys :: \<open>'a list\<close> and n
  assume \<open>n < length [] + length ys\<close>
     and \<open>length ys \<le> length []\<close>
  from this show \<open>splice [] ys ! n = (if even n then [] else ys) ! (n div 2)\<close>
    by simp
next
     fix x and xs ys :: \<open>'a list\<close> and n
  assume \<open>length ys \<le> length (x # xs)\<close>
     and \<open>length (x # xs) \<le> length ys + 1\<close>
     and \<open>n < length (x # xs) + length ys\<close>
     and \<open>\<And>n. n < length ys + length xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> length ys \<le> length xs + 1 \<Longrightarrow>
            splice ys xs ! n = (if even n then ys else xs) ! (n div 2)\<close>
  from this show \<open>splice (x # xs) ys ! n = (if even n then x # xs else ys) ! (n div 2)\<close>
    by (auto simp add: nth_Cons' minus1_div2)
qed

lemma div2_in_bounds:
  assumes \<open>braun (Node l x r)\<close>
      and \<open>n \<in> {1..size(Node l x r)}\<close>
      and \<open>n > 1\<close>
    shows \<open>(odd n \<longrightarrow> n div 2 \<in> {1..size r}) \<and> (even n \<longrightarrow> n div 2 \<in> {1..size l})\<close>
using assms by auto arith

paragraph \<open>\<^const>\<open>lookup1\<close>\<close>

lemma nth_list_lookup1:
  assumes \<open>braun t\<close>
      and \<open>i < size t\<close>
    shows \<open>braun_list t ! i = lookup1 t (i + 1)\<close>
using assms proof (induction t arbitrary: i)
  case Leaf
  thus ?case
    by simp
next
  case Node
  thus ?case using div2_in_bounds[OF Node.prems(1), of \<open>i+1\<close>]
    by (auto simp: nth_splice minus1_div2 size_list)
qed

lemma list_eq_map_lookup1:
  assumes \<open>braun t\<close>
    shows \<open>braun_list t = map (lookup1 t) [1..<size t + 1]\<close>
using assms by (auto simp add: list_eq_iff_nth_eq size_list nth_list_lookup1 simp del: upt_Suc)

paragraph \<open>\<^const>\<open>update1\<close>\<close>

lemma size_update1:
  assumes \<open>braun t\<close>
      and \<open>n \<in> {1.. size t}\<close>
    shows \<open>size (update1 n x t) = size t\<close>
using assms proof(induction t arbitrary: n)
  case Leaf
  thus ?case
    by simp
next
  case Node
  thus ?case
    using div2_in_bounds[OF Node.prems] by simp
qed

lemma braun_update1:
  assumes \<open>braun t\<close>
      and \<open>n \<in> {1.. size t}\<close>
    shows \<open>braun (update1 n x t)\<close>
using assms proof(induction t arbitrary: n)
  case Leaf
  thus ?case
    by simp
next
  case Node
  thus ?case
    using div2_in_bounds[OF Node.prems] by (simp add: size_update1)
qed

lemma lookup1_update1:
  assumes \<open>braun t\<close>
      and \<open>n \<in> {1.. size t}\<close>
    shows \<open>lookup1 (update1 n x t) m = (if n = m then x else lookup1 t m)\<close>
using assms proof (induction t arbitrary: m n)
  case Leaf
  then show ?case
    by simp
next
  case Node
  moreover have aux: \<open>odd n \<Longrightarrow> odd m  \<Longrightarrow> n div 2 = (m::nat) div 2 \<longleftrightarrow> m=n\<close> for m n
    using odd_two_times_div_two_succ by fastforce
  ultimately show ?case
    using div2_in_bounds[OF Node.prems] by (auto simp: aux)
qed

lemma list_update1:
  assumes \<open>braun t\<close>
      and \<open>n \<in> {1.. size t}\<close>
    shows \<open>braun_list (update1 n x t) = (braun_list t)[n-1 := x]\<close>
using assms by (auto simp add: list_eq_map_lookup1 list_eq_iff_nth_eq lookup1_update1 size_update1
  braun_update1 simp del: upt_Suc)

text\<open>A second proof of @{thm list_update1}:\<close>

lemma diff1_eq_iff:
  assumes \<open>n > 0\<close>
    shows \<open>n - Suc 0 = m \<longleftrightarrow> n = m+1\<close>
using assms by arith

lemma list_update_splice:
  assumes \<open>n < size xs + size ys\<close>
      and \<open>size ys \<le> size xs\<close>
      and \<open>size xs \<le> size ys + 1\<close>
    shows \<open>(splice xs ys)[n := x] =
              (if even n then splice (xs[n div 2 := x]) ys else splice xs (ys[n div 2 := x]))\<close>
using assms by (induction xs ys arbitrary: n rule: splice.induct) (auto split: nat.split)

lemma list_update2:
  assumes \<open>braun t\<close>
      and \<open>n \<in> {1.. size t}\<close>
    shows \<open>braun_list (update1 n x t) = (braun_list t)[n-1 := x]\<close>
using assms proof(induction t arbitrary: n)
  case Leaf
  thus ?case
    by simp
next case (Node l a r)
  thus ?case
    using div2_in_bounds[OF Node.prems] by(auto simp: list_update_splice diff1_eq_iff size_list
      split: nat.split)
qed

paragraph \<open>\<^const>\<open>adds\<close>\<close>

lemma splice_last:
  shows \<open>size ys \<le> size xs \<Longrightarrow> splice (xs @ [x]) ys = splice xs ys @ [x]\<close>
    and \<open>size ys+1 \<ge> size xs \<Longrightarrow> splice xs (ys @ [y]) = splice xs ys @ [y]\<close>
by (induction xs ys arbitrary: x y rule: splice.induct) auto

lemma list_add_hi:
  assumes \<open>braun t\<close>
    shows \<open>braun_list (update1 (Suc (size t)) x t) = braun_list t @ [x]\<close>
using assms by (induction t) (auto simp: splice_last size_list)

lemma size_add_hi:
  assumes \<open>braun t\<close>
      and \<open>m = size t\<close>
    shows \<open>size (update1 (Suc m) x t) = size t + 1\<close>
using assms by (induction t arbitrary: m) auto

lemma braun_add_hi:
  assumes \<open>braun t\<close>
    shows \<open>braun (update1 (Suc (size t)) x t)\<close>
using assms by(induction t) (auto simp: size_add_hi)

lemma size_braun_adds:
  assumes \<open>braun t\<close>
      and \<open>size t = n\<close>
    shows \<open>size (adds xs n t) = size t + length xs \<and> braun (adds xs n t)\<close>
using assms by(induction xs arbitrary: t n)(auto simp: braun_add_hi size_add_hi)

lemma list_adds:
  assumes \<open>braun t\<close>
      and \<open>size t = n\<close>
    shows \<open>braun_list (adds xs n t) = braun_list t @ xs\<close>
using assms by(induction xs arbitrary: t n) (auto simp: size_braun_adds list_add_hi size_add_hi
  braun_add_hi)

subsection\<open>Flexible Array\<close>

fun add_lo :: \<open>'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>add_lo x Leaf         = Node Leaf x Leaf\<close> |
  \<open>add_lo x (Node l a r) = Node (add_lo a r) x l\<close>

fun merge :: \<open>'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>merge Leaf r = r\<close> |
  \<open>merge (Node l a r) rr = Node rr a (merge l r)\<close>

fun del_lo :: \<open>'a tree \<Rightarrow> 'a tree\<close> where
  \<open>del_lo Leaf = Leaf\<close> |
  \<open>del_lo (Node l a r) = merge l r\<close>

fun del_hi :: \<open>nat \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>del_hi n Leaf         = Leaf\<close> |
  \<open>del_hi n (Node l x r) =
     (if n = 1 then
        Leaf
      else if even n then
        Node (del_hi (n div 2) l) x r
      else
        Node l x (del_hi (n div 2) r))\<close>

subsection\<open>Functional Correctness\<close>

paragraph \<open>\<^const>\<open>add_lo\<close>\<close>

lemma list_add_lo:
  assumes \<open>braun t\<close>
    shows \<open>braun_list (add_lo a t) = a # braun_list t\<close>
using assms by (induction t arbitrary: a) auto

lemma braun_add_lo:
  assumes \<open>braun t\<close>
    shows \<open>braun (add_lo x t)\<close>
using assms by (induction t arbitrary: x) (auto simp add: list_add_lo simp flip: size_list)

paragraph \<open>\<^const>\<open>del_lo\<close>\<close>

lemma list_merge:
  shows \<open>braun_list (merge l r) = splice (braun_list l) (braun_list r)\<close>
by (induction l r rule: merge.induct) auto

lemma braun_merge:
  assumes \<open>braun (Node l x r)\<close>
    shows \<open>braun(merge l r)\<close>
using assms by (induction l r rule: merge.induct) (auto simp add: list_merge simp flip: size_list)

lemma list_del_lo:
  assumes \<open>braun t\<close>
    shows \<open>braun_list(del_lo t) = tl (braun_list t)\<close>
by (cases t) (auto simp add: list_merge)

lemma braun_del_lo:
  assumes \<open>braun t\<close>
    shows \<open>braun(del_lo t)\<close>
using assms by (cases t) (auto simp add: braun_merge)

paragraph \<open>\<^const>\<open>del_hi\<close>\<close>

lemma list_Nil_iff:
  shows \<open>braun_list t = [] \<longleftrightarrow> t = Leaf\<close>
by (cases t) auto

lemma butlast_splice:
  shows \<open>butlast (splice xs ys) =
            (if size xs > size ys then splice (butlast xs) ys else splice xs (butlast ys))\<close>
by (induction xs ys rule: splice.induct) auto

lemma list_del_hi:
  assumes \<open>braun t\<close>
      and \<open>size t = st\<close>
    shows \<open>braun_list (del_hi st t) = butlast (braun_list t)\<close>
using assms by (induction t arbitrary: st) (auto simp: list_Nil_iff size_list butlast_splice)

lemma braun_del_hi:
  assumes \<open>braun t\<close>
      and \<open>size t = st\<close>
    shows \<open>braun (del_hi st t)\<close>
using assms by (induction t arbitrary: st) (auto simp: list_del_hi simp flip: size_list)

subsection\<open>Faster\<close>

subsubsection\<open>Size\<close>

fun tree_diff :: \<open>'a tree \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>tree_diff Leaf         _ = 0\<close> |
  \<open>tree_diff (Node l x r) n =
     (if n=0 then 1 else if even n then tree_diff r (n div 2 - 1) else tree_diff l (n div 2))\<close>

fun size_fast :: \<open>'a tree \<Rightarrow> nat\<close> where
  \<open>size_fast Leaf         = 0\<close> |
  \<open>size_fast (Node l x r) = (let n = size_fast r in 1 + 2*n + tree_diff l n)\<close>

lemma diff:
  assumes \<open>braun t\<close>
      and \<open>size t \<in> {n, n + 1}\<close>
    shows \<open>tree_diff t n = size t - n\<close>
using assms by (induction t arbitrary: n) auto

lemma size_fast:
  assumes \<open>braun t\<close>
    shows \<open>size_fast t = size t\<close>
using assms by (induction t) (auto simp add: diff)

subsubsection\<open>Initialization with 1 element\<close>

fun braun_of_naive :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a tree\<close> where
  \<open>braun_of_naive x n =
     (if n=0 then
        Leaf
      else
        let m = (n-1) div 2 in
          if odd n then
            Node (braun_of_naive x m) x (braun_of_naive x m)
          else
            Node (braun_of_naive x (m + 1)) x (braun_of_naive x m))\<close>

fun braun2_of :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a tree * 'a tree\<close> where
  \<open>braun2_of x n =
     (if n = 0 then
       (Leaf, Node Leaf x Leaf)
      else
        let (s,t) = braun2_of x ((n-1) div 2) in
          if odd n then
            (Node s x s, Node t x s)
          else
            (Node t x s, Node t x t))\<close>

definition braun_of :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a tree\<close> where
  \<open>braun_of x n \<equiv> fst (braun2_of x n)\<close>

lemma braun2_of_size_braun:
  assumes \<open>braun2_of x n = (s, t)\<close>
    shows \<open>size s = n \<and> size t = n+1 \<and> braun s \<and> braun t\<close>
using assms proof(induction x n arbitrary: s t rule: braun2_of.induct)
  case (1 x n)
  then show ?case
    by (auto simp: braun2_of.simps[of x n] split: prod.splits if_splits simp del: braun2_of.simps) presburger+
qed

lemma braun2_of_replicate:
  assumes \<open>braun2_of x n = (s,t)\<close>
    shows \<open>braun_list s = replicate n x \<and> braun_list t = replicate (n+1) x\<close>
using assms proof(induction x n arbitrary: s t rule: braun2_of.induct)
  case (1 x n)
  have \<open>x # replicate m x = replicate (m+1) x\<close> for m
    by simp
  with 1 show ?case
    by (auto simp: braun2_of.simps[of x n] replicate.simps(2)[of 0 x] simp del: replicate.simps(2)
      braun2_of.simps split: prod.splits if_splits) presburger+
qed

corollary braun_braun_of:
  shows \<open>braun (braun_of x n)\<close>
by (unfold braun_of_def) (metis eq_fst_iff braun2_of_size_braun)

corollary list_braun_of:
  shows \<open>braun_list (braun_of x n) = replicate n x\<close>
by (unfold braun_of_def) (metis eq_fst_iff braun2_of_replicate)

subsubsection\<open>Initialization with a family of elements\<close>

text \<open>Generate a Braun array from a function rather than from a constant\<close>

fun braun_of_fun :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a tree\<close> where
  \<open>braun_of_fun f n =
     (if n=0 then
        Leaf
      else
        let m = (n-1) div 2 in
          if odd n then
            Node (braun_of_fun (f \<circ> (*)2) m) (f 1) (braun_of_fun (\<lambda>i. f(Suc(2*i))) m)
          else
            Node (braun_of_fun (f \<circ> (*)2) (m + 1)) (f 1) (braun_of_fun (\<lambda>i. f(Suc(2*i))) m))\<close>

lemma lookup1_braun_of_fun:
  shows \<open>i \<in> {1..n} \<Longrightarrow> lookup1 (braun_of_fun f n) i = f i\<close>
proof (induction n arbitrary: f i rule: less_induct)
  case (less n f i)
  show ?case
  proof (cases \<open>n = 0\<close>)
    case True
    with less.prems show ?thesis by simp
  next
    case False
    then have n_pos: \<open>n > 0\<close> by simp
    define m where m_def: \<open>m = (n - 1) div 2\<close>
    show ?thesis
    proof (cases \<open>i = 1\<close>)
      case True
      with n_pos show ?thesis by (simp add: Let_def)
    next
      case i_ne_1: False
      with less.prems have i_gt_1: \<open>i > 1\<close> by auto
      show ?thesis
      proof (cases \<open>even i\<close>)
        case even_i: True
        define sz where sz_def: \<open>sz = (if odd n then m else m + 1)\<close>
        have sz_lt_n: \<open>sz < n\<close>
          using n_pos m_def sz_def by auto
        have div_in: \<open>i div 2 \<in> {1..sz}\<close>
          using less.prems even_i m_def sz_def even_i i_gt_1
        proof -
          from even_i i_gt_1 have \<open>1 \<le> i div 2\<close> by arith
          moreover have "i div 2 \<le> sz"
            using less.prems even_i m_def sz_def by simp arith
          ultimately show ?thesis by simp
        qed
        have \<open>lookup1 (braun_of_fun f n) i = lookup1 (braun_of_fun (f \<circ> (*) 2) sz) (i div 2)\<close>
          using n_pos i_ne_1 even_i by (simp add: Let_def m_def sz_def)
        also have \<open>\<dots> = (f \<circ> (*) 2) (i div 2)\<close>
          by (rule less.IH[OF sz_lt_n div_in])
        also have \<open>\<dots> = f i\<close>
          using even_i by auto
        finally show ?thesis .
      next
        case odd_i: False
        then have odd_i_fact: \<open>odd i\<close> by simp
        have m_lt_n: \<open>m < n\<close>
          using n_pos m_def by arith
        have div_in: \<open>i div 2 \<in> {1..m}\<close>
        proof -
          from odd_i_fact i_gt_1 have \<open>1 \<le> i div 2\<close> by arith
          moreover have \<open>i div 2 \<le> m\<close>
            using less.prems odd_i_fact m_def by simp arith
          ultimately show ?thesis by simp
        qed
        have \<open>lookup1 (braun_of_fun f n) i = lookup1 (braun_of_fun (\<lambda>i. f (Suc (2 * i))) m) (i div 2)\<close>
          using n_pos i_ne_1 odd_i
          by (subst braun_of_fun.simps) (simp del: braun_of_fun.simps add: Let_def m_def)
        also have \<open>\<dots> = (\<lambda>i. f (Suc (2 * i))) (i div 2)\<close>
          by (rule less.IH[OF m_lt_n div_in])
        also have \<open>\<dots> = f i\<close>
          using odd_i_fact by (simp add: odd_two_times_div_two_succ)
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma braun_of_fun_works:
  shows \<open>size (braun_of_fun f n) = n \<and> braun (braun_of_fun f n)\<close>
proof (induction n arbitrary: f rule: less_induct)
  case (less n)
  show ?case
  proof (cases \<open>n = 0\<close>)
    case True then show ?thesis by simp
  next
    case False
    define m where \<open>m = (n - 1) div 2\<close>
    have \<open>m < n\<close> using False m_def by arith
    show ?thesis
    proof (cases \<open>odd n\<close>)
      case True
      then show ?thesis
        using less.IH \<open>m < n\<close>
        by (simp add: braun_of_fun.simps [of f n] Let_def m_def del: braun_of_fun.simps) presburger
    next
      case False
      with \<open>n \<noteq> 0\<close> have \<open>m + 1 < n\<close> using m_def by arith
      then show ?thesis
        using less.IH \<open>m < n\<close>
        by (simp add: braun_of_fun.simps [of f n]Let_def m_def del: braun_of_fun.simps) presburger
    qed
  qed
qed

subsubsection\<open>Proof Infrastructure\<close>

text\<open>Originally due to Thomas Sewell.\<close>

paragraph \<open>\<open>take_nths\<close>\<close>

fun take_nths :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>take_nths i k []       = []\<close> |
  \<open>take_nths i k (x # xs) =
     (if i = 0 then x # take_nths (2^k - 1) k xs else take_nths (i - 1) k xs)\<close>

text \<open>This is the more concise definition but seems to complicate the proofs:\<close>
lemma take_nths_eq_nths:
  shows \<open>take_nths i k xs = nths xs (\<Union>n. {n*2^k + i})\<close>
proof(induction xs arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume [simp]: \<open>i = 0\<close>
    have \<open>\<And>m n. Suc m = n * 2 ^ k \<Longrightarrow> \<exists>q. \<forall>d. Suc q * 2 ^ k = Suc d \<longrightarrow> m = d\<close>
      by (metis mult_zero_left nat.inject nat.exhaust)
    then have \<open>(\<Union>n. {(n+1) * 2 ^ k - 1}) = {m. \<exists>n. Suc m = n * 2 ^ k}\<close>
      by (auto simp del: mult_Suc split: nat_diff_split)
    thus ?thesis
      by (simp add: Cons.IH ac_simps nths_Cons)
  next
    assume [arith]: \<open>i \<noteq> 0\<close>
    have \<open>(\<Union>n. {n * 2 ^ k + i - 1}) = {m. \<exists>n. Suc m = n * 2 ^ k + i}\<close>
      apply (auto split: nat_diff_split)
      by (metis nat.inject)
    thus ?thesis
      by (simp add: Cons.IH nths_Cons)
  qed
qed

lemma take_nths_drop:
  shows \<open>take_nths i k (drop j xs) = take_nths (i + j) k xs\<close>
by (induct xs arbitrary: i j; simp add: drop_Cons split: nat.split)

lemma take_nths_00:
  shows \<open>take_nths 0 0 xs = xs\<close>
by (induct xs; simp)

lemma splice_take_nths:
  shows \<open>splice (take_nths 0 (Suc 0) xs) (take_nths (Suc 0) (Suc 0) xs) = xs\<close>
by (induct xs; simp)

lemma take_nths_take_nths:
  shows \<open>take_nths i m (take_nths j n xs) = take_nths ((i * 2^n) + j) (m + n) xs\<close>
by (induct xs arbitrary: i j; simp add: algebra_simps power_add)

lemma take_nths_empty:
  shows \<open>(take_nths i k xs = []) \<longleftrightarrow> (length xs \<le> i)\<close>
by (induction xs arbitrary: i k) auto

lemma hd_take_nths:
  assumes \<open>i < length xs\<close>
    shows \<open>hd(take_nths i k xs) = xs ! i\<close>
using assms by (induction xs arbitrary: i k) auto

lemma take_nths_01_splice:
  assumes \<open>length xs = length ys \<or> length xs = length ys + 1\<close>
    shows \<open>take_nths 0 (Suc 0) (splice xs ys) = xs \<and> take_nths (Suc 0) (Suc 0) (splice xs ys) = ys\<close>
using assms by (induction xs arbitrary: ys; case_tac ysa; simp)

lemma length_take_nths_00:
  shows \<open>length (take_nths 0 (Suc 0) xs) = length (take_nths (Suc 0) (Suc 0) xs) \<or>
            length (take_nths 0 (Suc 0) xs) = length (take_nths (Suc 0) (Suc 0) xs) + 1\<close>
by (induct xs) auto

paragraph \<open>\<open>braun_list\<close>\<close>

fun is_braun_list :: \<open>'a tree \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>is_braun_list Leaf         xs = (xs = [])\<close> |
  \<open>is_braun_list (Node l x r) xs = (xs \<noteq> [] \<and> x = hd xs \<and>
     is_braun_list l (take_nths 1 1 xs) \<and>
     is_braun_list r (take_nths 2 1 xs))\<close>

lemma braun_list_eq:
  shows \<open>is_braun_list t xs \<longleftrightarrow> (braun t \<and> xs = braun_list t)\<close>
proof (induct t arbitrary: xs)
  case Leaf
  show ?case by simp
next
  case Node
  show ?case
    using length_take_nths_00[of xs] splice_take_nths[of xs]
    by (auto simp: neq_Nil_conv Node.hyps size_list[symmetric] take_nths_01_splice)
qed

subsubsection \<open>Converting a list of elements into a Braun tree\<close>

fun nodes :: \<open>'a tree list \<Rightarrow> 'a list \<Rightarrow> 'a tree list \<Rightarrow> 'a tree list\<close> where
  \<open>nodes (l#ls) (x#xs) (r#rs) = Node l x r # nodes ls xs rs\<close> |
  \<open>nodes (l#ls) (x#xs) []     = Node l x Leaf # nodes ls xs []\<close> |
  \<open>nodes []     (x#xs) (r#rs) = Node Leaf x r # nodes [] xs rs\<close> |
  \<open>nodes []     (x#xs) []     = Node Leaf x Leaf # nodes [] xs []\<close> |
  \<open>nodes ls     []     rs     = []\<close>

fun brauns :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a tree list\<close> where
  \<open>brauns k xs = (if xs = [] then [] else
     let ys = take (2^k) xs;
         zs = drop (2^k) xs;
         ts = brauns (k+1) zs
      in nodes ts ys (drop (2^k) ts))\<close>

definition brauns1 :: \<open>'a list \<Rightarrow> 'a tree\<close> where
  \<open>brauns1 xs \<equiv> if xs = [] then Leaf else brauns 0 xs ! 0\<close>

fun T_brauns :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>T_brauns k xs = (if xs = [] then 0 else
     let ys = take (2^k) xs;
         zs = drop (2^k) xs;
         ts = brauns (k+1) zs
      in 4 * min (2^k) (length xs) + T_brauns (k+1) zs)\<close>

paragraph\<open>Functional correctness\<close>

text\<open>The proof is originally due to Thomas Sewell.\<close>

lemma length_nodes:
  shows \<open>length (nodes ls xs rs) = length xs\<close>
by (induct ls xs rs rule: nodes.induct; simp)

lemma nth_nodes:
  assumes \<open>i < length xs\<close>
    shows \<open>nodes ls xs rs ! i = Node (if i < length ls then ls ! i else Leaf) (xs ! i)
                                  (if i < length rs then rs ! i else Leaf)\<close>
using assms by (induct ls xs rs arbitrary: i rule: nodes.induct) (auto simp add: nth_Cons split: nat.split)

theorem length_brauns:
  shows \<open>length (brauns k xs) = min (length xs) (2 ^ k)\<close>
proof (induct xs arbitrary: k rule: measure_induct_rule[where f=length])
  case (less xs) thus ?case
    by (simp add: brauns.simps[of k xs] Let_def length_nodes del: brauns.simps)
qed

theorem brauns_correct:
  assumes \<open>i < min (length xs) (2 ^ k)\<close>
    shows \<open>is_braun_list (brauns k xs ! i) (take_nths i k xs)\<close>
using assms proof (induct xs arbitrary: i k rule: measure_induct_rule[where f=length])
  case (less xs)
  let ?zs = \<open>drop (2^k) xs\<close>
  let ?ts = \<open>brauns (Suc k) ?zs\<close>
  have \<open>xs \<noteq> []\<close>
    using less.prems by auto
  from less.hyps[of ?zs _ "Suc k"] have IH: \<open>j = i + 2 ^ k \<Longrightarrow> i < min (length ?zs) (2 ^ (k+1)) \<Longrightarrow>
        is_braun_list (?ts ! i) (take_nths j (Suc k) xs)\<close> for i j
    using \<open>xs \<noteq> []\<close> by (simp add: take_nths_drop)
  show ?case
    using less.prems by (auto simp: brauns.simps[of k xs] nth_nodes take_nths_take_nths Let_def IH
      take_nths_empty hd_take_nths length_brauns simp del: brauns.simps)
qed

corollary brauns1_correct:
  shows \<open>braun (brauns1 xs) \<and> braun_list (brauns1 xs) = xs\<close>
using brauns_correct[of 0 xs 0] by (simp add: brauns1_def braun_list_eq take_nths_00 del: brauns.simps)

lemma brauns1_size_fast_bounded:
  assumes \<open>length xs \<le> m\<close>
    shows \<open>size_fast (brauns1 xs) \<le> m\<close>
using assms proof -
  have \<open>braun (brauns1 xs)\<close>
    by (simp add: brauns1_correct)
  moreover from this have \<open>size_fast (brauns1 xs) = size (brauns1 xs)\<close>
    by (simp add: size_fast)
  moreover from assms have \<open>size (brauns1 xs) \<le> m\<close>
  proof(induction xs arbitrary: m)
    fix m
    have \<open>size (brauns1 []) = 0\<close>
      by (clarsimp simp add: brauns1_def)
    also have \<open>\<dots> \<le> m\<close>
      by simp
    ultimately show \<open>size (brauns1 []) \<le> m\<close>
      by metis
  next
    fix x :: \<open>'a\<close> and xs m
    assume \<open>\<And>m. length xs \<le> m \<Longrightarrow> size (brauns1 xs) \<le> m\<close>
       and \<open>length (x#xs) \<le> m\<close>
    moreover from this obtain m' where \<open>length xs = m'\<close> and \<open>Suc m' \<le> m\<close>
      by auto
    moreover from calculation have \<open>size (brauns1 xs) \<le> m'\<close>
      by simp
    ultimately show \<open>size (brauns1 (x#xs)) \<le> m\<close>
      by (metis brauns1_correct size_list)
  qed
  ultimately show ?thesis
    by simp
qed

paragraph\<open>Running Time Analysis\<close>

theorem T_brauns:
  shows \<open>T_brauns k xs = 4 * length xs\<close>
proof (induction xs arbitrary: k rule: measure_induct_rule[where f = length])
  case (less xs)
  show ?case
  proof cases
    assume \<open>xs = []\<close>
    thus ?thesis
      by simp
  next
    let ?zs = \<open>drop (2^k) xs\<close>
    assume \<open>xs \<noteq> []\<close>
    have \<open>T_brauns k xs = T_brauns (k+1) ?zs + 4 * min (2^k) (length xs)\<close>
      using \<open>xs \<noteq> []\<close> by (simp add: Let_def)
    also have \<open>\<dots> = 4 * length ?zs + 4 * min (2^k) (length xs)\<close>
      using less[of ?zs \<open>k + 1\<close>] \<open>xs \<noteq> []\<close> by simp
    also have \<open>\<dots> = 4 * length xs\<close>
      by simp
    finally show ?case .
  qed
qed

subsubsection\<open>Converting a Braun Tree into a List of Elements\<close>

text\<open>The code and the proof are originally due to Thomas Sewell (except running time).\<close>

function list_fast_rec :: \<open>'a tree list \<Rightarrow> 'a list\<close> where
  \<open>list_fast_rec ts =
     (let us = filter (\<lambda>t. t \<noteq> Leaf) ts in
        if us = [] then
          []
        else
          map tree_value us @ list_fast_rec (map tree_left us @ map tree_right us))\<close>
by pat_completeness auto

lemma list_fast_rec_term1:
  assumes \<open>ts \<noteq> []\<close>
      and \<open>Leaf \<notin> set ts\<close>
    shows \<open>sum_list (map (size o tree_left) ts) + sum_list (map (size o tree_right) ts) < sum_list (map size ts)\<close>
proof -
  have \<open>\<lbrakk>Leaf \<notin> set ts; x \<in> set ts\<rbrakk>
         \<Longrightarrow> size (tree_left x) + size (tree_right x) < size x\<close> for x
    by (cases x; simp)
  with assms show ?thesis
    by (metis (mono_tags, lifting) comp_def sum_list_addf sum_list_strict_mono)
qed

lemma list_fast_rec_term:
  assumes \<open>us \<noteq> []\<close>
      and \<open>us = filter (\<lambda>t. t \<noteq> Leaf) ts\<close>
    shows \<open>sum_list (map (size o tree_left) us) + sum_list (map (size o tree_right) us) < sum_list (map size ts)\<close>
using assms
  using list_fast_rec_term1 order_less_le_trans sum_list_filter_le_nat by fastforce


termination
  by (relation \<open>measure (sum_list o map size)\<close>) (auto simp add: list_fast_rec_term)

definition list_fast :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>list_fast t \<equiv> list_fast_rec [t]\<close>

function T_list_fast_rec :: \<open>'a tree list \<Rightarrow> nat\<close> where
  \<open>T_list_fast_rec ts =
     (let us = filter (\<lambda>t. t \<noteq> Leaf) ts in
        length ts + (if us = [] then 0 else 5 * length us + T_list_fast_rec (map tree_left us @ map tree_right us)))\<close>
by pat_completeness auto

termination
  by (relation \<open>measure (sum_list o map size)\<close>) (auto simp add: list_fast_rec_term)

paragraph "Functional Correctness"

lemma list_fast_rec_all_Leaf:
  assumes \<open>\<And>t. t \<in> set ts \<Longrightarrow> t = Leaf\<close>
    shows \<open>list_fast_rec ts = []\<close>
using assms by (simp add: filter_empty_conv list_fast_rec.simps)

lemma take_nths_eq_single:
  assumes \<open>length xs - i < 2^n\<close>
    shows \<open>take_nths i n xs = take 1 (drop i xs)\<close>
using assms by (induction xs arbitrary: i n; simp add: drop_Cons')

lemma braun_list_Nil:
  shows \<open>is_braun_list t [] \<longleftrightarrow> (t = Leaf)\<close>
by (cases t) auto

lemma braun_list_not_Nil:
  assumes \<open>xs \<noteq> []\<close>
    shows \<open>is_braun_list t xs \<longleftrightarrow> (\<exists>l x r. t = Node l x r \<and> x = hd xs \<and>
            is_braun_list l (take_nths 1 1 xs) \<and>
              is_braun_list r (take_nths 2 1 xs))\<close>
using assms by (cases t) auto

theorem list_fast_rec_correct:
    notes list_fast_rec.simps [simp del]
  assumes \<open>length ts = 2 ^ k\<close>
      and \<open>\<forall>i < 2 ^ k. is_braun_list (ts ! i) (take_nths i k xs)\<close>
    shows \<open>list_fast_rec ts = xs\<close>
using assms proof (induct xs arbitrary: k ts rule: measure_induct_rule[where f=length])
  case (less xs)
  show ?case
  proof (cases "length xs < 2 ^ k")
    case True
    from less.prems True have filter:
      "\<exists>n. ts = map (\<lambda>x. Node Leaf x Leaf) xs @ replicate n Leaf"
      apply (rule_tac x="length ts - length xs" in exI)
      apply (clarsimp simp: list_eq_iff_nth_eq)
      apply (auto simp: nth_append braun_list_not_Nil take_nths_eq_single braun_list_Nil hd_drop_conv_nth)
      done
    thus ?thesis
      apply (clarsimp simp: list_fast_rec.simps[of ts] o_def list_fast_rec_all_Leaf Let_def)
      apply (metis in_set_replicate list_fast_rec_all_Leaf map_replicate_const replicate_add)
      done
  next
    case False
    with less.prems(2) have *:
      "\<forall>i < 2 ^ k. ts ! i \<noteq> Leaf
         \<and> tree_value (ts ! i) = xs ! i
         \<and> is_braun_list (tree_left (ts ! i)) (take_nths (i + 2 ^ k) (Suc k) xs)
         \<and> (\<forall>ys. ys = take_nths (i + 2 * 2 ^ k) (Suc k) xs
                 \<longrightarrow> is_braun_list (tree_right (ts ! i)) ys)"
      by (auto simp: take_nths_empty hd_take_nths braun_list_not_Nil take_nths_take_nths
                     algebra_simps)
    have 1: "map tree_value ts = take (2 ^ k) xs"
      using less.prems(1) False by (simp add: list_eq_iff_nth_eq *)
    have 2: "list_fast_rec (map tree_left ts @ map tree_right ts) = drop (2 ^ k) xs"
      using less.prems(1) False
      by (auto intro!: Nat.diff_less less.hyps[where k= "Suc k"]
               simp: nth_append * take_nths_drop algebra_simps)
    from less.prems(1) False show ?thesis
      by (auto simp: list_fast_rec.simps[of ts] 1 2 * all_set_conv_all_nth)
  qed
qed

corollary list_fast_correct:
    notes list_fast_rec.simps [simp del]
  assumes \<open>braun t\<close>
    shows \<open>list_fast t = braun_list t\<close>
using assms by (simp add: list_fast_def take_nths_00 braun_list_eq list_fast_rec_correct[where k=0])

paragraph\<open>Running Time Analysis\<close>

lemma sum_tree_list_children:
  assumes \<open>\<forall>t \<in> set ts. t \<noteq> Leaf\<close>
    shows \<open>(\<Sum>t\<leftarrow>ts. k * size t) = (\<Sum>t \<leftarrow> map tree_left ts @ map tree_right ts. k * size t) + k * length ts\<close>
using assms by (induction ts) (auto simp add: neq_Leaf_iff algebra_simps)

theorem T_list_fast_rec_ub:
  shows \<open>T_list_fast_rec ts \<le> sum_list (map (\<lambda>t. 7*size t + 1) ts)\<close>
proof (induction ts rule: measure_induct_rule[where f="sum_list o map size"])
  case (less ts)
  let ?us = \<open>filter (\<lambda>t. t \<noteq> Leaf) ts\<close>
  show ?case
  proof cases
    assume \<open>?us = []\<close>
    thus ?thesis using T_list_fast_rec.simps[of ts]
      by(simp add: sum_list_Suc)
    next
    assume \<open>?us \<noteq> []\<close>
    let ?children = \<open>map tree_left ?us @ map tree_right ?us\<close>
    have \<open>T_list_fast_rec ts = T_list_fast_rec ?children + 5 * length ?us + length ts\<close>
     using \<open>?us \<noteq> []\<close> T_list_fast_rec.simps[of ts] by (simp add: Let_def)
    also have \<open>\<dots> \<le> (\<Sum>t\<leftarrow>?children. 7 * size t + 1) + 5 * length ?us + length ts\<close>
      using less[of ?children] list_fast_rec_term[of ?us] \<open>?us \<noteq> []\<close> by simp
    also have \<open>\<dots> = (\<Sum>t\<leftarrow>?children. 7*size t) + 7 * length ?us + length ts\<close>
      by (simp add: sum_list_Suc o_def)
    also have \<open>\<dots> = (\<Sum>t\<leftarrow>?us. 7*size t) + length ts\<close>
      by (simp add: sum_tree_list_children)
    also have \<open>\<dots> \<le> (\<Sum>t\<leftarrow>ts. 7*size t) + length ts\<close>
      by (simp add: sum_list_filter_le_nat)
    also have \<open>\<dots> = (\<Sum>t\<leftarrow>ts. 7 * size t + 1)\<close>
      by (simp add: sum_list_Suc)
    finally show ?case .
  qed
qed

end