(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory ListAdditional
  imports Main "HOL-Library.Word" Word_Lib.More_Word Word_Lib.Typedef_Morphisms
    Word_Lib.Enumeration
begin
(*>*)

text\<open>This theory contains additional basic material around HOL lists.\<close>

text\<open>The following function maps \<^verbatim>\<open>a[0], a[1], ...\<close> to \<^verbatim>\<open>... (i, a[i]) ...\<close>:\<close>
definition enumerate_list :: \<open>'a list \<Rightarrow> (nat \<times> 'a) list\<close> where
  \<open>enumerate_list ls \<equiv> List.zip [0..<length ls] ls\<close>

lemma enumerate_list_at [simp]:
  shows \<open>length (enumerate_list ls) = length ls\<close>
    and \<open>\<And>i. i < length ls \<Longrightarrow> (enumerate_list ls) ! i = (i, ls ! i)\<close>
by (auto simp add: enumerate_list_def)

text\<open>The following is a generalization of \<^term>\<open>List.map\<close> which allows the map to take
into account the index of the source element.\<close>
definition mapi :: \<open>(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> where
  \<open>mapi f xs \<equiv> List.map (\<lambda>ix. f (fst ix) (snd ix)) (enumerate_list xs)\<close>

lemma mapi_at [simp]:
  shows \<open>length (mapi f ls) = length ls\<close>
    and \<open>\<And>i. i < length ls \<Longrightarrow> (mapi f ls) ! i = f i (ls ! i)\<close>
  by (auto simp add: mapi_def)

text\<open>Combine a prefix of one list with the suffix of another:\<close>
definition list_splice :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>list_splice n xs ys \<equiv> mapi (\<lambda>i v. if i < n then xs ! i else ys ! i) ys\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma list_splice_length:
  shows \<open>length (list_splice n xs ys) = length ys\<close>
  by (simp add: list_splice_def)

definition drop_nth :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>drop_nth n lst \<equiv> take n lst @ (drop (n+1) lst)\<close>

lemma drop_0th [simp]:
  shows \<open>drop_nth 0 ls = drop 1 ls\<close>
by (clarsimp simp add: drop_nth_def)

text\<open>Variant of \<^term>\<open>List.nth\<close> which returns \<^term>\<open>None\<close> for out-of-bounds accesses:\<close>
fun nth_opt :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a option\<close> where
  \<open>nth_opt n [] = None\<close> |
  \<open>nth_opt 0 (x#xs) = Some x\<close> |
  \<open>nth_opt (Suc n) (x#xs) = nth_opt n xs\<close>

lemma nth_opt_spec:
  assumes \<open>n < length xs\<close>
    shows \<open>nth_opt n xs = Some (nth xs n)\<close>
using assms by (induction xs arbitrary: n; force simp add: less_Suc_eq_0_disj)

lemma nth_opt_spec2:
   assumes \<open>nth_opt n xs = Some v\<close>
     shows \<open>xs ! n = v\<close> and \<open>n < length xs\<close>
using assms proof (induction xs arbitrary: n)
     fix n
  assume \<open>nth_opt n [] = Some v\<close>
  from this have \<open>False\<close>
    by simp
  from this show \<open>[] ! n = v\<close>
    by simp
next
     fix n
  assume \<open>nth_opt n [] = Some v\<close>
  from this have \<open>False\<close>
    by simp
  from this show \<open>n < length []\<close>
    by simp
next
     fix x xs n
  assume \<open>nth_opt n (x # xs) = Some v\<close>
     and \<open>\<And>n. nth_opt n xs = Some v \<Longrightarrow> xs ! n = v\<close>
  from this show \<open>(x # xs) ! n = v\<close>
    using nth_opt.elims by force
next
     fix x xs n
  assume \<open>nth_opt n (x # xs) = Some v\<close>
     and \<open>\<And>n. nth_opt n xs = Some v \<Longrightarrow> n < length xs\<close>
  from this show \<open>n < length (x # xs)\<close>
    using nth_opt.elims by force
qed

lemma nth_opt_None:
  assumes \<open>n \<ge> length xs\<close>
    shows \<open>nth_opt n xs = None\<close>
using assms nth_opt_spec2 by (cases \<open>nth_opt n xs\<close>; fastforce)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma nth_opt_rev:
  assumes \<open>n < length xs\<close>
    shows \<open>nth_opt n (rev xs) = nth_opt (length xs - n - 1) xs\<close>
using assms by (simp add: nth_opt_spec rev_nth)

lemma nth_optE:
  assumes \<open>nth_opt n xs = Some v\<close>
      and \<open>xs ! n = v \<Longrightarrow>  n < length xs \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms nth_opt_spec2 by metis

lemma nth_optI [intro]:
  assumes \<open>n < length xs\<close>
     and \<open>nth xs n = v\<close>
   shows \<open>nth_opt n xs = Some v\<close>
using assms by (auto simp add: nth_opt_spec)

text\<open>Apply a function to the n-th element of a list:\<close>
fun over_nth :: \<open>nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>over_nth n f [] = []\<close> |
  \<open>over_nth 0 f (x#xs) = f x # xs\<close> |
  \<open>over_nth (Suc n) f (x#xs) = x # over_nth n f xs\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma over_nth_length:
  shows \<open>length (over_nth n f xs) = length xs\<close>
by (induction n xs rule: nth_opt.induct; simp)+

lemma over_nth_is_valid:
  shows \<open>nth_opt n (over_nth n f l) = map_option f (nth_opt n l)\<close>
    and \<open>map_option f (nth_opt n l) = nth_opt n l \<Longrightarrow> over_nth n f l = l\<close>
    and \<open>over_nth n f (over_nth n g l) = over_nth n (\<lambda>x. f (g x)) l\<close>
by (induction n l rule: nth_opt.induct; simp)+

lemma over_nth_list_update:
  shows \<open>over_nth n f xs = list_update xs n (f (nth xs n))\<close>
by (induction n xs rule: nth_opt.induct; simp)

lemma over_nth_list_update':
  shows \<open>over_nth = (\<lambda>n f xs. list_update xs n (f (nth xs n)))\<close>
by (intro ext, blast intro: over_nth_list_update)

lemma over_nth_commute [rule_format]:
  assumes \<open>n \<noteq> m\<close>
    shows \<open>over_nth m f (over_nth n g l) = over_nth n g (over_nth m f l) \<and>
             nth_opt m (over_nth n g l) = nth_opt m l \<and>
             nth_opt n (over_nth m f l) = nth_opt n l\<close>
using assms proof (induction n l arbitrary: m rule: nth_opt.induct)
  case (2 x xs)
  then show ?case by (cases m; simp)
next
  case (3 n x xs)
  then show ?case by (cases m; simp)
qed auto

lemma nth_opt_take:
  assumes \<open>n < len\<close>
    shows \<open>nth_opt n (take len xs) = nth_opt n xs\<close>
using assms by (induction n xs arbitrary: len rule: nth_opt.induct; fastforce simp add: Suc_less_eq2)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma over_nth_expand_lemma:
  assumes \<open>i < length xs\<close>
    shows \<open>over_nth i f xs = take i xs @ f (xs!i) # drop (Suc i) xs\<close>
using assms by (induction i f xs rule: over_nth.induct; simp)

definition subrange :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list option\<close> where
  \<open>subrange start len xs \<equiv>
    if start + len \<le> length xs then
      Some (take len (drop start xs))
    else
      None\<close>

definition over_subrange :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>over_subrange start len f xs \<equiv>
     let front = take start xs;
         mid   = take len (drop start xs);
         end   = drop (start+len) xs
      in front @ f mid @ end\<close>

lemma subrange_succ:
  shows \<open>subrange (Suc start) len (x#xs) = subrange start len xs\<close>
by (auto simp add: subrange_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma subrange_nth_opt:
  assumes \<open>n < len\<close>
      and \<open>start + len \<le> length xs\<close>
    shows \<open>Option.bind (subrange start len xs) (nth_opt n) = nth_opt (start + n) xs\<close>
using assms proof (induction start arbitrary: len xs)
     fix len
     and xs :: \<open>'a list\<close>
  assume \<open>n < len\<close>
     and \<open>0 + len \<le> length xs\<close>
  from this show \<open>Option.bind (subrange 0 len xs) (nth_opt n) = nth_opt (0 + n) xs\<close>
    by (auto simp add: subrange_def nth_opt_take)
next
     fix start len
     and xs :: \<open>'a list\<close>
  assume \<open>n < len\<close>
     and \<open>Suc start + len \<le> length xs\<close>
     and \<open>\<And>len (xs::'a list). n < len \<Longrightarrow> start + len \<le> length xs \<Longrightarrow>
            Option.bind (subrange start len xs) (nth_opt n) = nth_opt (start + n) xs\<close>
  moreover {
    assume \<open>xs = []\<close>
    from this calculation have \<open>Option.bind (subrange (Suc start) len xs) (nth_opt n) = nth_opt (Suc start + n) xs\<close>
      by clarsimp
  } moreover {
      note calculation_thus_far = calculation
       fix y ys
    assume \<open>xs = y#ys\<close>
    moreover from this calculation_thus_far have \<open>start + len \<le> length ys\<close>
      by simp
    moreover from calculation calculation_thus_far have \<open>Option.bind (subrange start len ys) (nth_opt n) =
          nth_opt (start + n) ys\<close>
      by auto
    ultimately have \<open>Option.bind (subrange (Suc start) len xs) (nth_opt n) = nth_opt (Suc start + n) xs\<close>
      by (auto simp add: subrange_succ)
  }
  ultimately show \<open>Option.bind (subrange (Suc start) len xs) (nth_opt n) = nth_opt (Suc start + n) xs\<close>
    by (meson list.exhaust)
qed

subsection\<open>Facts about list splitting\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma list_map_split_rev:
  assumes \<open>ls = pre @ (mid # suf)\<close>
      and \<open>ls = List.map f ls'\<close>
  obtains pre' and mid' and suf' where \<open>ls' = pre' @ (mid' # suf')\<close> and \<open>List.map f pre' = pre\<close> and
    \<open>f mid' = mid\<close> and \<open>List.map f suf' = suf\<close>
using assms by (auto simp only: map_eq_append_conv)

lemma list_split_contains:
  assumes \<open>ls = pre @ (mid # suf)\<close>
    shows \<open>mid \<in> set ls\<close>
using assms by auto

lemma list_split_containsE:
  assumes \<open>ls = pre @ (mid # suf)\<close>
      and \<open>mid \<in> set ls \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by auto

lemma list_map_concat_rev:
  assumes \<open>List.map f ls = ls0' @ ls1'\<close>
  obtains ls0 and ls1 where \<open>ls = ls0 @ ls1\<close> and \<open>ls0' = List.map f ls0\<close> and \<open>ls1' = List.map f ls1\<close>
using assms map_eq_append_conv by blast

lemma list_map_concat_revE:
  assumes \<open>List.map f ls = ls0' @ ls1'\<close>
      and \<open>\<And>ls0 ls1. ls = ls0 @ ls1 \<Longrightarrow> List.map f ls0 = ls0' \<Longrightarrow> List.map f ls1 = ls1' \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using list_map_concat_rev assms by blast

lemma list_map_cons_rev:
  assumes \<open>List.map f ls = y # ys\<close>
  obtains x and xs where \<open>ls = x # xs\<close> and \<open>ys = List.map f xs\<close> and \<open>y = f x\<close>
using assms by blast

lemma list_map_cons_revE:
  assumes \<open>List.map f ls = y # ys\<close>
      and \<open>\<And>x xs. ls = x # xs \<Longrightarrow> f x = y \<Longrightarrow> List.map f xs = ys \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using list_map_cons_rev assms by blast

lemma natrange_split0:
  fixes a :: \<open>nat\<close>
  assumes \<open>a < b\<close>
      and \<open>[a..<b] = pre @ suf\<close>
    shows \<open>\<exists>c. a \<le> c \<and> c \<le> b \<and> pre = [a..<c] \<and> suf = [c..<b]\<close>
proof -
  have \<open>[a..<b] = [a..< a+length pre] @ [a+length pre ..< b]\<close>
    by (metis add.commute add_diff_inverse_nat append_eq_conv_conj assms drop_upt le_add1
      length_append length_upt order_less_imp_not_less
      ordered_cancel_comm_monoid_diff_class.le_diff_conv2 take_upt)
  from assms and this show ?thesis
    by (metis add_diff_cancel_left' append.right_neutral append_eq_append_conv le_add1
      length_upt less_imp_le_nat nat_le_linear upt_conv_Nil)
qed

subsubsection\<open>Splitting natural number ranges\<close>

lemma natrange_split1:
  assumes \<open>[a..<b] = pre @ (mid # suf)\<close>
  obtains c :: nat where \<open>a \<le> c\<close> and \<open>c < b\<close> and
    \<open>pre = [a..<c]\<close> and \<open>mid = c\<close> and \<open>suf = [c + 1..<b]\<close>
proof -
  have \<open>a < b\<close>
    using assms
    by (metis Nil_is_append_conv list.distinct(1) upt_rec)
  from this and assms show ?thesis
    by (metis natrange_split0 that upt_eq_Cons_conv)
qed

lemma natrange_splitE:
  assumes \<open>[a..<b] = pre @ (mid # suf)\<close>
      and  \<open>\<And>c. a \<le> c \<Longrightarrow> c < b \<Longrightarrow> pre = [a..<c] \<Longrightarrow> mid=c \<Longrightarrow> suf = [(c+1)..<b] \<Longrightarrow> R\<close>
    shows R
using assms by (blast intro: natrange_split1)

corollary natlist_up_to_split:
  assumes \<open>ls = pre @ (mid # suf)\<close>
      and \<open>ls = List.map f [0..<n]\<close>
  obtains s :: nat where \<open>pre = List.map f [0..<s]\<close> and \<open>mid = f s\<close> and \<open>suf = List.map f [(s+1)..<n]\<close>
using assms by (clarsimp elim!: list_map_cons_revE list_map_concat_revE natrange_splitE)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma least_in_natrange:
  assumes \<open>[a..<b] = pre@(mid#suf)\<close>
      and \<open>\<And>p. p \<in> set pre \<Longrightarrow> \<not> P p\<close>
      and \<open>P mid\<close>
    shows \<open>mid = (LEAST v. a \<le> v \<and> v < b \<and> P v)\<close>
using assms by (fastforce elim!: natrange_splitE intro: Least_equality[symmetric])

lemma least_in_ordered_list:
    fixes ls :: \<open>'a::{linorder} list\<close>
      and pre suf :: \<open>'a list\<close>
      and mid :: \<open>'a\<close>
  assumes \<open>List.sorted ls\<close>
      and \<open>ls = pre@(mid#suf)\<close>
      and \<open>\<And>p. p \<in> set pre \<Longrightarrow> \<not> P p\<close>
      and \<open>P mid\<close>
    shows \<open>mid = (LEAST v. v\<in>set ls \<and> P v)\<close>
using assms by (auto simp add: sorted_append intro!: Least_equality[symmetric])

lemma sorted_list_map_mono:
    fixes ls :: \<open>'a::{linorder} list\<close>
      and f :: \<open>'a \<Rightarrow> 'b::linorder\<close>
  assumes \<open>sorted ls\<close>
      and \<open>\<And>x y. x\<in>set ls \<Longrightarrow> y\<in>set ls \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y\<close>
    shows \<open>sorted (List.map f ls)\<close>
using assms by (induction ls) auto

lemma map_range_to_set_range:
  assumes \<open>List.map f [lo..<hi] = pre@cur#todo\<close>
    shows \<open>cur \<in> f ` {lo..<hi}\<close>
using assms by (metis atLeastLessThan_upt list.set_map list_split_contains)

lemma curr_in_range:
    fixes f :: \<open>nat \<Rightarrow> 'a::{linorder}\<close>
      and g :: \<open>'a \<Rightarrow> nat\<close>
  assumes \<open>0 \<le> lo\<close>
      \<comment> \<open>\<^verbatim>\<open>f\<close> is an order-preserving map over the desired range\<close>
      and \<open>\<And>x y. lo \<le> x \<Longrightarrow> y \<le> hi \<Longrightarrow> x < y \<Longrightarrow> f x < f y\<close>
      \<comment> \<open>\<^verbatim>\<open>g\<close> is the inverse of \<^verbatim>\<open>f\<close> over the desired range\<close>
      and \<open>\<And>x y. x \<in> {lo..<hi} \<Longrightarrow> f x = y \<longleftrightarrow> g y = x\<close>
      and \<open>List.map f [lo..<hi] = pre@cur#todo\<close>
    shows \<open>f lo \<le> cur \<and> cur < f hi\<close>
proof -
  have \<open>cur \<in> f ` {lo..<hi}\<close>
    using assms map_range_to_set_range by metis
  moreover have \<open>g cur \<in> {lo..<hi}\<close>
    using assms calculation by (metis image_iff)
  moreover have \<open>lo \<le> g cur\<close> and \<open>g cur < hi\<close>
    using calculation atLeastAtMost_iff by auto
  moreover have \<open>f lo \<le> cur\<close> and \<open>cur < f hi\<close>
    using assms calculation by (metis order.order_iff_strict)+
  ultimately show \<open>f lo \<le> cur \<and> cur < f hi\<close>
    by blast
qed

corollary curr_in_range':
    fixes cur :: \<open>'a::{len} word\<close>
  assumes \<open>List.map word_of_nat [lo..<hi] = pre@cur#todo\<close>
      and \<open>0 \<le> lo\<close>
      and \<open>hi < 2^LENGTH('a)\<close>
    shows \<open>word_of_nat lo \<le> cur \<and> cur < word_of_nat hi\<close>
proof -
  {
       fix x y
    assume \<open>lo \<le> x\<close>
       and \<open>y \<le> hi\<close>
       and \<open>x < y\<close>
    from this assms have \<open>x mod 2 ^ LENGTH('a) < y mod 2 ^ LENGTH('a)\<close>
      by (clarsimp simp add: take_bit_eq_mod)
    from this have \<open>word_of_nat x < ((word_of_nat y)::'a word)\<close>
      by (simp add: Typedef_Morphisms.unat_of_nat word_less_nat_alt)
  } moreover {
       fix x
       and y :: \<open>'a word\<close>
    assume \<open>x \<in> {lo..<hi}\<close>
    from this assms have \<open>word_of_nat x = y \<longleftrightarrow> unat y = x\<close>
      by (metis atLeastLessThan_iff le_unat_uoi nat_less_le unat_of_nat_len word_unat.Rep_inverse)
  }
  ultimately show \<open>word_of_nat lo \<le> cur \<and> cur < word_of_nat hi\<close>
    using assms by (intro curr_in_range[where g=\<open>unat\<close>]) auto
qed

lemma distinct_lookup_set_lemma:
  assumes \<open>distinct xs\<close>
      and \<open>i \<notin> idxs\<close>
      and \<open>i < length xs\<close>
      and \<open>\<forall>i \<in> idxs. i < length xs\<close>
    shows \<open>xs ! i \<notin> ((!) xs) ` idxs\<close>
proof
  assume \<open>xs!i \<in> ((!) xs ` idxs)\<close>
  from this and assms have \<open>i \<in> idxs\<close>
    by clarsimp (metis distinct_the_index_is_index)
  from this and assms show False
    by blast
qed

lemma foldr_plus_lift:
  fixes f :: \<open>'a \<Rightarrow> 'b::{semiring_0_cancel}\<close>
  shows \<open>List.foldr (\<lambda>x. (+) (f x)) past x = List.foldr (\<lambda>x. (+) (f x)) past 0 + x\<close>
by (induction past; simp add: add.assoc)

lemma take_suc_rev:
  assumes \<open>Suc n \<le> length ls\<close>
    shows \<open>rev (take (Suc n) ls) = ls!n #rev (take n ls)\<close>
using Suc_less_eq assms less_Suc_eq_le take_Suc_conv_app_nth by fastforce

lemma take_suc_rev':
  assumes \<open>n < length ls\<close>
    shows \<open>rev (take (Suc n) ls) = ls!n #rev (take n ls)\<close>
using Suc_less_eq assms less_Suc_eq_le take_Suc_conv_app_nth by fastforce

lemma list_update_id':
  assumes \<open>i < length x\<close>
      and \<open>t = x ! i\<close>
    shows \<open>x [i := t] = x\<close>
using assms and list_update_id by auto

lemma drop_last_butlast_facts:
  fixes xs :: \<open>'a list\<close> and i :: nat
  assumes idx: \<open>i < List.length xs\<close> and \<open>distinct xs\<close>
  shows \<open>drop i xs \<noteq> []\<close>
    and \<open>last xs = last (drop i xs)\<close>
    and \<open>Set.insert (last xs) (set (List.drop i (butlast xs))) = set (List.drop i xs)\<close>
    and \<open>last xs \<notin> set (List.drop i (butlast xs))\<close>
proof -
  from assms show \<open>drop i xs \<noteq> []\<close>
    by auto
  moreover from idx show \<open>last xs = last (drop i xs)\<close>
    by simp
  moreover from idx append_butlast_last_id[OF \<open>drop i xs \<noteq> []\<close>]
    show \<open>Set.insert (last xs) (set (List.drop i (butlast xs))) = set (List.drop i xs)\<close>
    by (simp add: drop_butlast flip: last_drop)
     (subst (3) append_butlast_last_id[of \<open>List.drop i xs\<close>, symmetric]; simp)
  ultimately show \<open>last xs \<notin> set (List.drop i (butlast xs))\<close>
    by (metis append_butlast_last_id assms(2) distinct_butlast
        drop.simps(1) in_set_dropD not_distinct_conv_prefix)
qed

lemma last_butlast_facts:
  fixes xs :: \<open>'a list\<close> and i :: nat
  assumes \<open>distinct xs\<close> and \<open>xs \<noteq> []\<close>
  shows \<open>set (butlast xs) = set xs - { last xs }\<close>
    and \<open>last xs \<in> set xs\<close>
  using assms(2) drop_last_butlast_facts[where i=0, OF _ assms(1)] by auto

(*<*)
end
(*>*)