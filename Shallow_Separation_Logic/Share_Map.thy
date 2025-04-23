(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Share_Map
  imports
    "HOL-Library.Datatype_Records"
    Apartness
    Separation_Algebra
    Shareable_Value
    Tree_Shares
    Data_Structures.RedBlackTree_Extensional
    Lenses_And_Other_Optics.Lenses_And_Other_Optics
begin
(*>*)

section\<open>Share maps\<close>

text\<open>In the following, we develop an efficient presentation of finitely
supported maps\<^typ>\<open>'k \<Rightarrow> 'v shareable_value\<close> using Red-Black trees.

We first identify \<^typ>\<open>'k \<Rightarrow> 'v shareable_value\<close> with finitely-supported partial maps
\<^typ>\<open>'k \<rightharpoonup> 'v \<times> nonempty_share\<close>, and then use Red-Black trees as an efficient
partial-map implementation.

We work with extensional equality on the type of Red-Black trees, which makes it
isomorphic to finitely supported maps \<^typ>\<open>'k \<Rightarrow> 'v shareable_value\<close> and allows to
trivially transfer the separation algebra axioms from \<^typ>\<open>'k \<Rightarrow> 'v shareable_value\<close>.\<close>

(*<*)
context
  notes [[typedef_overloaded]]
begin
(*>*)

datatype ('k, 'v) rbt_share_map
  =  RmShareMap (rbt_share_map: \<open>('k, 'v \<times> nonempty_share) rbt_ext\<close>)

(*<*)
end
(*>*)

definition rbt_share_map_bulkload :: \<open>('k::{linorder} \<times> 'v \<times> nonempty_share) list \<Rightarrow>
    ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_bulkload ls \<equiv> RmShareMap (rbt_ext_bulkload ls)\<close>

definition rbt_share_map_bulkload_top :: \<open>('k::{linorder} \<times> 'v) list \<Rightarrow> ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_bulkload_top ls \<equiv> rbt_share_map_bulkload (List.map (\<lambda>(k,v). (k, (v, top))) ls)\<close>

definition rbt_share_map_update :: \<open>'k::{linorder} \<Rightarrow> 'v shareable_value \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow>
      ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_update k v m \<equiv>
     case v of
       No_Value          \<Rightarrow> RmShareMap (rbt_ext_delete k (rbt_share_map m))
     | Shared_Value sh v \<Rightarrow> RmShareMap (rbt_ext_update k (v, sh) (rbt_share_map m))\<close>

text\<open>The following is key to identifying \<^typ>\<open>'k \<Rightarrow> 'v shareable_value\<close> with partial maps
\<^typ>\<open>'k \<rightharpoonup> 'v \<times> nonempty_share\<close>:\<close>

definition shareable_value_option :: \<open>('v \<times> nonempty_share) option \<Rightarrow> 'v shareable_value\<close> where
  \<open>shareable_value_option x \<equiv>
     case x of
        None         \<Rightarrow> No_Value
      | Some (v, sh) \<Rightarrow> Shared_Value sh v\<close>

definition shareable_value_option_inv :: \<open>'v shareable_value \<Rightarrow> ('v \<times> nonempty_share) option\<close> where
  \<open>shareable_value_option_inv x \<equiv>
     case x of
        No_Value          \<Rightarrow> None
      | Shared_Value sh v \<Rightarrow> Some (v, sh)\<close>

lemma shareable_value_option_simps[simp]:
  shows \<open>shareable_value_option None = No_Value\<close>
    and \<open>shareable_value_option (Some (v, sh)) = Shared_Value sh v\<close>
by (auto simp add: shareable_value_option_def)

lemma shareable_value_option_inj:
  assumes \<open>shareable_value_option a = shareable_value_option b\<close>
    shows \<open>a = b\<close>
using assms by (auto simp add: shareable_value_option_def split!: option.splits)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma shareable_value_option_inv_bij:
  shows \<open>shareable_value_option (shareable_value_option_inv x) = x\<close>
    and \<open>shareable_value_option_inv (shareable_value_option y) = y\<close>
by (auto simp add: shareable_value_option_def shareable_value_option_inv_def
  split!: option.splits shareable_value.splits)

text\<open>The abstraction isomorphism from Red-Black trees to (finitely supported)
\<^typ>\<open>'k \<Rightarrow> 'v shareable_value\<close>:\<close>

definition rbt_share_map_\<alpha> :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> 'k \<Rightarrow> 'v shareable_value\<close> where
  \<open>rbt_share_map_\<alpha> mem \<equiv> \<lambda>a. shareable_value_option (rbt_ext_\<alpha> (rbt_share_map mem) a)\<close>

abbreviation rbt_share_map_\<alpha>' :: \<open>'k::{linorder} \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow> 'v shareable_value\<close> where
  \<open>rbt_share_map_\<alpha>' k mem \<equiv> rbt_share_map_\<alpha> mem k\<close>

lemma rbt_share_map_\<alpha>_update[simp]:
  shows \<open>rbt_share_map_\<alpha> (rbt_share_map_update k v m) = (rbt_share_map_\<alpha> m) (k := v)\<close>
by (auto simp add: rbt_share_map_\<alpha>_def rbt_ext_correct rbt_share_map_update_def
  split!: rbt_share_map.splits shareable_value.splits)

definition rbt_share_map_map_entry :: \<open>'k::{linorder} \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow>
      ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_map_entry k f m \<equiv> RmShareMap (rbt_ext_map_entry k (apfst f) (rbt_share_map m))\<close>

lemma rbt_share_map_\<alpha>_map_entry [simp]:
  shows \<open>rbt_share_map_\<alpha> (rbt_share_map_map_entry k f m) =
            (rbt_share_map_\<alpha> m) (k := map_shareable_value f (rbt_share_map_\<alpha> m k))\<close>
  apply (clarsimp intro!: ext simp add: rbt_share_map_\<alpha>_def rbt_ext_correct rbt_share_map_map_entry_def
    map_shareable_value_def split!: rbt_share_map.splits shareable_value.splits)
  apply (metis apfst_conv option.simps(9) shareable_value_option_inj shareable_value_option_simps(2))
  apply (metis option.simps(8) shareable_value_option_inj shareable_value_option_simps(1))
  done

text\<open>The following is a trivial consequence of the extensional equality we imposed on Red-Black trees.\<close>
lemma rbt_share_map_eqI:
  assumes \<open>rbt_share_map_\<alpha> rm0 = rbt_share_map_\<alpha> rm1\<close>
  shows \<open>rm0 = rm1\<close>
  using assms unfolding rbt_share_map_\<alpha>_def
  by (metis (lifting) ext rbt_ext_eqI rbt_share_map.expand  shareable_value_option_inj)

lemma rbt_share_map_eqE:
  assumes \<open>rm0 = rm1\<close>
    and \<open>(\<And>k. rbt_share_map_\<alpha> rm0 k = rbt_share_map_\<alpha> rm1 k) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by simp

lemma rbt_share_map_\<alpha>_empty':
  shows \<open>rbt_share_map_\<alpha> (RmShareMap rbt_ext_empty) = 0\<close>
  by (simp add: rbt_share_map_\<alpha>_def rbt_ext_basic rbt_ext_correct zero_fun_def)

context
  fixes k :: \<open>'k::{linorder}\<close>
begin

global_interpretation lens_share_map_eval: lens \<open>\<lambda>m. rbt_share_map_\<alpha> m k\<close> \<open>rbt_share_map_update k\<close>
proof (standard, simp add: is_valid_lens_def, safe)
   fix mem :: \<open>('k, 'a) rbt_share_map\<close>
  show \<open>rbt_share_map_update k (rbt_share_map_\<alpha>' k mem) mem = mem\<close>
    by (clarsimp simp add: rbt_ext_correct intro!: rbt_share_map_eqI)
next
   fix y0 y1 :: \<open>'a shareable_value\<close>
   and mem :: \<open>('k, 'a) rbt_share_map\<close>
  show \<open>rbt_share_map_update k y1 (rbt_share_map_update k y0 mem) = rbt_share_map_update k y1 mem\<close>
    by (clarsimp simp add: rbt_ext_correct intro!: rbt_share_map_eqI)
qed

end

abbreviation lens_share_map_eval :: \<open>'k::{linorder} \<Rightarrow>
    (('k, 'v) rbt_share_map, 'v shareable_value) lens\<close> where
  \<open>lens_share_map_eval \<equiv> lens_share_map_eval.get_lens\<close>

abbreviation rbt_share_map_modify :: \<open>'k::{linorder} \<Rightarrow> ('v shareable_value \<Rightarrow> 'v shareable_value) \<Rightarrow>
    ('k, 'v) rbt_share_map \<Rightarrow> ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_modify k \<equiv> lens_modify (lens_share_map_eval k)\<close>

lemma rbt_share_map_\<alpha>_modify [simp]:
  shows \<open>rbt_share_map_\<alpha> (rbt_share_map_modify k f m) = (rbt_share_map_\<alpha> m) (k := f (rbt_share_map_\<alpha> m k))\<close>
by (simp add: lens_modify_def)

instantiation rbt_share_map :: (linorder, type) apart
begin

definition zero_rbt_share_map :: \<open>('k::{linorder}, 'v) rbt_share_map\<close> where
  \<open>zero_rbt_share_map \<equiv> RmShareMap rbt_ext_empty\<close>

definition disjoint_rbt_share_map :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow> bool\<close> where
  \<open>disjoint_rbt_share_map rm0 rm1 \<equiv> (rbt_share_map_\<alpha> rm0) \<sharp> (rbt_share_map_\<alpha> rm1)\<close>

instance
proof
  fix x :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  show \<open>x \<sharp> 0\<close>
    by (clarsimp simp add: zero_rbt_share_map_def rbt_share_map_\<alpha>_empty' disjoint_rbt_share_map_def)
next
   fix x y :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>
    by (clarsimp simp add: disjoint_rbt_share_map_def)
next
     fix x :: \<open>('k::linorder, 'v) rbt_share_map\<close>
  assume \<open>x \<sharp> x\<close>
  from this show \<open>x = 0\<close>
    by (simp add: disjoint_rbt_share_map_def rbt_share_map_\<alpha>_empty' rbt_share_map_eqI
      unique zero_rbt_share_map_def)
qed

end

fun add_nonempty_share :: \<open>('v \<times> nonempty_share) \<Rightarrow> ('v \<times> nonempty_share) \<Rightarrow> ('v \<times> nonempty_share)\<close> where
  \<open>add_nonempty_share (v0, sh0) (v1, sh1) = (v0, sh0 + sh1)\<close>

lemma rbt_share_map_\<alpha>_empty [simp]:
  shows \<open>rbt_share_map_\<alpha> 0 = 0\<close>
by (simp add: rbt_share_map_\<alpha>_empty' zero_rbt_share_map_def)

definition add_rbt_share_map :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow>
    ('k, 'v) rbt_share_map\<close> where
  \<open>add_rbt_share_map x y \<equiv> RmShareMap (rbt_ext_combine add_nonempty_share (rbt_share_map x) (rbt_share_map y))\<close>

lemma add_rbt_share_map:
  shows \<open>rbt_share_map (add_rbt_share_map x y) =
          rbt_ext_combine add_nonempty_share (rbt_share_map x) (rbt_share_map y)\<close>
by (simp add: add_rbt_share_map_def)

lemma shareable_value_option_combine:
  shows \<open>shareable_value_option (combine_options add_nonempty_share x y) =
            shareable_value_option x + shareable_value_option y\<close>
by (auto split!: option.splits simp add: shareable_value_option_def)

lemma add_rbt_share_map_\<alpha>':
  shows \<open>rbt_share_map_\<alpha> (add_rbt_share_map x y) = rbt_share_map_\<alpha> x + rbt_share_map_\<alpha> y\<close>
by (simp add: add_rbt_share_map_def add_rbt_share_map rbt_share_map_\<alpha>_def rbt_ext_correct
  shareable_value_option_combine plus_fun_def)

instantiation rbt_share_map :: (linorder, type)sepalg
begin

definition plus_rbt_share_map  :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow>
    ('k, 'v) rbt_share_map\<close> where
  \<open>plus_rbt_share_map x y \<equiv> add_rbt_share_map x y\<close>

instance
proof
   fix x :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  show \<open>x + 0 = x\<close>
    by (clarsimp intro!: rbt_share_map_eqI simp add: plus_rbt_share_map_def add_rbt_share_map_\<alpha>')
next
     fix x y :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (clarsimp intro!: rbt_share_map_eqI simp add: disjoint_rbt_share_map_def
      plus_rbt_share_map_def add_rbt_share_map_\<alpha>')
next
     fix x y z :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assume \<open>x \<sharp> y\<close>
     and \<open>y \<sharp> z\<close>
     and \<open>x \<sharp> z\<close>
  then show \<open>x + (y + z) = x + y + z\<close>
    unfolding plus_rbt_share_map_def disjoint_rbt_share_map_def
    by (metis (no_types, lifting) add_rbt_share_map_\<alpha>' rbt_share_map_eqI sepalg_assoc)
next
     fix x y z :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assume \<open>x \<sharp> y + z\<close> and \<open>y \<sharp> z\<close>
  then show \<open>x \<sharp> y\<close>
    unfolding plus_rbt_share_map_def disjoint_rbt_share_map_def
    by (metis add_rbt_share_map_\<alpha>' sepalg_apart_plus2)
next
     fix x y z :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  then show \<open>x + y \<sharp> z\<close>
    by (metis add_rbt_share_map_\<alpha>' disjoint_rbt_share_map_def plus_rbt_share_map_def
      sepalg_apart_assoc2)
qed

end

lemma add_rbt_share_map_\<alpha> [simp]:
  shows \<open>rbt_share_map_\<alpha> (rm0 + rm1) = rbt_share_map_\<alpha> rm0 + rbt_share_map_\<alpha> rm1\<close>
  by (simp add: plus_rbt_share_map_def add_rbt_share_map_\<alpha>')

instantiation rbt_share_map :: (linorder, type) strong_sepalg
begin

instance
proof
  fix x y z :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assume \<open>x \<sharp> y\<close> then show \<open>x + y \<sharp> z \<longleftrightarrow> y \<sharp> z \<and> x \<sharp> z\<close>
    using disjoint_rbt_share_map_def by fastforce
qed

end

instantiation rbt_share_map :: (linorder, type) cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>('a, 'b) rbt_share_map\<close>
  assume \<open>x + z = y + z\<close>
     and \<open>x \<sharp> z\<close>
     and \<open>y \<sharp> z\<close>
  then show \<open>x = y\<close>
    by (metis add_rbt_share_map_\<alpha> disjoint_rbt_share_map_def rbt_share_map_eqI sepalg_cancel)
qed

end

text\<open>The following studies domain-based separation of share maps. In particular, we essentially
show that a share map decomposes as the disjoint sum of singletons, indexed by the map's domain.\<close>

text\<open>The domain of a share map is the set of keys with non-zero associated share:\<close>

definition rbt_share_map_dom :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> 'k set\<close> where
  \<open>rbt_share_map_dom m \<equiv> rbt_ext_dom (rbt_share_map m)\<close>

lemma rbt_share_map_dom':
  fixes m :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  shows \<open>rbt_share_map_dom m = { k . rbt_share_map_\<alpha> m k \<noteq> No_Value }\<close>
by (clarsimp simp add: rbt_share_map_dom_def dom_def rbt_share_map_\<alpha>_def shareable_value_option_def
  split!: option.splits)

text\<open>The domain is always finite:\<close>
lemma rbt_share_map_dom_finite:
  shows \<open>finite (rbt_share_map_dom m)\<close>
by (simp add: rbt_share_map_dom_def rbt_ext_dom_finite) \<comment> \<open>It is a bit puzzling that this is so easy...\<close>

lemma rbt_share_map_empty_dom_is_empty:
  shows \<open>m = 0 \<longleftrightarrow> rbt_share_map_dom m = {}\<close>
by (cases m) (auto simp add: zero_rbt_share_map_def rbt_share_map_dom_def rbt_ext_empty_dom_is_empty)

lemma rbt_share_map_dom_empty[simp]:
  shows \<open>rbt_share_map_dom 0 = {}\<close>
by (simp add: rbt_share_map_empty_dom_is_empty[where m=0, simplified])

text\<open>Share maps with disjoint domain are disjoint w.r.t. the separation algebra structure
on share maps. Note that the converse is \<^emph>\<open>NOT\<close> true: One can also have disjointness on the
level of an individual share.\<close>
lemma share_map_disjoint_dom_is_disjoint:
    fixes m m' :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assumes \<open>rbt_share_map_dom m \<sharp> rbt_share_map_dom m'\<close>
    shows \<open>m \<sharp> m'\<close>
using assms by (clarsimp simp add: disjoint_rbt_share_map_def disjoint_fun_def) (metis
  Share_Map.rbt_share_map_\<alpha>_def assms disjoint_iff_not_equal disjoint_set_def
  disjoint_shareable_value.simps(1) disjoint_sym domIff rbt_share_map_dom_def
  shareable_value_option_simps(1))

text\<open>A singleton share map is a share map supported in a single key:\<close>
definition rbt_share_map_singleton :: \<open>'k::{linorder} \<Rightarrow> 'v shareable_value \<Rightarrow> ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_singleton k v \<equiv> rbt_share_map_update k v 0\<close>

lemma rbt_share_map_\<alpha>_singleton [simp]:
  shows \<open>rbt_share_map_\<alpha> (rbt_share_map_singleton k v) k' = (if k = k' then v else No_Value)\<close>
by (clarsimp simp add: rbt_share_map_dom' rbt_share_map_singleton_def zero_fun_def)

lemma rbt_share_map_singleton_dom [simp]:
  shows \<open>rbt_share_map_dom (rbt_share_map_singleton k v) = (if v = No_Value then {} else {k})\<close>
by (clarsimp simp add: rbt_share_map_dom')

text\<open>The converse is true as well:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma rbt_share_map_singleton_alt:
  assumes \<open>rbt_share_map_dom m = {k}\<close>
    shows \<open>m = rbt_share_map_singleton k (rbt_share_map_\<alpha> m k)\<close>
using assms by (auto simp add: rbt_share_map_dom' rbt_share_map_singleton_def zero_fun_def
  intro!: rbt_share_map_eqI ext)

lemma rbt_share_map_decompose_core:
  fixes m :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  shows \<open>m = rbt_share_map_update k No_Value m + rbt_share_map_singleton k (rbt_share_map_\<alpha> m k)\<close> (is ?g1)
    and \<open>rbt_share_map_update k No_Value m \<sharp> rbt_share_map_singleton k (rbt_share_map_\<alpha> m k)\<close> (is ?g2)
proof -
  show ?g1
    by (clarsimp intro!: rbt_share_map_eqI ext simp add: plus_fun_def)
next
  show ?g2
    by (intro share_map_disjoint_dom_is_disjoint; auto simp add: rbt_share_map_dom' disjoint_set_def)
qed

corollary rbt_share_map_decompose_core':
    fixes m :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assumes \<open>k \<notin> rbt_share_map_dom m\<close>
    shows \<open>rbt_share_map_update k v m = m + rbt_share_map_singleton k v\<close> (is ?g1)
      and \<open>m \<sharp> rbt_share_map_singleton k v\<close> (is ?g2)
proof -
  show ?g2
    using assms by (clarsimp intro!: share_map_disjoint_dom_is_disjoint simp add: disjoint_set_def)
next
  show ?g1
    using assms rbt_share_map_decompose_core by (clarsimp intro!: rbt_share_map_eqI ext simp add:
      plus_fun_def rbt_share_map_dom')
qed

corollary rbt_share_map_induct:
    fixes P :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> bool\<close>
  assumes Ibase: \<open>P 0\<close>
      and Istep: \<open>\<And>k sh v m. k \<notin> rbt_share_map_dom m \<Longrightarrow> P m \<Longrightarrow> P (rbt_share_map_update k (Shared_Value sh v) m)\<close>
    shows \<open>P m\<close>
proof -
  have \<open>card (rbt_share_map_dom m) = n \<Longrightarrow> P m\<close> for m and n :: \<open>nat\<close>
  proof (induction n arbitrary: m)
    case 0
    then show ?case
      by (metis Ibase card_0_eq rbt_share_map_dom_finite rbt_share_map_empty_dom_is_empty)
  next
    case (Suc n)
    then obtain k where k: \<open>k \<in> rbt_share_map_dom m\<close>
      by fastforce
    let ?m' = \<open>rbt_share_map_update k No_Value m\<close>
    have \<open>m = rbt_share_map_update k (rbt_share_map_\<alpha> m k) ?m'\<close>
      by (simp add: rbt_share_map_eqI)
    moreover have \<open>k \<notin> rbt_share_map_dom ?m'\<close>
      by (simp add: rbt_share_map_dom')
    moreover have \<open>rbt_share_map_dom ?m' = rbt_share_map_dom m - {k}\<close>
      by (auto simp: rbt_share_map_dom')
    then have \<open>card (rbt_share_map_dom ?m') = n\<close>
      by (simp add: Suc.prems k)
    ultimately show ?case
      using Suc 
      by (metis Istep fun_upd_triv rbt_share_map_\<alpha>_update rbt_share_map_eqI shareable_value.exhaust)
  qed
  then show ?thesis
    by auto
qed

text\<open>The following views a share map as a set of key-value-share triples:\<close>
definition rbt_share_map_entries :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow>
      ('k \<times> 'v \<times> nonempty_share) list\<close> where
  \<open>rbt_share_map_entries m \<equiv> rbt_ext_entries (rbt_share_map m)\<close>

abbreviation rbt_share_map_set :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow>
      ('k \<times> 'v \<times> nonempty_share) set\<close> where
  \<open>rbt_share_map_set m \<equiv> set (rbt_share_map_entries m)\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma rbt_share_map_set_bulkload:
  assumes \<open>distinct (map fst al)\<close>
    shows \<open>rbt_share_map_set (rbt_share_map_bulkload al) = set al\<close>
by (simp add: assms rbt_ext_bulkload_entries rbt_share_map_bulkload_def rbt_share_map_entries_def)

lemma rbt_share_map_set':
  shows \<open>rbt_share_map_set m = {(k, v, sh) . rbt_share_map_\<alpha> m k = Shared_Value sh v}\<close>
by (auto simp add: rbt_ext_set_alt rbt_share_map_entries_def rbt_share_map_\<alpha>_def
  shareable_value_option_def split!: option.splits)

definition rbt_share_map_top_from_map :: \<open>('k:: {linorder, enum} \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_top_from_map f \<equiv> RmShareMap (rbt_ext_from_map (\<lambda>k. (f k, \<top>)))\<close>

lemma rbt_share_map_\<alpha>_from_map:
  shows \<open>rbt_share_map_\<alpha> (rbt_share_map_top_from_map f) = Shared_Value \<top> \<circ> f\<close>
by (clarsimp simp add: rbt_share_map_top_from_map_def rbt_share_map_\<alpha>_def comp_def)

lemma rbt_share_map_set_from_map:
  shows \<open>rbt_share_map_set (rbt_share_map_top_from_map f) = (\<lambda>k. (k, f k, \<top>)) ` UNIV\<close>
by (auto simp add: rbt_share_map_set' rbt_share_map_\<alpha>_from_map)

lemma rbt_share_map_domain_from_map:
  shows \<open>rbt_share_map_dom (rbt_share_map_top_from_map f) = UNIV\<close>
by (simp add: rbt_share_map_dom' rbt_share_map_\<alpha>_from_map)

text\<open>\<^verbatim>\<open>rbt_share_map_dest\<close> refines the domain of a share map in the following way:\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma rbt_share_map_dest_to_domain:
  shows \<open>fst ` (rbt_share_map_set m) = rbt_share_map_dom m\<close> (is ?g1)
    and \<open>inj_on fst (rbt_share_map_set m)\<close> (is ?g2)
    and [simp]: \<open>finite (rbt_share_map_set m)\<close> (is ?g3)
by (auto simp add: rbt_share_map_entries_def rbt_share_map_dom_def rbt_ext_dest_to_domain)

lemma rbt_share_map_set_empty [simp]:
  shows \<open>rbt_share_map_set 0 = {}\<close>
by (simp add: rbt_share_map_entries_def zero_rbt_share_map_def)

lemma rbt_share_map_set_update [simp]:
  assumes \<open>rbt_share_map_\<alpha> m k = No_Value\<close>
    shows \<open>rbt_share_map_set (rbt_share_map_update k (Shared_Value sh v) m) = rbt_share_map_set m \<union> {(k, v, sh)}\<close>
      and \<open>(k, v, sh) \<notin> rbt_share_map_set m\<close>
using assms by (auto simp add: rbt_share_map_set' split!: if_splits)

abbreviation rbt_share_map_mset :: \<open>('k::{linorder}, 'v) rbt_share_map \<Rightarrow> ('k \<times> 'v \<times> nonempty_share) multiset\<close> where
  \<open>rbt_share_map_mset m \<equiv> mset_set (rbt_share_map_set m)\<close>

lemma rbt_share_map_mset_update [simp]:
  assumes \<open>rbt_share_map_\<alpha> m k = No_Value\<close>
    shows \<open>rbt_share_map_mset (rbt_share_map_update k (Shared_Value sh v) m) = {# (k, v, sh) #} + rbt_share_map_mset m\<close>
using assms by simp

text\<open>The following is a general way of saying that a share map decomposes as a finite sum
over its singleton submaps.\<close>

lemma rbt_share_map_decompose_generic:
    fixes m :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assumes \<open>\<And>k sh v. (k, v, sh) \<in> rbt_share_map_set m \<Longrightarrow> rbt_share_map_singleton k (Shared_Value sh v) \<Turnstile> P k sh v\<close>
    shows \<open>m \<Turnstile> \<star>\<star>{# P k sh v . (k, v, sh) \<leftarrow> rbt_share_map_mset m #}\<close>
  using assms 
proof (induct rule: rbt_share_map_induct)
  case 1
  then show ?case
    by (clarsimp simp add: asat_def asepconj_simp)
next
  case (2 k sh v m)
  then have ND': \<open>rbt_share_map_\<alpha> m k = No_Value\<close>
    by (simp add: rbt_share_map_dom')
  with 2 have IH: \<open>m \<Turnstile> \<star>\<star> {# P k sh v . (k, v, sh) \<leftarrow> rbt_share_map_mset m #}\<close>
    by simp
  let ?m' = \<open>rbt_share_map_update k (Shared_Value sh v) m\<close>
  let ?\<epsilon> = \<open>rbt_share_map_singleton k (Shared_Value sh v)\<close>
  have \<open>?m' = m + ?\<epsilon>\<close> and \<open>m \<sharp> ?\<epsilon>\<close>
    using \<open>k \<notin> rbt_share_map_dom m\<close> rbt_share_map_decompose_core' by blast+
  moreover from ND' 2 have \<open>?\<epsilon> \<Turnstile> P k sh v\<close>
    by simp
  ultimately have \<open>?m' \<Turnstile> P k sh v \<star> \<star>\<star>{# P k sh v . (k, v, sh) \<leftarrow> rbt_share_map_mset m #}\<close>
    by (metis IH asepconjI asepconj_comm)
  then show ?case
    using \<open>k \<notin> rbt_share_map_dom m\<close> by (clarsimp simp add: asat_def asepconj_simp rbt_share_map_dom')
qed    

lemma rbt_share_map_decompose_by_domain:
    fixes m :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assumes \<open>\<And>k sh v. (k, v, sh) \<in> rbt_share_map_set m \<Longrightarrow> rbt_share_map_singleton k (Shared_Value sh v) \<Turnstile> P k\<close>
    shows \<open>m \<Turnstile> \<star>\<star>{# P k . k \<leftarrow> mset_set (rbt_share_map_dom m) #}\<close>
  using assms  
proof (induct rule: rbt_share_map_induct)
  case 1
  then show ?case
    by (auto simp add: asat_def asepconj_simp)
next
  case (2 k sh v m)
  then have ND': \<open>rbt_share_map_\<alpha> m k = No_Value\<close>
    by (simp add: rbt_share_map_dom')
  with 2 have \<open>(\<And>k v sh. (k, v, sh) \<in> rbt_share_map_set m
                          \<Longrightarrow> rbt_share_map_singleton k (Shared_Value sh v) \<Turnstile> P k)\<close>
    by clarsimp
  with 2 have IH: \<open>m \<Turnstile> \<star>\<star> {# P k . k \<leftarrow> mset_set (rbt_share_map_dom m) #}\<close>
    by simp
  let ?m' = \<open>rbt_share_map_update k (Shared_Value sh v) m\<close>
  let ?\<epsilon> = \<open>rbt_share_map_singleton k (Shared_Value sh v)\<close>
  have \<open>?m' = m + ?\<epsilon>\<close> and \<open>m \<sharp> ?\<epsilon>\<close>
    using \<open>k \<notin> rbt_share_map_dom m\<close> rbt_share_map_decompose_core' by blast+
  moreover from ND' 2 have \<open>?\<epsilon> \<Turnstile> P k\<close>
    by simp
  ultimately have \<open>?m' \<Turnstile> P k \<star> \<star>\<star>{# P k . k \<leftarrow> mset_set (rbt_share_map_dom m) #}\<close>
    using IH asepconjI by fastforce
  moreover have \<open>rbt_share_map_dom ?m' = rbt_share_map_dom m \<union> { k }\<close>
    by (auto simp add: rbt_share_map_dom')
  moreover from this and \<open>k \<notin> rbt_share_map_dom m\<close> 
  have \<open>mset_set (rbt_share_map_dom ?m') = mset_set (rbt_share_map_dom m) + {# k #}\<close>
    by (metis Un_insert_right add_mset_add_single mset_set.insert rbt_share_map_dom_finite sup_bot.comm_neutral)
  ultimately show ?case
    by simp
qed

lemma rbt_share_map_decompose_by_domain':
    fixes m :: \<open>('k::{linorder}, 'v) rbt_share_map\<close>
  assumes \<open>ms = mset_set (rbt_share_map_dom m)\<close>
      and \<open>\<And>k sh v. (k, v, sh) \<in> rbt_share_map_set m \<Longrightarrow> rbt_share_map_singleton k (Shared_Value sh v) \<Turnstile> P k\<close>
    shows \<open>m \<Turnstile> \<star>\<star>{# P k . k \<leftarrow> ms #}\<close>
  using assms by (simp add: rbt_share_map_decompose_by_domain)


definition to_nonempty_share :: \<open>share \<Rightarrow> nonempty_share option\<close> where
  \<open>to_nonempty_share x \<equiv> if x = bot then None else Some (Abs_nonempty_share x)\<close>

lemma to_nonempty_share_nonempty:
  assumes \<open>bot < sh\<close>
    shows \<open>\<exists>sh'. to_nonempty_share sh = Some sh' \<and> Rep_nonempty_share sh' = sh\<close>
using assms by (clarsimp split: if_splits simp add: to_nonempty_share_def Abs_nonempty_share_inverse
  order_less_imp_not_eq2)

lemma to_nonempty_share_empty:
  assumes \<open>bot = sh\<close>
    shows \<open>to_nonempty_share sh = None\<close>
using assms by (clarsimp simp add: to_nonempty_share_def)

definition restrict_nonempty_share :: \<open>share \<Rightarrow> nonempty_share \<Rightarrow> nonempty_share option\<close> where
  \<open>restrict_nonempty_share sh0 sh1 \<equiv> to_nonempty_share (inf (Rep_nonempty_share sh1) sh0)\<close>

definition restrict_shareable_map :: \<open>('a \<Rightarrow> 'v shareable_value) \<Rightarrow> ('a \<Rightarrow> share) \<Rightarrow> ('a \<Rightarrow> 'v shareable_value)\<close> where
  \<open>restrict_shareable_map m p \<equiv> \<lambda>a.
     case m a of
       No_Value \<Rightarrow> No_Value
     | Shared_Value sh v \<Rightarrow>
         (case restrict_nonempty_share (p a) sh of
            None \<Rightarrow> No_Value
          | Some sh' \<Rightarrow> Shared_Value sh' v)\<close>

text\<open>Definining \<^term>\<open>restrict_shareable_map\<close> on the level of \<^typ>\<open>('k, 'v) rbt_share_map\<close>
is a little cumbersome since it is a combination of filtering and mapping.\<close>

definition share_restrict_transform :: \<open>('k :: linorder \<Rightarrow> share) \<Rightarrow>  'k \<Rightarrow> 'v \<times> nonempty_share \<Rightarrow>
      ('v \<times> nonempty_share) option\<close> where
  \<open>share_restrict_transform p k v_sh \<equiv>
     case v_sh of
       (v, sh) \<Rightarrow>
         (case restrict_nonempty_share (p k) sh of
            None     \<Rightarrow> None
          | Some sh' \<Rightarrow> Some (v, sh'))\<close>

definition rbt_share_map_restrict :: \<open>('k::{linorder} \<Rightarrow> share) \<Rightarrow> ('k, 'v) rbt_share_map \<Rightarrow>
      ('k, 'v) rbt_share_map\<close> where
  \<open>rbt_share_map_restrict p m \<equiv>
     RmShareMap (rbt_ext_filter_map (share_restrict_transform p) (rbt_share_map m))\<close>

lemma rbt_share_map_\<alpha>_restrict:
  shows \<open>rbt_share_map_\<alpha> (rbt_share_map_restrict p m) = restrict_shareable_map (rbt_share_map_\<alpha> m) p\<close>
by (auto intro!: ext simp add: restrict_shareable_map_def rbt_share_map_restrict_def
  rbt_share_map_\<alpha>_def share_restrict_transform_def shareable_value_option_def rbt_ext_correct
  split!: rbt_share_map.splits shareable_value.splits option.splits)

lemma sh_dom_restrict:
  shows \<open>sh_dom (restrict_shareable_map s p) = { a. inf (shareable_value_to_share (s a)) (p a) \<noteq> bot }\<close>
  by (auto simp add: sh_dom_def restrict_shareable_map_def to_nonempty_share_def
    restrict_nonempty_share_def shareable_value_to_share_def split: shareable_value.splits)

lemma restrict_shareable_map_perms:
  fixes m :: \<open>nat \<Rightarrow> 'v shareable_value\<close>
    and p :: \<open>nat \<Rightarrow> share\<close>
  shows \<open>shareable_value_to_share ((restrict_shareable_map m p) k) = inf (shareable_value_to_share (m k)) (p k)\<close>
  apply (clarsimp simp add: shareable_value_to_share_def restrict_shareable_map_def
   split!: shareable_value.splits option.splits)
  apply (metis bot.not_eq_extremum option.distinct(1) option.inject restrict_nonempty_share_def
    to_nonempty_share_empty to_nonempty_share_nonempty)
  apply (metis option.distinct(1) restrict_nonempty_share_def to_nonempty_share_def)
  done

lemma restrict_shareable_map_disjoint:
  assumes \<open>p1 \<sharp> p2\<close>
    shows \<open>restrict_shareable_map m p1 \<sharp> restrict_shareable_map m p2\<close>
using assms by (clarsimp split: shareable_value.splits option.splits simp add:
  Abs_nonempty_share_inverse bot.not_eq_extremum inf_assoc inf_left_commute
  restrict_nonempty_share_def disjoint_fun_def restrict_shareable_map_def to_nonempty_share_def
  disjoint_share_def)

(*<*)
end
(*>*)
