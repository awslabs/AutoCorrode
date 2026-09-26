(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Locality
  imports Assertion_Language
begin

context sepalg begin
(*>*)

definition is_local :: \<open>('a \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool) \<Rightarrow> 'a assert \<Rightarrow> bool\<close> where
  \<open>is_local R \<phi> \<equiv> \<forall>\<sigma>_0 \<sigma>_1. \<sigma>_0 \<sharp> \<sigma>_1 \<longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<longrightarrow>
      ((\<forall>\<sigma>_0' v. R \<sigma>_0 (v, \<sigma>_0') \<longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1) \<and>
       (\<forall>\<sigma>' v. R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>') \<longleftrightarrow> (\<exists>\<sigma>_0'. R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1)))\<close>

definition is_local0 :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a assert \<Rightarrow> bool\<close> where
  \<open>is_local0 R \<phi> \<equiv> \<forall>\<sigma>_0 \<sigma>_1. \<sigma>_0 \<sharp> \<sigma>_1 \<longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<longrightarrow>
      ((\<forall>\<sigma>_0'. R \<sigma>_0 \<sigma>_0' \<longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1) \<and>
       (\<forall>\<sigma>'. R (\<sigma>_0 + \<sigma>_1) \<sigma>' \<longleftrightarrow> (\<exists>\<sigma>_0'. R \<sigma>_0 \<sigma>_0' \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1)))\<close>

definition lift_rel0 :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> (unit \<times> 'a) \<Rightarrow> bool)\<close> where
  \<open>lift_rel0 R \<equiv> \<lambda>x (_,y). R x y\<close>

lemma is_local0_is_local:
  shows \<open>is_local0 R \<phi> \<longleftrightarrow> is_local (lift_rel0 R) \<phi>\<close>
by (auto simp add: is_local0_def is_local_def lift_rel0_def)

lemma is_localI:
  assumes \<open>\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v. \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow> R \<sigma>_0 (v, \<sigma>_0') \<Longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1\<close>
      and \<open>\<And>\<sigma>_0 \<sigma>_1 \<sigma>' v.  \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow>  R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>') \<Longrightarrow>
               (\<exists>\<sigma>_0'. R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1)\<close>
      and \<open>\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v \<sigma>'.  \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow>
               R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1 \<Longrightarrow> R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')\<close>
    shows \<open>is_local R \<phi>\<close>
using assms by (auto simp add: is_local_def) blast

lemma is_localD:
  assumes \<open>is_local R \<phi>\<close>
    shows \<open>(\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v. \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow> R \<sigma>_0 (v, \<sigma>_0') \<Longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1)
        &&& (\<And>\<sigma>_0 \<sigma>_1 \<sigma>' v.  \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow>
             R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>') \<Longrightarrow> (\<exists>\<sigma>_0'. R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1))
        &&& (\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v \<sigma>'.  \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow>
             R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1 \<Longrightarrow> R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>'))\<close>
using assms by (auto simp add: is_local_def) blast

lemma is_localE:
  assumes \<open>is_local R \<phi>\<close>
      and \<open>(\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v. \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow> R \<sigma>_0 (v, \<sigma>_0') \<Longrightarrow> \<sigma>_0' \<sharp> \<sigma>_1) \<Longrightarrow>
              (\<And>\<sigma>_0 \<sigma>_1 \<sigma>' v.  \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow>
                 R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>') \<Longrightarrow> (\<exists>\<sigma>_0'. R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1)) \<Longrightarrow>
           (\<And>\<sigma>_0 \<sigma>_1 \<sigma>_0' v \<sigma>'.  \<sigma>_0 \<sharp> \<sigma>_1 \<Longrightarrow> \<sigma>_0 \<Turnstile> \<phi> \<Longrightarrow>
                 R \<sigma>_0 (v, \<sigma>_0') \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1 \<Longrightarrow> R (\<sigma>_0 + \<sigma>_1) (v, \<sigma>')) \<Longrightarrow> Q\<close>
    shows \<open>Q\<close>
using assms by (force dest!: is_localD)

text\<open>Note that the converse of the following lemma is not true:\<close>
lemma is_local_disj:
  assumes \<open>is_local R \<phi>\<close>
      and \<open>is_local S \<phi>\<close>
    shows \<open>is_local (\<lambda>a b. R a b \<or> S a b) \<phi>\<close>
using assms by (elim is_localE, intro is_localI) metis+

lemma is_local_Union:
  assumes \<open>\<And>x. is_local R (\<phi> x)\<close>
    shows \<open>is_local R (\<Union>x. \<phi> x)\<close>
  using assms
  unfolding asat_def is_local_def by blast

lemma is_local0_Union:
  assumes \<open>\<And>x. is_local0 R (\<phi> x)\<close>
    shows \<open>is_local0 R (\<Union>x. \<phi> x)\<close>
using assms by (auto intro: is_local_Union simp add: is_local0_is_local lift_rel0_def)

lemma is_local_Union':
  assumes \<open>\<And>\<phi>. \<phi> \<in> \<Phi> \<Longrightarrow> is_local R \<phi>\<close>
    shows \<open>is_local R (\<Union>\<Phi>)\<close>
  using assms
  unfolding asat_def is_local_def by blast

\<comment>\<open>TODO: This lemma is currently unused -- remove?\<close>
lemma is_local0_Union':
  assumes \<open>\<And>\<phi>. \<phi> \<in> \<Phi> \<Longrightarrow> is_local0 R \<phi>\<close>
    shows \<open>is_local0 R (\<Union>\<Phi>)\<close>
  by (meson assms is_local0_is_local is_local_Union')

lemma is_local_bUnion:
  assumes \<open>\<And>x. x\<in>S \<Longrightarrow> is_local R (\<phi> x)\<close>
    shows \<open>is_local R (\<Union>x\<in>S. \<phi> x)\<close>
  by (metis (mono_tags, lifting) assms imageE is_local_Union')

\<comment>\<open>TODO: This lemma is currently unused -- remove?\<close>
lemma is_local0_bUnion:
  assumes \<open>\<And>x. x\<in>S \<Longrightarrow> is_local0 R (\<phi> x)\<close>
    shows \<open>is_local0 R (\<Union>x\<in>S. \<phi> x)\<close>
using assms by (auto intro: is_local_bUnion simp add: is_local0_is_local lift_rel0_def)

lemma is_local_weaken:
  assumes \<open>is_local R \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>is_local R \<phi>\<close>
  using assms
  unfolding is_local_def aentails_def by blast

\<comment>\<open>TODO: This lemma is currently unused -- remove?\<close>
lemma is_local0_weaken:
  assumes \<open>is_local0 R \<psi>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi>\<close>
    shows \<open>is_local0 R \<phi>\<close>
  using assms is_local0_is_local is_local_weaken by blast

lemma is_local_empty:
  shows \<open>is_local R \<bottom>\<close>
  by (simp add: local.is_local_def)

\<comment>\<open>TODO: This lemma is currently unused -- remove?\<close>
lemma is_local0_empty:
  shows \<open>is_local0 R \<bottom>\<close>
  by (auto intro: is_local_empty simp add: is_local0_is_local lift_rel0_def)

lemma is_local_frame:
  assumes \<open>is_local R \<phi>\<close>
  shows \<open>is_local R (\<phi> \<star> \<pi>)\<close>
proof -
  {
       fix \<sigma>A \<sigma>B \<sigma>C v \<sigma>'
    assume \<open>\<sigma>A \<sharp> \<sigma>B\<close>
       and \<open>\<sigma>A \<Turnstile> \<phi>\<close>
       and \<open>\<sigma>C \<sharp> (\<sigma>A + \<sigma>B)\<close>
       and \<open>R (\<sigma>A + \<sigma>B + \<sigma>C) (v, \<sigma>')\<close>
    moreover from this have \<open>(\<sigma>B + \<sigma>C) \<sharp> \<sigma>A\<close>
      by auto
    ultimately have \<open>\<exists>\<sigma>A'. R \<sigma>A (v, \<sigma>A') \<and> \<sigma>' = \<sigma>A' + \<sigma>B + \<sigma>C\<close>
      using assms unfolding is_local_def
      by (metis local.disjoint_sym local.sepalg_apart_plus local.sepalg_assoc)
  } moreover {
       fix \<sigma>A \<sigma>B \<sigma>C v \<sigma>AB'
    assume \<open>\<sigma>A \<sharp> \<sigma>B\<close>
       and \<open>\<sigma>A \<Turnstile> \<phi>\<close>
       and \<open>\<sigma>C \<sharp> (\<sigma>A + \<sigma>B)\<close>
       and \<open>R (\<sigma>A + \<sigma>B) (v, \<sigma>AB')\<close>
    moreover from this have \<open>\<sigma>B \<sharp> \<sigma>C\<close> and \<open>(\<sigma>B + \<sigma>C) \<sharp> \<sigma>A\<close>
      by auto
    ultimately have \<open>R (\<sigma>A + \<sigma>B + \<sigma>C) (v, \<sigma>AB' + \<sigma>C)\<close>
      using assms unfolding is_local_def
      by (smt (verit) local.disjoint_sym local.sepalg_apart_plus local.sepalg_assoc)
  }
  ultimately show ?thesis
    using assms
    unfolding is_local_def asepconj_def asat_def mem_Collect_eq
    by (smt (verit, ccfv_threshold) disjoint_sym sepalg_apart_assoc sepalg_apart_plus)
qed

\<comment>\<open>TODO: This lemma is currently unused -- remove?\<close>
lemma is_local0_frame:
  assumes \<open>is_local0 R \<phi>\<close>
    shows \<open>is_local0 R (\<phi> \<star> \<pi>)\<close>
  using assms is_local0_is_local is_local_frame by blast

lemma is_local_upwards_closure:
  shows \<open>is_local R (\<phi> \<star> \<top>) = is_local R \<phi>\<close> (is ?g1)
    and \<open>is_local R (\<top> \<star> \<phi>) = is_local R \<phi>\<close> (is ?g2)
proof -
  show ?g1 using is_local_frame is_local_weaken
    aentails_refl local.aentails_top_R' local.ucincl_UNIV by blast
  from this show ?g2 using asepconj_comm
    by auto
qed

lemma is_local_hoist_pure:
  shows \<open>is_local R (\<phi> \<star> apure (P)) \<longleftrightarrow> P \<longrightarrow> is_local R \<phi>\<close>
  by (simp add: apure_def is_local_empty is_local_upwards_closure(1) local.asepconj_bot_zero2)

lemma is_local_False:
  shows \<open>is_local (\<lambda>x (v, y). False) \<phi>\<close>
by (clarsimp simp add: is_local_def)

text\<open>The only local relation with the empty footprint is the identity. More precisely:\<close>

lemma is_local_UNIV_0:
  assumes \<open>is_local R UNIV\<close>
     and \<open>R 0 (v, \<sigma>)\<close>
   shows \<open>\<sigma> = 0\<close>
  using assms unfolding asat_def is_local_def by blast

lemma is_local_UNIV:
  shows \<open>is_local R UNIV \<longleftrightarrow> (\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> R 0 (v, 0))\<close>
proof (safe)
     fix \<sigma> \<sigma>' v
  assume \<open>is_local R UNIV\<close>
     and \<open>R \<sigma> (v, \<sigma>')\<close>
  then show \<open>R 0 (v, 0)\<close> and \<open>\<sigma> = \<sigma>'\<close>
    by (metis asat_connectives_characterisation(1) is_localE is_local_UNIV_0 local.sepalg_ident local.zero_disjoint2)+
next
     fix \<sigma> v
  assume \<open>is_local R UNIV\<close>
     and \<open>R 0 (v, 0)\<close>
  from this show \<open>R \<sigma> (v, \<sigma>)\<close>
    by (metis asat_connectives_characterisation(1) is_localE sepalg_ident zero_disjoint2)
next
  assume \<open>\<forall>\<sigma> \<sigma>' v. R \<sigma> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> R 0 (v, 0)\<close>
  then show \<open>is_local R UNIV\<close>
    unfolding is_local_def by metis
qed
(*<*)
end

end
(*>*)
