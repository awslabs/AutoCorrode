(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Read_Write_Resource
  imports Crush.Crush
    Shallow_Separation_Logic.Assertion_Language
begin

section\<open>Random-access resources\<close>

text\<open>This theory defines an abstraction for a read/write-accessible resource.
It then shows that separation lenses to \<^verbatim>\<open>shareable_value\<close>'s provide concrete
realizations of that interface.\<close>

subsection\<open>Abstract RW interface\<close>

datatype_record ('s, 'a, 'abort, 'i, 'o) rw_resource =
  rw_resource_is :: \<open>share \<Rightarrow> 'a \<Rightarrow> 's assert\<close>
  rw_resource_read :: \<open>('s, 'a, 'abort, 'i, 'o) function_body\<close>
  rw_resource_write :: \<open>'a \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>

definition generic_read_contract :: \<open>(share \<Rightarrow> 'v \<Rightarrow> 's::{sepalg} assert) \<Rightarrow> 'v \<Rightarrow>
                                       share \<Rightarrow> ('s, 'v, 'abort) function_contract\<close> where
  \<open>generic_read_contract \<equiv> \<lambda>has v sh.
     let pre = has sh v in
     let post = \<lambda>r. has sh v \<star> \<langle>r = v\<rangle> in
     make_function_contract pre post\<close>

definition generic_write_contract :: \<open>(share \<Rightarrow> 'v \<Rightarrow> 's::{sepalg} assert) \<Rightarrow>  'v \<Rightarrow>
                                         ('s, unit, 'abort) function_contract\<close> where
  \<open>generic_write_contract \<equiv> \<lambda>has v.
     let pre = \<Squnion>v0. has \<top> v0 in
     let post = \<lambda>r. has \<top> v in
     make_function_contract pre post\<close>

definition standard_rw_resource :: \<open>('s::{sepalg}, 'v, 'abort, 'i prompt, 'o prompt_output) rw_resource \<Rightarrow> bool\<close>
  where
  \<open>standard_rw_resource r \<equiv>
    (\<forall>sh0 sh1 v. 0 < sh0 \<longrightarrow> 0 < sh1 \<longrightarrow> sh0 \<sharp> sh1 \<longrightarrow>
        rw_resource_is r (sh0 + sh1) v \<longlongrightarrow> rw_resource_is r sh0 v \<star> rw_resource_is r sh1 v) \<and>
    (\<forall>sh0 sh1 v0 v1. rw_resource_is r sh0 v0 \<star> rw_resource_is r sh1 v1
        \<longlongrightarrow> \<langle>sh0 \<sharp> sh1\<rangle> \<star> \<langle>v0 = v1\<rangle> \<star>
          rw_resource_is r (sh0 + sh1) v0) \<and>
    (\<forall>\<Gamma> v. \<Gamma> ; rw_resource_write r v \<Turnstile>\<^sub>F generic_write_contract (rw_resource_is r) v) \<and>
    (\<forall>\<Gamma> v sh. \<Gamma> ; rw_resource_read r \<Turnstile>\<^sub>F generic_read_contract (rw_resource_is r) v sh)\<close>

lemma standard_rw_resourceI:
  assumes \<open>\<And>sh0 sh1 v. 0 < sh0 \<Longrightarrow> 0 < sh1 \<Longrightarrow> sh0 \<sharp> sh1 \<Longrightarrow>
        rw_resource_is r (sh0 + sh1) v \<longlongrightarrow> rw_resource_is r sh0 v \<star> rw_resource_is r sh1 v\<close>
     and \<open>\<And>sh0 sh1 v0 v1. rw_resource_is r sh0 v0 \<star> rw_resource_is r sh1 v1
        \<longlongrightarrow> \<langle>sh0 \<sharp> sh1\<rangle> \<star> \<langle>v0 = v1\<rangle> \<star>
          rw_resource_is r (sh0 + sh1) v0\<close>
     and \<open>\<And>\<Gamma> v. \<Gamma> ; rw_resource_write r v \<Turnstile>\<^sub>F generic_write_contract (rw_resource_is r) v\<close>
     and \<open>\<And>\<Gamma> v sh. \<Gamma> ; rw_resource_read r \<Turnstile>\<^sub>F generic_read_contract (rw_resource_is r) v sh\<close>
   shows \<open>standard_rw_resource r\<close>
  using assms unfolding standard_rw_resource_def by simp

lemma standard_rw_resource_read_spec:
  assumes \<open>standard_rw_resource r\<close>
  shows [simplified generic_read_contract_def Let_def]:
     \<open>\<Gamma> ; rw_resource_read r \<Turnstile>\<^sub>F generic_read_contract (rw_resource_is r) v sh\<close>
  using assms standard_rw_resource_def by fastforce

lemma standard_rw_resource_write_spec:
  assumes \<open>standard_rw_resource r\<close>
  shows [simplified generic_write_contract_def Let_def]:
    \<open>\<Gamma> ; rw_resource_write r v \<Turnstile>\<^sub>F generic_write_contract (rw_resource_is r) v\<close>
  using assms standard_rw_resource_def by fastforce

lemma standard_rw_resource_combine:
  assumes \<open>standard_rw_resource reg\<close>
  shows
     \<open>rw_resource_is reg sh1 a1 \<star> rw_resource_is reg sh2 a2 \<longlongrightarrow>
      rw_resource_is reg (sh1+sh2) a1 \<star> \<langle>sh1\<sharp>sh2 \<and> a1 = a2\<rangle>\<close>
  using assms by (simp add: asepconj_comm asepconj_pure2_precise standard_rw_resource_def)

lemma standard_rw_resource_split:
  assumes
    \<open>standard_rw_resource reg\<close>
    \<open>sh1 \<sharp> sh2\<close> \<open>sh = sh1 + sh2\<close> \<open>0 < sh1\<close> \<open>0 < sh2\<close>
  shows
    \<open>rw_resource_is reg sh a \<longlongrightarrow>
     rw_resource_is reg sh1 a \<star> rw_resource_is reg sh2 a\<close>
  using assms by (simp add: standard_rw_resource_def)

end
