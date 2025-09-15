(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Arithmetic
  imports Crush.Crush StdLib_References
begin
(*>*)

subsection\<open>Arithmetic\<close>

definition overflowing_mul :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_mul x y \<equiv> FunctionBody(literal (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil))\<close>

definition overflowing_add :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_add x y \<equiv> FunctionBody (literal (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil))\<close>

definition wrapping_add_unsigned :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_add_unsigned \<equiv> \<lambda>self rhs. FunctionBody (literal (self + rhs))\<close>

definition word_sub_saturating_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word\<close> where
  \<open>word_sub_saturating_core e f \<equiv> if e < f then 0 else e - f\<close>

definition saturating_sub :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>saturating_sub e f \<equiv> FunctionBody (literal (word_sub_saturating_core e f))\<close>

definition checked_mul_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_mul_core w v \<equiv>
     if unat w * unat v \<ge> 2^LENGTH('a) then None else Some (w * v)\<close>

definition checked_add_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_add_core w v \<equiv>
     if unat w + unat v \<ge> 2^LENGTH('a) then None else Some (w + v)\<close>

definition checked_mul :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_mul w v \<equiv> FunctionBody (literal (checked_mul_core w v))\<close>

definition checked_add :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_add w v \<equiv> FunctionBody (literal (checked_add_core w v))\<close>

definition div_ceil_pure :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close> where
  \<open>div_ceil_pure x y \<equiv> (x + y - 1) div y\<close>

definition div_ceil :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('machine, 'a word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_ceil x y \<equiv> FunctionBody (literal (div_ceil_pure x y))\<close>

\<comment> \<open>Contracts and verifications\<close>

definition overflowing_mul_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close> where
  [crush_contracts]: \<open>overflowing_mul_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in \<comment> \<open>Any inputs are acceptable\<close>
    let post = \<lambda>ret. \<langle>ret = (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil)\<rangle> in \<comment> \<open>The specification is not different from the function body\<close>
      make_function_contract pre post\<close>
ucincl_auto overflowing_mul_contract

lemma overflowing_mul_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_mul x y \<Turnstile>\<^sub>F overflowing_mul_contract x y\<close>
by (crush_boot f: overflowing_mul_def contract: overflowing_mul_contract_def) crush_base

definition overflowing_add_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close>where
  [crush_contracts]: \<open>overflowing_add_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in
    let post = \<lambda>ret. \<langle>ret = (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto overflowing_add_contract

lemma overflowing_add_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_add x y \<Turnstile>\<^sub>F overflowing_add_contract x y\<close>
by (crush_boot f: overflowing_add_def contract: overflowing_add_contract_def) crush_base

definition wrapping_add_unsigned_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_add_unsigned_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in
    let post = \<lambda>ret. \<langle>ret = x + y\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto wrapping_add_unsigned_contract

lemma wrapping_add_unsigned_spec [crush_specs]:
  shows \<open>\<Gamma> ; wrapping_add_unsigned x y \<Turnstile>\<^sub>F wrapping_add_unsigned_contract x y\<close>
by (crush_boot f: wrapping_add_unsigned_def contract: wrapping_add_unsigned_contract_def) crush_base

definition saturating_sub_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>saturating_sub_contract x y \<equiv>
    let pre = \<langle>True\<rangle> in
    let post = \<lambda>ret. \<langle>ret = (if x < y then 0 else x - y)\<rangle> in
      make_function_contract pre post\<close>
ucincl_auto saturating_sub_contract

lemma saturating_sub_spec [crush_specs]:
  shows \<open>\<Gamma> ; saturating_sub x y \<Turnstile>\<^sub>F saturating_sub_contract x y\<close>
by (crush_boot f: saturating_sub_def contract: saturating_sub_contract_def)
  (crush_base simp add: word_sub_saturating_core_def)

definition div_ceil_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>div_ceil_contract x y \<equiv>
    let pre  = \<top>;
        post = \<lambda>ret. \<langle>ret = (x + y - 1) div y\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto div_ceil_contract

lemma div_ceil_spec [crush_specs]:
  shows \<open>\<Gamma> ; div_ceil x y \<Turnstile>\<^sub>F div_ceil_contract x y\<close>
by (crush_boot f: div_ceil_def contract: div_ceil_contract_def) (crush_base simp add: div_ceil_pure_def)

section\<open>\<^verbatim>\<open>NonZeroU64\<close>\<close>

typedef nonzero_u64 = \<open>{ w::64 word. w \<noteq> 0 }\<close>
  morphisms nonzero_u64_project nonzero_u64_inject
proof -
  have \<open>1 \<in> { w::64 word. w \<noteq> 0 }\<close>
    by simp
  from this show ?thesis
    by blast
qed

setup_lifting type_definition_nonzero_u64

lift_definition nonzerou64_new_core :: \<open>64 word \<Rightarrow> nonzero_u64 option\<close> is
  \<open>\<lambda>(n::64 word). if n = 0 then None else Some n\<close> by simp

definition nonzerou64_new :: \<open>64 word \<Rightarrow> ('machine, nonzero_u64 option, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzerou64_new n \<equiv> FunctionBody (if n = 0 then literal None else literal (Some (nonzero_u64_inject n)))\<close>
notation_nano_rust_function nonzerou64_new ("NonZeroU64::new")

definition nonzerou64_new_contract :: \<open>64 word \<Rightarrow>
      ('machine::{sepalg}, nonzero_u64 option, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzerou64_new_contract n \<equiv>
     let pre  = \<top>;
         post = \<lambda>res. \<langle>res = nonzerou64_new_core n\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto nonzerou64_new_contract

lemma nonzerou64_new_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzerou64_new n \<Turnstile>\<^sub>F nonzerou64_new_contract n\<close>
by (crush_boot f: nonzerou64_new_def contract: nonzerou64_new_contract_def) (crush_base simp add: nonzerou64_new_core_def)

definition nonzerou64_get :: \<open>nonzero_u64 \<Rightarrow> ('machine, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzerou64_get self \<equiv> FunctionBody (literal (nonzero_u64_project self))\<close>

definition nonzerou64_get_contract :: \<open>nonzero_u64 \<Rightarrow> ('machine::{sepalg}, 64 word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzerou64_get_contract nz \<equiv>
     let pre  = \<top>;
         post = \<lambda>res. \<langle>res = nonzero_u64_project nz\<rangle>
      in make_function_contract pre post\<close>
ucincl_auto nonzerou64_get_contract

lemma nonzero_u64_get_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzerou64_get nz \<Turnstile>\<^sub>F nonzerou64_get_contract nz\<close>
  apply (crush_boot f: nonzerou64_get_def contract: nonzerou64_get_contract_def)
  apply (cases nz)
  apply (simp add: aentails_refl asepconj_False_True(2) asepconj_UNIV_idempotent wp_literalI)
  done

(*<*)
end
(*>*)