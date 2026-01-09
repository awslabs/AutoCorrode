(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Iterators
  imports Crush.Crush StdLib_References
begin
(*>*)

\<comment>\<open>Force one-by-one unrolling of loops\<close>
declare raw_for_loop_unroll_once_cong[crush_cong]

definition find ::
  \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
   ('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
   ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>find self predicate \<equiv> FunctionBody \<lbrakk>
    for x in self {
      if predicate(x) { return Some(x); }
    };
    None
  \<rbrakk>\<close>

definition enumerate :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
      ('s, ('s, 64 word \<times> 'v \<times> tnil, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>enumerate self \<equiv> FunctionBody (literal (make_iterator (mapi (\<lambda>i f. FunctionBody \<lbrakk>
      let feval = f();
      (\<llangle>word_of_nat i\<rrangle>, feval)
    \<rbrakk>) (iterator_thunks self))))\<close>

definition any :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
    ('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
    ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>any self predicate \<equiv> FunctionBody \<lbrakk>
     match self.find(predicate) {
       Some(_) \<Rightarrow> True,
       None    \<Rightarrow> False
     }
   \<rbrakk>\<close>

definition count :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
      ('s, 64 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count self \<equiv> FunctionBody \<lbrakk>
    \<llangle>of_nat \<circ> length \<circ> iterator_thunks\<rrangle>\<^sub>1(self)
   \<rbrakk>\<close>

context reference
begin

definition iter_mut ::
  \<open>('a, 'b, 'v list) ref \<Rightarrow> ('s, ('s, ('a, 'b, 'v) ref, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  where
  \<open>iter_mut ref \<equiv> FunctionBody \<lbrakk>
    let xs = *ref;
    \<llangle>make_iterator_from_list (List.map (\<lambda>i. (focus_nth i ref)) [0 ..< length xs])\<rrangle>
  \<rbrakk>\<close>

(*<*)
end
(*>*)

subsection\<open>Debug printing\<close>

instantiation iterator :: (type, type, type, type, type)generate_debug
begin

definition generate_debug_iterator :: \<open>('a, 'b, 'c, 'd, 'e) iterator \<Rightarrow> log_data\<close> where
  \<open>generate_debug_iterator i \<equiv> [str ''<Iterator (length ='', LogNat (iterator_len i), str ''>'']\<close>

instance ..

end

(*<*)
end
(*>*)