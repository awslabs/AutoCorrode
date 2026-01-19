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


definition iterator_find_contract :: \<open>'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
  ('machine::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('a \<Rightarrow> ('machine, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('machine, 'a option, 'abort) function_contract\<close> where
  \<open>iterator_find_contract vs pred_pure \<Gamma> pred_rust \<equiv>
    let pre = \<langle>\<forall> i. \<Gamma>; pred_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (pred_pure i)\<rangle> in
    let post = \<lambda> ret. \<langle>ret = List.find pred_pure vs\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto iterator_find_contract

declare lift_pure_to_contract_def [crush_contracts]
ucincl_auto lift_pure_to_contract

lemma iterator_find_spec:
  shows \<open>\<Gamma> ; StdLib_Iterators.find (make_iterator_from_list vs) pred_rust \<Turnstile>\<^sub>F iterator_find_contract vs pred_pure \<Gamma> pred_rust\<close>
proof (crush_boot f: StdLib_Iterators.find_def contract: iterator_find_contract_def, goal_cases)
  case 1
  note pred_spec = this[THEN spec]
  show ?case proof (crush_base inline: iterator_into_iter_def, induction vs)
    case Nil
    then show ?case
      by (crush_base simp add: raw_for_loop_def)
  next
    case (Cons a vs)
    note IH = this
    show ?case
      apply (crush_base specs add: pred_spec)
      apply (cases \<open>pred_pure a\<close>)
       apply crush_base
      apply (subst List.find.simps(2), simp)
      by (rule IH)
  qed
qed

(*<*)
end
(*>*)
