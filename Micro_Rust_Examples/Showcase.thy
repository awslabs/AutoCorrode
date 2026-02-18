(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Showcase
  imports
    Micro_Rust_Std_Lib.StdLib_All
begin
(*>*)

section\<open>AutoCorrode showcase\<close>

text\<open>This file contains a concise showcase of some of AutoCorrode's verification infrastructure.
We start with below '\<^verbatim>\<open>locale\<close>'. This is some boilerplate that you can ignore for now:
it is responsible for making various types available as being mutable and allocatable.\<close>
locale showcase_ctx =
    reference reference_types +
    \<comment> \<open>Import \<^verbatim>\<open>reference_allocatable\<close> so we can allocate references for \<^verbatim>\<open>64 word\<close>.\<close>
    ref_word64: reference_allocatable reference_types _ _ _ _ _ _ _ word64_prism +
    ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism +
    ref_bool: reference_allocatable reference_types _ _ _ _ _ _ _ bool_prism
  for 
  reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  \<comment> \<open>Ignore for now\<close>
  and word64_prism :: \<open>('gv, 64 word) prism\<close>
  and bool_prism :: \<open>('gv, bool) prism\<close>
  and nat_prism :: \<open>('gv, nat) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word64.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_bool.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun
text\<open>That was it for the boilerplate, now we can proceed with verifying some Rust!\<close>

text\<open>This first example relies on local mutable variables. The syntax is eyeball-close
to Rust: this is a dialect of Rust we call uRust. uRust is shallowly embedded in
Isabelle/HOL, so we can 'escape' the uRust syntax if needed or convenient.
This is done here with \<^verbatim>\<open>\<llangle>_\<rrangle>\<close>, used in this example for providing type annotations.\<close>
definition ref_test where \<open>ref_test \<equiv> FunctionBody \<lbrakk>
    let mut nat_ref = \<llangle>0 :: nat\<rrangle>;
    let mut bool_ref = \<llangle>False :: bool\<rrangle>;
    if *bool_ref {
      nat_ref = 42;
    } else {
      nat_ref = 12;
    };
    *nat_ref
  \<rbrakk>\<close>

text\<open>For more in-depth details on uRust (including ways to symbolically evaluate it),
see \<^file>\<open>Basic_Micro_Rust.thy\<close>.\<close>

text\<open>We can now write down the specification or \<^emph>\<open>contract\<close> of this function:
it should always return \<^term>\<open>12 :: nat\<close>. However, executing this functions requires
the allocation of local mutables. Owning the \<^term>\<open>can_alloc_reference\<close> resource makes
sure that we have the capability to do this.
Note also the embedding of a pure fact \<^verbatim>\<open>r = 12\<close> into separation logic via the
\<^verbatim>\<open>\<langle>_\<rangle>\<close> antiquotation.\<close>
definition ref_test_contract where
  \<open>ref_test_contract \<equiv>
     let pre  = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = 12\<rangle> in
     make_function_contract pre post\<close>
text\<open>The \<^verbatim>\<open>ucincl_auto\<close> command is necessary boilerplate for every contract, ignore for now.\<close>
ucincl_auto ref_test_contract

text\<open>Now we prove that the function satisfies the contract!\<close>
lemma ref_test_spec:
  shows \<open>\<Gamma>; ref_test \<Turnstile>\<^sub>F ref_test_contract\<close>
\<comment> \<open>\<^verbatim>\<open>crush_boot\<close> unfolds function and contract, and turns the satisfies contract goal \<^verbatim>\<open>\<Turnstile>\<^sub>F\<close>
into a symbolic execution goal \<^verbatim>\<open>\<Delta> \<turnstile> WP e _\<close> in weakest-precondition style.\<close>
  apply (crush_boot f: ref_test_def contract: ref_test_contract_def)
\<comment> \<open>\<^verbatim>\<open>crush_base\<close> calls the automation, which fully automatically proves this goal\<close>
  apply crush_base
  done

text\<open>Let's make this a bit more interesting, and verify the classic \<^verbatim>\<open>swap\<close> function\<close>
definition swap_ref :: \<open>('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> ('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>swap_ref rA rB \<equiv> FunctionBody \<lbrakk>
     let oldA = *rA;
     let oldB = *rB;
     rA = oldB;
     rB = oldA;
  \<rbrakk>\<close>

text\<open>The contract of \<^term>\<open>swap_ref\<close> might differ slightly from what you'd expect, specifically
in the arguments of the points-to connective \<^verbatim>\<open>\<mapsto>\<close>. \<^term>\<open>l \<mapsto>\<langle>s\<rangle> g\<down>v\<close> describes the resource where we
partially own (indicated by share \<^term>\<open>s :: share\<close>) a location \<^term>\<open>l :: ('addr, 'gv, 'v) Global_Store.ref\<close> that
points to a 'global' value \<^term>\<open>g :: 'gv\<close>, which we currently read/interpret as a value
\<^term>\<open>v :: 'v\<close>. You can think of \<^term>\<open>g :: 'gv\<close> being a bitwise representation of an actual
value \<^term>\<open>v :: 'v\<close>, where \<^term>\<open>g :: 'gv\<close> might comprise bitfields for other values. Writing
to this location will only change the bits related to \<^term>\<open>v :: 'v\<close>, while the rest remain the same.
This effect is captured with the \<^term>\<open>l \<mapsto>\<langle>s\<rangle> (\<lambda>_. w) \<sqdot> (g\<down>v)\<close> resource, which describes that
we (partially) own a location \<^term>\<open>l\<close> that points to a 'global' value \<^term>\<open>g\<close>, but field \<^term>\<open>v\<close>
of that global value has been overwritten with new content \<^term>\<open>w\<close>.\<close>
definition swap_ref_contract :: \<open>('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> ('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 'gv \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>swap_ref_contract lref rref lg rg lval rval \<equiv>
    let pre  = lref \<mapsto>\<langle>\<top>\<rangle> lg\<down>lval \<star> rref \<mapsto>\<langle>\<top>\<rangle> rg\<down>rval in
    let post = \<lambda> _.
               lref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. rval) \<sqdot> (lg\<down>lval) \<star>
               rref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. lval) \<sqdot> (rg\<down>rval) in
    make_function_contract pre post\<close>
ucincl_auto swap_ref_contract

text\<open>Proving this specification is as straightforward as before\<close>
lemma swap_ref_spec:
  shows \<open>\<Gamma>; swap_ref lref rref \<Turnstile>\<^sub>F swap_ref_contract lref rref lg rg lval rval\<close>
  apply (crush_boot f: swap_ref_def contract: swap_ref_contract_def)
  apply crush_base
  done

text\<open>Now, let's use this function in some client program\<close>
definition swap_client where
  \<open>swap_client \<equiv> FunctionBody \<lbrakk>
    let mut left = \<llangle>42 :: nat\<rrangle>;
    let mut right = 72;
    swap_ref(left, right);
    *left
  \<rbrakk>\<close>

text\<open>After swapping, the variable left should now contain the value \<^term>\<open>72 :: nat\<close>\<close>
definition swap_client_contract where
  \<open>swap_client_contract \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda> r. \<langle>r = (72 :: nat)\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>
ucincl_auto swap_client_contract

text\<open>We can verify this in two ways. Firstly, we can tell the automation to use the verified
specification of \<^term>\<open>swap_ref\<close>, using the \<^verbatim>\<open>specs add:\<close> and \<^verbatim>\<open>contracts add:\<close> modifiers\<close>
lemma swap_client_spec_using_swap_spec:
  shows \<open>\<Gamma>; swap_client \<Turnstile>\<^sub>F swap_client_contract\<close>
  apply (crush_boot f: swap_client_def contract: swap_client_contract_def)
  apply (crush_base specs add: swap_ref_spec contracts add: swap_ref_contract_def )
  done

text\<open>Alternatively, we can just choose to inline/unfold \<^term>\<open>swap_ref\<close>, and symbolically execute.\<close>
lemma swap_client_inline_spec:
  shows \<open>\<Gamma>; swap_client  \<Turnstile>\<^sub>F swap_client_contract\<close>
  apply (crush_boot f: swap_client_def contract: swap_client_contract_def)
  apply (crush_base inline: swap_ref_def)
  done

text\<open>For more details about the automation tactics like \<^verbatim>\<open>crush_base\<close> and \<^verbatim>\<open>crush_boot\<close>,
see \<^file>\<open>Crush_Examples.thy\<close>.\<close>


text\<open>We will now verify a slightly more involved example, summing the contents of an array.
For simplicity, we will work with an array of natural numbers, to avoid possible overflow problems.\<close>

text\<open>Adding two mathematical numbers of \<^typ>\<open>nat\<close> is not allowed in uRust by default, so we need to
register the addition operator first. The next command takes care of that, this can be ignored. \<close>
adhoc_overloading urust_add \<rightleftharpoons> \<open>bind2 (lift_exp2 (plus :: nat \<Rightarrow> nat \<Rightarrow> nat))\<close>

text\<open>We can now define this summing operation of an array in uRust.
Note also the availability of indexing notation \<^verbatim>\<open>nums[i]\<close> for arrays.\<close>
definition sum_array :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sum_array nums l \<equiv> FunctionBody \<lbrakk>
    let mut sum = \<llangle>0 :: nat\<rrangle>;
    for i in 0..l {
      let num = nums[i];
      sum = *sum + num;
    };
    *sum
  \<rbrakk>\<close>

text\<open>The contract for \<^term>\<open>sum_array\<close>: the stateful implementations returns the same value
as the functional implementation that uses \<^term>\<open>sum_list\<close>\<close>
definition sum_array_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_array_contract nums l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r.
               \<langle>r = sum_list (array_to_list nums)\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>
ucincl_auto sum_array_contract

text\<open>The proof of the specification is a bit more involved, since we need to deal with the loop\<close>
lemma sum_spec:
  shows \<open>\<Gamma>; sum_array nums l \<Turnstile>\<^sub>F sum_array_contract nums l\<close>
proof (crush_boot f: sum_array_def contract: sum_array_contract_def, goal_cases)
  case 1
\<comment> \<open>We follow the Isar \<^verbatim>\<open>moreover\<close> .. \<^verbatim>\<open>ultimately\<close> pattern, first gathering required facts.
This first fact relates the partial sums from before and after executing the loop body.\<close>
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow> sum_list (take (Suc i) (array_to_list nums)) = sum_list (take i (array_to_list nums)) + array_nth nums i\<close>
    by (simp add: take_Suc_conv_app_nth)
\<comment> \<open>Second fact asserts that \<^term>\<open>l\<close> is bounded (since it is a \<^typ>\<open>64 word\<close>). This boundedness
condition comes arises from using an \<^verbatim>\<open>i \<in> 0..l\<close> to index into \<^term>\<open>nums\<close>.\<close>
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
\<comment> \<open>We can now start the proof. The first call to \<^verbatim>\<open>crush_base\<close> symbolically executes up until
the start of the loop.\<close>
    apply crush_base
\<comment> \<open>Some reference sum has been allocated in the mean time: give it a name with \<^verbatim>\<open>subgoal\<close>,
so that we can reference it in the loop invariant.\<close>
    subgoal for sum_ref
\<comment> \<open>Now, apply the rule for proving for-loops. The \<^verbatim>\<open>INV=\<open>\<lambda> _ i. \<dots>\<close>\<close> states the loop-invariant
that we will use in the proof to verify our specification. The \<^verbatim>\<open>\<tau>=\<dots>\<close> and \<^verbatim>\<open>\<theta>=\<dots>\<close> refer to
conditions for raising exceptions or returning early while inside the loop body. Making these
equal to \<^term>\<open>\<lambda>_. \<langle>False\<rangle>\<close> ensures that raising an exception or returning early is illegal,
like we would expect.\<close>
      apply (ucincl_discharge\<open>
        rule_tac 
          INV=\<open>\<lambda>_ i. \<Squnion> g. sum_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(sum_list (take i (array_to_list nums)))\<close> and 
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
\<comment> \<open>We are left with two subgoals:
- The first subgoal states that our current state entails the loop invariant after 0 iterations,
and that the loop invariant after all iterations entails our postcondition.
- The second subgoal states that executing the loop body is safe, given that the loop invariant
after n iterations holds. Moreover, the loop invariant after (n+1) iterations holds after execution
of the loop body has finished.
In this case, the automation requires one extra simplification rule to be able to finish the proof\<close>
      by (crush_base simp add: More_Word.unat_of_nat_eq)
  done
qed

section\<open>Further reading\<close>
text\<open>This file did not further discuss the \<^verbatim>\<open>locale\<close>/\<^verbatim>\<open>context\<close> incantations
at the start of the file. To learn more about that, see \<^file>\<open>Reference_Examples.thy\<close>.
\<close>

(*<*)
end
end
(*>*)