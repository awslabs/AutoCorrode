theory Fibonacci_Iterative
  imports Micro_Rust_Std_Lib.StdLib_All
begin

locale fibonacci_ctx =
    reference reference_types +
    ref_word64: reference_allocatable reference_types _ _ _ _ _ _ _ word64_prism +
    ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism
  for 
  reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>

  and word64_prism :: \<open>('gv, 64 word) prism\<close>
  and nat_prism :: \<open>('gv, nat) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word64.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun
adhoc_overloading urust_add \<rightleftharpoons> \<open>bind2 (lift_exp2 (plus :: nat \<Rightarrow> nat \<Rightarrow> nat))\<close>

section\<open>Iterative Fibonacci Function\<close>

text\<open>This example demonstrates an iterative Fibonacci function implementation
with a complete correctness proof. We verify that the implementation matches
the mathematical definition of Fibonacci numbers.\<close>

subsection\<open>Mathematical Specification\<close>

text\<open>First, we define the mathematical Fibonacci function recursively.
Solution taken from: https://isabelle.in.tum.de/library/HOL/HOL-Number_Theory/Fib.html \<close>

fun fib :: \<open>nat \<Rightarrow> nat\<close> where
    fib0: \<open>fib 0 = 0\<close> |
    fib1: \<open>fib (Suc 0) = 1\<close> |
    fib2: \<open>fib (Suc (Suc n)) = fib (Suc n) + fib n\<close>

lemma fib_plus_2: 
  shows \<open>fib (n + 2) = fib (n + 1) + fib n\<close>
  by (metis Suc_eq_plus1 add_2_eq_Suc' fib.simps(3))

subsection\<open>Iterative Implementation\<close>

text\<open>Implementation of an iterative version in Micro Rust that computes
the nth Fibonacci number efficiently without recursion.\<close>

definition fib_iterative :: \<open>64 word \<Rightarrow> (_, nat, _, _, _) function_body\<close> where
  \<open>fib_iterative n \<equiv> FunctionBody \<lbrakk>
    let mut a = \<llangle>0 :: nat\<rrangle>;
    let mut b = \<llangle>1 :: nat\<rrangle>;
    for i in 0..n {
      let temp = *a + *b;
      a = *b;
      b = temp
    };
    *a
  \<rbrakk>\<close>

text\<open>Contract specification and correctness proof for the iterative Fibonacci function.\<close>

definition fib_correct_contract :: \<open>64 word \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>fib_correct_contract n \<equiv>
     let pre  = can_alloc_reference in
     let post = \<lambda>r. \<langle>r = fib (unat n)\<rangle> \<star> can_alloc_reference in
     make_function_contract pre post\<close>
ucincl_auto fib_correct_contract

lemma fib_correct_spec:
  shows \<open>\<Gamma>; fib_iterative n \<Turnstile>\<^sub>F fib_correct_contract n\<close>
proof (crush_boot f: fib_iterative_def contract: fib_correct_contract_def, goal_cases)
  case 1
  then show ?case
    apply crush_base
    subgoal for a_ref b_ref
    apply (ucincl_discharge\<open>
          rule_tac 
            INV=\<open>\<lambda>_ i. \<Squnion> ga gb. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>(fib i) \<star> b_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>(fib (i + 1))\<close>
            and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_raw_for_loop_framedI'
        \<close>)
       apply (crush_base simp add: fib_plus_2)
      done
    done
qed

end
end
