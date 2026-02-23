(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Array_Examples
  imports
    Simple_C_Functions 
begin

section \<open>C Array Verification\<close>

text \<open>
  This theory demonstrates verification of C array indexing operations.
  Arrays are modeled as references to @{typ \<open>c_int list\<close>}.
  Array indexing uses @{const focus_nth} (focus-based access).
\<close>

context c_verification_ctx begin

subsection \<open>C Array Functions\<close>

micro_c_translate \<open>
int read_at(int *arr, int idx) {
  return arr[idx];
}
\<close>

thm c_read_at_def

micro_c_translate \<open>
void write_at(int *arr, int idx, int val) {
  arr[idx] = val;
}
\<close>

thm c_write_at_def

subsection \<open>Read-at Contract and Proof\<close>

text \<open>
  The contract for @{text read_at}: given a reference to a @{typ \<open>c_int list\<close>}
  and a valid index, the function returns the element at that index.
  The @{const c_idx_to_nat} function converts the C integer index to a natural number.
\<close>

definition c_read_at_contract ::
    \<open>('addr, 'gv, c_int list) Global_Store.ref \<Rightarrow> c_int \<Rightarrow>
     'gv \<Rightarrow> c_int list \<Rightarrow> ('s, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_at_contract arr idx g vs \<equiv>
    let pre  = arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>c_idx_to_nat idx < length vs\<rangle>;
        post = \<lambda>r. arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>r = vs ! (c_idx_to_nat idx)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_at_contract

lemma c_read_at_spec:
  shows \<open>\<Gamma>; c_read_at arr idx \<Turnstile>\<^sub>F c_read_at_contract arr idx g vs\<close>
  apply (crush_boot f: c_read_at_def contract: c_read_at_contract_def)
  apply crush_base
  done

end

end
