theory C_Array_Examples
  imports
    Simple_C_Functions 
begin

section \<open>C array verification\<close>

text \<open>
  This theory demonstrates verification of C array indexing operations.
  Arrays are modeled as references to @{typ \<open>c_int list\<close>}.
  Array indexing uses @{const focus_nth} (focus-based access).
\<close>

subsection \<open>Helper Definitions for Array Loop Proofs\<close>

definition list_fill_prefix :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>list_fill_prefix k v xs \<equiv> replicate k v @ drop k xs\<close>

lemma list_fill_prefix_length [simp]:
  assumes \<open>k \<le> length xs\<close>
    shows \<open>length (list_fill_prefix k v xs) = length xs\<close>
using assms by (simp add: list_fill_prefix_def)

lemma list_fill_prefix_zero [simp]:
  shows \<open>list_fill_prefix 0 v xs = xs\<close>
by (simp add: list_fill_prefix_def)

lemma list_fill_prefix_step:
  assumes \<open>k < length xs\<close>
    shows \<open>(list_fill_prefix k v xs)[k := v] = list_fill_prefix (Suc k) v xs\<close>
proof -
  have \<open>drop k xs = xs ! k # drop (Suc k) xs\<close>
    using assms by (simp add: Cons_nth_drop_Suc)
  then have \<open>(list_fill_prefix k v xs)[k := v] = replicate k v @ v # drop (Suc k) xs\<close>
    by (simp add: list_fill_prefix_def list_update_append)
  also have \<open>\<dots> = replicate (Suc k) v @ drop (Suc k) xs\<close>
    by (simp add: replicate_app_Cons_same)
  finally show ?thesis
    by (simp add: list_fill_prefix_def)
qed

definition list_copy_prefix :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>list_copy_prefix k src dst \<equiv> take k src @ drop k dst\<close>

lemma list_copy_prefix_length [simp]:
  assumes \<open>k \<le> length src\<close>
      and \<open>k \<le> length dst\<close>
    shows \<open>length (list_copy_prefix k src dst) = length dst\<close>
using assms by (simp add: list_copy_prefix_def)

lemma list_copy_prefix_zero [simp]:
  shows \<open>list_copy_prefix 0 src dst = dst\<close>
by (simp add: list_copy_prefix_def)

lemma list_copy_prefix_step:
  assumes \<open>k < length src\<close> \<open>k < length dst\<close>
    shows \<open>(list_copy_prefix k src dst)[k := src ! k] = list_copy_prefix (Suc k) src dst\<close>
proof -
  have drop_eq: \<open>drop k dst = dst ! k # drop (Suc k) dst\<close>
    using assms by (simp add: Cons_nth_drop_Suc)
  have \<open>(list_copy_prefix k src dst)[k := src ! k] = take k src @ src ! k # drop (Suc k) dst\<close>
    using assms by (simp add: list_copy_prefix_def list_update_append drop_eq)
  also have \<open>\<dots> = take (Suc k) src @ drop (Suc k) dst\<close>
    using assms by (simp add: take_Suc_conv_app_nth)
  finally show ?thesis
    by (simp add: list_copy_prefix_def)
qed

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

definition c_read_at_contract :: \<open>('addr, 'gv, c_int list) Global_Store.ref \<Rightarrow> c_int \<Rightarrow>
     'gv \<Rightarrow> c_int list \<Rightarrow> ('s, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_at_contract arr idx g vs \<equiv>
    let pre  = arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>c_idx_to_nat idx < length vs\<rangle>;
        post = \<lambda>r. arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star> \<langle>r = vs ! (c_idx_to_nat idx)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_at_contract

lemma c_read_at_spec:
  shows \<open>\<Gamma>; c_read_at arr idx \<Turnstile>\<^sub>F c_read_at_contract arr idx g vs\<close>
by (crush_boot f: c_read_at_def contract: c_read_at_contract_def) crush_base

subsection \<open>Array Fill (memset-style)\<close>

text \<open>
  A loop-based function that fills the first @{text n} elements of an array
  with a given value. This is the first C loop verification example.
\<close>

micro_c_translate \<open>
  void array_fill(int *arr, int val, int n) {
    for (int i = 0; i < n; i++) {
      arr[i] = val;
    }
  }
\<close>

thm c_array_fill_def

definition c_array_fill_contract :: \<open>('addr, 'gv, c_int list) Global_Store.ref \<Rightarrow> c_int \<Rightarrow> c_int \<Rightarrow>
     'gv \<Rightarrow> c_int list \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>c_array_fill_contract arr val n g vs \<equiv>
    let pre  = arr \<mapsto>\<langle>\<top>\<rangle> g\<down>vs \<star>
               \<langle>c_idx_to_nat n \<le> length vs\<rangle> \<star>
               can_alloc_reference;
        post = \<lambda>_. (\<Squnion>g'. arr \<mapsto>\<langle>\<top>\<rangle> g'\<down>(list_fill_prefix (c_idx_to_nat n) val vs)) \<star>
               can_alloc_reference
     in make_function_contract pre post\<close>
ucincl_auto c_array_fill_contract

lemma c_array_fill_spec:
  shows \<open>\<Gamma>; c_array_fill TYPE(32 signed) arr val n \<Turnstile>\<^sub>F c_array_fill_contract arr val n g vs\<close>
  apply (crush_boot f: c_array_fill_def contract: c_array_fill_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>_ i. \<Squnion> g. arr \<mapsto>\<langle>\<top>\<rangle> g\<down>(list_fill_prefix i val vs)\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
  using unat_lt2p[of n] apply (crush_base simp add: list_fill_prefix_step unat_of_nat_eq)
  done

subsection \<open>Array Copy (memcpy-style)\<close>

text \<open>
  A loop-based function that copies the first @{text n} elements from
  @{text src} to @{text dst}. The source array is read-only.
\<close>

micro_c_translate \<open>
  void array_copy(int *dst, int *src, int n) {
    for (int i = 0; i < n; i++) {
      dst[i] = src[i];
    }
  }
\<close>

thm c_array_copy_def

definition c_array_copy_contract :: \<open>('addr, 'gv, c_int list) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, c_int list) Global_Store.ref \<Rightarrow> c_int \<Rightarrow> 'gv \<Rightarrow> c_int list \<Rightarrow> 'gv \<Rightarrow>
      c_int list \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>c_array_copy_contract dst src n gd vd gs vs \<equiv>
    let pre  = dst \<mapsto>\<langle>\<top>\<rangle> gd\<down>vd \<star> src \<mapsto>\<langle>\<top>\<rangle> gs\<down>vs \<star>
               \<langle>c_idx_to_nat n \<le> length vd\<rangle> \<star>
               \<langle>c_idx_to_nat n \<le> length vs\<rangle> \<star>
               can_alloc_reference;
        post = \<lambda>_. (\<Squnion> g'. dst \<mapsto>\<langle>\<top>\<rangle> g'\<down>(list_copy_prefix (c_idx_to_nat n) vs vd)) \<star>
               src \<mapsto>\<langle>\<top>\<rangle> gs\<down>vs \<star>
               can_alloc_reference
     in make_function_contract pre post\<close>
ucincl_auto c_array_copy_contract

lemma c_array_copy_spec:
  shows \<open>\<Gamma>; c_array_copy TYPE(32 signed) dst src n \<Turnstile>\<^sub>F c_array_copy_contract dst src n gd vd gs vs\<close>
  apply (crush_boot f: c_array_copy_def contract: c_array_copy_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>_ i. (\<Squnion> g. dst \<mapsto>\<langle>\<top>\<rangle> g\<down>(list_copy_prefix i vs vd)) \<star> src \<mapsto>\<langle>\<top>\<rangle> gs\<down>vs\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
  using unat_lt2p[of n] apply (crush_base simp add: list_copy_prefix_step unat_of_nat_eq)
  done

end

end
