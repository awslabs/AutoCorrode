theory C_Array_Examples
  imports
    Simple_C_Functions 
begin

section \<open>C array verification\<close>

text \<open>
  This theory demonstrates verification of pointer-indexed C array operations.
  Pointer parameters are modeled as references to the current element, and
  indexing is expressed via @{const c_ptr_add} over the underlying pointer model.
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


lemma sint_word_of_nat_Suc_ge_zero:
  assumes \<open>i < n\<close>
      and \<open>n < 2147483648\<close>
    shows \<open>sint (1 + word_of_nat i :: 32 sword) \<ge> 0\<close>
  apply (simp only: add.commute[of 1] word_succ_p1[symmetric] Abs_fnat_hom_Suc)
  apply (rule More_Word.sint_of_nat_ge_zero)
  using assms apply simp
  done

context c_verification_ctx begin

definition c_int_ref_at :: \<open>('addr, 'gv, c_int) Global_Store.ref \<Rightarrow> c_int \<Rightarrow> ('addr, 'gv, c_int) Global_Store.ref\<close> where
  \<open>c_int_ref_at arr idx \<equiv>
    make_focused
      (c_ptr_shift_signed (unwrap_focused arr) (sint idx) (c_sizeof TYPE(c_int)))
      (get_focus arr)\<close>

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
  The contract for @{text read_at}: given a reference to the current element of an
  integer array and an index, the function reads the element at that shifted location.
\<close>

definition c_read_at_contract :: \<open>('addr, 'gv, c_int) Global_Store.ref \<Rightarrow> c_int \<Rightarrow>
     'gv \<Rightarrow> c_int \<Rightarrow> ('s, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_at_contract arr idx g v \<equiv>
    let elem_ref = c_int_ref_at arr idx;
        pre  = elem_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post = \<lambda>r. elem_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_at_contract

lemma c_read_at_spec:
  shows \<open>\<Gamma>; c_read_at arr idx \<Turnstile>\<^sub>F c_read_at_contract arr idx g v\<close>
by (crush_boot f: c_read_at_def contract: c_read_at_contract_def)
  (crush_base simp add: c_int_ref_at_def)

subsection \<open>Write-at Contract and Proof\<close>

definition c_write_at_contract :: \<open>('addr, 'gv, c_int) Global_Store.ref \<Rightarrow> c_int \<Rightarrow>
     'gv \<Rightarrow> c_int \<Rightarrow> c_int \<Rightarrow> ('s, unit, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_write_at_contract arr idx g old_v new_v \<equiv>
    let elem_ref = c_int_ref_at arr idx;
        pre  = elem_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post = \<lambda>_. elem_ref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v)
     in make_function_contract pre post\<close>
ucincl_auto c_write_at_contract

lemma c_write_at_spec:
  shows \<open>\<Gamma>; c_write_at arr idx val \<Turnstile>\<^sub>F c_write_at_contract arr idx g old_v val\<close>
by (crush_boot f: c_write_at_def contract: c_write_at_contract_def)
  (crush_base simp add: c_int_ref_at_def)

subsection \<open>Array Fill (memset-style)\<close>

text \<open>
  A loop-based function that fills the first @{text n} elements of an array
  with a given value. This is the first C loop verification example.
\<close>

micro_c_translate \<open>
  void array_fill(int *arr, int val, unsigned int n) {
    for (unsigned int i = 0; i < n; i++) {
      arr[i] = val;
    }
  }
\<close>

thm c_array_fill_def

text \<open>
  @{term c_array_fill_def} is kept as a translation regression for pointer-indexed loop writes.
  A full whole-array contract now requires a contiguous raw-pointer region predicate, rather than
  the old list-backed pointer model this theory previously assumed.
\<close>

subsection \<open>Array Copy (memcpy-style)\<close>

text \<open>
  A loop-based function that copies the first @{text n} elements from
  @{text src} to @{text dst}. The source array is read-only.
\<close>

micro_c_translate \<open>
  void array_copy(int *dst, int *src, unsigned int n) {
    for (unsigned int i = 0; i < n; i++) {
      dst[i] = src[i];
    }
  }
\<close>

thm c_array_copy_def

text \<open>
  @{term c_array_copy_def} is kept as a translation regression for pointer-indexed read/write loops.
  Proving a semantic copy contract over raw pointers needs the same contiguous-region predicate as
  @{term c_array_fill_def}.
\<close>

end

end
