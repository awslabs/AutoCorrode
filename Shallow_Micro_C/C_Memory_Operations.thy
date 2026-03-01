theory C_Memory_Operations
  imports
    C_Pointer_Types
    C_Sizeof
begin

section \<open>C Pointer Arithmetic\<close>

text \<open>
  In C, pointer arithmetic @{text "p + n"} advances the pointer by
  @{text "n * sizeof(*p)"} bytes. We define this as pure address arithmetic
  on @{type gref} values.
\<close>

definition c_ptr_add :: \<open>(nat, 'b) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'b) gref\<close> where
  \<open>c_ptr_add p n stride \<equiv> make_gref (gref_address p + n * stride)\<close>

text \<open>A convenience abbreviation using @{const c_sizeof} for the stride.\<close>

abbreviation c_ptr_add_typed :: \<open>(nat, 'b) gref \<Rightarrow> nat \<Rightarrow> 'v itself \<Rightarrow> (nat, 'b) gref\<close> where
  \<open>c_ptr_add_typed p n T \<equiv> c_ptr_add p n (c_sizeof T)\<close>

subsection \<open>Basic Pointer Arithmetic Lemmas\<close>

lemma c_ptr_add_zero [simp]:
  shows \<open>c_ptr_add p 0 stride = p\<close>
by (simp add: c_ptr_add_def)

lemma c_ptr_add_address [simp]:
  shows \<open>gref_address (c_ptr_add p n stride) = gref_address p + n * stride\<close>
by (simp add: c_ptr_add_def)

lemma c_ptr_add_add:
  shows \<open>c_ptr_add (c_ptr_add p m stride) n stride = c_ptr_add p (m + n) stride\<close>
by (simp add: c_ptr_add_def algebra_simps)

lemma c_ptr_add_null_guard:
  assumes \<open>\<not> is_null_nat p\<close>
      and \<open>n * stride < gref_address p + n * stride\<close>
    shows \<open>\<not> is_null_nat (c_ptr_add p n stride)\<close>
using assms by (simp add: is_null_nat_def c_ptr_add_def)

section \<open>Array Element References\<close>

text \<open>
  In C, @{text "p[i]"} is defined as @{text "*(p + i)"}. The function @{text c_ptr_at}
  computes the @{type gref} for the i-th element of an array starting at @{text p}.
  The actual dereference or update is performed by locale-provided operations
  such as @{text dereference_by_value_raw_fun} and @{text update_raw_fun}.
\<close>
definition c_ptr_at :: \<open>(nat, 'b) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'b) gref\<close> where
  \<open>c_ptr_at p i stride \<equiv> c_ptr_add p i stride\<close>

lemma c_ptr_at_address [simp]:
  shows \<open>gref_address (c_ptr_at p i stride) = gref_address p + i * stride\<close>
by (simp add: c_ptr_at_def)

lemma c_ptr_at_zero [simp]:
  shows \<open>c_ptr_at p 0 stride = p\<close>
by (simp add: c_ptr_at_def)

section \<open>C Pointer Subtraction\<close>

text \<open>
  C pointer subtraction yields a signed element-distance (typically @{typ c_long}
  in this LP64 model), not an unsigned natural.
\<close>

definition c_ptr_diff :: \<open>(nat, 'b) gref \<Rightarrow> (nat, 'b) gref \<Rightarrow> nat \<Rightarrow> c_long\<close> where
  \<open>c_ptr_diff p q stride \<equiv>
     word_of_int
       (c_trunc_div_int (int (gref_address p) - int (gref_address q)) (int stride))\<close>

section \<open>C Pointer Relational Comparisons\<close>

definition c_ptr_less :: \<open>(nat, 'b) gref \<Rightarrow> (nat, 'b) gref \<Rightarrow> bool\<close> where
  \<open>c_ptr_less p q \<equiv> gref_address p < gref_address q\<close>

definition c_ptr_le :: \<open>(nat, 'b) gref \<Rightarrow> (nat, 'b) gref \<Rightarrow> bool\<close> where
  \<open>c_ptr_le p q \<equiv> gref_address p \<le> gref_address q\<close>

definition c_ptr_greater :: \<open>(nat, 'b) gref \<Rightarrow> (nat, 'b) gref \<Rightarrow> bool\<close> where
  \<open>c_ptr_greater p q \<equiv> gref_address p > gref_address q\<close>

definition c_ptr_ge :: \<open>(nat, 'b) gref \<Rightarrow> (nat, 'b) gref \<Rightarrow> bool\<close> where
  \<open>c_ptr_ge p q \<equiv> gref_address p \<ge> gref_address q\<close>

section \<open>Pointer\<leftrightarrow>Integer Casts\<close>

definition c_ptr_to_uintptr :: \<open>(nat, 'b) gref \<Rightarrow> 'l::len word\<close> where
  \<open>c_ptr_to_uintptr p \<equiv> of_nat (gref_address p)\<close>

definition c_uintptr_to_ptr :: \<open>'l::len word \<Rightarrow> (nat, 'b) gref\<close> where
  \<open>c_uintptr_to_ptr w \<equiv> make_gref (unat w)\<close>

end
