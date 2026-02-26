theory C_Pointer_Types
  imports
    C_Abort
    "Shallow_Micro_Rust.Global_Store"
begin

section \<open>C Pointer Types\<close>

text \<open>
  C pointers are modeled using the existing @{type gref} type. We define a
  distinguished null address value and a null-check operation that aborts
  with @{const NullPointerDereference} on null pointer access.
\<close>

subsection \<open>Null pointer\<close>

text \<open>
  We define null as the zero address for numeric address types.
\<close>

definition c_null :: \<open>(nat, 'b) gref\<close> where
  \<open>c_null \<equiv> make_gref 0\<close>

definition is_null_nat :: \<open>(nat, 'b) gref \<Rightarrow> bool\<close> where
  \<open>is_null_nat p \<equiv> address p = 0\<close>

lemma is_null_c_null [simp]:
  shows \<open>is_null_nat c_null\<close>
by (simp add: is_null_nat_def c_null_def gref.sel)

subsection \<open>Null-checked pointer operations\<close>

text \<open>
  These operations check for null before performing the underlying memory
  operation. A null pointer dereference aborts with @{const NullPointerDereference}.
  The operations are defined generically: the null check is a pure guard that
  can be composed with any locale-provided dereference or update.
\<close>

definition c_null_guard :: \<open>(nat, 'b) gref \<Rightarrow> ((nat, 'b) gref \<Rightarrow>
    ('s, 'v, 'r, c_abort, 'i, 'o) expression) \<Rightarrow>
    ('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_null_guard p op \<equiv>
     if is_null_nat p then
       c_null_pointer_dereference
     else
      op p\<close>

end
