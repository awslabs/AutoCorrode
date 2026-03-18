theory C_Translation_Smoke_ILP32
  imports
    C_To_Core_Translation
begin

section \<open>ILP32 Arithmetic Conversion Smoke Tests\<close>

text \<open>
  Regression tests for C11-compliant @{text "usual_arith_conv"} under ILP32,
  where @{text "long"} is 32-bit and @{text "long long"} is 64-bit.

  \<^item> @{text "type_rank"}: @{text "CLongLong"} must rank strictly above @{text "CLong"}
    (C11 \<section>6.3.1.1p1). Without this, @{text "long + long long"} returns the
    narrower @{text "long"} type.

  \<^item> @{text "usual_arith_conv"} mixed-signedness: when the signed operand has
    higher rank but NOT strictly more bits (e.g.\ 32-bit @{text "long"} vs.\
    32-bit @{text "unsigned int"}), C11 \<section>6.3.1.8 rule 3 requires converting to
    the unsigned type, not the signed one.
\<close>

subsection \<open>Rank ordering: \<^verbatim>\<open>long\<close> vs \<^verbatim>\<open>long long\<close>\<close>

text \<open>
  Under ILP32, @{text "long"} is 32-bit and @{text "long long"} is 64-bit.
  The result of @{text "long + long long"} must be @{text "long long"} (64-bit).
  A buggy @{text "type_rank"} that gives both the same rank would return @{text "long"}
  (32-bit), silently losing precision.
\<close>

micro_c_translate prefix: ilp32_ abi: ilp32-le \<open>
long long add_long_longlong(long a, long long b) {
  return a + b;
}
\<close>

thm ilp32_add_long_longlong_def

text \<open>Same test for unsigned variants.\<close>

micro_c_translate prefix: ilp32_ abi: ilp32-le \<open>
unsigned long long add_ulong_ulonglong(unsigned long a, unsigned long long b) {
  return a + b;
}
\<close>

thm ilp32_add_ulong_ulonglong_def

subsection \<open>Mixed-signedness bit-width check\<close>

text \<open>
  Under ILP32, @{text "unsigned int"} (32-bit) and @{text "long"} (32-bit signed)
  have the same width. C11 \<section>6.3.1.8 rule 3: since the signed type cannot represent
  all unsigned values, convert to the unsigned counterpart (@{text "unsigned long"}).
  A buggy implementation that skips the bit-width check would return @{text "long"}
  (signed), silently changing the signedness of the result.
\<close>

micro_c_translate prefix: ilp32_ abi: ilp32-le \<open>
unsigned long add_uint_long(unsigned int a, long b) {
  return a + b;
}
\<close>

thm ilp32_add_uint_long_def

subsection \<open>ABI sanity checks\<close>

micro_c_translate prefix: ilp32_ abi: ilp32-le \<open>
unsigned int sizeof_long(void) { return sizeof(long); }
unsigned int sizeof_ptr(void) { return sizeof(int *); }
unsigned int sizeof_longlong(void) { return sizeof(long long); }
\<close>

thm ilp32_sizeof_long_def
thm ilp32_sizeof_ptr_def
thm ilp32_sizeof_longlong_def

lemma ilp32_abi_profile_values:
  shows "ilp32_abi_pointer_bits = 32"
    and "ilp32_abi_long_bits = 32"
    and "ilp32_abi_big_endian = False"
  by (simp_all add: ilp32_abi_pointer_bits_def ilp32_abi_long_bits_def ilp32_abi_big_endian_def)

end
