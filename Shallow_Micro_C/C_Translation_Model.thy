theory C_Translation_Model
  imports
    C_Memory_Operations
    C_Void_Pointer
begin

section \<open>C Translation Model Interface\<close>

text \<open>
  The C frontend translates pointer-manipulating code against a locale-provided
  interface rather than hard-wiring one concrete machine model into the parser.
  The pointer operations below are the semantic surface that generated terms may
  depend on. Domain-specific models can extend this locale with additional
  prisms, memory lemmas, and stronger invariants.
\<close>

locale c_pointer_model =
  fixes
    c_ptr_add :: \<open>('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_shift_signed :: \<open>('addr, 'gv) gref \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_diff :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> int\<close>
  and c_ptr_less :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_le :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_greater :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_ge :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_to_uintptr :: \<open>('addr, 'gv) gref \<Rightarrow> int\<close>
  and c_uintptr_to_ptr :: \<open>int \<Rightarrow> ('addr, 'gv) gref\<close>
  assumes c_ptr_add_zero [simp]: \<open>c_ptr_add p 0 stride = p\<close>
    and c_ptr_add_add: \<open>c_ptr_add (c_ptr_add p m stride) n stride = c_ptr_add p (m + n) stride\<close>
    and c_ptr_diff_self [simp]: \<open>c_ptr_diff p p stride = 0\<close>
    and c_ptr_less_irrefl [simp]: \<open>\<not> c_ptr_less p p\<close>
    and c_ptr_le_refl [simp]: \<open>c_ptr_le p p\<close>
    and c_ptr_ge_refl [simp]: \<open>c_ptr_ge p p\<close>

locale c_abi_model =
  fixes
    c_abi_pointer_bits :: nat
  and c_abi_long_bits :: nat
  and c_abi_char_is_signed :: bool
  and c_abi_big_endian :: bool
  assumes c_abi_pointer_bits_supported [simp]: \<open>c_abi_pointer_bits = 32 \<or> c_abi_pointer_bits = 64\<close>
    and c_abi_long_bits_supported [simp]: \<open>c_abi_long_bits = 32 \<or> c_abi_long_bits = 64\<close>
begin

text \<open>
  ABI-derived sizeof for C-level type names that vary by ABI.
  Use these in manual specifications instead of @{text "c_sizeof TYPE(c_long)"},
  which always returns 8 because @{typ c_long} is a fixed alias for @{typ "64 sword"}.
\<close>

definition c_sizeof_c_long :: nat where
  \<open>c_sizeof_c_long \<equiv> c_abi_long_bits div 8\<close>

definition c_sizeof_c_pointer :: nat where
  \<open>c_sizeof_c_pointer \<equiv> c_abi_pointer_bits div 8\<close>

end

locale c_translation_model =
  c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
    c_ptr_to_uintptr c_uintptr_to_ptr +
  c_abi_model c_abi_pointer_bits c_abi_long_bits c_abi_char_is_signed c_abi_big_endian
  for
    c_ptr_add :: \<open>('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_shift_signed :: \<open>('addr, 'gv) gref \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_diff :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> int\<close>
  and c_ptr_less :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_le :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_greater :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_ge :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_to_uintptr :: \<open>('addr, 'gv) gref \<Rightarrow> int\<close>
  and c_uintptr_to_ptr :: \<open>int \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_abi_pointer_bits :: nat
  and c_abi_long_bits :: nat
  and c_abi_char_is_signed :: bool
  and c_abi_big_endian :: bool

end
