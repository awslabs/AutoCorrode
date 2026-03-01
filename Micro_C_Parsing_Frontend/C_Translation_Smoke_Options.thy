theory C_Translation_Smoke_Options
  imports
    C_To_Core_Translation
begin

section \<open>\<^verbatim>\<open>micro_c_translate\<close> Prefix Smoke\<close>

micro_c_translate prefix: smoke_ \<open>
  struct counter {
    unsigned int value;
  };

  unsigned int bump(struct counter *c) {
    c->value = c->value + 1;
    return c->value;
  }
\<close>

thm smoke_bump_def
thm smoke_counter.record_simps
thm smoke_abi_pointer_bits_def
thm smoke_abi_long_bits_def
thm smoke_abi_char_is_signed_def
thm smoke_abi_big_endian_def

section \<open>\<^verbatim>\<open>micro_c_translate\<close> ABI Smoke\<close>

micro_c_translate prefix: smoke32_ \<open>
  unsigned int size_long(void) { return sizeof(long); }
  unsigned int size_ptr(void) { return sizeof(int *); }
  unsigned int align_long(void) { return _Alignof(long); }
\<close> abi: ilp32-le

thm smoke32_size_long_def
thm smoke32_size_ptr_def
thm smoke32_align_long_def
thm smoke32_abi_pointer_bits_def
thm smoke32_abi_long_bits_def
thm smoke32_abi_big_endian_def

lemma smoke32_abi_profile_values:
  shows "smoke32_abi_pointer_bits = 32"
    and "smoke32_abi_long_bits = 32"
    and "smoke32_abi_big_endian = False"
  by (simp_all add: smoke32_abi_pointer_bits_def smoke32_abi_long_bits_def smoke32_abi_big_endian_def)

section \<open>\<^verbatim>\<open>micro_c_translate\<close> Big-Endian ABI Smoke\<close>

micro_c_translate prefix: smokebe_ abi: lp64-be \<open>
  unsigned long size_ptr(void) { return sizeof(int *); }
\<close>

thm smokebe_size_ptr_def
thm smokebe_abi_pointer_bits_def
thm smokebe_abi_long_bits_def
thm smokebe_abi_big_endian_def

lemma smokebe_abi_profile_values:
  shows "smokebe_abi_pointer_bits = 64"
    and "smokebe_abi_long_bits = 64"
    and "smokebe_abi_big_endian = True"
  by (simp_all add: smokebe_abi_pointer_bits_def smokebe_abi_long_bits_def smokebe_abi_big_endian_def)

section \<open>\<^verbatim>\<open>micro_c_file\<close> Prefix and Manifest Smoke\<close>

micro_c_file prefix: smoke_ manifest: "smoke_manifest.txt" "smoke_manifest_file.c"

thm smoke_keep_add_def
thm smoke_poly_get0_def
thm smoke_poly_t.record_simps

ML \<open>
  val _ =
    ((Proof_Context.read_const {proper = true, strict = true} @{context} "smoke_drop_mul"; error "manifest filtering failed")
      handle ERROR _ => ());
\<close>

section \<open>Two-Phase Type-Then-Function Smoke\<close>

micro_c_file prefix: smoke_split_ manifest: "smoke_manifest_types.txt" "smoke_manifest_file_types_phase1.c"

micro_c_file prefix: smoke_split_ addr: 'addr gv: 'gv
  manifest: "smoke_manifest_phase2.txt" "smoke_manifest_file_types_phase2.c"

thm smoke_split_poly_get0_def
thm smoke_split_poly_t.record_simps

section \<open>\<^verbatim>\<open>micro_c_file\<close> ABI Smoke\<close>

micro_c_file prefix: smoke32_file_ abi: ilp32-le
  manifest: "smoke_manifest_abi.txt" "smoke_manifest_file_abi.c"

thm smoke32_file_keep_add_def
thm smoke32_file_poly_get0_def
thm smoke32_file_poly_t.record_simps
thm smoke32_file_abi_pointer_bits_def
thm smoke32_file_abi_long_bits_def
thm smoke32_file_abi_big_endian_def

end
