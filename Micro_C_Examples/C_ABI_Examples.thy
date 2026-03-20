theory C_ABI_Examples
  imports
    Simple_C_Functions
    "Shallow_Micro_C.C_Byte_Encoding"
begin

section \<open>ABI-Critical C Examples\<close>

text \<open>
  This theory collects examples where ABI choices matter directly:
  \<^item> Portable wire parsing via explicit shifts and masks (wire-order fixed, host-order independent).
  \<^item> ABI-sensitive native loads via pointer casts.
  \<^item> Prism selection from generated @{text "<prefix>abi_big_endian"} metadata.
\<close>

locale c_char_uint_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_char: reference_allocatable reference_types _ _ _ _ _ _ _ c_char_prism +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism
  for c_ptr_add :: \<open>('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_shift_signed :: \<open>('addr, 'gv) gref \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_diff :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> int\<close>
  and c_ptr_less :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_le :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_greater :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_ge :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_to_uintptr :: \<open>('addr, 'gv) gref \<Rightarrow> int\<close>
  and c_uintptr_to_ptr :: \<open>int \<Rightarrow> ('addr, 'gv) gref\<close>
  and reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and c_char_prism :: \<open>('gv, c_char) prism\<close>
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_char.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun
adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> c_char_prism
adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> c_uint_prism

definition c_char_ref_at :: \<open>('addr, 'gv, c_char) Global_Store.ref \<Rightarrow> nat \<Rightarrow> ('addr, 'gv, c_char) Global_Store.ref\<close> where
  \<open>c_char_ref_at buf i \<equiv>
    make_focused
      (c_ptr_add (unwrap_focused buf) i (c_sizeof TYPE(c_char)))
      (get_focus buf)\<close>

definition be32_from_bytes4 :: \<open>c_char list \<Rightarrow> c_uint\<close> where
  \<open>be32_from_bytes4 vs \<equiv>
      (push_bit 24 (ucast (vs ! 0) :: c_uint))
    OR (push_bit 16 (ucast (vs ! 1) :: c_uint))
    OR (push_bit 8 (ucast (vs ! 2) :: c_uint))
    OR  (ucast (vs ! 3) :: c_uint)\<close>

definition bswap32_math :: \<open>c_uint \<Rightarrow> c_uint\<close> where
  \<open>bswap32_math x \<equiv>
      (push_bit 24 (x AND 255))
    OR (push_bit 8 (x AND 65280))
    OR (drop_bit 8 (x AND 16711680))
    OR (drop_bit 24 (x AND 4278190080))\<close>

definition host_u32_from_wire_be :: \<open>bool \<Rightarrow> c_uint \<Rightarrow> c_uint\<close> where
  \<open>host_u32_from_wire_be host_is_be w \<equiv> if host_is_be then w else bswap32_math w\<close>

section \<open>Little-Endian 32-bit ABI (ILP32)\<close>

micro_c_translate prefix: wire_le_ abi: ilp32-le \<open>
  typedef unsigned char uint8_t;
  typedef unsigned int uint32_t;

  uint32_t load_be32_portable(uint8_t *buf) {
    return ((uint32_t)buf[0] << 24)
         | ((uint32_t)buf[1] << 16)
         | ((uint32_t)buf[2] << 8)
         |  (uint32_t)buf[3];
  }

  uint32_t load_native32(uint8_t *buf) {
    return *(uint32_t *)buf;
  }

  uint32_t bswap32(uint32_t x) {
    return ((x & 255U) << 24)
         | ((x & 65280U) << 8)
         | ((x & 16711680U) >> 8)
         | ((x & 4278190080U) >> 24);
  }
\<close>

thm wire_le_load_be32_portable_def
thm wire_le_load_native32_def
thm wire_le_bswap32_def

lemma wire_le_abi_profile_values:
  shows \<open>wire_le_abi_pointer_bits = 32\<close>
    and \<open>wire_le_abi_long_bits = 32\<close>
    and \<open>wire_le_abi_big_endian = False\<close>
by (simp_all add: wire_le_abi_pointer_bits_def wire_le_abi_long_bits_def wire_le_abi_big_endian_def)

definition wire_le_load_be32_portable_contract ::
  \<open>('addr, 'gv, c_char) Global_Store.ref \<Rightarrow> c_char \<Rightarrow> c_char \<Rightarrow> c_char \<Rightarrow> c_char \<Rightarrow>
    ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wire_le_load_be32_portable_contract buf b0 b1 b2 b3 \<equiv>
    let r0 = c_char_ref_at buf 0;
        r1 = c_char_ref_at buf 1;
        r2 = c_char_ref_at buf 2;
        r3 = c_char_ref_at buf 3;
        pre  = (\<Squnion>g0. r0 \<mapsto>\<langle>\<top>\<rangle> g0\<down>b0)
             \<star> (\<Squnion>g1. r1 \<mapsto>\<langle>\<top>\<rangle> g1\<down>b1)
             \<star> (\<Squnion>g2. r2 \<mapsto>\<langle>\<top>\<rangle> g2\<down>b2)
             \<star> (\<Squnion>g3. r3 \<mapsto>\<langle>\<top>\<rangle> g3\<down>b3);
        post = \<lambda>r. (\<Squnion>g0. r0 \<mapsto>\<langle>\<top>\<rangle> g0\<down>b0)
             \<star> (\<Squnion>g1. r1 \<mapsto>\<langle>\<top>\<rangle> g1\<down>b1)
             \<star> (\<Squnion>g2. r2 \<mapsto>\<langle>\<top>\<rangle> g2\<down>b2)
             \<star> (\<Squnion>g3. r3 \<mapsto>\<langle>\<top>\<rangle> g3\<down>b3)
             \<star> \<langle>r = be32_from_bytes4 [b0, b1, b2, b3]\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto wire_le_load_be32_portable_contract

lemma wire_le_load_be32_portable_spec [crush_specs]:
  shows \<open>\<Gamma>; wire_le_load_be32_portable buf \<Turnstile>\<^sub>F wire_le_load_be32_portable_contract buf b0 b1 b2 b3\<close>
  apply (crush_boot f: wire_le_load_be32_portable_def contract: wire_le_load_be32_portable_contract_def)
  apply (crush_base simp add: c_char_ref_at_def be32_from_bytes4_def c_unsigned_or_def c_unsigned_shl_def c_ucast_def)
  apply (simp add: ac_simps)
  done

definition wire_le_bswap32_contract ::
  \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wire_le_bswap32_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = bswap32_math x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto wire_le_bswap32_contract

lemma wire_le_bswap32_spec [crush_specs]:
  shows \<open>\<Gamma>; wire_le_bswap32 x \<Turnstile>\<^sub>F wire_le_bswap32_contract x\<close>
  apply (crush_boot f: wire_le_bswap32_def contract: wire_le_bswap32_contract_def)
  apply (crush_base simp add: bswap32_math_def c_unsigned_and_def c_unsigned_or_def c_unsigned_shl_def c_unsigned_shr_def)
  apply (simp add: ac_simps)
  done

lemma wire_le_host_from_wire_be:
  shows \<open>host_u32_from_wire_be wire_le_abi_big_endian w = bswap32_math w\<close>
  by (simp add: host_u32_from_wire_be_def wire_le_abi_big_endian_def)

section \<open>Big-Endian 64-bit ABI (LP64)\<close>

micro_c_translate prefix: wire_be_ abi: lp64-be \<open>
  typedef unsigned char uint8_t;
  typedef unsigned int uint32_t;

  uint32_t load_be32_portable(uint8_t *buf) {
    return ((uint32_t)buf[0] << 24)
         | ((uint32_t)buf[1] << 16)
         | ((uint32_t)buf[2] << 8)
         |  (uint32_t)buf[3];
  }

  uint32_t load_native32(uint8_t *buf) {
    return *(uint32_t *)buf;
  }
\<close>

thm wire_be_load_be32_portable_def
thm wire_be_load_native32_def

lemma wire_be_abi_profile_values:
  shows \<open>wire_be_abi_pointer_bits = 64\<close>
    and \<open>wire_be_abi_long_bits = 64\<close>
    and \<open>wire_be_abi_big_endian = True\<close>
by (simp_all add: wire_be_abi_pointer_bits_def wire_be_abi_long_bits_def wire_be_abi_big_endian_def)

definition wire_be_load_be32_portable_contract ::
  \<open>('addr, 'gv, c_char) Global_Store.ref \<Rightarrow> c_char \<Rightarrow> c_char \<Rightarrow> c_char \<Rightarrow> c_char \<Rightarrow>
    ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wire_be_load_be32_portable_contract buf b0 b1 b2 b3 \<equiv>
    let r0 = c_char_ref_at buf 0;
        r1 = c_char_ref_at buf 1;
        r2 = c_char_ref_at buf 2;
        r3 = c_char_ref_at buf 3;
        pre  = (\<Squnion>g0. r0 \<mapsto>\<langle>\<top>\<rangle> g0\<down>b0)
             \<star> (\<Squnion>g1. r1 \<mapsto>\<langle>\<top>\<rangle> g1\<down>b1)
             \<star> (\<Squnion>g2. r2 \<mapsto>\<langle>\<top>\<rangle> g2\<down>b2)
             \<star> (\<Squnion>g3. r3 \<mapsto>\<langle>\<top>\<rangle> g3\<down>b3);
        post = \<lambda>r. (\<Squnion>g0. r0 \<mapsto>\<langle>\<top>\<rangle> g0\<down>b0)
             \<star> (\<Squnion>g1. r1 \<mapsto>\<langle>\<top>\<rangle> g1\<down>b1)
             \<star> (\<Squnion>g2. r2 \<mapsto>\<langle>\<top>\<rangle> g2\<down>b2)
             \<star> (\<Squnion>g3. r3 \<mapsto>\<langle>\<top>\<rangle> g3\<down>b3)
             \<star> \<langle>r = be32_from_bytes4 [b0, b1, b2, b3]\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto wire_be_load_be32_portable_contract

lemma wire_be_load_be32_portable_spec [crush_specs]:
  shows \<open>\<Gamma>; wire_be_load_be32_portable buf \<Turnstile>\<^sub>F wire_be_load_be32_portable_contract buf b0 b1 b2 b3\<close>
  apply (crush_boot f: wire_be_load_be32_portable_def contract: wire_be_load_be32_portable_contract_def)
  apply (crush_base simp add: c_char_ref_at_def be32_from_bytes4_def c_unsigned_or_def c_unsigned_shl_def c_ucast_def)
  apply (simp add: ac_simps)
  done

lemma wire_be_host_from_wire_be:
  shows \<open>host_u32_from_wire_be wire_be_abi_big_endian w = w\<close>
  by (simp add: host_u32_from_wire_be_def wire_be_abi_big_endian_def)

section \<open>Driving Prism Choice from ABI Metadata\<close>

text \<open>
  The selected C ABI can be threaded directly into byte encoding prism selection.
\<close>

definition wire_le_u32_prism :: \<open>(byte list, c_uint) prism\<close> where
  \<open>wire_le_u32_prism \<equiv> c_uint_byte_prism_of (c_endianness_of_bool wire_le_abi_big_endian)\<close>

lemma wire_le_u32_prism_is_le:
  shows \<open>wire_le_u32_prism = c_uint_byte_prism\<close>
  by (simp add: wire_le_u32_prism_def c_endianness_of_bool_def c_uint_byte_prism_of_def wire_le_abi_big_endian_def)

definition wire_be_u32_prism :: \<open>(byte list, c_uint) prism\<close> where
  \<open>wire_be_u32_prism = c_uint_byte_prism_of (c_endianness_of_bool wire_be_abi_big_endian)\<close>

lemma wire_be_u32_prism_is_be:
  shows \<open>wire_be_u32_prism = c_uint_byte_prism_be\<close>
  by (simp add: wire_be_u32_prism_def c_endianness_of_bool_def c_uint_byte_prism_of_def wire_be_abi_big_endian_def)

section \<open>Raw Struct Field Address Regression\<close>

text \<open>
  Regression for raw @{verbatim "void *"} cast to struct pointer followed by
  address-of field extraction and a helper that immediately reinterprets the
  resulting field pointer as bytes.
\<close>

micro_c_translate prefix: raw_struct_ abi: ilp32-le \<open>
  typedef unsigned char uint8_t;
  typedef unsigned int uint32_t;

  struct pair {
    uint32_t x;
    uint32_t y;
  };

  static uint32_t load_be32(const uint32_t *p) {
    const uint8_t *bp = (const uint8_t *)p;
    return ((uint32_t)bp[0] << 24)
         | ((uint32_t)bp[1] << 16)
         | ((uint32_t)bp[2] << 8)
         |  (uint32_t)bp[3];
  }

  uint32_t read_pair_y_be(const void *p) {
    return load_be32(&((const struct pair *)p)->y);
  }
\<close>

thm raw_struct_load_be32_def
thm raw_struct_read_pair_y_be_def

end

end
