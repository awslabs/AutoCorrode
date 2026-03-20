theory C_Misc_Examples
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    "Micro_Rust_Std_Lib.StdLib_All"
begin

section \<open>Miscellaneous C Feature Tests\<close>

text \<open>
  Smoke tests for minor C frontend features: @{text "_Static_assert"},
  range case labels, @{text "_Alignas"}, @{text "__builtin_types_compatible_p"},
  and character constants.
\<close>

locale c_misc_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_uint_ptr: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_ptr_prism +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism
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
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
  and c_uint_ptr_prism :: \<open>('gv, ('addr, 'gv, c_uint) Global_Store.ref) prism\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint_ptr.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

subsection \<open>Static Assert\<close>

micro_c_translate \<open>
  _Static_assert(sizeof(int) == 4, "int must be 32 bits");

  unsigned int static_assert_test(unsigned int x) {
    _Static_assert(1, "trivially true");
    return x + 1;
  }
\<close>

definition c_static_assert_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_static_assert_test_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_static_assert_test_contract

lemma c_static_assert_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_static_assert_test x \<Turnstile>\<^sub>F c_static_assert_test_contract x\<close>
by (crush_boot f: c_static_assert_test_def contract: c_static_assert_test_contract_def)
   (crush_base simp add: c_unsigned_add_def)

subsection \<open>Range Case Labels\<close>

micro_c_translate \<open>
  unsigned int range_case(unsigned int x) {
    switch (x) {
      case 1 ... 5:
        return 1;
      case 10 ... 20:
        return 2;
      default:
        return 0;
    }
  }
\<close>

definition c_range_case_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_range_case_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if 1 \<le> x \<and> x \<le> 5 then 1
                         else if 10 \<le> x \<and> x \<le> 20 then 2
                         else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_range_case_contract

lemma c_range_case_spec [crush_specs]:
  shows \<open>\<Gamma>; c_range_case x \<Turnstile>\<^sub>F c_range_case_contract x\<close>
by (crush_boot f: c_range_case_def contract: c_range_case_contract_def)
   crush_base

subsection \<open>Alignas Specifier\<close>

micro_c_translate \<open>
  unsigned int alignas_test(unsigned int x) {
    _Alignas(16) unsigned int y = x + 1;
    return y;
  }
\<close>

definition c_alignas_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_alignas_test_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_alignas_test_contract

lemma c_alignas_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_alignas_test x \<Turnstile>\<^sub>F c_alignas_test_contract x\<close>
by (crush_boot f: c_alignas_test_def contract: c_alignas_test_contract_def)
   (crush_base simp add: c_unsigned_add_def)

subsection \<open>Builtin Types Compatible\<close>

micro_c_translate \<open>
  unsigned int types_compat_test(unsigned int x) {
    if (__builtin_types_compatible_p(unsigned int, unsigned int))
      return x;
    else
      return 0;
  }
\<close>

definition c_types_compat_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_types_compat_test_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_types_compat_test_contract

lemma c_types_compat_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_types_compat_test x \<Turnstile>\<^sub>F c_types_compat_test_contract x\<close>
by (crush_boot f: c_types_compat_test_def contract: c_types_compat_test_contract_def)
   crush_base

subsection \<open>Character Constants\<close>

micro_c_translate \<open>
  int char_val(void) {
    return 'A';
  }
\<close>

definition c_char_val_contract :: \<open>('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_char_val_contract \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = 65\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_char_val_contract

lemma c_char_val_spec [crush_specs]:
  shows \<open>\<Gamma>; c_char_val \<Turnstile>\<^sub>F c_char_val_contract\<close>
by (crush_boot f: c_char_val_def contract: c_char_val_contract_def)
   crush_base

end

end
