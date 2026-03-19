theory Simple_C_Functions
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    "Micro_Rust_Std_Lib.StdLib_All"
begin

section \<open>First end-to-end C verification example\<close>

text \<open>
  This theory demonstrates end-to-end verification of C source code using
  AutoCorrode. The pipeline is:
  \<^enum> Parse C source via @{text micro_c_translate} to produce HOL definitions
  \<^enum> Define a separation-logic contract
  \<^enum> Prove the contract using @{text crush_boot} and @{text crush_base}
\<close>

subsection \<open>Locale setup\<close>

text \<open>
  The locale provides the reference infrastructure: allocation, dereference,
  and update operations with their separation-logic specifications.
  This is the same boilerplate as the Rust examples.
\<close>

locale c_translation_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr
  for c_ptr_add :: \<open>('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_shift_signed :: \<open>('addr, 'gv) gref \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_diff :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> int\<close>
  and c_ptr_less :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_le :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_greater :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_ge :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_to_uintptr :: \<open>('addr, 'gv) gref \<Rightarrow> int\<close>
  and c_uintptr_to_ptr :: \<open>int \<Rightarrow> ('addr, 'gv) gref\<close>

locale c_base_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types
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

locale c_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
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
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

subsection \<open>C swap function\<close>

text \<open>Parse the C swap function.\<close>
micro_c_translate \<open>

  void swap(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
  }
\<close>

thm c_swap_def

text \<open>
  The contract for swap: given two disjoint references with values
  @{text lval} and @{text rval}, after swap the references hold each
  other's original values.
\<close>
definition c_swap_contract :: \<open>('addr, 'gv, c_int) Global_Store.ref \<Rightarrow>
      ('addr, 'gv, c_int) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> 'gv \<Rightarrow> c_int \<Rightarrow> c_int \<Rightarrow>
      ('s, 'a, 'b) function_contract\<close> where
  \<open>c_swap_contract lref rref lg rg lval rval \<equiv>
    let pre  = can_alloc_reference \<star>
               lref \<mapsto>\<langle>\<top>\<rangle> lg\<down>lval \<star> rref \<mapsto>\<langle>\<top>\<rangle> rg\<down>rval;
        post = \<lambda> _. can_alloc_reference \<star>
               lref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. rval) \<sqdot> (lg\<down>lval) \<star>
               rref \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. lval) \<sqdot> (rg\<down>rval)
     in make_function_contract pre post\<close>
ucincl_auto c_swap_contract

text \<open>Prove that the C swap function satisfies its contract.\<close>
lemma c_swap_spec:
  shows \<open>\<Gamma>; c_swap lref rref \<Turnstile>\<^sub>F c_swap_contract lref rref lg rg lval rval\<close>
by (crush_boot f: c_swap_def contract: c_swap_contract_def) crush_base

subsection \<open>C Max Function\<close>

text \<open>A simple function exercising conditionals and return.\<close>
micro_c_translate \<open>
  int max(int a, int b) {
    if (a > b)
      return a;
    else
      return b;
  }
\<close>

thm c_max_def

text \<open>
  The contract for max uses signed comparison on words.
  The translated code uses @{const c_signed_less} which compares
  @{term "sint b < sint a"} (operands swapped for >).
\<close>
definition c_max_contract ::
    \<open>c_int \<Rightarrow> c_int \<Rightarrow> ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if sint b < sint a then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_max_contract

lemma c_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_max a b \<Turnstile>\<^sub>F c_max_contract a b\<close>
by (crush_boot f: c_max_def contract: c_max_contract_def) (crush_base simp add: c_signed_less_def)

subsection \<open>C abs function\<close>

micro_c_translate \<open>
  int abs_val(int x) {
    if (x > 0)
      return x;
    else
      return 0 - x;
  }
\<close>

thm c_abs_val_def

text \<open>
  The abs function requires a no-overflow precondition: subtraction
  overflows when x is the minimum signed value. The precondition
  ensures the negation is safe.
\<close>
definition c_abs_val_contract :: \<open>c_int \<Rightarrow> ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_abs_val_contract x \<equiv>
    let pre  = \<langle>-(2^31 :: int) < sint x\<rangle>;
        post = \<lambda>r. \<langle>r = (if sint x > sint (0 :: c_int) then x else word_of_int (0 - sint x))\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_abs_val_contract

lemma c_abs_val_spec [crush_specs]:
  shows \<open>\<Gamma>; c_abs_val x \<Turnstile>\<^sub>F c_abs_val_contract x\<close>
by (crush_boot f: c_abs_val_def contract: c_abs_val_contract_def) (crush_base simp add:
  c_signed_less_def c_signed_sub_def c_signed_overflow_def Let_def)

subsection \<open>Signed Addition (with Overflow Precondition)\<close>

text \<open>
  A function exercising signed addition directly.
  The precondition establishes no-overflow using @{const c_signed_in_range},
  and the postcondition shows the result equals @{term "word_of_int (sint a + sint b)"}.
\<close>
micro_c_translate \<open>
  int signed_add(int a, int b) {
    return a + b;
  }
\<close>

definition c_signed_add_contract ::
    \<open>c_int \<Rightarrow> c_int \<Rightarrow> ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_signed_add_contract a b \<equiv>
    let pre  = \<langle>c_signed_in_range (sint a + sint b) LENGTH(32)\<rangle>;
        post = \<lambda>r. \<langle>r = word_of_int (sint a + sint b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_signed_add_contract

lemma c_signed_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_signed_add a b \<Turnstile>\<^sub>F c_signed_add_contract a b\<close>
by (crush_boot f: c_signed_add_def contract: c_signed_add_contract_def)
   (crush_base simp add: c_signed_add_def c_signed_overflow_def Let_def)

end

section \<open>C Unsigned Arithmetic Verification\<close>

text \<open>
  This section demonstrates verification of C code using unsigned integer types.
  Unsigned arithmetic wraps modulo @{term \<open>2^32\<close>} and uses @{const c_unsigned_add}
  instead of @{const c_signed_add}.
\<close>

locale c_uint_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_uint_ptr: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_ptr_prism
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
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint_ptr.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  unsigned int u_add(unsigned int a, unsigned int b) {
    return a + b;
  }
\<close>

thm c_u_add_def

micro_c_translate \<open>
  unsigned int u_call_helper(unsigned int x) {
    return x;
  }

  unsigned int u_call_caller(unsigned int a, unsigned int b) {
    return u_call_helper(a) + u_call_helper(b);
  }
\<close>

thm c_u_call_helper_def c_u_call_caller_def

text \<open>
  The contract for @{text u_add}: unsigned addition wraps, so the result is
  always @{term \<open>a + b\<close>} (Isabelle word addition already wraps).
  No overflow precondition needed.
\<close>
definition c_u_add_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_add_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_add_contract

lemma c_u_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_add a b \<Turnstile>\<^sub>F c_u_add_contract a b\<close>
by (crush_boot f: c_u_add_def contract: c_u_add_contract_def) (crush_base simp add: c_unsigned_add_def)

micro_c_translate \<open>
  unsigned int u_max(unsigned int a, unsigned int b) {
    if (a > b)
      return a;
    else
      return b;
  }
\<close>

thm c_u_max_def

definition c_u_max_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if b < a then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_max_contract

lemma c_u_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_max a b \<Turnstile>\<^sub>F c_u_max_contract a b\<close>
by (crush_boot f: c_u_max_def contract: c_u_max_contract_def) (crush_base simp add: c_unsigned_less_def)

subsection \<open>Comma operator\<close>

micro_c_translate \<open>

  unsigned int comma_test(unsigned int a, unsigned int b) {
    unsigned int x = (a, b);
    return x;
  }
\<close>

definition c_comma_test_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_comma_test_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_comma_test_contract

lemma c_comma_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_comma_test a b \<Turnstile>\<^sub>F c_comma_test_contract a b\<close>
by (crush_boot f: c_comma_test_def contract: c_comma_test_contract_def) crush_base

subsection \<open>Multiple Declarations\<close>

micro_c_translate \<open>
  unsigned int multi_decl_add(unsigned int a, unsigned int b) {
    unsigned int x = a, y = b;
    return x + y;
  }
\<close>

definition c_multi_decl_add_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_multi_decl_add_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_multi_decl_add_contract

lemma c_multi_decl_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_multi_decl_add a b \<Turnstile>\<^sub>F c_multi_decl_add_contract a b\<close>
by (crush_boot f: c_multi_decl_add_def contract: c_multi_decl_add_contract_def)
  (crush_base simp add: c_unsigned_add_def)
  
subsection \<open>Pre-increment\<close>

micro_c_translate \<open>
  unsigned int pre_inc_test(unsigned int init) {
    unsigned int x = init;
    unsigned int r = ++x;
    return r;
  }
\<close>

definition c_pre_inc_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_pre_inc_test_contract init \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = init + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_pre_inc_test_contract

lemma c_pre_inc_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_pre_inc_test init \<Turnstile>\<^sub>F c_pre_inc_test_contract init\<close>
by (crush_boot f: c_pre_inc_test_def contract: c_pre_inc_test_contract_def)
  (crush_base simp add: c_unsigned_add_def)
  
subsection \<open>Post-Increment\<close>

micro_c_translate \<open>
  unsigned int post_inc_test(unsigned int init) {
    unsigned int x = init;
    unsigned int r = x++;
    return r;
  }
\<close>

definition c_post_inc_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_post_inc_test_contract init \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = init\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_post_inc_test_contract

lemma c_post_inc_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_post_inc_test init \<Turnstile>\<^sub>F c_post_inc_test_contract init\<close>
by (crush_boot f: c_post_inc_test_def contract: c_post_inc_test_contract_def)
  (crush_base simp add: c_unsigned_add_def)

subsection \<open>Post-Decrement\<close>

micro_c_translate \<open>
  unsigned int post_dec_test(unsigned int init) {
    unsigned int x = init;
    unsigned int r = x--;
    return r;
  }
\<close>

definition c_post_dec_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_post_dec_test_contract init \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = init\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_post_dec_test_contract

lemma c_post_dec_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_post_dec_test init \<Turnstile>\<^sub>F c_post_dec_test_contract init\<close>
by (crush_boot f: c_post_dec_test_def contract: c_post_dec_test_contract_def)
  (crush_base simp add: c_unsigned_sub_def)

subsection \<open>Not-Equal Operator\<close>

micro_c_translate \<open>
  unsigned int neq_test(unsigned int a, unsigned int b) {
    if (a != b)
      return 1;
    else
      return 0;
  }
\<close>

definition c_neq_test_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_neq_test_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if a \<noteq> b then 1 else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_neq_test_contract

lemma c_neq_test_spec [crush_specs]:
  shows \<open>\<Gamma>; c_neq_test a b \<Turnstile>\<^sub>F c_neq_test_contract a b\<close>
by (crush_boot f: c_neq_test_def contract: c_neq_test_contract_def)
  (crush_base simp add: c_unsigned_neq_def)

subsection \<open>Logical NOT\<close>

micro_c_translate \<open>
  unsigned int is_zero(unsigned int x) {
    if (!x)
      return 1;
    else
      return 0;
  }
\<close>

definition c_is_zero_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_is_zero_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if x = 0 then 1 else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_is_zero_contract

lemma c_is_zero_spec [crush_specs]:
  shows \<open>\<Gamma>; c_is_zero x \<Turnstile>\<^sub>F c_is_zero_contract x\<close>
by (crush_boot f: c_is_zero_def contract: c_is_zero_contract_def)
  (crush_base simp add: c_unsigned_eq_def)

subsection \<open>Unary plus\<close>

micro_c_translate \<open>
  unsigned int uplus(unsigned int x) {
    return +x;
  }
\<close>

definition c_uplus_contract ::
    \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_uplus_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_uplus_contract

lemma c_uplus_spec [crush_specs]:
  shows \<open>\<Gamma>; c_uplus x \<Turnstile>\<^sub>F c_uplus_contract x\<close>
by (crush_boot f: c_uplus_def contract: c_uplus_contract_def) crush_base

subsection \<open>Ternary operator\<close>

micro_c_translate \<open>
  unsigned int ternary_max(unsigned int a, unsigned int b) {
    return (a > b) ? a : b;
  }
\<close>

definition c_ternary_max_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_ternary_max_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = (if b < a then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_ternary_max_contract

lemma c_ternary_max_spec [crush_specs]:
  shows \<open>\<Gamma>; c_ternary_max a b \<Turnstile>\<^sub>F c_ternary_max_contract a b\<close>
by (crush_boot f: c_ternary_max_def contract: c_ternary_max_contract_def)
    (crush_base simp add: c_unsigned_less_def)

subsection \<open>Compound assignment\<close>

micro_c_translate \<open>
  unsigned int add_assign(unsigned int a, unsigned int b) {
    unsigned int x = a;
    x += b;
    return x;
  }
\<close>

definition c_add_assign_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow>
      ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_add_assign_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_add_assign_contract

lemma c_add_assign_spec [crush_specs]:
  shows \<open>\<Gamma>; c_add_assign a b \<Turnstile>\<^sub>F c_add_assign_contract a b\<close>
by (crush_boot f: c_add_assign_def contract: c_add_assign_contract_def)
  (crush_base simp add: c_unsigned_add_def)

subsection \<open>Cast: widen unsigned char to unsigned int\<close>

micro_c_translate \<open>
  unsigned int widen_char(unsigned char x) {
    return (unsigned int)x;
  }
\<close>

thm c_widen_char_def

definition c_widen_char_contract :: \<open>c_char \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_widen_char_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = ucast x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_widen_char_contract

lemma c_widen_char_spec [crush_specs]:
  shows \<open>\<Gamma>; c_widen_char x \<Turnstile>\<^sub>F c_widen_char_contract x\<close>
by (crush_boot f: c_widen_char_def contract: c_widen_char_contract_def) (crush_base simp add: c_ucast_def)

subsection \<open>Integer literal suffix\<close>

micro_c_translate \<open>
  unsigned int suffix_add(unsigned int x) {
    return x + 1U;
  }
\<close>

thm c_suffix_add_def

definition c_suffix_add_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_suffix_add_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_suffix_add_contract

lemma c_suffix_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_suffix_add x \<Turnstile>\<^sub>F c_suffix_add_contract x\<close>
by (crush_boot f: c_suffix_add_def contract: c_suffix_add_contract_def)
  (crush_base simp add: c_unsigned_add_def)

subsection \<open>Assignment to parameter\<close>

micro_c_translate \<open>
  unsigned int double_val(unsigned int x) {
    x = x + x;
    return x;
  }
\<close>

thm c_double_val_def

definition c_double_val_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_double_val_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = x + x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_double_val_contract

lemma c_double_val_spec [crush_specs]:
  shows \<open>\<Gamma>; c_double_val x \<Turnstile>\<^sub>F c_double_val_contract x\<close>
by (crush_boot f: c_double_val_def contract: c_double_val_contract_def)
  (crush_base simp add: c_unsigned_add_def)

subsection \<open>Compound pointer dereference\<close>

micro_c_translate \<open>
  unsigned int inc_ptr(unsigned int *p) {
    *p += 1;
    return *p;
  }
\<close>

thm c_inc_ptr_def

definition c_inc_ptr_contract :: \<open>('addr, 'gv, c_uint) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_inc_ptr_contract p pg val \<equiv>
    let pre  = p \<mapsto>\<langle>\<top>\<rangle> pg\<down>val;
        post = \<lambda>r. p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. val + 1) \<sqdot> (pg\<down>val) \<star> \<langle>r = val + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_inc_ptr_contract

lemma c_inc_ptr_spec [crush_specs]:
  shows \<open>\<Gamma>; c_inc_ptr p \<Turnstile>\<^sub>F c_inc_ptr_contract p pg val\<close>
by (crush_boot f: c_inc_ptr_def contract: c_inc_ptr_contract_def)
  (crush_base simp add: c_unsigned_add_def)

subsection \<open>Sizeof\<close>

micro_c_translate \<open>
  unsigned int size_of_int(void) {
    return sizeof(int);
  }
\<close>

thm c_size_of_int_def

subsection \<open>Switch statement\<close>

micro_c_translate \<open>
  unsigned int classify(unsigned int x) {
    unsigned int result;

    switch (x) {
    case 0:
      result = 10;
      break;
    case 1:
      result = 20;
      break;
    default:
      result = 30;
      break;
    }
    return result;
}
\<close>

thm c_classify_def

definition c_classify_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_classify_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = (if x = 0 then 10 else if x = 1 then 20 else 30)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_classify_contract

lemma c_classify_spec [crush_specs]:
  shows \<open>\<Gamma>; c_classify x \<Turnstile>\<^sub>F c_classify_contract x\<close>
by (crush_boot f: c_classify_def contract: c_classify_contract_def) crush_base

subsection \<open>Address-of\<close>

text \<open>
  Test address-of: @{text "&x"} on a local variable returns the ref itself.
  The parameter @{text x} is auto-promoted to a local ref because @{text "&x"} appears.
\<close>

micro_c_translate \<open>
  unsigned int inc_via_addr(void) {
    unsigned int x = 5;
    unsigned int *p = &x;
    *p = *p + 1;
    return x;
  }
\<close>

thm c_inc_via_addr_def

definition c_inc_via_addr_contract :: \<open>('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_inc_via_addr_contract \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = 6\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_inc_via_addr_contract

lemma c_inc_via_addr_spec [crush_specs]:
  shows \<open>\<Gamma>; c_inc_via_addr \<Turnstile>\<^sub>F c_inc_via_addr_contract\<close>
by (crush_boot f: c_inc_via_addr_def contract: c_inc_via_addr_contract_def)
  (crush_base simp add: c_unsigned_add_def)

subsection \<open>Pointer arithmetic\<close>

text \<open>
  Test pointer arithmetic: @{text "*(arr + idx)"} reads through the
  pointer model by shifting the base reference and dereferencing the result.
\<close>

micro_c_translate \<open>
  unsigned int ptr_add_read(unsigned int *arr, unsigned int idx) {
    return *(arr + idx);
  }
\<close>

thm c_ptr_add_read_def

definition c_ptr_add_read_contract :: \<open>('addr, 'gv, c_uint) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_ptr_add_read_contract arr ag v idx \<equiv>
    let elem_ref = make_focused
                     (c_ptr_add (unwrap_focused arr) (c_idx_to_nat idx) (c_sizeof TYPE(c_uint)))
                     (get_focus arr);
        pre  = elem_ref \<mapsto>\<langle>\<top>\<rangle> ag\<down>v;
        post = \<lambda>r. elem_ref \<mapsto>\<langle>\<top>\<rangle> ag\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_ptr_add_read_contract

lemma c_ptr_add_read_spec [crush_specs]:
  shows \<open>\<Gamma>; c_ptr_add_read arr idx \<Turnstile>\<^sub>F c_ptr_add_read_contract arr ag v idx\<close>
by (crush_boot f: c_ptr_add_read_def contract: c_ptr_add_read_contract_def) crush_base

subsection \<open>Forward-only goto\<close>

text \<open>
  Test forward-only goto: @{text "goto done"} skips @{text "result = a + b"}
  when @{text "b == 0"}, using a per-label flag mechanism.
\<close>

micro_c_translate \<open>
  unsigned int skip_add(unsigned int a, unsigned int b) {
    unsigned int result = a;
    if (b == 0)
      goto done;
    result = a + b;
  done:
    return result;
  }
\<close>

thm c_skip_add_def

definition c_skip_add_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_skip_add_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if b = 0 then a else a + b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_skip_add_contract

lemma c_skip_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_skip_add a b \<Turnstile>\<^sub>F c_skip_add_contract a b\<close>
by (crush_boot f: c_skip_add_def contract: c_skip_add_contract_def)
    (crush_base simp add: c_unsigned_eq_def c_unsigned_add_def)

subsection \<open>Unsigned Division (with Division-by-Zero Precondition)\<close>

text \<open>
  Exercises unsigned division end-to-end. The precondition ensures
  the divisor is non-zero (division by zero aborts with @{const DivisionByZero}).
  Unsigned division has no overflow — the result is always representable.
\<close>
micro_c_translate \<open>
  unsigned int u_div(unsigned int a, unsigned int b) {
    return a / b;
  }
\<close>

definition c_u_div_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_u_div_contract a b \<equiv>
    let pre  = \<langle>b \<noteq> 0\<rangle>;
        post = \<lambda>r. \<langle>r = a div b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_div_contract

lemma c_u_div_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_div a b \<Turnstile>\<^sub>F c_u_div_contract a b\<close>
by (crush_boot f: c_u_div_def contract: c_u_div_contract_def)
   (crush_base simp add: c_unsigned_div_def c_division_by_zero_def c_abort_def)

end

section \<open>Fixed-width integer type verification (\<^verbatim>\<open>uint16_t\<close>)\<close>

locale c_ushort_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_ushort: reference_allocatable reference_types _ _ _ _ _ _ _ c_ushort_prism
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
  and c_ushort_prism :: \<open>('gv, c_ushort) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_ushort.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  typedef unsigned short uint16_t;

  uint16_t u16_add(uint16_t a, uint16_t b) {
    return a + b;
  }
\<close>

thm c_u16_add_def

definition c_u16_add_contract ::
    \<open>c_ushort \<Rightarrow> c_ushort \<Rightarrow> ('s::{sepalg}, c_ushort, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u16_add_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u16_add_contract

lemma c_u16_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u16_add a b \<Turnstile>\<^sub>F c_u16_add_contract a b\<close>
by (crush_boot f: c_u16_add_def contract: c_u16_add_contract_def)
  (crush_base simp add: c_unsigned_add_def)

micro_c_translate \<open>
  typedef unsigned long size_t;

  size_t size_add(size_t a, size_t b) {
    return a + b;
  }
\<close>

end

section \<open>Void function verification\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  void void_write(unsigned int *p, unsigned int v) {
    *p = v;
  }
\<close>

thm c_void_write_def

definition c_void_write_contract ::
    \<open>('addr, 'gv, c_uint) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, unit, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_void_write_contract p pg old_val v \<equiv>
    let pre  = p \<mapsto>\<langle>\<top>\<rangle> pg\<down>old_val;
        post = \<lambda>_. p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. v) \<sqdot> (pg\<down>old_val)
     in make_function_contract pre post\<close>
ucincl_auto c_void_write_contract

lemma c_void_write_spec [crush_specs]:
  shows \<open>\<Gamma>; c_void_write p v \<Turnstile>\<^sub>F c_void_write_contract p pg old_val v\<close>
by (crush_boot f: c_void_write_def contract: c_void_write_contract_def) crush_base

end

section \<open>Chained Struct-Array Access Verification\<close>

micro_c_translate \<open>
  struct poly {
    int coeffs[256];
  };
\<close>

thm c_poly.record_simps

locale c_poly_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_poly: reference_allocatable reference_types _ _ _ _ _ _ _ c_poly_prism
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
  and c_poly_prism :: \<open>('gv, c_poly) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_poly.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>

  struct poly {
    int coeffs[256];
  };

  int read_coeff(struct poly *p, unsigned int i) {
    return p->coeffs[i];
  }
\<close>

thm c_read_coeff_def

definition c_read_coeff_contract ::
    \<open>('addr, 'gv, c_poly) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> c_poly \<Rightarrow> c_uint \<Rightarrow>
     ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_coeff_contract p pg pval i \<equiv>
    let pre  = p \<mapsto>\<langle>\<top>\<rangle> pg\<down>pval \<star>
               \<langle>c_idx_to_nat i < length (c_poly_coeffs pval)\<rangle>;
        post = \<lambda>r. p \<mapsto>\<langle>\<top>\<rangle> pg\<down>pval \<star>
               \<langle>r = c_poly_coeffs pval ! c_idx_to_nat i\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_coeff_contract

lemma c_read_coeff_spec [crush_specs]:
  shows \<open>\<Gamma>; c_read_coeff p i \<Turnstile>\<^sub>F c_read_coeff_contract p pg pval i\<close>
by (crush_boot f: c_read_coeff_def contract: c_read_coeff_contract_def) crush_base

micro_c_translate \<open>
  struct poly {
    int coeffs[256];
  };

  void write_coeff(struct poly *p, unsigned int i, int v) {
    p->coeffs[i] = v;
  }
\<close>

thm c_write_coeff_def

definition c_write_coeff_contract ::
    \<open>('addr, 'gv, c_poly) Global_Store.ref \<Rightarrow>
     'gv \<Rightarrow> c_poly \<Rightarrow> c_uint \<Rightarrow> c_int \<Rightarrow>
     ('s::{sepalg}, unit, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_write_coeff_contract p pg pval i v \<equiv>
    let pre  = p \<mapsto>\<langle>\<top>\<rangle> pg\<down>pval \<star> \<langle>c_idx_to_nat i < length (c_poly_coeffs pval)\<rangle>;
        post = \<lambda>_. p \<mapsto>\<langle>\<top>\<rangle>
                   (\<lambda>_. pval\<lparr>c_poly_coeffs := (c_poly_coeffs pval)[c_idx_to_nat i := v]\<rparr>)
                   \<sqdot> (pg\<down>pval)
     in make_function_contract pre post\<close>
ucincl_auto c_write_coeff_contract

lemma c_write_coeff_spec [crush_specs]:
  shows \<open>\<Gamma>; c_write_coeff p i v \<Turnstile>\<^sub>F c_write_coeff_contract p pg pval i v\<close>
by (crush_boot f: c_write_coeff_def contract: c_write_coeff_contract_def) crush_base

micro_c_translate \<open>
  struct poly {
    int coeffs[256];
  };

  void dot_write_coeff(struct poly *p, unsigned int i, int v) {
    (*p).coeffs[i] = v;
  }
\<close>

thm c_dot_write_coeff_def

lemma c_dot_write_coeff_spec [crush_specs]:
  shows \<open>\<Gamma>; c_dot_write_coeff p i v \<Turnstile>\<^sub>F c_write_coeff_contract p pg pval i v\<close>
by (crush_boot f: c_dot_write_coeff_def contract: c_write_coeff_contract_def) crush_base

end

section \<open>Array parameter and local array verification\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>

  unsigned int arr_sum(unsigned int arr[], unsigned int i, unsigned int j) {
    return arr[i] + arr[j];
  }
\<close>

thm c_arr_sum_def

end

section \<open>Non-constant local array initializers\<close>

locale c_uint_arr_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_uint_list: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_list_prism
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
  and c_uint_list_prism :: \<open>('gv, c_uint list) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint_list.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  unsigned int dyn_arr_sum(unsigned int a, unsigned int b) {
    unsigned int arr[2] = {a, b};
    return arr[0] + arr[1];
  }
\<close>

thm c_dyn_arr_sum_def

micro_c_translate \<open>
  unsigned int desig_arr_test(void) {
    unsigned int arr[4] = {[2] = 42, [0] = 10};
    return arr[0] + arr[2];
  }
\<close>

thm c_desig_arr_test_def

end

section \<open>Pointer subtraction\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  typedef unsigned int uint32_t;

  long ptr_diff_test(uint32_t *p, uint32_t *q) {
    return p - q;
  }
\<close>

thm c_ptr_diff_test_def

end

section \<open>Byte buffer pointer arithmetic verification\<close>

locale c_char_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_char: reference_allocatable reference_types _ _ _ _ _ _ _ c_char_prism
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
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_char.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  typedef unsigned char uint8_t;

  uint8_t read_byte(uint8_t *buf, unsigned int idx) {
    return *(buf + idx);
  }
\<close>

thm c_read_byte_def

definition c_read_byte_contract :: \<open>('addr, 'gv, c_char) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
     c_char \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_char, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_byte_contract buf bg v idx \<equiv>
    let elem_ref = make_focused
                     (c_ptr_add (unwrap_focused buf) (c_idx_to_nat idx) (c_sizeof TYPE(c_char)))
                     (get_focus buf);
        pre  = elem_ref \<mapsto>\<langle>\<top>\<rangle> bg\<down>v;
        post = \<lambda>r. elem_ref \<mapsto>\<langle>\<top>\<rangle> bg\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_byte_contract

lemma c_read_byte_spec [crush_specs]:
  shows \<open>\<Gamma>; c_read_byte buf idx \<Turnstile>\<^sub>F c_read_byte_contract buf bg v idx\<close>
by (crush_boot f: c_read_byte_def contract: c_read_byte_contract_def) crush_base

end

section \<open>Long long type verification\<close>

locale c_ulong_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_ulong: reference_allocatable reference_types _ _ _ _ _ _ _ c_ulong_prism
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
  and c_ulong_prism :: \<open>('gv, c_ulong) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_ulong.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  typedef unsigned long long uint64_ll_t;

  uint64_ll_t long_long_add(uint64_ll_t a, uint64_ll_t b) {
    return a + b;
  }

\<close>

thm c_long_long_add_def

definition c_long_long_add_contract :: \<open>c_ulong \<Rightarrow> c_ulong \<Rightarrow> ('s::{sepalg}, c_ulong, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_long_long_add_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_long_long_add_contract

lemma c_long_long_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_long_long_add a b \<Turnstile>\<^sub>F c_long_long_add_contract a b\<close>
by (crush_boot f: c_long_long_add_def contract: c_long_long_add_contract_def)
  (crush_base simp add: c_unsigned_add_def)

end

section \<open>128-bit integer type verification\<close>

locale c_uint128_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_uint128: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint128_prism
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
  and c_uint128_prism :: \<open>('gv, c_uint128) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint128.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  typedef unsigned __int128 uint128_t;

  uint128_t int128_add(uint128_t a, uint128_t b) {
    return a + b;
  }

\<close>

thm c_int128_add_def

definition c_int128_add_contract :: \<open>c_uint128 \<Rightarrow> c_uint128 \<Rightarrow> ('s::{sepalg}, c_uint128, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_int128_add_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a + b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_int128_add_contract

lemma c_int128_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_int128_add a b \<Turnstile>\<^sub>F c_int128_add_contract a b\<close>
by (crush_boot f: c_int128_add_def contract: c_int128_add_contract_def)
  (crush_base simp add: c_unsigned_add_def)

end

section \<open>Struct initializer list verification\<close>

micro_c_translate \<open>
  typedef struct { unsigned int x; unsigned int y; } point;
\<close>

locale c_point_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_point: reference_allocatable reference_types _ _ _ _ _ _ _ c_point_prism
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
  and c_point_prism :: \<open>('gv, c_point) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_point.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  typedef struct { unsigned int x; unsigned int y; } point;

  unsigned int point_sum_init(void) {
    point p = {.x = 3, .y = 7};
    return p.x + p.y;
  }
\<close>

thm c_point_sum_init_def

definition c_point_sum_init_contract :: \<open>('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_point_sum_init_contract \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. \<langle>r = 10\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_point_sum_init_contract

lemma c_point_sum_init_spec [crush_specs]:
  shows \<open>\<Gamma>; c_point_sum_init \<Turnstile>\<^sub>F c_point_sum_init_contract\<close>
by (crush_boot f: c_point_sum_init_def contract: c_point_sum_init_contract_def)
  crush_base

end

section \<open>Pointer ternary\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  unsigned int *pick_ptr(unsigned int flag, unsigned int *a, unsigned int *b) {
    return flag ? a : b;
  }
\<close>

thm c_pick_ptr_def

end

section \<open>Alignof\<close>

context c_ulong_verification_ctx
begin

micro_c_translate \<open>
  unsigned long long get_align(void) {
    return _Alignof(int);
  }
\<close>

thm c_get_align_def

definition c_get_align_contract :: \<open>('s::{sepalg}, c_ulong, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_get_align_contract \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = 4\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_get_align_contract

lemma c_get_align_spec [crush_specs]:
  shows \<open>\<Gamma>; c_get_align \<Turnstile>\<^sub>F c_get_align_contract\<close>
by (crush_boot f: c_get_align_def contract: c_get_align_contract_def)
  crush_base

end

section \<open>More than 10 function arguments\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  unsigned int sum12(unsigned int a, unsigned int b, unsigned int c,
                     unsigned int d, unsigned int e, unsigned int f,
                     unsigned int g, unsigned int h, unsigned int i,
                     unsigned int j, unsigned int k, unsigned int l) {
    return a + l;
  }
\<close>

thm c_sum12_def

definition c_sum12_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow>
    c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow>
    ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_sum12_contract a b c d e f g h i j k l \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a + l\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_sum12_contract

lemma c_sum12_spec [crush_specs]:
  shows \<open>\<Gamma>; c_sum12 a b c d e f g h i j k l \<Turnstile>\<^sub>F c_sum12_contract a b c d e f g h i j k l\<close>
by (crush_boot f: c_sum12_def contract: c_sum12_contract_def)
  crush_base

end

section \<open>sizeof(struct)\<close>

context c_point_verification_ctx
begin

micro_c_translate \<open>
  typedef struct { unsigned int x; unsigned int y; } point;

  unsigned int point_size(void) {
    return sizeof(point);
  }
\<close>

thm c_point_size_def

definition c_point_size_contract :: \<open>('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_point_size_contract \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = 8\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_point_size_contract

lemma c_point_size_spec [crush_specs]:
  shows \<open>\<Gamma>; c_point_size \<Turnstile>\<^sub>F c_point_size_contract\<close>
by (crush_boot f: c_point_size_def contract: c_point_size_contract_def)
  crush_base

end

section \<open>Increment on dereference\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  void inc_deref(unsigned int *p) {
    ++*p;
  }
\<close>

thm c_inc_deref_def

end

section \<open>Increment on array element\<close>

context c_uint_arr_verification_ctx
begin

micro_c_translate \<open>
  unsigned int inc_arr_elem(void) {
    unsigned int arr[3] = {10, 20, 30};
    ++arr[1];
    return arr[1];
  }
\<close>

thm c_inc_arr_elem_def

end

section \<open>Scalar compound literal\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  unsigned int compound_scalar(unsigned int x) {
    return (unsigned int){x};
  }
\<close>

thm c_compound_scalar_def

definition c_compound_scalar_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_compound_scalar_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_compound_scalar_contract

lemma c_compound_scalar_spec [crush_specs]:
  shows \<open>\<Gamma>; c_compound_scalar x \<Turnstile>\<^sub>F c_compound_scalar_contract x\<close>
by (crush_boot f: c_compound_scalar_def contract: c_compound_scalar_contract_def)
  crush_base

end

section \<open>Pointer to integer cast\<close>

context c_ulong_verification_ctx
begin

micro_c_translate \<open>
  typedef unsigned long long uintptr_t;

  unsigned long long ptr_to_int(unsigned int *p) {
    return (uintptr_t)p;
  }
\<close>

thm c_ptr_to_int_def

micro_c_translate \<open>
  typedef unsigned long long uintptr_t;

  unsigned int *int_to_ptr(uintptr_t p) {
    return (unsigned int *)p;
  }
\<close>

thm c_int_to_ptr_def

end

section \<open>String literal as array initializer\<close>

locale c_char_arr_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_char: reference_allocatable reference_types _ _ _ _ _ _ _ c_char_prism +
    ref_c_char_list: reference_allocatable reference_types _ _ _ _ _ _ _ c_char_list_prism
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
  and c_char_list_prism :: \<open>('gv, c_char list) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_char.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_char_list.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  unsigned char read_str_first(void) {
    unsigned char s[] = "AB";
    return s[0];
  }
\<close>

thm c_read_str_first_def

definition c_read_str_first_contract :: \<open>('s::{sepalg}, c_char, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_str_first_contract \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. \<langle>r = 65\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_str_first_contract

lemma c_read_str_first_spec [crush_specs]:
  shows \<open>\<Gamma>; c_read_str_first \<Turnstile>\<^sub>F c_read_str_first_contract\<close>
by (crush_boot f: c_read_str_first_def contract: c_read_str_first_contract_def)
  crush_base

end

section \<open>Generic selection\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  unsigned int generic_add(unsigned int x) {
    return _Generic(x, unsigned int: x + 1, default: x);
  }
\<close>

thm c_generic_add_def

definition c_generic_add_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_generic_add_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_generic_add_contract

lemma c_generic_add_spec [crush_specs]:
  shows \<open>\<Gamma>; c_generic_add x \<Turnstile>\<^sub>F c_generic_add_contract x\<close>
by (crush_boot f: c_generic_add_def contract: c_generic_add_contract_def)
  crush_base

end

end
