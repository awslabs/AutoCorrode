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

locale c_verification_ctx =
    reference reference_types +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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

end

section \<open>C Unsigned Arithmetic Verification\<close>

text \<open>
  This section demonstrates verification of C code using unsigned integer types.
  Unsigned arithmetic wraps modulo @{term \<open>2^32\<close>} and uses @{const c_unsigned_add}
  instead of @{const c_signed_add}.
\<close>

locale c_uint_verification_ctx =
    reference reference_types +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_uint_ptr: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_ptr_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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
  Test pointer arithmetic: @{text "*(arr + idx)"} reads the element at offset @{text idx}
  via @{const focus_focused} and @{const nth_focus}.
\<close>

micro_c_translate \<open>
  unsigned int ptr_add_read(unsigned int *arr, unsigned int idx) {
    return *(arr + idx);
  }
\<close>

thm c_ptr_add_read_def

definition c_ptr_add_read_contract :: \<open>('addr, 'gv, c_uint list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      c_uint list \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_ptr_add_read_contract arr ag vs idx \<equiv>
    let pre  = arr \<mapsto>\<langle>\<top>\<rangle> ag\<down>vs \<star> \<langle>c_idx_to_nat idx < size arr\<rangle> \<star>
               \<langle>c_idx_to_nat idx < length vs\<rangle>;
        post = \<lambda>r. arr \<mapsto>\<langle>\<top>\<rangle> ag\<down>vs \<star> \<langle>r = vs ! c_idx_to_nat idx\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_ptr_add_read_contract

lemma c_ptr_add_read_spec [crush_specs]:
  shows \<open>\<Gamma>; c_ptr_add_read arr idx \<Turnstile>\<^sub>F c_ptr_add_read_contract arr ag vs idx\<close>
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

end

section \<open>Fixed-width integer type verification (\<^verbatim>\<open>uint16_t\<close>)\<close>

locale c_ushort_verification_ctx =
    reference reference_types +
    ref_c_ushort: reference_allocatable reference_types _ _ _ _ _ _ _ c_ushort_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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
    reference reference_types +
    ref_c_poly: reference_allocatable reference_types _ _ _ _ _ _ _ c_poly_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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
    reference reference_types +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_uint_list: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_list_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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

section \<open>Pointer relational comparison and subtraction\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  typedef unsigned int uint32_t;

  _Bool ptr_less(uint32_t *p, uint32_t *q) {
    return p < q;
  }

  _Bool ptr_le(uint32_t *p, uint32_t *q) {
    return p <= q;
  }

  _Bool ptr_greater(uint32_t *p, uint32_t *q) {
    return p > q;
  }

  _Bool ptr_ge(uint32_t *p, uint32_t *q) {
    return p >= q;
  }

  unsigned long ptr_diff(uint32_t *p, uint32_t *q) {
    return p - q;
  }
\<close>

thm c_ptr_less_def c_ptr_le_def c_ptr_greater_def c_ptr_ge_def c_ptr_diff_def

end

section \<open>Byte buffer pointer arithmetic verification\<close>

locale c_char_verification_ctx =
    reference reference_types +
    ref_c_char: reference_allocatable reference_types _ _ _ _ _ _ _ c_char_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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

definition c_read_byte_contract :: \<open>('addr, 'gv, c_char list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
     c_char list \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_char, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_read_byte_contract buf bg vs idx \<equiv>
    let pre  = buf \<mapsto>\<langle>\<top>\<rangle> bg\<down>vs \<star> \<langle>c_idx_to_nat idx < size buf\<rangle> \<star>
               \<langle>c_idx_to_nat idx < length vs\<rangle>;
        post = \<lambda>r. buf \<mapsto>\<langle>\<top>\<rangle> bg\<down>vs \<star> \<langle>r = vs ! c_idx_to_nat idx\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_byte_contract

lemma c_read_byte_spec [crush_specs]:
  shows \<open>\<Gamma>; c_read_byte buf idx \<Turnstile>\<^sub>F c_read_byte_contract buf bg vs idx\<close>
by (crush_boot f: c_read_byte_def contract: c_read_byte_contract_def) crush_base

end

section \<open>Long long type verification\<close>

locale c_ulong_verification_ctx =
    reference reference_types +
    ref_c_ulong: reference_allocatable reference_types _ _ _ _ _ _ _ c_ulong_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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
    reference reference_types +
    ref_c_uint128: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint128_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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
    reference reference_types +
    ref_c_point: reference_allocatable reference_types _ _ _ _ _ _ _ c_point_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
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
end


