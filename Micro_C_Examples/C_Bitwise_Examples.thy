theory C_Bitwise_Examples
  imports
    Simple_C_Functions
begin

section \<open>C Bitwise Operation Verification\<close>

text \<open>
  This theory demonstrates verification of C bitwise and shift operations.
  Bitwise AND, OR, XOR, and NOT have no undefined behavior in C.
  Shifts abort when the shift amount is out of range, and signed shifts
  additionally detect negative-operand and overflow UB.
\<close>

subsection \<open>Unsigned bitwise smoke tests\<close>

context c_uint_verification_ctx
begin

micro_c_translate \<open>
  unsigned int u_and(unsigned int a, unsigned int b) {
    return a & b;
  }
\<close>

definition c_u_and_bw_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_and_bw_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a AND b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_and_bw_contract

lemma c_u_and_bw_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_and a b \<Turnstile>\<^sub>F c_u_and_bw_contract a b\<close>
by (crush_boot f: c_u_and_def contract: c_u_and_bw_contract_def)
  (crush_base simp add: c_unsigned_and_def)

micro_c_translate \<open>
  unsigned int u_not(unsigned int x) {
    return ~x;
  }
\<close>

definition c_u_not_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_not_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = NOT x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_not_contract

lemma c_u_not_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_not x \<Turnstile>\<^sub>F c_u_not_contract x\<close>
by (crush_boot f: c_u_not_def contract: c_u_not_contract_def)
  (crush_base simp add: c_unsigned_not_def)

micro_c_translate \<open>
  unsigned int u_shl(unsigned int x, unsigned int n) {
    return x << n;
  }
\<close>

definition c_u_shl_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_u_shl_contract x n \<equiv>
    let pre  = \<langle>unat n < 32\<rangle>;
        post = \<lambda>r. \<langle>r = push_bit (unat n) x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_u_shl_contract

lemma c_u_shl_spec [crush_specs]:
  shows \<open>\<Gamma>; c_u_shl x n \<Turnstile>\<^sub>F c_u_shl_contract x n\<close>
by (crush_boot f: c_u_shl_def contract: c_u_shl_contract_def)
    (crush_base simp add: c_unsigned_shl_def)

text \<open>Shift out of range: when the shift amount exceeds the bit width,
  the operation correctly aborts with @{const ShiftOutOfRange}.\<close>

definition c_u_shl_oor_contract ::
    \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_u_shl_oor_contract x n \<equiv>
    let pre  = \<langle>\<not> unat n < 32\<rangle>;
        post = \<lambda>_. \<langle>True\<rangle>;
        abort_post = \<lambda>ab. \<langle>ab = CustomAbort ShiftOutOfRange\<rangle>
     in make_function_contract_with_abort pre post abort_post\<close>
ucincl_auto c_u_shl_oor_contract

lemma c_u_shl_oor_spec:
  shows \<open>\<Gamma>; c_u_shl x n \<Turnstile>\<^sub>F c_u_shl_oor_contract x n\<close>
  apply (crush_boot f: c_u_shl_def contract: c_u_shl_oor_contract_def)
  apply (simp only: c_unsigned_shl_def)
  apply (crush_base simp add: c_shift_out_of_range_def c_abort_def)
  done

subsection \<open>Interesting semantic examples\<close>

text \<open>Mask low byte: result fits in a byte.\<close>

micro_c_translate \<open>
  unsigned int mask_low_byte(unsigned int x) {
    return x & 255;
  }
\<close>

definition c_mask_low_byte_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_mask_low_byte_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>unat r < 256\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mask_low_byte_contract

lemma c_mask_low_byte_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mask_low_byte x \<Turnstile>\<^sub>F c_mask_low_byte_contract x\<close>
by (crush_boot f: c_mask_low_byte_def contract: c_mask_low_byte_contract_def)
    (crush_base simp add: c_unsigned_and_def intro!: word_unat_and_lt)

text \<open>Set bit: the bit at position n is set in the result.\<close>

micro_c_translate \<open>
  unsigned int set_bit(unsigned int x, unsigned int n) {
    return x | (1U << n);
  }
\<close>

definition c_set_bit_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_set_bit_contract x n \<equiv>
    let pre  = \<langle>unat n < 32\<rangle>;
        post = \<lambda>r. \<langle>bit r (unat n)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_set_bit_contract

lemma c_set_bit_spec [crush_specs]:
  shows \<open>\<Gamma>; c_set_bit x n \<Turnstile>\<^sub>F c_set_bit_contract x n\<close>
  apply (crush_boot f: c_set_bit_def contract: c_set_bit_contract_def)
  apply (crush_base simp add: c_unsigned_or_def c_unsigned_shl_def bit_or_iff bit_push_bit_iff
    nth_w2p_same)
  done

text \<open>Clear bit: the bit at position n is cleared in the result.\<close>

micro_c_translate \<open>
  unsigned int clear_bit(unsigned int x, unsigned int n) {
    return x & ~(1U << n);
  }
\<close>

definition c_clear_bit_contract :: \<open>c_uint \<Rightarrow> c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_clear_bit_contract x n \<equiv>
    let pre  = \<langle>unat n < 32\<rangle>;
        post = \<lambda>r. \<langle>\<not> bit r (unat n)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_clear_bit_contract

lemma c_clear_bit_spec [crush_specs]:
  shows \<open>\<Gamma>; c_clear_bit x n \<Turnstile>\<^sub>F c_clear_bit_contract x n\<close>
  apply (crush_boot f: c_clear_bit_def contract: c_clear_bit_contract_def)
  apply (crush_base simp add: c_unsigned_and_def c_unsigned_not_def c_unsigned_shl_def
      bit_and_iff bit_not_iff bit_push_bit_iff nth_w2p_same)
  done

end

subsection \<open>Signed bitwise\<close>

context c_verification_ctx
begin

text \<open>Signed bitwise AND has no UB precondition.\<close>

micro_c_translate \<open>
  int s_and(int a, int b) {
    return a & b;
  }
\<close>

definition c_s_and_contract :: \<open>c_int \<Rightarrow> c_int \<Rightarrow> ('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_s_and_contract a b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = a AND b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_s_and_contract

lemma c_s_and_spec [crush_specs]:
  shows \<open>\<Gamma>; c_s_and a b \<Turnstile>\<^sub>F c_s_and_contract a b\<close>
by (crush_boot f: c_s_and_def contract: c_s_and_contract_def) (crush_base simp add: c_signed_and_def)

end

end
