theory C_Bitwise_Examples
  imports
    Simple_C_Functions
begin

section ‹C Bitwise Operation Verification›

text ‹
  This theory demonstrates verification of C bitwise and shift operations.
  Bitwise AND, OR, XOR, and NOT have no undefined behavior in C.
  Shifts abort when the shift amount is out of range, and signed shifts
  additionally detect negative-operand and overflow UB.
›

subsection ‹Unsigned bitwise smoke tests›

context c_uint_verification_ctx
begin

micro_c_translate ‹
  unsigned int u_and(unsigned int a, unsigned int b) {
    return a & b;
  }
›

definition c_u_and_bw_contract ::
    ‹c_uint ⇒ c_uint ⇒ ('s::{sepalg}, c_uint, 'b) function_contract› where
  [crush_contracts]: ‹c_u_and_bw_contract a b ≡
    let pre  = ⟨True⟩;
        post = λr. ⟨r = a AND b⟩
     in make_function_contract pre post›
ucincl_auto c_u_and_bw_contract

lemma c_u_and_bw_spec [crush_specs]:
  shows ‹Γ; c_u_and a b ⊨⇩F c_u_and_bw_contract a b›
by (crush_boot f: c_u_and_def contract: c_u_and_bw_contract_def)
  (crush_base simp add: c_unsigned_and_def)

micro_c_translate ‹
  unsigned int u_not(unsigned int x) {
    return ~x;
  }
›

definition c_u_not_contract :: ‹c_uint ⇒ ('s::{sepalg}, c_uint, 'b) function_contract› where
  [crush_contracts]: ‹c_u_not_contract x ≡
    let pre  = ⟨True⟩;
        post = λr. ⟨r = NOT x⟩
     in make_function_contract pre post›
ucincl_auto c_u_not_contract

lemma c_u_not_spec [crush_specs]:
  shows ‹Γ; c_u_not x ⊨⇩F c_u_not_contract x›
by (crush_boot f: c_u_not_def contract: c_u_not_contract_def)
  (crush_base simp add: c_unsigned_not_def)

micro_c_translate ‹
  unsigned int u_shl(unsigned int x, unsigned int n) {
    return x << n;
  }
›

definition c_u_shl_contract ::
    ‹c_uint ⇒ c_uint ⇒ ('s::{sepalg}, c_uint, 'b) function_contract› where
  [crush_contracts]: ‹c_u_shl_contract x n ≡
    let pre  = ⟨unat n < 32⟩;
        post = λr. ⟨r = push_bit (unat n) x⟩
     in make_function_contract pre post›
ucincl_auto c_u_shl_contract

lemma c_u_shl_spec [crush_specs]:
  shows ‹Γ; c_u_shl x n ⊨⇩F c_u_shl_contract x n›
by (crush_boot f: c_u_shl_def contract: c_u_shl_contract_def)
    (crush_base simp add: c_unsigned_shl_def)

subsection ‹Interesting semantic examples›

text ‹Mask low byte: result fits in a byte.›

micro_c_translate ‹
  unsigned int mask_low_byte(unsigned int x) {
    return x & 255;
  }
›

definition c_mask_low_byte_contract :: ‹c_uint ⇒ ('s::{sepalg}, c_uint, 'b) function_contract› where
  [crush_contracts]: ‹c_mask_low_byte_contract x ≡
    let pre  = ⟨True⟩;
        post = λr. ⟨unat r < 256⟩
     in make_function_contract pre post›
ucincl_auto c_mask_low_byte_contract

lemma c_mask_low_byte_spec [crush_specs]:
  shows ‹Γ; c_mask_low_byte x ⊨⇩F c_mask_low_byte_contract x›
by (crush_boot f: c_mask_low_byte_def contract: c_mask_low_byte_contract_def)
    (crush_base simp add: c_unsigned_and_def intro!: word_unat_and_lt)

text ‹Set bit: the bit at position n is set in the result.›

micro_c_translate ‹
  unsigned int set_bit(unsigned int x, unsigned int n) {
    return x | (1U << n);
  }
›

definition c_set_bit_contract :: ‹c_uint ⇒ c_uint ⇒ ('s::{sepalg}, c_uint, 'b) function_contract› where
  [crush_contracts]: ‹c_set_bit_contract x n ≡
    let pre  = ⟨unat n < 32⟩;
        post = λr. ⟨bit r (unat n)⟩
     in make_function_contract pre post›
ucincl_auto c_set_bit_contract

lemma c_set_bit_spec [crush_specs]:
  shows ‹Γ; c_set_bit x n ⊨⇩F c_set_bit_contract x n›
  apply (crush_boot f: c_set_bit_def contract: c_set_bit_contract_def)
  apply (crush_base simp add: c_unsigned_or_def c_unsigned_shl_def bit_or_iff bit_push_bit_iff
    nth_w2p_same)
  done

text ‹Clear bit: the bit at position n is cleared in the result.›

micro_c_translate ‹
  unsigned int clear_bit(unsigned int x, unsigned int n) {
    return x & ~(1U << n);
  }
›

definition c_clear_bit_contract :: ‹c_uint ⇒ c_uint ⇒ ('s::{sepalg}, c_uint, 'b) function_contract› where
  [crush_contracts]: ‹c_clear_bit_contract x n ≡
    let pre  = ⟨unat n < 32⟩;
        post = λr. ⟨¬ bit r (unat n)⟩
     in make_function_contract pre post›
ucincl_auto c_clear_bit_contract

lemma c_clear_bit_spec [crush_specs]:
  shows ‹Γ; c_clear_bit x n ⊨⇩F c_clear_bit_contract x n›
  apply (crush_boot f: c_clear_bit_def contract: c_clear_bit_contract_def)
  apply (crush_base simp add: c_unsigned_and_def c_unsigned_not_def c_unsigned_shl_def
      bit_and_iff bit_not_iff bit_push_bit_iff nth_w2p_same)
  done

end

subsection ‹Signed bitwise›

context c_verification_ctx
begin

text ‹Signed bitwise AND has no UB precondition.›

micro_c_translate ‹
  int s_and(int a, int b) {
    return a & b;
  }
›

definition c_s_and_contract :: ‹c_int ⇒ c_int ⇒ ('s::{sepalg}, c_int, 'b) function_contract› where
  [crush_contracts]: ‹c_s_and_contract a b ≡
    let pre  = ⟨True⟩;
        post = λr. ⟨r = a AND b⟩
     in make_function_contract pre post›
ucincl_auto c_s_and_contract

lemma c_s_and_spec [crush_specs]:
  shows ‹Γ; c_s_and a b ⊨⇩F c_s_and_contract a b›
by (crush_boot f: c_s_and_def contract: c_s_and_contract_def) (crush_base simp add: c_signed_and_def)

end

end
