theory SmA_C
  imports SmA_A SmA_B
begin

lemma "sma_b1 = sma_a + 1"
  by (simp add: sma_b1_def)

end
