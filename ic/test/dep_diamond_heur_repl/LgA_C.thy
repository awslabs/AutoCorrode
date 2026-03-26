theory LgA_C
  imports LgA_A LgA_B
begin

lemma "lga_b = lga_a1 + 1"
  by (simp add: lga_b_def)

end
