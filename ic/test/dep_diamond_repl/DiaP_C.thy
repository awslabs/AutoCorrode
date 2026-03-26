theory DiaP_C
  imports DiaP_A DiaP_B
begin

lemma "diap_b = diap_a + 1"
  by (simp add: diap_b_def)

end
