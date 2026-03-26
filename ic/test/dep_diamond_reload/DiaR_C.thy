theory DiaR_C
  imports DiaR_A DiaR_B
begin

lemma "diar_b = diar_a + 1"
  by (simp add: diar_b_def)

end
