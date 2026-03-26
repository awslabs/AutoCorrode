theory DR_B
  imports DR_A
begin

lemma val_a_is_one: "val_a = 1"
  unfolding val_a_def by (rule refl)

end
