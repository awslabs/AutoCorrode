theory DRT_C
  imports DRT_B
begin

lemma val_b_is_two: "val_b = 2"
  unfolding val_b_def val_a_def by eval

end
