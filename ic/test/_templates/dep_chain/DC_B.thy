theory DC_B
  imports DC_A
begin

definition b_val where "b_val = a_val + 1"

lemma b_val_is_two: "b_val = 2"
  unfolding b_val_def a_val_def by eval

end
