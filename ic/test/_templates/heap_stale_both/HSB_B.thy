theory HSB_B
  imports HSB_A
begin

definition hsb_sum where "hsb_sum = hsb_val + 1"

lemma hsb_sum_is_two: "hsb_sum = 2"
  unfolding hsb_sum_def hsb_val_def by eval

end
