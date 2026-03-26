theory SD2_B
  imports SD2_A
begin

definition sd2_sum where "sd2_sum = sd2_val + 1"

lemma sd2_sum_is_two: "sd2_sum = 2"
  unfolding sd2_sum_def sd2_val_def by eval

end
