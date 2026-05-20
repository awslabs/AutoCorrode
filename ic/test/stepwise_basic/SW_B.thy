theory SW_B
  imports SW_A
begin

definition sw_sum where "sw_sum = sw_val + 1"

lemma sw_sum_is_two: "sw_sum = 2"
  unfolding sw_sum_def sw_val_def by eval

end
