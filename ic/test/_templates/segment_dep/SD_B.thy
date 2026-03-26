theory SD_B
  imports SD_A
begin

definition sd_sum where "sd_sum = sd_val + 1"

lemma sd_sum_is_two: "sd_sum = 2"
  unfolding sd_sum_def sd_val_def by eval

end
