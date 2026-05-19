theory SDR_B
  imports SDR_A
begin

definition sdr_sum where "sdr_sum = sdr_val + 1"

lemma sdr_sum_val: "sdr_sum = 2"
  unfolding sdr_sum_def sdr_val_def by eval

end
