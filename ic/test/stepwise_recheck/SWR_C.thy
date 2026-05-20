theory SWR_C
  imports SWR_B
begin

lemma swr_sum_is_two: "swr_sum = 2"
  unfolding swr_sum_def swr_val_def by eval

end
