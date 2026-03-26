theory SDC_C
  imports SDC_B
begin

lemma sdc_sum_is_30: "sdc_sum = 30"
  unfolding sdc_sum_def sdc_x_def sdc_y_def by eval

end
