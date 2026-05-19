theory SHT_Target
  imports SHT_Dep
begin

definition sht_sum where "sht_sum = sht_val + 1"

lemma sht_sum_val: "sht_sum = 2"
  unfolding sht_sum_def sht_val_def by eval

end
