theory DRC_D
  imports DRC_B DRC_C
begin

definition drc_d where "drc_d = drc_b + drc_c"

lemma "drc_d = 103"
  unfolding drc_d_def drc_b_def drc_c_def drc_a_def by eval

end
