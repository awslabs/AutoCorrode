theory DIS_D
  imports DIS_B DIS_C
begin

definition dis_d where "dis_d = dis_b + dis_c"

lemma "dis_d = 123"
  unfolding dis_d_def dis_b_def dis_c_def dis_a_def dis_x_def by eval

end
