theory IM_Target
  imports IM_Dep
begin

definition im_sum where "im_sum = im_a + im_e"

lemma im_sum_val: "im_sum = 6"
  unfolding im_sum_def im_a_def im_e_def by eval

end
