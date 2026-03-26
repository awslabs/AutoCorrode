theory DR_D
  imports DR_B DR_C
begin

definition dr_d where "dr_d = dr_b + dr_c"

lemma "dr_d = 112"
  unfolding dr_d_def dr_b_def dr_c_def dr_e_def dr_a_def by eval

end
