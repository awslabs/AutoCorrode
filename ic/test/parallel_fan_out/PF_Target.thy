theory PF_Target
  imports PF_Dep1 PF_Dep2 PF_Dep3 PF_Dep4 PF_Dep5 PF_Dep6
begin

definition pf_sum where
  "pf_sum = pf_d1 + pf_d2 + pf_d3 + pf_d4 + pf_d5 + pf_d6"

lemma pf_sum_val: "pf_sum = 27"
  by (simp add: pf_sum_def pf_d1_def pf_d2_def pf_d3_def
                pf_d4_def pf_d5_def pf_d6_def pf_base_def)

end
