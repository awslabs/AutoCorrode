theory PF_Dep3
  imports PF_Base
begin

definition pf_d3 where "pf_d3 = pf_base + 3"

lemma pf_d3_val: "pf_d3 = 4"
  by (simp add: pf_d3_def pf_base_def)

end
