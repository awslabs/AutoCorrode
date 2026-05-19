theory PF_Dep1
  imports PF_Base
begin

definition pf_d1 where "pf_d1 = pf_base + 1"

lemma pf_d1_val: "pf_d1 = 2"
  by (simp add: pf_d1_def pf_base_def)

end
