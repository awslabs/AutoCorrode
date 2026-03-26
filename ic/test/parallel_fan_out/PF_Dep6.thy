theory PF_Dep6
  imports PF_Base
begin

definition pf_d6 where "pf_d6 = pf_base + 6"

lemma pf_d6_val: "pf_d6 = 7"
  by (simp add: pf_d6_def pf_base_def)

end
