theory PF_Dep2
  imports PF_Base
begin

definition pf_d2 where "pf_d2 = pf_base + 2"

lemma pf_d2_val: "pf_d2 = 3"
  by (simp add: pf_d2_def pf_base_def)

end
