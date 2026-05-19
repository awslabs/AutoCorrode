theory PF_Dep5
  imports PF_Base
begin

definition pf_d5 where "pf_d5 = pf_base + 5"

lemma pf_d5_val: "pf_d5 = 6"
  by (simp add: pf_d5_def pf_base_def)

end
