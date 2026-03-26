theory PF_Dep4
  imports PF_Base
begin

definition pf_d4 where "pf_d4 = pf_base + 4"

lemma pf_d4_val: "pf_d4 = 5"
  by (simp add: pf_d4_def pf_base_def)

end
