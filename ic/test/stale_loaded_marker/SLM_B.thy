theory SLM_B
  imports SLM_A
begin

definition slm_b where "slm_b = slm_a + 1"

lemma "slm_b = 2"
  unfolding slm_b_def slm_a_def by eval

end
