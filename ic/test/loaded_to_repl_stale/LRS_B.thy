theory LRS_B
  imports LRS_A
begin

definition lrs_b where "lrs_b = lrs_a + 1"

lemma "lrs_b = 2"
  unfolding lrs_b_def lrs_a_def by eval

end
