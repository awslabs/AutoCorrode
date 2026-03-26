theory MLC_D
  imports MLC_A MLC_C
begin

lemma "mlc_a + mlc_c = 4"
  unfolding mlc_a_def mlc_c_def mlc_b_def by eval

end
