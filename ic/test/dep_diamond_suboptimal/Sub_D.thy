theory Sub_D
  imports Sub_B Sub_C
begin

lemma "b1 + c1 = 13"
  unfolding b1_def c1_def a1_def by eval

end
