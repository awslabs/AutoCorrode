theory UserA
  imports SameNameA.Common
begin

lemma "common_a = 1"
  unfolding common_a_def by eval

end
