theory PTH_A
  imports Main
begin

definition pth_a :: nat where "pth_a = 1"
definition pth_a2 :: nat where "pth_a2 = pth_a + 1"
definition pth_a3 :: nat where "pth_a3 = pth_a2 + 1"
definition pth_a4 :: nat where "pth_a4 = pth_a3 + 1"

lemma "pth_a4 = 4" unfolding pth_a4_def pth_a3_def pth_a2_def pth_a_def by simp

end
