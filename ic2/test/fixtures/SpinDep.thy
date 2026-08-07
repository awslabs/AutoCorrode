theory SpinDep
  imports Main
begin

lemma spin_dep_lemma: "(m::nat) + 0 = m"
  by simp

definition spin_dep_const :: nat where "spin_dep_const = 42"

end
