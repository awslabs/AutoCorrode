theory SMT_Test
  imports Main
begin

lemma "(x::int) + y = y + x"
  by (smt (verit))

end
