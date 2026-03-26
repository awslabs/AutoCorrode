theory Check_Error
  imports Main
begin

definition a_val where "a_val = (42::nat)"
lemma bad: "(0::nat) = 1" by (rule TrueI)

end
