theory Check_All
  imports Main
begin

definition a_val where "a_val = (42::nat)"

lemma a_pos: "a_val > 0" by (simp add: a_val_def)

end
