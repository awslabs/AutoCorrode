theory Inner_Test
  imports Main
begin

definition base_val where "base_val = (1::nat)"

locale Inner =
  fixes x :: nat
  assumes pos: "x > 0"
begin

lemma x_pos: "x > 0" by (rule pos)

end

lemma base_val_eq: "base_val = 1" by (simp add: base_val_def)

end
