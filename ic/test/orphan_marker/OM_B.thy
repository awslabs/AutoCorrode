theory OM_B
  imports OM_A
begin

lemma om_a_is_one: "om_a = 1"
  unfolding om_a_def by (rule refl)

end
