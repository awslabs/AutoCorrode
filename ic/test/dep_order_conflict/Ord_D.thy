theory Ord_D
  imports Ord_B Ord_C
begin

lemma check_all: "base_val + derived_val + other_val = 14"
  unfolding base_val_def derived_val_def other_val_def by eval

end
