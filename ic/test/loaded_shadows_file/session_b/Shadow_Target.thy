theory Shadow_Target
  imports ShadowA.Shadow_Dep
begin

lemma shadow_check: "shadow_val = 1"
  unfolding shadow_val_def by eval

end
