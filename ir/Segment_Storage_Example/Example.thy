theory Example
imports Main
begin

declare [[ML_write_global = true]]
ML_file \<open>segment_storage.ML\<close>
declare [[ML_write_global = false]]

lemma example_one: "True" by simp

lemma example_two: "1 + 1 = (2::nat)" by simp

definition my_const :: nat where "my_const = 42"

lemma example_three: "my_const = 42" unfolding my_const_def by simp

end
