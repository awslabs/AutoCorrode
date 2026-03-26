theory DCS_B
  imports DCS_A
begin

section\<open>Use constants from DCS_A\<close>

text\<open>This definition references constants defined in DCS_A
  using Isabelle symbol encoding (\<open>\<equiv>\<close>, \<open>\<Rightarrow>\<close>).\<close>

definition combined :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>combined x \<equiv> x + SHIFT_A + SHIFT_B + SHIFT_C\<close>

lemma combined_zero: \<open>combined 0 = 63\<close>
  unfolding combined_def SHIFT_A_def SHIFT_B_def SHIFT_C_def by eval

end
