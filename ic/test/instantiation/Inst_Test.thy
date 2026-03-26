theory Inst_Test
  imports Main
begin

datatype primary = Red | Green | Blue

fun primary_to_nat :: "primary \<Rightarrow> nat" where
  "primary_to_nat Red = 0"
| "primary_to_nat Green = 1"
| "primary_to_nat Blue = 2"

instantiation primary :: linorder
begin

definition less_eq_primary :: "primary \<Rightarrow> primary \<Rightarrow> bool" where
  "less_eq_primary c1 c2 = (primary_to_nat c1 \<le> primary_to_nat c2)"

definition less_primary :: "primary \<Rightarrow> primary \<Rightarrow> bool" where
  "less_primary c1 c2 = (primary_to_nat c1 < primary_to_nat c2)"

instance proof (standard)
  fix x y z :: primary
  show "x \<le> x" by (simp add: less_eq_primary_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (simp add: less_eq_primary_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto simp: less_eq_primary_def)
  show "x \<le> y \<or> y \<le> x" by (simp add: less_eq_primary_def linear)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (auto simp: less_primary_def less_eq_primary_def)
qed

end

lemma "Red \<le> Blue"
  by (simp add: less_eq_primary_def)

end
