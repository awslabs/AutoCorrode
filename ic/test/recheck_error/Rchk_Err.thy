theory Rchk_Err
  imports Main
begin

definition rchk_a where "rchk_a = (1::nat)"

definition rchk_b where "rchk_b = (2::nat)"

definition rchk_c where "rchk_c = (3::nat)"

definition rchk_d where "rchk_d = (4::nat)"

definition rchk_e where "rchk_e = (5::nat)"

lemma bad: "(0::nat) = 1" by (rule TrueI)

end
