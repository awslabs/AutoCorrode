theory Seg_Plain
  imports Main
begin

text \<open>This is a long text block that exceeds eighty characters and would be truncated without full_spans mode enabled.\<close>

definition sp_a :: "nat" where
  "sp_a = (1::nat)"
definition sp_b where "sp_b = (2::nat)"
definition sp_c where "sp_c = (3::nat)"

end
