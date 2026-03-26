theory Sym_Test
  imports Main
begin

section\<open>Isabelle symbol encoding test\<close>

text\<open>
  This theory uses \<open>...\<close> brackets and other Isabelle symbols
  to verify that recheck does not falsely detect changes due to
  symbol encoding differences between disk (\<open>\<close>) and
  Ir.text() output (Unicode \<open>\<rightarrow>\<close> characters).
\<close>

definition sym_val :: "nat \<Rightarrow> nat" where
  "sym_val x \<equiv> x + 1"

lemma sym_test: "sym_val 0 = 1"
  unfolding sym_val_def by eval

end
