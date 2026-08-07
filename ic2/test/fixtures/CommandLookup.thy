theory CommandLookup
  imports Main
begin

    definition foo :: nat where "foo = 0"

definition bar :: nat where "bar = 1"
definition baz :: nat where "baz = 2"

definition p :: nat where "p = 3" definition q :: nat where "q = 4"

lemma apply_style: "P \<longrightarrow> P"
  apply (rule impI)
  apply assumption
  done

lemma structured: "(n::nat) * 1 = n"
  proof -
    show ?thesis by simp
  qed

end
