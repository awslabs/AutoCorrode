theory MLC_A
  imports Main
begin

ML \<open>val mlc_counter = Unsynchronized.ref 0\<close>

definition mlc_a where "mlc_a = (1::nat)"

end
