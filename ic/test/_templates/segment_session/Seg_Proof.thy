(*<*)
theory Seg_Proof
  imports Main
begin
(*>*)

definition proof_val where "proof_val = (1::nat)"

lemma proof_lemma: "proof_val = 1"
  by (simp add: proof_val_def)

definition proof_after where "proof_after = (2::nat)"

end
