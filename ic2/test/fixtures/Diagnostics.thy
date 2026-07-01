theory Diagnostics
  imports Main
begin

(* Fixture for the SessionTools diagnostic-tool e2e suite. It exercises every
   tool variant in one processed theory:
     - several entity keywords (definition / fun / datatype / lemma),
     - a structured (Isar) proof block AND an apply-style one,
     - a `sorry` with a known enclosing lemma,
     - a deliberate `simp` warning (no error, so the theory still consolidates).
   It is checked once by the suite; the tools then read its snapshot. *)

definition answer :: nat where
  "answer = 42"

datatype color = Red | Green | Blue

fun isRed :: "color \<Rightarrow> bool" where
  "isRed Red = True"
| "isRed _ = False"

(* Structured proof block (not apply-style). *)
lemma structured: "answer = 42"
proof -
  show "answer = 42" by (simp add: answer_def)
qed

(* Apply-style proof block. *)
lemma applied: "isRed Red = True"
  apply simp
  done

(* A lemma left unfinished with sorry — get_sorry_positions should find it and
   report `incomplete` as the enclosing proof. *)
lemma incomplete: "answer + 0 = answer"
  sorry

end
