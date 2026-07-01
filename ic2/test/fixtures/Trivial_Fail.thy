theory Trivial_Fail
  imports Main
begin

(* Deliberately broken: the goal is unprovable. *)
lemma broken: "False" by simp

end
