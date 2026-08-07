theory SpinImport
  imports SpinDep
begin

method_setup spin =
  ‹Scan.lift Parse.number >> (fn n => fn _ => SIMPLE_METHOD (fn st =>
     if Thm.nprems_of st = 0 then Seq.single st
     else
       let
         val secs = Real.fromInt (the (Int.fromString n))
         val deadline = Time.+ (Time.now (), Time.fromReal secs)
         fun loop () =
           (ignore (Unsynchronized.ref 0);
            if Time.< (Time.now (), deadline) then loop () else ())
       in loop (); Seq.single st end))›
  "spin N seconds"

(* uses a fact FROM the dependency — only type-checks if SpinDep evaluated *)
lemma uses_dep: "(n::nat) + 0 = n + spin_dep_const - spin_dep_const"
  by (spin 30; simp add: spin_dep_const_def)

end
