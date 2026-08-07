theory SpinTactic
  imports Main
begin

(* test *)

(* Fixture for the long-running-command display and forked-proof cancellation:
   two `by (spin N)` proofs — spin1 15s, spin2 30s (unequal so a partial check).

   `spin N` busy-loops for N seconds, allocating each iteration so it hits
   Poly/ML safepoints (no interrupt manipulation), then behaves as `all_tac`.
   The Thm.nprems_of guard makes it a no-op when Isabelle invokes the method
   on the dummy goal used for method-text elaboration — otherwise that pass
   would spin too and double the observed cost.

   A terminal `by` runs as a FORKED background proof (future_terminal_proof,
   Pure/Isar/proof.ML), which PIDE's own Command_Timings.running cannot
   represent (the fork and its ~1ms toplevel transition collide on one
   source-offset key, and the transition's `elapsed` clears the shared slot
   — jEdit's Timing dockable has the same blind spot). ic2's Timing_Tracker
   sidesteps that by COUNTING the raw command_timing stream per exec id
   (running:+1 / elapsed:-1), so a spinning forked `by` is correctly shown
   as long-running while a `text`/`class` presentation fork — which never
   emits command_timing — is not. This fixture therefore exercises the
   forked-proof path specifically. *)

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
  "spin N seconds when a real subgoal is present, else all_tac"

lemma spin1: "(n::nat) + 0 = n"
  by (spin 15; simp)

lemma spin2: "(n::nat) * 1 = n"
  by (spin 30; simp)

end
