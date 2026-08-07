theory Slow
  imports Main
begin

(* A theory whose processing time is dominated by a genuine, interruptible
   delay, so the cancel / disconnect e2e tests have a wide, deterministic
   window to act in. The trivial lemmas below consolidate in well under a
   second on a warm HOL heap; the ML sleep does not — and an Isabelle
   interrupt (from progress.stop()) unblocks OS.Process.sleep, so a working
   cancel returns promptly while a broken one waits out the full delay. *)

lemma slow1: "(n::nat) + 0 = n"
  by simp

(* The dominating delay. 8s is long enough to reliably cancel against, short
   enough that a regressed cancel path fails the test in bounded time. *)
ML ‹OS.Process.sleep (Time.fromReal 8.0)›

lemma slow2: "(n::nat) * 1 = n"
  by simp

end
