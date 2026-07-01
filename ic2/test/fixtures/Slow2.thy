theory Slow2
  imports Main
begin

(* A second slow theory, identical in spirit to Slow.thy, dedicated to the
   `check` timeout-abort test. Kept separate so the timeout test always runs
   against a not-yet-consolidated node — a fresh check that genuinely re-runs
   the ML sleep — rather than depending on whether use_theories re-processes
   an already-checked theory. The 8s ML sleep dominates processing time and is
   interruptible: progress.stop() (fired when the timeout budget expires)
   unblocks OS.Process.sleep, so a working timeout returns promptly. *)

lemma slow2_1: "(n::nat) + 0 = n"
  by simp

ML ‹OS.Process.sleep (Time.fromReal 8.0)›

lemma slow2_2: "(n::nat) * 1 = n"
  by simp

end
