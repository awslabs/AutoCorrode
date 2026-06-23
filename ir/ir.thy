(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*
  I/R server bootstrap.

  Loading this theory defines the `Ir`, `Tcp_Handler`, and `ML_Repl`
  structures and registers the `IR_Repl.start` / `IR_Repl.stop` PIDE
  protocol commands.  Once loaded into a live Isabelle/jEdit session, the
  I/Q plugin can start the I/R REPL daemon via `protocol_command
  "IR_Repl.start"`.

  NOTE: this theory and the three ML files it loads are symlinked into the
  `iq/` session directory (`iq/ir.thy`, `iq/ir.ML`, `iq/ml_repl.ML`,
  `iq/tcp_handler.ML`).  The symlinks exist because I/P only synchronizes
  the directories listed in a session's ROOT when building AutoCorrode
  remotely; keeping copies inside `iq/` ensures the I/R sources are
  available without listing `../ir` as an extra session directory.  The
  `iq` session and `iq.thy` import the `iq/`-local copies.

  The `ML_write_global` flag makes the structures available as top-level
  globals (rather than only inside the theory's ML environment), which is
  required for the protocol commands and the REPL evaluation context.
*)

theory ir
  imports Main
begin

declare [[ML_write_global = true]]
ML_file\<open>ir.ML\<close>
ML_file\<open>tcp_handler.ML\<close>
ML_file\<open>ml_repl.ML\<close>
declare [[ML_write_global = false]]

end
