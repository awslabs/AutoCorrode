/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

/** The jEdit-backed `Extended_Query_Operation.Host`: the editor-specific
  * capabilities a query operation needs (overlay mutation, flush, dispatch)
  * delegated to Isabelle/jEdit's live `Editor` (`PIDE.editor`). Shared by the
  * I/Q server (IQServer) and the Explore dockable (IQExploreDockable) so both
  * drive the generic, session-based Extended_Query_Operation the same way. A
  * headless caller (ic2) would instead supply a Host backed by `session.update`. */
object IQ_Editor_Host extends Extended_Query_Operation.Host {
  def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    PIDE.editor.insert_overlay(command, fn, args)
  def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    PIDE.editor.remove_overlay(command, fn, args)
  def flush(): Unit = PIDE.editor.flush()
  def require_dispatcher[A](body: => A): A = PIDE.editor.require_dispatcher(body)
  def send_dispatcher(body: => Unit): Unit = PIDE.editor.send_dispatcher(body)
}
