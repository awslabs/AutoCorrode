/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

/** The jEdit-backed `Extended_Query_Operation.Host`: the editor-specific
  * capabilities a query operation needs (overlay mutation, flush, dispatch)
  * delegated to Isabelle/jEdit's live `Editor` (`JEdit_Editor`). Shared by the
  * I/Q server (IQServer) and the Explore dockable (IQExploreDockable) so both
  * drive the generic, session-based Extended_Query_Operation the same way. A
  * headless caller (ic2) would instead supply a Host backed by `session.update`. */
object IQ_Editor_Host extends Extended_Query_Operation.Host {
  def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    JEdit_Editor.insert_overlay(command, fn, args)
  def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    JEdit_Editor.remove_overlay(command, fn, args)
  def flush(): Unit = JEdit_Editor.flush()
  def require_dispatcher[A](body: => A): A = JEdit_Editor.require_dispatcher(body)
  def send_dispatcher(body: => Unit): Unit = JEdit_Editor.send_dispatcher(body)
}
