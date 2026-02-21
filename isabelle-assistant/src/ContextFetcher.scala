/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import java.util.concurrent.{CountDownLatch, TimeUnit}
import javax.swing.SwingUtilities

/** Fetches definitions of constants/types referenced in code.
  * Uses PIDE markup to extract entity references, then queries Isabelle for definitions.
  *
  * IMPORTANT: getContext must NOT be called from the GUI thread — it blocks waiting
  * for GUI_Thread.later work. All callers run on Isabelle_Thread or background threads.
  */
object ContextFetcher {

  /** Get context for code at cursor by extracting referenced entities from PIDE markup.
    * Must be called from a background thread (not the GUI thread).
    * Returns None safely if called from EDT to avoid deadlock. */
  def getContext(view: View, timeoutMs: Long = 3000): Option[String] = {
    if (SwingUtilities.isEventDispatchThread) {
      Output.warning("[Assistant] ContextFetcher.getContext called from GUI thread — returning None to avoid deadlock")
      return None
    }

    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    
    val latch = new CountDownLatch(1)
    @volatile var entities: List[(String, String)] = Nil
    @volatile var commandOpt: Option[Command] = None
    
    GUI_Thread.later {
      entities = extractEntities(buffer, offset)
      commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
      latch.countDown()
    }
    
    latch.await(AssistantConstants.CONTEXT_FETCH_TIMEOUT, TimeUnit.MILLISECONDS)
    
    commandOpt match {
      case Some(command) if entities.nonEmpty =>
        val interesting = entities.filter { case (kind, n) =>
          (kind == Markup.CONSTANT || kind == Markup.TYPE_NAME) && !isMetaLevel(n)
        }.map(_._2).distinct

        if (interesting.isEmpty || !IQAvailable.isAvailable) None
        else {
          val resultLatch = new CountDownLatch(1)
          @volatile var result: Option[String] = None

          GUI_Thread.later {
            fetchDefinitions(view, command, interesting, timeoutMs, { response =>
              response match {
                case Right(output) if output.trim.nonEmpty &&
                    !output.contains("No additional context") &&
                    !output.startsWith("Error:") =>
                  result = Some(output.trim)
                case _ =>
              }
              resultLatch.countDown()
            })
          }

          resultLatch.await(timeoutMs + 1000, TimeUnit.MILLISECONDS)
          result
        }
      case _ => None
    }
  }

  /** Extract entity references from PIDE markup at offset */
  def extractEntities(buffer: JEditBuffer, offset: Int): List[(String, String)] = {
    Document_Model.get_model(buffer).map { model =>
      val snapshot = Document_Model.snapshot(model)
      
      val commandRange = snapshot.node.command_iterator(offset)
        .collectFirst { case (cmd, cmdOffset) if offset >= cmdOffset && offset < cmdOffset + cmd.length =>
          Text.Range(cmdOffset, cmdOffset + cmd.length)
        }.getOrElse(Text.Range(offset, offset + 1))
      
      val entities = snapshot.cumulate(commandRange, List.empty[(String, String)],
        Markup.Elements(Markup.ENTITY), _ => {
          case (acc, Text.Info(_, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
            val kind = Markup.Kind.unapply(props).getOrElse("")
            val name = Markup.Name.unapply(props).getOrElse("")
            if (kind.nonEmpty && name.nonEmpty) Some(acc :+ (kind, name))
            else None
          case _ => None
        })
      
      entities.flatMap(_._2).distinct
    }.getOrElse(Nil)
  }
  
  /** Fetch definitions for a specific list of constant names via PIDE/I/Q.
   *  Uses the same isar_explore mechanism as getContext but for arbitrary names.
   *  Must NOT be called from the GUI thread. */
  def fetchDefinitionsForNames(
    view: View, command: Command, names: List[String], timeoutMs: Long = 3000
  ): Option[String] = {
    if (javax.swing.SwingUtilities.isEventDispatchThread) {
      Output.warning("[Assistant] fetchDefinitionsForNames called from GUI thread — returning None")
      return None
    }
    if (names.isEmpty || !IQAvailable.isAvailable) return None

    val interesting = names.filter(n => !isMetaLevel(n)).distinct
    if (interesting.isEmpty) return None

    val resultLatch = new CountDownLatch(1)
    @volatile var result: Option[String] = None

    GUI_Thread.later {
      fetchDefinitions(view, command, interesting, timeoutMs, { response =>
        response match {
          case Right(output) if output.trim.nonEmpty &&
              !output.contains("No additional context") &&
              !output.startsWith("Error:") =>
            result = Some(output.trim)
          case _ =>
        }
        resultLatch.countDown()
      })
    }

    resultLatch.await(timeoutMs + 1000, TimeUnit.MILLISECONDS)
    result
  }

  private def isMetaLevel(name: String): Boolean = {
    name.startsWith("Pure.") || name == "Trueprop" || 
    name == "Pure.imp" || name == "Pure.eq" || name == "Pure.all" ||
    name == "fun" || name == "itself"
  }

  private def fetchDefinitions(
    view: View,
    command: Command,
    names: List[String],
    timeoutMs: Long,
    callback: Either[String, String] => Unit
  ): Unit = {
    val outputLock = new Object()
    val output = new StringBuilder
    @volatile var operation: Option[Extended_Query_Operation] = None
    val lifecycle = new IQOperationLifecycle[Either[String, String]](
      onComplete = callback,
      deactivate = () => operation.foreach(_.deactivate())
    )
    val op = new Extended_Query_Operation(
      PIDE.editor, view, "isar_explore",
      status => {
        if (status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed) {
          lifecycle.complete(Right(output.synchronized { output.toString }))
        }
      },
      (snapshot, cmdResults, results) => {
        outputLock.synchronized {
          if (!lifecycle.isCompleted) {
            val text = results.map(XML.content(_)).mkString("\n")
            if (text.nonEmpty) output.synchronized {
              val _ = output.append(text).append("\n")
            }
          }
        }
      }
    )
    operation = Some(op)

    val _ = lifecycle.forkTimeout(name = "context-fetch-timeout", timeoutMs = timeoutMs) {
      Right(output.synchronized { output.toString })
    }

    try {
      op.activate()
      op.apply_query_at_command(command, List("get_defs " + names.mkString(" ")))
    } catch {
      case ex: Exception =>
        lifecycle.complete(Left(s"context fetch setup failed: ${ex.getMessage}"))
    }
  }
}
