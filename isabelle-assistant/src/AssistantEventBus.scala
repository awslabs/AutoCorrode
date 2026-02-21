/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle.Output
import java.util.concurrent.CopyOnWriteArrayList

/** Events representing UI updates that need to be broadcast to all instances of
  * the Assistant UI panel (if any exist).
  */
sealed trait AssistantEvent

object AssistantEvent {
  case class StatusUpdate(status: AssistantStatus) extends AssistantEvent
  case class BadgeUpdate(badge: VerificationBadge.BadgeType)
      extends AssistantEvent
  case class ChatResponse(
      text: String,
      insertCode: Option[(String, () => Unit)] = None
  ) extends AssistantEvent
  case class ShowConversation(history: List[ChatAction.Message])
      extends AssistantEvent
  case class IQStatusRefresh() extends AssistantEvent
  case class ModelLabelRefresh() extends AssistantEvent
}

/** Global event bus for broadcasting UI state changes to active Assistant
  * panels.
  *
  * This replaces the brittle `Option[AssistantDockable]` singleton pattern,
  * allowing the backend to push state updates without caring whether zero, one,
  * or multiple Assistant UI frames are currently open in the IDE.
  */
object AssistantEventBus {
  // CopyOnWriteArrayList provides thread-safe iteration for listeners
  // and cheap reads, which is optimal for a UI event bus where subscriptions
  // change rarely (only when dockables open/close) but publishes happen often.
  private val listeners = new CopyOnWriteArrayList[AssistantEvent => Unit]()

  /** Register a callback for UI events. \@param listener The callback function.
    */
  def subscribe(listener: AssistantEvent => Unit): Unit = {
    val _ = listeners.add(listener)
  }

  /** Unregister a previously registered callback. \@param listener The specific
    * callback function instance to remove.
    */
  def unsubscribe(listener: AssistantEvent => Unit): Unit = {
    val removed = listeners.remove(listener)
    if (!removed) Output.warning("[Assistant] EventBus unsubscribe: listener not found")
  }

  /** Broadcast an event to all registered UI views.
    */
  def publish(event: AssistantEvent): Unit = {
    val iter = listeners.iterator()
    while (iter.hasNext) {
      val listener = iter.next()
      try {
        listener(event)
      } catch {
        case ex: Throwable =>
          ErrorHandler.logSilentError("AssistantEventBus", ex)
      }
    }
  }
}
