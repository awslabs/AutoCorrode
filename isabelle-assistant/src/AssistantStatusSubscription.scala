/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * Managed lifecycle wrapper for session outlet subscriptions.
 * Provides idempotent start/stop so UI reopen/close cycles do not leak consumers.
 */
final class AssistantStatusSubscription[A] private[assistant] (
  name: String,
  onEvent: A => Unit,
  register: Session.Consumer[A] => Unit,
  unregister: Session.Consumer[A] => Unit
) {
  private[this] val lock = new Object()
  private[this] val consumer = Session.Consumer[A](name)(onEvent)
  @volatile private[this] var started = false

  def start(): Unit = lock.synchronized {
    if (!started) {
      register(consumer)
      started = true
    }
  }

  def stop(): Unit = lock.synchronized {
    if (started) {
      unregister(consumer)
      started = false
    }
  }

  private[assistant] def isStarted: Boolean = started
}

object AssistantStatusSubscription {
  def create(
    session: Session,
    name: String,
    onEvent: Session.Commands_Changed => Unit
  ): AssistantStatusSubscription[Session.Commands_Changed] =
    new AssistantStatusSubscription[Session.Commands_Changed](
      name,
      onEvent,
      session.commands_changed += _,
      session.commands_changed -= _
    )

  private[assistant] def createForTest[A](
    name: String,
    onEvent: A => Unit,
    register: Session.Consumer[A] => Unit,
    unregister: Session.Consumer[A] => Unit
  ): AssistantStatusSubscription[A] =
    new AssistantStatusSubscription[A](name, onEvent, register, unregister)
}
