/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Bounded registry of insert actions referenced from chat hyperlinks.
  *
  * Backed by a single synchronized LinkedHashMap with `removeEldestEntry`,
  * so the map and its insertion order cannot drift apart — which was a
  * real risk with the previous two-collection approach (ConcurrentHashMap
  * plus ConcurrentLinkedDeque). Capacity is configured by
  * AssistantConstants.MAX_INSERT_ACTIONS.
  */
object AssistantInsertRegistry {
  private val maxEntries = AssistantConstants.MAX_INSERT_ACTIONS

  private val lock = new Object()

  private val store: java.util.LinkedHashMap[String, () => Unit] =
    new java.util.LinkedHashMap[String, () => Unit](maxEntries + 1, 0.75f, false) {
      override def removeEldestEntry(
          eldest: java.util.Map.Entry[String, () => Unit]
      ): Boolean = this.size() > maxEntries
    }

  /** Register an insert action and return its id. Callers embed the id in a
    * hyperlink; `lookup` retrieves the action when the link is clicked.
    */
  def register(action: () => Unit): String = lock.synchronized {
    val id = java.util.UUID.randomUUID().toString.take(8)
    val _ = store.put(id, action)
    id
  }

  /** Look up a previously-registered action. Returns None if the id has been
    * evicted or never existed.
    */
  def lookup(id: String): Option[() => Unit] = lock.synchronized {
    Option(store.get(id))
  }

  /** Drop every registered action (e.g. on plugin teardown or chat clear). */
  def clear(): Unit = lock.synchronized { store.clear() }

  /** Size snapshot — primarily for diagnostics / tests. */
  private[assistant] def size: Int = lock.synchronized { store.size }
}
