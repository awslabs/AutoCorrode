/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import scala.util.control.NonFatal
import java.io.{File, PrintWriter}
import scala.io.Source
import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonGenerator, JsonToken}

/**
 * Thread-safe persistent memory store for LLM-managed knowledge base.
 * 
 * Memories are organized hierarchically under topics (e.g., "user", "isabelle")
 * and persist across sessions in a JSON file in the jEdit settings directory.
 * Unlike TaskList (session-scoped), memories survive chat clears and restarts.
 */
object MemoryStore {
  
  /** Memory data structure */
  case class Memory(
    id: Int,
    topic: String,
    title: String,
    body: String,
    created: LocalDateTime
  )
  
  // Thread-safe state
  private val lock = new Object()
  @volatile private var memories: Map[String, List[Memory]] = Map.empty
  @volatile private var nextId: Int = 1
  @volatile private var loaded: Boolean = false
  private val timeFormatter = DateTimeFormatter.ofPattern("yyyy-MM-dd'T'HH:mm:ss")
  
  // Validation limits
  private val MAX_TOPICS = 100
  private val MAX_MEMORIES_PER_TOPIC = 200
  private val MAX_TITLE_LENGTH = 200
  private val MAX_BODY_LENGTH = 2000
  private val TOPIC_NAME_PATTERN = "^[a-z0-9_]+$".r
  
  /** Toggle for the /tmp storage fallback. Set to "true" in test beforeEach
    * hooks — or anywhere the test harness needs a writable store without
    * jEdit wired up. Out of test mode, a null settings directory is treated
    * as a hard error rather than silently redirecting persistent memories
    * to a world-readable temp path. */
  private val TEST_MODE_PROPERTY = "assistant.storage.test_mode"
  @volatile private var warnedAboutTestFallback: Boolean = false

  private def isTestMode: Boolean =
    java.lang.Boolean.parseBoolean(System.getProperty(TEST_MODE_PROPERTY, "false"))

  private def tmpFallbackFile(reason: String): File = {
    // Warn once per JVM so operators notice this path — but not so loudly
    // that the test suite drowns in log lines.
    if (!warnedAboutTestFallback) {
      warnedAboutTestFallback = true
      safeLog(
        s"[MemoryStore] Using test-mode /tmp fallback for memory storage ($reason). " +
        s"Set -D$TEST_MODE_PROPERTY=true only in tests; production writes must go to the jEdit settings directory."
      )
    }
    new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
  }

  /**
   * Get the storage file path in jEdit settings directory.
   *
   * Only falls back to the temp directory when `assistant.storage.test_mode`
   * is explicitly set — a null settings directory in production is a real
   * configuration problem and should not be masked by silently routing
   * writes to `/tmp`.
   */
  private def storageFile: File = {
    try {
      val settingsDir = org.gjt.sp.jedit.jEdit.getSettingsDirectory
      if (settingsDir != null) {
        new File(settingsDir, "assistant-memories.json")
      } else if (isTestMode) {
        tmpFallbackFile("jEdit.getSettingsDirectory returned null")
      } else {
        throw new IllegalStateException(
          s"MemoryStore: jEdit settings directory is null. This is a configuration error. " +
          s"If this is a test, set -D$TEST_MODE_PROPERTY=true."
        )
      }
    } catch {
      case _: IllegalStateException if !isTestMode =>
        // Re-raise so the caller (ensureLoaded / save) can decide whether
        // to swallow into a safeLog or propagate. Keeping the type narrow.
        throw new IllegalStateException(
          s"MemoryStore: jEdit settings directory not available. " +
          s"Set -D$TEST_MODE_PROPERTY=true for non-jEdit test contexts."
        )
      case NonFatal(_) if isTestMode =>
        // jEdit classes not available (typical unit-test environment).
        tmpFallbackFile("jEdit classes not on classpath")
      case NonFatal(e) =>
        throw new IllegalStateException(
          s"MemoryStore: could not resolve storage path: ${e.getMessage}. " +
          s"Set -D$TEST_MODE_PROPERTY=true for non-jEdit test contexts.",
          e
        )
    }
  }
  
  /**
   * Lazy-load memories from disk on first access. Also sweeps any leftover
   * `.tmp` siblings so crashes during `save()` do not leave debris forever.
   */
  private def ensureLoaded(): Unit = lock.synchronized {
    if (!loaded) {
      cleanupStaleTempFiles()
      load()
      loaded = true
    }
  }

  /** Per-JVM suffix used to name atomic-save temporaries. Two jEdit
    * processes sharing a settings directory must not clobber each
    * other's in-progress writes; the UUID makes every tmp path unique
    * to this JVM instance so the cleanup sweep can age-gate unrelated
    * tmps without deleting a live one. */
  private val tmpSuffix: String = java.util.UUID.randomUUID().toString.take(8)

  /** Age (milliseconds) after which an unrelated `.tmp` sibling is
    * assumed to be abandoned. One hour is far longer than any normal
    * save takes but short enough that debris is not permanent. */
  private val staleTmpAgeMs: Long = 60L * 60L * 1000L

  private def tmpFileFor(storage: File): File =
    new File(storage.getParent, s"${storage.getName}.$tmpSuffix.tmp")

  /** Remove `<storageFile>.*.tmp` siblings from prior crashed saves.
    *
    * Two-tier policy:
    *   - legacy `<storageFile>.tmp` (single canonical name used before
    *     this fix): delete unconditionally to clean up old debris;
    *   - `<storageFile>.<uuid>.tmp`: delete only if older than
    *     `staleTmpAgeMs` AND not the current-JVM tmp. Age-gating makes
    *     a parallel jEdit process's live tmp safe from this sweep.
    *
    * Note: `storageFile` itself can throw an `IllegalStateException`
    * when `jEdit.getSettingsDirectory` is null outside test mode. That
    * throw is intentionally swallowed by the outer `catch NonFatal`
    * below — the cleanup is best-effort, and the real error will
    * surface from the subsequent `load()` call inside `ensureLoaded`
    * with its more specific diagnostic path.
    */
  private def cleanupStaleTempFiles(): Unit = {
    try {
      val file = storageFile
      val parent = file.getParentFile
      if (parent == null || !parent.isDirectory) return

      val baseName = file.getName
      val legacyTmp = new File(parent, s"$baseName.tmp")
      if (legacyTmp.isFile) {
        if (legacyTmp.delete()) {
          safeLog(s"[MemoryStore] Removed legacy ${legacyTmp.getName} from a prior crashed save.")
        } else {
          safeLog(s"[MemoryStore] Could not remove legacy ${legacyTmp.getName}; ignoring.")
        }
      }

      val suffixedTmpRegex =
        java.util.regex.Pattern.compile(
          java.util.regex.Pattern.quote(baseName) + "\\.[A-Za-z0-9-]+\\.tmp"
        )
      val currentTmp = tmpFileFor(file).getName
      val now = System.currentTimeMillis()
      val children = Option(parent.listFiles()).getOrElse(Array.empty[File])
      children.foreach { child =>
        val name = child.getName
        if (
          name != currentTmp &&
          suffixedTmpRegex.matcher(name).matches() &&
          child.isFile &&
          now - child.lastModified() > staleTmpAgeMs
        ) {
          if (child.delete())
            safeLog(s"[MemoryStore] Removed stale $name from a prior crashed save.")
        }
      }
    } catch {
      case NonFatal(e) =>
        safeLog(s"[MemoryStore] Stale-tmp sweep failed: ${e.getMessage}")
    }
  }
  
  /**
   * Safe logging that doesn't fail if Output is unavailable. Also swallows
   * LinkageError because Output.writeln transitively touches classes that
   * aren't on the test classpath.
   */
  private def safeLog(message: String): Unit = {
    try {
      Output.writeln(message)
    } catch {
      case NonFatal(_)      => // Ignore if Output not available
      case _: LinkageError  => // test classpath lacks Output's dependencies
    }
  }

  /**
   * Safe cache clearing that doesn't fail if PromptLoader is unavailable.
   */
  private def safeClearCache(): Unit = {
    try {
      PromptLoader.clearCache()
    } catch {
      case NonFatal(_) => // Ignore if PromptLoader not available
    }
  }
  
  // Shared Jackson factory for both reading and writing.
  private val jsonFactory = new JsonFactory()


  /**
   * Load memories from JSON file using Jackson streaming parser.
   */
  private def load(): Unit = {
    val file = storageFile
    if (!file.exists()) {
      memories = Map.empty
      nextId = 1
      return
    }
    
    try {
      val source = Source.fromFile(file, "UTF-8")
      val content = try source.mkString finally source.close()
      
      val parser = jsonFactory.createParser(content)
      val loadedMemories = scala.collection.mutable.Map[String, List[Memory]]()
      
      try {
        // Expect START_OBJECT
        if (parser.nextToken() != JsonToken.START_OBJECT) return
        
        while (parser.nextToken() != JsonToken.END_OBJECT) {
          val fieldName = parser.currentName()
          parser.nextToken() // Move to field value
          
          fieldName match {
            case "version" => val _ = parser.getIntValue // Ignore for now
            case "nextId" => nextId = parser.getIntValue
            case "topics" =>
              // Parse topics object
              if (parser.getCurrentToken == JsonToken.START_OBJECT) {
                while (parser.nextToken() != JsonToken.END_OBJECT) {
                  val topic = parser.currentName()
                  parser.nextToken() // Move to array
                  
                  if (parser.getCurrentToken == JsonToken.START_ARRAY) {
                    val mems = scala.collection.mutable.ListBuffer[Memory]()
                    
                    while (parser.nextToken() != JsonToken.END_ARRAY) {
                      // Parse memory object
                      var id = 0
                      var title = ""
                      var body = ""
                      var createdStr = ""
                      
                      if (parser.getCurrentToken == JsonToken.START_OBJECT) {
                        while (parser.nextToken() != JsonToken.END_OBJECT) {
                          val memField = parser.currentName()
                          parser.nextToken()
                          
                          memField match {
                            case "id" => id = parser.getIntValue
                            case "title" => title = parser.getText
                            case "body" => body = parser.getText
                            case "created" => createdStr = parser.getText
                            case _ => val _ = parser.skipChildren()
                          }
                        }
                        
                        if (id > 0 && title.nonEmpty && createdStr.nonEmpty) {
                          try {
                            val created = LocalDateTime.parse(createdStr, timeFormatter)
                            mems += Memory(id, topic, title, body, created)
                          } catch {
                            case NonFatal(e) =>
                              safeLog(s"[MemoryStore] Skipping corrupted memory in topic '$topic': ${e.getMessage}")
                          }
                        }
                      }
                    }
                    
                    if (mems.nonEmpty) {
                      loadedMemories(topic) = mems.toList
                    }
                  }
                }
              }
            case _ => val _ = parser.skipChildren()
          }
        }
        
        memories = loadedMemories.toMap
        safeLog(s"[MemoryStore] Loaded ${totalMemoryCount} memories from ${memories.size} topics")
      } finally {
        parser.close()
      }
    } catch {
      case NonFatal(e) =>
        safeLog(s"[MemoryStore] Failed to load memories: ${e.getMessage}")
        memories = Map.empty
        nextId = 1
    }
  }
  
  /**
   * Save memories to JSON file with atomic write (tmp + rename).
   * On rename failure, leave the tmp file in place rather than rewriting the
   * original: the tmp has valid data and the destination is untouched, so the
   * store remains consistent for this session and the tmp is inspectable.
   */
  private def save(): Unit = {
    try {
      val json = renderJson()

      val file = storageFile
      file.getParentFile.mkdirs()

      val tmpFile = tmpFileFor(file)
      val writer = new PrintWriter(tmpFile, "UTF-8")
      try {
        writer.write(json)
      } finally {
        writer.close()
      }

      if (!tmpFile.renameTo(file)) {
        safeLog(
          s"[MemoryStore] Could not rename ${tmpFile.getName} to ${file.getName}; leaving tmp in place for inspection."
        )
      }
    } catch {
      case NonFatal(e) =>
        safeLog(s"[MemoryStore] Failed to save memories: ${e.getMessage}")
    }
  }

  /**
   * Render the in-memory store as a pretty-printed JSON string using Jackson.
   * This replaces the hand-rolled JSON builder + escape logic.
   */
  private def renderJson(): String = {
    val sw = new java.io.StringWriter()
    val g: JsonGenerator = jsonFactory.createGenerator(sw)
    g.useDefaultPrettyPrinter()
    try {
      g.writeStartObject()
      g.writeNumberField("version", 1)
      g.writeNumberField("nextId", nextId)
      g.writeObjectFieldStart("topics")
      for ((topic, mems) <- memories.toList.sortBy(_._1)) {
        g.writeArrayFieldStart(topic)
        for (mem <- mems) {
          g.writeStartObject()
          g.writeNumberField("id", mem.id)
          g.writeStringField("title", mem.title)
          g.writeStringField("body", mem.body)
          g.writeStringField("created", mem.created.format(timeFormatter))
          g.writeEndObject()
        }
        g.writeEndArray()
      }
      g.writeEndObject()
      g.writeEndObject()
    } finally {
      g.close()
    }
    sw.toString
  }

  /**
   * Validate topic name.
   */
  private def validateTopicName(topic: String): Either[String, String] = {
    val trimmed = topic.trim.toLowerCase
    if (trimmed.isEmpty) Left("Error: topic name cannot be empty")
    else if (trimmed.length > 50) Left("Error: topic name too long (max 50 characters)")
    else if (TOPIC_NAME_PATTERN.findFirstIn(trimmed).isEmpty)
      Left(s"Error: invalid topic name '$trimmed' (use lowercase alphanumeric and underscores only)")
    else Right(trimmed)
  }
  
  /**
   * Validate title.
   */
  private def validateTitle(title: String): Either[String, String] = {
    val trimmed = title.trim
    if (trimmed.isEmpty) Left("Error: title cannot be empty")
    else if (trimmed.length > MAX_TITLE_LENGTH)
      Left(s"Error: title too long (max $MAX_TITLE_LENGTH characters)")
    else Right(trimmed)
  }
  
  /**
   * Validate body.
   */
  private def validateBody(body: String): Either[String, String] = {
    val trimmed = body.trim
    if (trimmed.isEmpty) Left("Error: body cannot be empty")
    else if (trimmed.length > MAX_BODY_LENGTH)
      Left(s"Error: body too long (max $MAX_BODY_LENGTH characters)")
    else Right(trimmed)
  }
  
  /**
   * Add a new memory to a topic.
   * Creates the topic if it doesn't exist.
   */
  def addMemory(topic: String, title: String, body: String): String = lock.synchronized {
    ensureLoaded()
    
    val result = for {
      validTopic <- validateTopicName(topic)
      validTitle <- validateTitle(title)
      validBody <- validateBody(body)
    } yield {
      // Check topic limit
      if (!memories.contains(validTopic) && memories.size >= MAX_TOPICS) {
        Left(s"Error: maximum number of topics ($MAX_TOPICS) reached")
      } else {
        // Check memories per topic limit
        val topicMems = memories.getOrElse(validTopic, Nil)
        if (topicMems.length >= MAX_MEMORIES_PER_TOPIC) {
          Left(s"Error: maximum number of memories ($MAX_MEMORIES_PER_TOPIC) reached for topic '$validTopic'")
        } else {
          val mem = Memory(
            id = nextId,
            topic = validTopic,
            title = validTitle,
            body = validBody,
            created = LocalDateTime.now()
          )
          
          memories = memories.updated(validTopic, topicMems :+ mem)
          nextId += 1
          save()
          safeClearCache()
          
          Right(s"Memory #${mem.id} added to topic '$validTopic': ${mem.title}")
        }
      }
    }
    
    result match {
      case Right(Right(msg)) => msg
      case Right(Left(err)) => err
      case Left(err) => err
    }
  }
  
  /**
   * Delete a memory by ID.
   */
  def deleteMemory(memoryId: Int): String = lock.synchronized {
    ensureLoaded()
    
    // Find the memory
    memories.iterator.flatMap { case (topic, mems) =>
      mems.find(_.id == memoryId).map(mem => (topic, mem))
    }.toList.headOption match {
      case None => s"Error: memory #$memoryId not found"
      case Some((topic, mem)) =>
        val updatedMems = memories(topic).filterNot(_.id == memoryId)
        if (updatedMems.isEmpty) {
          memories = memories - topic
        } else {
          memories = memories.updated(topic, updatedMems)
        }
        save()
        safeClearCache()
        s"Memory #$memoryId '${mem.title}' deleted from topic '$topic'"
    }
  }
  
  /**
   * Delete an entire topic and all its memories.
   */
  def deleteTopic(topic: String): String = lock.synchronized {
    ensureLoaded()
    
    validateTopicName(topic) match {
      case Left(err) => err
      case Right(validTopic) =>
        memories.get(validTopic) match {
          case None => s"Error: topic '$validTopic' not found"
          case Some(mems) =>
            val count = mems.length
            memories = memories - validTopic
            save()
            safeClearCache()
            s"Topic '$validTopic' deleted ($count memories removed)"
        }
    }
  }
  
  /**
   * List all topics with memory counts.
   */
  def listTopics(): String = lock.synchronized {
    ensureLoaded()
    
    if (memories.isEmpty)
      "No topics found. Add memories to create topics."
    else {
      val sorted = memories.toList.sortBy(_._1)
      val lines = sorted.map { case (topic, mems) =>
        s"• $topic (${mems.length} ${if (mems.length == 1) "memory" else "memories"})"
      }
      s"Topics (${memories.size}):\n${lines.mkString("\n")}"
    }
  }
  
  /**
   * List all memories in a topic.
   */
  def listMemories(topic: String): String = lock.synchronized {
    ensureLoaded()
    
    validateTopicName(topic) match {
      case Left(err) => err
      case Right(validTopic) =>
        memories.get(validTopic) match {
          case None => s"Topic '$validTopic' not found or empty"
          case Some(mems) if mems.isEmpty => s"Topic '$validTopic' is empty"
          case Some(mems) =>
            val lines = mems.map { mem =>
              s"#${mem.id}. ${mem.title}"
            }
            s"Memories in topic '$validTopic' (${mems.length}):\n${lines.mkString("\n")}"
        }
    }
  }
  
  /**
   * Get full details of a specific memory.
   */
  def getMemory(memoryId: Int): String = lock.synchronized {
    ensureLoaded()
    
    memories.iterator.flatMap { case (topic, mems) =>
      mems.find(_.id == memoryId)
    }.toList.headOption match {
      case None => s"Error: memory #$memoryId not found"
      case Some(mem) =>
        s"Memory #${mem.id} in topic '${mem.topic}':\n" +
        s"Title: ${mem.title}\n" +
        s"Created: ${mem.created.format(DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm"))}\n\n" +
        s"${mem.body}"
    }
  }
  
  /**
   * Search for memories matching a query (case-insensitive).
   */
  def searchMemories(query: String): String = lock.synchronized {
    ensureLoaded()
    
    val trimmedQuery = query.trim
    if (trimmedQuery.isEmpty) {
      "Error: search query cannot be empty"
    } else {
      val lowerQuery = trimmedQuery.toLowerCase
      val matches = scala.collection.mutable.ListBuffer[(String, Memory, String)]()
      
      for ((topic, mems) <- memories; mem <- mems) {
        val titleMatch = mem.title.toLowerCase.contains(lowerQuery)
        val bodyMatch = mem.body.toLowerCase.contains(lowerQuery)
        
        if (titleMatch || bodyMatch) {
          // Extract a snippet
          val snippet = if (titleMatch) {
            mem.title
          } else {
            // Find context around match in body
            val idx = mem.body.toLowerCase.indexOf(lowerQuery)
            val start = math.max(0, idx - 40)
            val end = math.min(mem.body.length, idx + lowerQuery.length + 40)
            val prefix = if (start > 0) "…" else ""
            val suffix = if (end < mem.body.length) "…" else ""
            prefix + mem.body.substring(start, end) + suffix
          }
          matches += ((topic, mem, snippet))
        }
      }
      
      if (matches.isEmpty)
        s"No memories found matching: $trimmedQuery"
      else {
        val lines = matches.map { case (topic, mem, snippet) =>
          s"#${mem.id} [$topic] ${mem.title}\n  $snippet"
        }
        s"Found ${matches.length} ${if (matches.length == 1) "memory" else "memories"} matching '$trimmedQuery':\n\n${lines.mkString("\n\n")}"
      }
    }
  }
  
  /** Cap on the size of the memory summary injected into the system prompt.
    * 1500 characters works out to roughly 400–600 tokens under the
    * tokenizers Claude uses. The summary is glued into the system prompt by
    * `PromptLoader.injectMemorySummary`, so every message of every session
    * pays for it — keep this tight. */
  private val MAX_SUMMARY_CHARS = 1500

  /**
   * Get a compact summary of all memories for system prompt injection.
   * Caps output at [[MAX_SUMMARY_CHARS]]; the summary is spliced into the
   * system prompt by `PromptLoader.injectMemorySummary` and rendered anew
   * whenever `PromptLoader.clearCache()` is called (which happens after
   * every successful add/delete/deleteTopic via [[safeClearCache]]).
   */
  def getAllMemoriesSummary(): String = lock.synchronized {
    ensureLoaded()

    if (memories.isEmpty)
      "No memories recorded yet."
    else {
      val lines = scala.collection.mutable.ListBuffer[String]()
      val sorted = memories.toList.sortBy(_._1)
      var charCount = 0
      val maxChars = MAX_SUMMARY_CHARS
      var truncated = false
      
      for ((topic, mems) <- sorted if !truncated) {
        val topicLine = s"**$topic** (${mems.length}):"
        if (charCount + topicLine.length < maxChars) {
          lines += topicLine
          charCount += topicLine.length + 1
          
          for (mem <- mems.take(10) if !truncated) {
            val memLine = s"  • #${mem.id}: ${mem.title}"
            if (charCount + memLine.length < maxChars) {
              lines += memLine
              charCount += memLine.length + 1
            } else {
              truncated = true
            }
          }
          
          if (!truncated && mems.length > 10) {
            val moreLine = s"  ... and ${mems.length - 10} more"
            if (charCount + moreLine.length < maxChars) {
              lines += moreLine
              charCount += moreLine.length + 1
            } else {
              truncated = true
            }
          }
        } else {
          truncated = true
        }
      }
      
      val result = lines.mkString("\n")
      if (truncated) result + s"\n\n(Summary truncated at $MAX_SUMMARY_CHARS characters)" else result
    }
  }
  
  /**
   * Get all memories as structured data (for testing).
   */
  private[assistant] def getAllMemories: Map[String, List[Memory]] = lock.synchronized {
    ensureLoaded()
    memories
  }
  
  /**
   * Get the next ID (for testing).
   */
  private[assistant] def getNextId: Int = lock.synchronized {
    ensureLoaded()
    nextId
  }
  
  /**
   * Total count of all memories across all topics.
   */
  private def totalMemoryCount: Int = memories.values.map(_.length).sum
  
  /**
   * Force reload from disk (for testing).
   */
  private[assistant] def reload(): Unit = lock.synchronized {
    loaded = false
    ensureLoaded()
  }
  
  /**
   * Delete all memories (for testing only - not exposed as a tool).
   */
  private[assistant] def deleteAll(): Unit = lock.synchronized {
    memories = Map.empty
    nextId = 1
    save()
    safeClearCache()
  }
  
  /**
   * Reset the singleton state (for testing only).
   * Clears in-memory state and marks as not loaded, forcing reload on next access.
   */
  private[assistant] def resetForTest(): Unit = lock.synchronized {
    memories = Map.empty
    nextId = 1
    loaded = false
  }
}
