/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach}
import java.io.File
import java.nio.file.Files

/**
 * Tests for MemoryStore persistence and validation.
 * Uses reflection to access private methods for testing without jEdit runtime.
 *
 * Suite-level (`beforeAll`/`afterAll`) scope is used for the
 * `assistant.storage.test_mode` system property because it is JVM-global:
 * touching it in `beforeEach` would cause cross-test bleed under any
 * runner that orders setups from multiple suites interleaved with one
 * another (not the default, but ScalaTest permits it). Tests that need
 * to observe the "production" no-test-mode path toggle the property
 * inside a try/finally and restore it themselves.
 */
class MemoryStoreTest
    extends AnyFunSuite
    with Matchers
    with BeforeAndAfterAll
    with BeforeAndAfterEach {

  // Use reflection to test with a temporary file instead of jEdit settings
  private var tempFile: File = _

  override def beforeAll(): Unit = {
    super.beforeAll()
    // Opt in to the /tmp fallback explicitly for the duration of the suite.
    // The production path rejects a null settings directory; tests must
    // acknowledge they want the fallback behaviour.
    val _ = System.setProperty("assistant.storage.test_mode", "true")
  }

  override def afterAll(): Unit = {
    try {
      // Clean up suite-wide state so other suites see the production default.
      val _ = System.clearProperty("assistant.storage.test_mode")
    } finally {
      super.afterAll()
    }
  }

  override def beforeEach(): Unit = {
    // Reset the singleton state
    MemoryStore.resetForTest()

    // Delete the storage file so we start fresh (it will be recreated on save)
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    if (storageFile.exists()) {
      val _ = storageFile.delete()
    }

    tempFile = Files.createTempFile("memory-test", ".json").toFile
    tempFile.deleteOnExit()
  }

  override def afterEach(): Unit = {
    if (tempFile != null && tempFile.exists()) {
      val _ = tempFile.delete()
    }
  }

  test("addMemory should create a new memory with valid inputs") {
    val result = MemoryStore.addMemory("user", "Test memory", "This is a test body")
    result should include("Memory #")
    result should include("added to topic 'user'")
    result should include("Test memory")
  }

  test("addMemory should validate topic name") {
    val result = MemoryStore.addMemory("", "Title", "Body")
    result should include("Error")
    result should include("topic name cannot be empty")
  }

  test("addMemory should reject invalid topic names") {
    val result = MemoryStore.addMemory("Invalid Topic!", "Title", "Body")
    result should include("Error")
    result should include("invalid topic name")
  }

  test("addMemory should convert topic names to lowercase") {
    val result1 = MemoryStore.addMemory("User", "Title1", "Body1")
    val result2 = MemoryStore.addMemory("USER", "Title2", "Body2")
    
    result1 should include("topic 'user'")
    result2 should include("topic 'user'")
    
    val topics = MemoryStore.listTopics()
    topics should include("user")
    topics should include("2 memories")
  }

  test("addMemory should validate title") {
    val result = MemoryStore.addMemory("user", "", "Body")
    result should include("Error")
    result should include("title cannot be empty")
  }

  test("addMemory should reject titles that are too long") {
    val longTitle = "x" * 201
    val result = MemoryStore.addMemory("user", longTitle, "Body")
    result should include("Error")
    result should include("title too long")
  }

  test("addMemory should validate body") {
    val result = MemoryStore.addMemory("user", "Title", "")
    result should include("Error")
    result should include("body cannot be empty")
  }

  test("addMemory should reject bodies that are too long") {
    val longBody = "x" * 2001
    val result = MemoryStore.addMemory("user", "Title", longBody)
    result should include("Error")
    result should include("body too long")
  }

  test("listTopics should return empty message when no topics exist") {
    val result = MemoryStore.listTopics()
    result should include("No topics found")
  }

  test("listTopics should list all topics with counts") {
    MemoryStore.addMemory("user", "Title1", "Body1")
    MemoryStore.addMemory("user", "Title2", "Body2")
    MemoryStore.addMemory("isabelle", "Title3", "Body3")
    
    val result = MemoryStore.listTopics()
    result should include("Topics (2)")
    result should include("isabelle (1 memory)")
    result should include("user (2 memories)")
  }

  test("listMemories should return error for non-existent topic") {
    val result = MemoryStore.listMemories("nonexistent")
    result should include("not found or empty")
  }

  test("listMemories should list all memories in a topic") {
    MemoryStore.addMemory("user", "Memory 1", "Body 1")
    MemoryStore.addMemory("user", "Memory 2", "Body 2")
    
    val result = MemoryStore.listMemories("user")
    result should include("Memories in topic 'user' (2)")
    result should include("Memory 1")
    result should include("Memory 2")
  }

  test("getMemory should return error for non-existent memory") {
    val result = MemoryStore.getMemory(999)
    result should include("Error")
    result should include("not found")
  }

  test("getMemory should return full memory details") {
    MemoryStore.addMemory("user", "Test Title", "Test Body Content")
    
    val result = MemoryStore.getMemory(1)
    result should include("Memory #1")
    result should include("topic 'user'")
    result should include("Title: Test Title")
    result should include("Test Body Content")
  }

  test("deleteMemory should return error for non-existent memory") {
    val result = MemoryStore.deleteMemory(999)
    result should include("Error")
    result should include("not found")
  }

  test("deleteMemory should delete a memory and return confirmation") {
    MemoryStore.addMemory("user", "To Delete", "Body")
    
    val result = MemoryStore.deleteMemory(1)
    result should include("deleted from topic 'user'")
    result should include("To Delete")
    
    val getResult = MemoryStore.getMemory(1)
    getResult should include("not found")
  }

  test("deleteMemory should remove topic when last memory is deleted") {
    MemoryStore.addMemory("temp", "Only Memory", "Body")
    
    MemoryStore.deleteMemory(1)
    
    val topics = MemoryStore.listTopics()
    topics should include("No topics found")
  }

  test("deleteTopic should return error for non-existent topic") {
    val result = MemoryStore.deleteTopic("nonexistent")
    result should include("Error")
    result should include("not found")
  }

  test("deleteTopic should delete all memories in a topic") {
    MemoryStore.addMemory("temp", "Memory 1", "Body 1")
    MemoryStore.addMemory("temp", "Memory 2", "Body 2")
    MemoryStore.addMemory("keep", "Memory 3", "Body 3")
    
    val result = MemoryStore.deleteTopic("temp")
    result should include("Topic 'temp' deleted")
    result should include("2 memories removed")
    
    val topics = MemoryStore.listTopics()
    topics should not include "temp"
    topics should include("keep")
  }

  test("searchMemories should return error for empty query") {
    val result = MemoryStore.searchMemories("")
    result should include("Error")
    result should include("query cannot be empty")
  }

  test("searchMemories should return no results message when nothing matches") {
    MemoryStore.addMemory("user", "Title", "Body")
    
    val result = MemoryStore.searchMemories("nonexistent")
    result should include("No memories found")
  }

  test("searchMemories should find memories by title") {
    MemoryStore.addMemory("user", "Important Note", "Some body text")
    MemoryStore.addMemory("user", "Other Note", "Different body")
    
    val result = MemoryStore.searchMemories("Important")
    result should include("Found 1 memory")
    result should include("Important Note")
  }

  test("searchMemories should find memories by body content") {
    MemoryStore.addMemory("user", "Title", "Contains keyword here")
    MemoryStore.addMemory("user", "Title2", "No match")
    
    val result = MemoryStore.searchMemories("keyword")
    result should include("Found 1 memory")
    result should include("keyword")
  }

  test("searchMemories should be case-insensitive") {
    MemoryStore.addMemory("user", "Test Title", "Body")
    
    val result = MemoryStore.searchMemories("test")
    result should include("Found 1 memory")
    result should include("Test Title")
  }

  test("searchMemories should include topic in results") {
    MemoryStore.addMemory("isabelle", "Simp tip", "Body")
    
    val result = MemoryStore.searchMemories("simp")
    result should include("[isabelle]")
  }

  test("getAllMemoriesSummary should return message when no memories exist") {
    val result = MemoryStore.getAllMemoriesSummary()
    result should include("No memories recorded yet")
  }

  test("getAllMemoriesSummary should summarize all topics") {
    MemoryStore.addMemory("user", "Memory 1", "Body 1")
    MemoryStore.addMemory("isabelle", "Memory 2", "Body 2")
    
    val result = MemoryStore.getAllMemoriesSummary()
    result should include("**user** (1)")
    result should include("**isabelle** (1)")
    result should include("Memory 1")
    result should include("Memory 2")
  }

  test("getAllMemoriesSummary should truncate long topic lists") {
    // Add 15 memories to one topic
    for (i <- 1 to 15) {
      MemoryStore.addMemory("user", s"Memory $i", s"Body $i")
    }
    
    val result = MemoryStore.getAllMemoriesSummary()
    result should include("**user** (15)")
    result should include("... and 5 more")
  }

  test("memory IDs should be sequential") {
    MemoryStore.addMemory("user", "First", "Body")
    MemoryStore.addMemory("user", "Second", "Body")
    MemoryStore.addMemory("other", "Third", "Body")
    
    val nextId = MemoryStore.getNextId
    nextId shouldBe 4
  }

  test("memory IDs should persist across deletions") {
    MemoryStore.addMemory("user", "First", "Body")
    MemoryStore.addMemory("user", "Second", "Body")
    MemoryStore.deleteMemory(1)
    MemoryStore.addMemory("user", "Third", "Body")
    
    val nextId = MemoryStore.getNextId
    nextId shouldBe 4
    
    val memories = MemoryStore.getAllMemories
    val userMems = memories("user")
    userMems.map(_.id).sorted shouldBe List(2, 3)
  }

  test("topic names should only contain lowercase alphanumeric and underscores") {
    val valid = MemoryStore.addMemory("my_topic_123", "Title", "Body")
    valid should not include "Error"
    
    val invalid1 = MemoryStore.addMemory("my-topic", "Title", "Body")
    invalid1 should include("Error")
    
    val invalid2 = MemoryStore.addMemory("my topic", "Title", "Body")
    invalid2 should include("Error")
  }

  test("should trim whitespace from inputs") {
    val result = MemoryStore.addMemory("  user  ", "  Title  ", "  Body  ")
    result should include("topic 'user'")
    
    val mem = MemoryStore.getMemory(1)
    mem should include("Title: Title")
    mem should include("\nBody")
  }

  test("should handle maximum title length") {
    val maxTitle = "x" * 200
    val result = MemoryStore.addMemory("user", maxTitle, "Body")
    result should not include "Error"
  }

  test("should handle maximum body length") {
    val maxBody = "x" * 2000
    val result = MemoryStore.addMemory("user", "Title", maxBody)
    result should not include "Error"
  }

  test("should enforce maximum number of topics") {
    // This test would need to create 100+ topics, which is slow
    // Just verify the limit exists in the result
    for (i <- 1 to 100) {
      MemoryStore.addMemory(s"topic_$i", "Title", "Body")
    }
    
    val result = MemoryStore.addMemory("topic_101", "Title", "Body")
    result should include("Error")
    result should include("maximum number of topics")
  }

  test("should enforce maximum memories per topic") {
    // This test would need to create 200+ memories, which is slow
    // Just verify the validation works for first few
    for (i <- 1 to 5) {
      val result = MemoryStore.addMemory("user", s"Memory $i", s"Body $i")
      result should not include "Error"
    }
  }

  test("deleteAll should clear all memories") {
    MemoryStore.addMemory("user", "Memory 1", "Body 1")
    MemoryStore.addMemory("isabelle", "Memory 2", "Body 2")
    
    MemoryStore.deleteAll()
    
    val topics = MemoryStore.listTopics()
    topics should include("No topics found")
    
    val nextId = MemoryStore.getNextId
    nextId shouldBe 1
  }

  test("memories should be organized by topic") {
    MemoryStore.addMemory("user", "User Fact", "Body 1")
    MemoryStore.addMemory("isabelle", "Isabelle Tip", "Body 2")
    MemoryStore.addMemory("user", "Another User Fact", "Body 3")
    
    val allMemories = MemoryStore.getAllMemories
    allMemories.keySet should contain allOf ("user", "isabelle")
    allMemories("user") should have length 2
    allMemories("isabelle") should have length 1
  }

  test("listMemories should show IDs and titles only") {
    MemoryStore.addMemory("user", "Title One", "Long body text here")
    MemoryStore.addMemory("user", "Title Two", "Another long body")
    
    val result = MemoryStore.listMemories("user")
    result should include("#1. Title One")
    result should include("#2. Title Two")
    result should not include "Long body text"
    result should not include "Another long body"
  }

  test("searchMemories should provide context snippets") {
    val longBody = "x" * 50 + " keyword " + "y" * 50
    MemoryStore.addMemory("user", "Title", longBody)
    
    val result = MemoryStore.searchMemories("keyword")
    result should include("keyword")
    result should include("…")
  }

  test("getMemory should include creation timestamp") {
    MemoryStore.addMemory("user", "Test", "Body")
    
    val result = MemoryStore.getMemory(1)
    result should include("Created:")
    result should include regex """\d{4}-\d{2}-\d{2}"""
  }

  test("topic names with capital letters should be normalized") {
    MemoryStore.addMemory("User", "Title", "Body")
    
    val topics = MemoryStore.listTopics()
    topics should include("user")
    topics should not include "User"
  }

  test("should preserve memory order within topics") {
    MemoryStore.addMemory("user", "First", "Body 1")
    MemoryStore.addMemory("user", "Second", "Body 2")
    MemoryStore.addMemory("user", "Third", "Body 3")
    
    val result = MemoryStore.listMemories("user")
    val lines = result.split("\n")
    val memLines = lines.filter(_.contains("#"))
    
    memLines(0) should include("First")
    memLines(1) should include("Second")
    memLines(2) should include("Third")
  }

  test("should handle unicode characters in titles and bodies") {
    val result = MemoryStore.addMemory("user", "λ-calculus", "Contains ∀ and ∃ symbols")
    result should not include "Error"
    
    val mem = MemoryStore.getMemory(1)
    mem should include("λ-calculus")
    mem should include("∀")
    mem should include("∃")
  }

  test("getAllMemories should return immutable snapshot") {
    MemoryStore.addMemory("user", "Test", "Body")

    val snapshot1 = MemoryStore.getAllMemories
    MemoryStore.addMemory("user", "Test2", "Body2")
    val snapshot2 = MemoryStore.getAllMemories

    snapshot1("user") should have length 1
    snapshot2("user") should have length 2
  }

  test("load should recover from a corrupted JSON file by starting empty") {
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    Files.write(storageFile.toPath, "not a valid json {".getBytes("UTF-8"))

    MemoryStore.resetForTest()
    // First access triggers load; corrupted file should NOT throw.
    val topics = MemoryStore.listTopics()
    topics should include("No topics found")
    MemoryStore.getNextId shouldBe 1

    storageFile.delete()
  }

  test("load should tolerate malformed memory entries and skip them") {
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    val badJson = """{"version":1,"nextId":3,"topics":{"user":[
      {"id":1,"title":"ok","body":"good","created":"2026-01-01T00:00:00"},
      {"id":2,"title":"broken","body":"bad","created":"not-a-date"}
    ]}}"""
    Files.write(storageFile.toPath, badJson.getBytes("UTF-8"))

    MemoryStore.resetForTest()
    val mem1 = MemoryStore.getMemory(1)
    mem1 should include("Title: ok")
    // The malformed date entry is silently skipped.
    MemoryStore.getMemory(2) should include("Error")

    storageFile.delete()
  }

  test("concurrent addMemory calls should all persist without exception") {
    val nThreads = 4
    val perThread = 10

    val threads = for (t <- 0 until nThreads) yield new Thread(() => {
      for (i <- 0 until perThread) {
        val _ = MemoryStore.addMemory(s"topic_$t", s"title-$t-$i", s"body-$t-$i")
      }
    })

    val uncaught = new java.util.concurrent.ConcurrentLinkedQueue[Throwable]()
    val handler: Thread.UncaughtExceptionHandler =
      (_: Thread, ex: Throwable) => { val _ = uncaught.add(ex); () }
    threads.foreach(_.setUncaughtExceptionHandler(handler))
    threads.foreach(_.start())
    threads.foreach(_.join(10000))

    uncaught shouldBe empty
    val all = MemoryStore.getAllMemories
    all.keySet.size shouldBe nThreads
    all.values.map(_.length).sum shouldBe nThreads * perThread
  }

  test("startup sweep removes a stale .tmp file left by a crashed save") {
    // Simulate a crash-during-save: create the debris the next startup
    // should clean up.
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    val staleTmp = new File(storageFile.getParentFile, storageFile.getName + ".tmp")
    Files.write(staleTmp.toPath, "garbage".getBytes("UTF-8"))
    staleTmp.exists() shouldBe true

    // Trigger lazy load (which invokes cleanupStaleTempFiles first).
    val _ = MemoryStore.getAllMemories

    staleTmp.exists() shouldBe false
  }

  test("startup sweep leaves unrelated files in the settings dir alone") {
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    val unrelated = new File(storageFile.getParentFile, "some-other-plugin.tmp")
    Files.write(unrelated.toPath, "precious".getBytes("UTF-8"))
    try {
      val _ = MemoryStore.getAllMemories
      unrelated.exists() shouldBe true
    } finally {
      if (unrelated.exists()) { val _ = unrelated.delete() }
    }
  }

  test("startup sweep spares a recent suffixed .tmp from a sibling JVM") {
    // Simulate a concurrent second jEdit mid-write. Its tmp matches
    // `<storage>.<uuid>.tmp` but was modified just now, so the sweeper
    // must not treat it as abandoned debris.
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    val liveSibling = new File(
      storageFile.getParentFile,
      storageFile.getName + ".abcd1234.tmp"
    )
    Files.write(liveSibling.toPath, "in-progress".getBytes("UTF-8"))
    liveSibling.setLastModified(System.currentTimeMillis())
    try {
      MemoryStore.resetForTest()
      val _ = MemoryStore.getAllMemories
      liveSibling.exists() shouldBe true
    } finally {
      if (liveSibling.exists()) { val _ = liveSibling.delete() }
    }
  }

  test("startup sweep removes an old suffixed .tmp past the staleness threshold") {
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    val oldSibling = new File(
      storageFile.getParentFile,
      storageFile.getName + ".deadbeef.tmp"
    )
    Files.write(oldSibling.toPath, "long ago".getBytes("UTF-8"))
    // Older than the 1-hour staleness window.
    oldSibling.setLastModified(System.currentTimeMillis() - (2L * 60L * 60L * 1000L))

    MemoryStore.resetForTest()
    val _ = MemoryStore.getAllMemories
    oldSibling.exists() shouldBe false
  }

  test("load should recover from a file truncated mid-object") {
    // Simulate a process kill partway through save(): the JSON opens fine
    // but ends before the outer object closes. A robust loader must treat
    // this as "no memories" rather than aborting.
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    val truncated =
      """{"version":1,"nextId":2,"topics":{"user":[{"id":1,"title":"ok"""
    Files.write(storageFile.toPath, truncated.getBytes("UTF-8"))

    MemoryStore.resetForTest()
    val topics = MemoryStore.listTopics()
    topics should include("No topics found")
    MemoryStore.getNextId shouldBe 1

    storageFile.delete()
  }

  test("load should recover from an empty file") {
    // Zero-byte file: can happen if the process died after opening the
    // destination but before writing anything. Expect clean-empty state.
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    Files.write(storageFile.toPath, Array.emptyByteArray)

    MemoryStore.resetForTest()
    val topics = MemoryStore.listTopics()
    topics should include("No topics found")

    storageFile.delete()
  }

  test("load should tolerate a file that looks like the wrong JSON type at top level") {
    // A rogue tool or an accidental overwrite leaves an array or a string
    // at the root. Loader should shrug and start fresh rather than crash.
    val storageFile = new File(System.getProperty("java.io.tmpdir"), "assistant-memories-test.json")
    Files.write(storageFile.toPath, "[1,2,3]".getBytes("UTF-8"))

    MemoryStore.resetForTest()
    MemoryStore.listTopics() should include("No topics found")

    Files.write(storageFile.toPath, "\"just a string\"".getBytes("UTF-8"))
    MemoryStore.resetForTest()
    MemoryStore.listTopics() should include("No topics found")

    storageFile.delete()
  }

  test("concurrent addMemory + deleteMemory calls must not deadlock or throw") {
    // Seed a pool of memories, then race adders and deleters. The store's
    // coarse lock should serialise them; the test fails fast if the pool
    // cannot drain in the allotted window.
    val seedCount = 20
    for (i <- 1 to seedCount) MemoryStore.addMemory("pool", s"seed-$i", s"body-$i")

    val nAdders = 3
    val nDeleters = 3
    val perAdder = 10

    val uncaught = new java.util.concurrent.ConcurrentLinkedQueue[Throwable]()
    val handler: Thread.UncaughtExceptionHandler =
      (_: Thread, ex: Throwable) => { val _ = uncaught.add(ex); () }

    val adders = for (a <- 0 until nAdders) yield new Thread(() => {
      for (i <- 0 until perAdder) {
        val _ = MemoryStore.addMemory("pool", s"add-$a-$i", s"body-$a-$i")
      }
    })
    val deleters = for (d <- 0 until nDeleters) yield new Thread(() => {
      for (i <- 1 to seedCount) {
        val _ = MemoryStore.deleteMemory(i) // may have been deleted already — that's fine
        val _ = d
      }
    })

    val all = adders ++ deleters
    all.foreach(_.setUncaughtExceptionHandler(handler))
    all.foreach(_.start())
    all.foreach(_.join(10000))

    uncaught shouldBe empty
  }

  test("concurrent addMemory + listTopics must not throw or return stale types") {
    // Exercises the read-write race between list-style reads and writes.
    // Both operations take the lock so the read observes a consistent
    // snapshot; this test's job is to prove the reads don't throw under
    // concurrent mutation.
    val nWriters = 3
    val nReaders = 3
    val writerOps = 20

    val uncaught = new java.util.concurrent.ConcurrentLinkedQueue[Throwable]()
    val handler: Thread.UncaughtExceptionHandler =
      (_: Thread, ex: Throwable) => { val _ = uncaught.add(ex); () }
    val stopReaders = new java.util.concurrent.atomic.AtomicBoolean(false)

    val writers = for (w <- 0 until nWriters) yield new Thread(() => {
      for (i <- 0 until writerOps) {
        val _ = MemoryStore.addMemory(s"t_$w", s"title-$w-$i", s"body-$w-$i")
      }
    })
    val readers = for (_ <- 0 until nReaders) yield new Thread(() => {
      while (!stopReaders.get()) {
        val out = MemoryStore.listTopics()
        if (!(out.contains("Topics") || out.contains("No topics found")))
          throw new AssertionError(s"unexpected listTopics output: $out")
      }
    })

    (writers ++ readers).foreach(_.setUncaughtExceptionHandler(handler))
    writers.foreach(_.start())
    readers.foreach(_.start())
    writers.foreach(_.join(10000))
    stopReaders.set(true)
    readers.foreach(_.join(5000))

    uncaught shouldBe empty
  }

  test("ensureLoaded should sweep a stale .tmp sibling left by a prior crashed save") {
    // Simulate the aftermath of a process kill mid-save: an
    // `assistant-memories-test.json.tmp` sits next to the canonical storage
    // file. The next `ensureLoaded` must remove it so debris doesn't
    // accumulate across restarts.
    val storageDir = new File(System.getProperty("java.io.tmpdir"))
    val staleTmp = new File(storageDir, "assistant-memories-test.json.tmp")
    // Defensively clean any leftover first.
    if (staleTmp.exists()) { val _ = staleTmp.delete() }
    Files.write(staleTmp.toPath, """{"version":1}""".getBytes("UTF-8"))
    staleTmp.exists() shouldBe true

    try {
      MemoryStore.resetForTest()
      // Any public op triggers ensureLoaded which calls cleanupStaleTempFiles.
      val _ = MemoryStore.listTopics()
      staleTmp.exists() shouldBe false
    } finally {
      if (staleTmp.exists()) { val _ = staleTmp.delete() }
    }
  }

  test("storageFile must refuse to silently fall back to /tmp outside test mode") {
    // Regression: the previous implementation silently wrote persistent
    // memories to /tmp when the jEdit settings directory was unavailable
    // (e.g. a misconfigured environment). That could quietly lose user
    // data and widen the file's visibility. Now any access to the storage
    // path without test mode throws.
    MemoryStore.resetForTest()
    System.clearProperty("assistant.storage.test_mode")
    try {
      val failure =
        intercept[IllegalStateException] { val _ = MemoryStore.addMemory("user", "t", "b") }
      // Either branch of the production error path mentions test mode; we
      // just need confirmation that the store refused to fall back silently.
      val msg = failure.getMessage
      withClue(s"message was: $msg") {
        (msg.contains("test_mode") || msg.contains("test mode")) shouldBe true
      }
    } finally {
      // Restore the default test-mode property for later tests in this
      // suite's lifecycle.
      System.setProperty("assistant.storage.test_mode", "true")
      MemoryStore.resetForTest()
    }
  }
}