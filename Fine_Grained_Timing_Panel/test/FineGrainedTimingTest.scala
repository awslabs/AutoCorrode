/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle.{Markup, Value, XML, YXML}

object FineGrainedTimingTest {
  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def bucket(index: Int, count: Long): XML.Tree =
    XML.Elem(
      Markup(
        FineGrainedTiming.BucketMarkup,
        List("bucket" -> Value.Int(index), "count" -> Value.Long(count))
      ),
      Nil
    )

  private def entry(
      name: String,
      success: Boolean,
      count: Long,
      elapsed: Long,
      histogram: List[XML.Tree]
  ): XML.Tree =
    XML.Elem(
      Markup(
        FineGrainedTiming.EntryMarkup,
        List(
          "name" -> name,
          "success" -> Value.Boolean(success),
          "count" -> Value.Long(count),
          "elapsed_us" -> Value.Long(elapsed),
          "cpu_us" -> Value.Long(elapsed / 2),
          "gc_us" -> Value.Long(elapsed / 4),
          "min_elapsed_us" -> Value.Long(1),
          "max_elapsed_us" -> Value.Long(elapsed)
        )
      ),
      histogram
    )

  private def report(
      version: Int,
      body: XML.Body,
      invocationTiming: Option[FineGrainedTiming.Timing] = None,
      success: Boolean = true
  ): XML.Tree =
    XML.Elem(
      Markup(
        FineGrainedTiming.ReportMarkup,
        List(
          "version" -> Value.Int(version),
          "invocation" -> Value.Long(17L),
          "method" -> "example_method",
          "success" -> Value.Boolean(success)
        ) ++
          (if (version == FineGrainedTiming.LegacySchemaVersion)
             List(
               "elapsed_us" -> Value.Long(100L),
               "cpu_us" -> Value.Long(60L),
               "gc_us" -> Value.Long(10L)
             )
           else invocationTiming.toList.flatMap(timing =>
             List(
               "elapsed_us" -> Value.Long(timing.elapsedMicros),
               "cpu_us" -> Value.Long(timing.cpuMicros),
               "gc_us" -> Value.Long(timing.gcMicros)
             )))
      ),
      body
    )

  private def testDecodeNestedAndYxmlBodies(): Unit = {
    val body = List(entry("branch", success = false, 3L, 7L, List(bucket(0, 1), bucket(1, 2))))
    val nested =
      FineGrainedTiming.decode(report(FineGrainedTiming.SchemaVersion, body))
    val encoded =
      FineGrainedTiming.decode(
        report(
          FineGrainedTiming.SchemaVersion,
          List(XML.Text(YXML.string_of_body(body)))
        )
      )
    requireThat(nested == encoded, "nested and YXML-text bodies should decode identically")
    val invocation = nested.getOrElse(sys.error("expected a decoded invocation"))
    requireThat(invocation.id == 17L, s"unexpected invocation id ${invocation.id}")
    requireThat(invocation.timing.isEmpty,
      "schema 2 without outer timing should remain valid")
    requireThat(invocation.samples.head.aggregate.count == 3L, "sample count was not decoded")
  }

  private def testDecodeLegacyOuterTiming(): Unit = {
    val invocation =
      FineGrainedTiming
        .decode(report(FineGrainedTiming.LegacySchemaVersion, Nil))
        .getOrElse(sys.error("expected a decoded legacy invocation"))
    requireThat(
      invocation.timing.contains(FineGrainedTiming.Timing(100L, 60L, 10L)),
      "version 1 outer timing was not decoded"
    )
  }

  private def testRejectMalformedHistogram(): Unit = {
    val malformed =
      report(
        FineGrainedTiming.SchemaVersion,
        List(entry("branch", success = true, 2L, 5L, List(bucket(0, 1))))
      )
    requireThat(FineGrainedTiming.decode(malformed).isEmpty, "histogram count mismatch should be rejected")
  }

  private def testAssociativeMergeAndPercentiles(): Unit = {
    val a = FineGrainedTiming.Aggregate(
      1L,
      FineGrainedTiming.Timing(1L, 1L, 0L),
      1L,
      1L,
      Map(0 -> 1L)
    )
    val b = FineGrainedTiming.Aggregate(
      2L,
      FineGrainedTiming.Timing(6L, 2L, 0L),
      2L,
      4L,
      Map(1 -> 1L, 2 -> 1L)
    )
    val c = FineGrainedTiming.Aggregate(
      1L,
      FineGrainedTiming.Timing(8L, 4L, 1L),
      8L,
      8L,
      Map(3 -> 1L)
    )
    requireThat((a + b) + c == a + (b + c), "aggregate merge should be associative")
    val merged = a + b + c
    requireThat(merged.averageElapsedMicros == 3.75, "average elapsed time is incorrect")
    requireThat(merged.percentileElapsedMicros(0.5) == 3L, "p50 bucket is incorrect")
    requireThat(merged.percentileElapsedMicros(0.99) == 15L, "p99 bucket is incorrect")
    val empty =
      FineGrainedTiming.Aggregate(
        0L,
        FineGrainedTiming.Timing(0L, 0L, 0L),
        0L,
        0L,
        Map.empty
      )
    requireThat(empty + merged == merged && merged + empty == merged,
      "empty aggregate should be an additive identity")
  }

  private def testSchemaTwoUsesOuterTiming(): Unit = {
    val outer = FineGrainedTiming.Timing(70L, 40L, 5L)
    val decoded = FineGrainedTiming.decode(report(
      FineGrainedTiming.SchemaVersion,
      List(
        entry("first", success = true, 2L, 40L, List(bucket(5, 2))),
        entry("second", success = true, 1L, 60L, List(bucket(5, 1)))
      ),
      invocationTiming = Some(outer)
    ))
    requireThat(decoded.isDefined, "schema 2 report should decode")
    val invocation = decoded.get
    requireThat(invocation.totalTiming.contains(outer),
      s"schema 2 should use its outer timing, got ${invocation.totalTiming}")
    requireThat(invocation.totalElapsedMicros == 70L,
      s"nested samples must not be added, got ${invocation.totalElapsedMicros}")

    val legacySchemaTwo = FineGrainedTiming.decode(report(
      FineGrainedTiming.SchemaVersion,
      List(entry("sample", success = true, 1L, 60L, List(bucket(5, 1))))
    )).get
    requireThat(legacySchemaTwo.totalTiming.isEmpty,
      "schema 2 reports without an outer timing should remain decodable")
  }

  private def testRepeatedSnapshotsKeepTheLatest(): Unit = {
    def snapshot(count: Long, elapsed: Long) =
      FineGrainedTiming.decode(report(
        FineGrainedTiming.SchemaVersion,
        List(entry("step", success = true, count, elapsed, List(bucket(5, count))))
      )).get

    val partial = snapshot(1L, 10L)
    val complete = snapshot(3L, 90L)
    /* Both snapshots share invocation id 17: the later one supersedes the
       earlier rather than adding to it. */
    val kept = FineGrainedTiming.latestPerInvocation(Vector(partial, complete))
    requireThat(kept.length == 1,
      s"snapshots of one invocation should collapse, got ${kept.length}")
    requireThat(kept.head.samples.head.aggregate.count == 3L,
      s"the largest snapshot should win, got ${kept.head.samples.head.aggregate.count}")

    val reordered = FineGrainedTiming.latestPerInvocation(Vector(complete, partial))
    requireThat(reordered.head.samples.head.aggregate.count == 3L,
      "collapsing must not depend on report order")

    val failed = partial.copy(success = false)
    val successful = partial.copy(success = true)
    val latestOutcome =
      FineGrainedTiming.latestPerInvocation(Vector(failed, successful))
    requireThat(latestOutcome.head.success,
      "success should supersede failure when sample counts are equal")

    val earlyTiming =
      partial.copy(timing = Some(FineGrainedTiming.Timing(10L, 5L, 0L)))
    val lateTiming =
      partial.copy(timing = Some(FineGrainedTiming.Timing(90L, 20L, 1L)))
    val latestTiming =
      FineGrainedTiming.latestPerInvocation(Vector(earlyTiming, lateTiming))
    requireThat(latestTiming.head.timing == lateTiming.timing,
      "outer timing should supersede an otherwise equal snapshot")
  }

  private def testDistinctInvocationsAreKept(): Unit = {
    val first = FineGrainedTiming.decode(report(
      FineGrainedTiming.SchemaVersion,
      List(entry("a", success = true, 1L, 10L, List(bucket(3, 1))))
    )).get
    val second = first.copy(id = 18L)
    val kept = FineGrainedTiming.latestPerInvocation(Vector(first, second))
    requireThat(kept.length == 2,
      s"distinct invocations must both survive, got ${kept.length}")
  }

  def main(_args: Array[String]): Unit = {
    testDecodeNestedAndYxmlBodies()
    testDecodeLegacyOuterTiming()
    testRejectMalformedHistogram()
    testAssociativeMergeAndPercentiles()
    testSchemaTwoUsesOuterTiming()
    testRepeatedSnapshotsKeepTheLatest()
    testDistinctInvocationsAreKept()
    println("FineGrainedTimingTest: all tests passed")
  }
}
