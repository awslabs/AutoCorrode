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
      body: XML.Body
  ): XML.Tree =
    XML.Elem(
      Markup(
        FineGrainedTiming.ReportMarkup,
        List(
          "version" -> Value.Int(version),
          "invocation" -> Value.Long(17L),
          "method" -> "example_method",
          "success" -> Value.Boolean(true)
        ) ++
          (if (version == FineGrainedTiming.LegacySchemaVersion)
            List(
              "elapsed_us" -> Value.Long(100L),
              "cpu_us" -> Value.Long(60L),
              "gc_us" -> Value.Long(10L)
            )
          else Nil)
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
    requireThat(invocation.timing.isEmpty, "version 2 should not contain implicit outer timing")
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

  def main(_args: Array[String]): Unit = {
    testDecodeNestedAndYxmlBodies()
    testDecodeLegacyOuterTiming()
    testRejectMalformedHistogram()
    testAssociativeMergeAndPercentiles()
    println("FineGrainedTimingTest: all tests passed")
  }
}
