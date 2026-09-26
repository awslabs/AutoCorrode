/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

object FineGrainedTimingHierarchyTest {
  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def aggregate(
      count: Long,
      elapsed: Long
  ): FineGrainedTiming.Aggregate =
    FineGrainedTiming.Aggregate(
      count,
      FineGrainedTiming.Timing(elapsed, elapsed / 2, 0L),
      elapsed,
      elapsed,
      Map(0 -> count)
    )

  private def invocation(
      id: Long,
      method: String,
      success: Boolean,
      elapsed: Long,
      samples: (String, Boolean, FineGrainedTiming.Aggregate)*
  ): FineGrainedTiming.Invocation =
    FineGrainedTiming.Invocation(
      id,
      method,
      success,
      Some(FineGrainedTiming.Timing(elapsed, elapsed / 2, 0L)),
      samples.map { case (name, sampleSuccess, sampleAggregate) =>
        FineGrainedTiming.Sample(name, sampleSuccess, sampleAggregate)
      }.toVector
    )

  private def untimedInvocation(
      id: Long,
      method: String,
      success: Boolean,
      samples: (String, Boolean, FineGrainedTiming.Aggregate)*
  ): FineGrainedTiming.Invocation =
    FineGrainedTiming.Invocation(
      id,
      method,
      success,
      None,
      samples.map { case (name, sampleSuccess, sampleAggregate) =>
        FineGrainedTiming.Sample(name, sampleSuccess, sampleAggregate)
      }.toVector
    )

  private val commands =
    Vector(
      FineGrainedTimingHierarchy.Command(
        "command-1",
        order = 0,
        theory = "T1",
        proof = Some("p1"),
        Vector(
          invocation(
            1L,
            "profile",
            success = true,
            elapsed = 10L,
            ("branch", true, aggregate(2L, 8L))
          ),
          invocation(
            2L,
            "profile",
            success = false,
            elapsed = 2L,
            ("branch", false, aggregate(1L, 2L))
          )
        )
      ),
      FineGrainedTimingHierarchy.Command(
        "command-2",
        order = 1,
        theory = "T2",
        proof = Some("p2"),
        Vector(
          invocation(
            3L,
            "profile",
            success = true,
            elapsed = 20L,
            ("branch", true, aggregate(3L, 12L))
          )
        )
      ),
      FineGrainedTimingHierarchy.Command(
        "command-3",
        order = 2,
        theory = "T3",
        proof = Some("p3"),
        Vector(
          invocation(
            4L,
            "empty_profile",
            success = true,
            elapsed = 30L
          )
        )
      ),
      FineGrainedTimingHierarchy.Command(
        "command-4",
        order = 3,
        theory = "T4",
        proof = Some("p4"),
        Vector(
          invocation(
            5L,
            "slow_profile",
            success = true,
            elapsed = 1000L
          ),
          untimedInvocation(
            6L,
            "unknown_profile",
            success = true,
            ("branch", true, aggregate(1L, 4L))
          )
        )
      )
    )

  private def testAggregateIndex(): Unit = {
    val index =
      FineGrainedTimingHierarchy.build(
        commands,
        FineGrainedTimingHierarchy.Aggregate,
        nameFilter = "bran",
        showSuccess = true,
        showFailure = false
      )
    requireThat(index.signals.length == 1, s"unexpected signals: ${index.signals}")
    val signal = index.signals.head
    requireThat(signal.signal == FineGrainedTimingHierarchy.Signal("branch", true),
      s"unexpected signal ${signal.signal}")
    requireThat(signal.aggregate.count == 6L,
      s"aggregate count should merge commands: ${signal.aggregate.count}")
    requireThat(signal.commands.map(_.command.theory) ==
      Vector("T1", "T2", "T4"),
      s"command order was not retained: ${signal.commands}")
  }

  private def testCallsAndIndexMerge(): Unit = {
    val index =
      FineGrainedTimingHierarchy.build(
        commands,
        FineGrainedTimingHierarchy.Calls,
        nameFilter = "",
        showSuccess = true,
        showFailure = true
      )
    val signal =
      index.signals.find(_.signal ==
        FineGrainedTimingHierarchy.Signal("profile", true))
        .getOrElse(sys.error(s"missing profile signal: ${index.signals}"))
    requireThat(signal.commands.length == 2,
      s"both successful commands should remain indexed: ${signal.commands}")
    requireThat(signal.commands.forall(_.invocations.length == 1),
      s"call details were not retained: ${signal.commands}")
    val empty =
      index.signals.find(_.signal ==
        FineGrainedTimingHierarchy.Signal("empty_profile", true))
        .getOrElse(sys.error(s"missing zero-sample call: ${index.signals}"))
    requireThat(
      empty.aggregate.count == 1L &&
        empty.aggregate.timing.elapsedMicros == 30L &&
        empty.commands.head.invocations.length == 1,
      s"zero-sample call was not aggregated from invocation timing: $empty")
    requireThat(
      index.signals.head.signal ==
        FineGrainedTimingHierarchy.Signal("slow_profile", true),
      s"Calls groups were not sorted by invocation timing: ${index.signals}")
    val unknown =
      index.signals.find(_.signal ==
        FineGrainedTimingHierarchy.Signal("unknown_profile", true))
        .getOrElse(sys.error(s"missing unknown-timing signal: ${index.signals}"))
    requireThat(
      unknown.aggregate.count == 0L &&
        unknown.aggregate.timing.elapsedMicros == 0L &&
        unknown.aggregate.histogram.isEmpty &&
        unknown.commands.head.invocations.length == 1,
      s"unknown timings were included in Calls aggregates: $unknown")

    val left =
      FineGrainedTimingHierarchy.build(
        commands.take(1),
        FineGrainedTimingHierarchy.Calls,
        nameFilter = "",
        showSuccess = true,
        showFailure = true
      )
    val right =
      FineGrainedTimingHierarchy.build(
        commands.drop(1),
        FineGrainedTimingHierarchy.Calls,
        nameFilter = "",
        showSuccess = true,
        showFailure = true
      )
    val merged = FineGrainedTimingHierarchy.mergeIndexes(Vector(left, right))
    requireThat(merged.signals.map(_.signal).toSet ==
      index.signals.map(_.signal).toSet,
      s"merged index lost signals: $merged")
    val mergedProfile =
      merged.signals.find(_.signal ==
        FineGrainedTimingHierarchy.Signal("profile", true))
        .getOrElse(sys.error(s"merged profile signal is missing: $merged"))
    requireThat(
      mergedProfile.aggregate.count == signal.aggregate.count &&
        mergedProfile.commands.length == signal.commands.length,
      s"merged index did not combine matching signals: $mergedProfile"
    )
  }

  def main(_args: Array[String]): Unit = {
    testAggregateIndex()
    testCallsAndIndexMerge()
    println("FineGrainedTimingHierarchyTest: all tests passed")
  }
}
