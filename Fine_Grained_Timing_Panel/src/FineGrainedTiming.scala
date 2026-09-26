/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle.{Markup, Properties, Value, XML, YXML}

object FineGrainedTiming {
  val ReportMarkup = "fine_grained_timing"
  val EntryMarkup = "fine_grained_timing_entry"
  val BucketMarkup = "fine_grained_timing_bucket"
  val SchemaVersion = 2
  val LegacySchemaVersion = 1

  final case class Timing(elapsedMicros: Long, cpuMicros: Long, gcMicros: Long) {
    def +(other: Timing): Timing =
      Timing(
        elapsedMicros + other.elapsedMicros,
        cpuMicros + other.cpuMicros,
        gcMicros + other.gcMicros
      )
  }

  final case class Aggregate(
      count: Long,
      timing: Timing,
      minElapsedMicros: Long,
      maxElapsedMicros: Long,
      histogram: Map[Int, Long]
  ) {
    def +(other: Aggregate): Aggregate =
      if (count == 0L) other
      else if (other.count == 0L) this
      else {
      val mergedHistogram =
        (histogram.keySet ++ other.histogram.keySet).iterator.map { bucket =>
          bucket -> (histogram.getOrElse(bucket, 0L) + other.histogram.getOrElse(bucket, 0L))
        }.toMap
      Aggregate(
        count = count + other.count,
        timing = timing + other.timing,
        minElapsedMicros = math.min(minElapsedMicros, other.minElapsedMicros),
        maxElapsedMicros = math.max(maxElapsedMicros, other.maxElapsedMicros),
        histogram = mergedHistogram
      )
      }

    def averageElapsedMicros: Double =
      if (count == 0L) 0.0 else timing.elapsedMicros.toDouble / count.toDouble

    def percentileElapsedMicros(fraction: Double): Long = {
      if (count == 0L || histogram.isEmpty) 0L
      else {
        val bounded = math.max(0.0, math.min(1.0, fraction))
        val target = math.max(1L, math.ceil(bounded * count.toDouble).toLong)
        var accumulated = 0L
        val bucket = histogram.toSeq.sortBy(_._1).collectFirst {
          case (index, bucketCount) if {
            accumulated += bucketCount
            accumulated >= target
          } => index
        }.getOrElse(histogram.keys.max)
        bucketUpperBoundMicros(bucket)
      }
    }
  }

  final case class Sample(name: String, success: Boolean, aggregate: Aggregate)

  final case class Invocation(
      id: Long,
      method: String,
      success: Boolean,
      timing: Option[Timing],
      samples: Vector[Sample],
      raised: Boolean = false
  ) {
    /* Nested samples may overlap, so their aggregate times cannot be added to
       obtain the invocation's wall time. New schema 2 producers carry an
       explicit outer timing; older reports leave this empty. */
    def totalTiming: Option[Timing] = timing

    def totalElapsedMicros: Long =
      totalTiming.map(_.elapsedMicros).getOrElse(0L)
  }

  private def sampleCount(invocation: Invocation): Long =
    invocation.samples.iterator.map(_.aggregate.count).sum

  private def timingExtent(invocation: Invocation): (Long, Long, Long) =
    invocation.timing match {
      case Some(timing) =>
        (timing.elapsedMicros, timing.cpuMicros, timing.gcMicros)
      case None => (-1L, -1L, -1L)
    }

  private def laterTiming(
      candidate: Invocation,
      existing: Invocation
  ): Boolean = {
    val (candidateElapsed, candidateCpu, candidateGc) =
      timingExtent(candidate)
    val (existingElapsed, existingCpu, existingGc) =
      timingExtent(existing)
    candidateElapsed > existingElapsed ||
      candidateElapsed == existingElapsed &&
        (candidateCpu > existingCpu ||
          candidateCpu == existingCpu && candidateGc > existingGc)
  }

  private def supersedes(candidate: Invocation, existing: Invocation): Boolean = {
    val candidateSamples = sampleCount(candidate)
    val existingSamples = sampleCount(existing)
    def outcomeRank(invocation: Invocation): Int =
      if (invocation.raised) 2 else if (invocation.success) 1 else 0
    candidateSamples > existingSamples ||
      (candidateSamples == existingSamples &&
        (outcomeRank(candidate) > outcomeRank(existing) ||
          outcomeRank(candidate) == outcomeRank(existing) &&
            laterTiming(candidate, existing)))
  }

  /* A profile re-reports as its caller pulls more results. Every report of one
     invocation carries the same id and a complete snapshot. Keep the snapshot
     with the most samples, then the terminal outcome and outer timing. */
  def latestPerInvocation(
      invocations: Iterable[Invocation]
  ): Vector[Invocation] =
    invocations.iterator
      .foldLeft(Map.empty[Long, Invocation]) { (result, invocation) =>
        result.updatedWith(invocation.id) {
          case Some(existing) if !supersedes(invocation, existing) =>
            Some(existing)
          case _ => Some(invocation)
        }
      }
      .values
      .toVector
      .sortBy(_.id)

  final case class SampleKey(name: String, success: Boolean)

  def aggregate(invocations: Iterable[Invocation]): Map[SampleKey, Aggregate] =
    invocations.iterator
      .flatMap(_.samples)
      .foldLeft(Map.empty[SampleKey, Aggregate]) { (result, sample) =>
        val key = SampleKey(sample.name, sample.success)
        result.updatedWith(key) {
          case Some(existing) => Some(existing + sample.aggregate)
          case None => Some(sample.aggregate)
        }
      }

  def decode(tree: XML.Tree): Option[Invocation] =
    tree match {
      case XML.Elem(Markup(ReportMarkup, properties), body) =>
        for {
          version <- intProperty(properties, "version")
          if version == LegacySchemaVersion || version == SchemaVersion
          invocation <- longProperty(properties, "invocation")
          method <- Properties.get(properties, "method")
          success <- booleanProperty(properties, "success")
          timing <- decodeInvocationTiming(version, properties)
          samples <- decodeSamples(normalizeBody(body))
        } yield Invocation(
          id = invocation,
          method = method,
          success = success,
          timing = timing,
          samples = samples,
          raised = Properties.get(properties, "raised")
            .flatMap(Value.Boolean.unapply)
            .getOrElse(false)
        )
      case _ => None
    }

  private def decodeInvocationTiming(
      version: Int,
      properties: Properties.T
  ): Option[Option[Timing]] =
    {
      val names = List("elapsed_us", "cpu_us", "gc_us")
      val present = names.count(name => Properties.get(properties, name).isDefined)
      if (version == SchemaVersion && present == 0) Some(None)
      else if (present != names.length) None
      else {
        for {
          elapsed <- longProperty(properties, "elapsed_us")
          cpu <- longProperty(properties, "cpu_us")
          gc <- longProperty(properties, "gc_us")
        } yield Some(Timing(elapsed, cpu, gc))
      }
    }

  private def normalizeBody(body: XML.Body): XML.Body =
    body match {
      case List(XML.Text(text)) if YXML.detect(text) =>
        try YXML.parse_body(YXML.Source(text))
        catch { case _: XML.Error => body }
      case _ => body
    }

  private def decodeSamples(body: XML.Body): Option[Vector[Sample]] = {
    val decoded = body.map(decodeSample)
    if (decoded.forall(_.isDefined)) Some(decoded.flatten.toVector)
    else None
  }

  private def decodeSample(tree: XML.Tree): Option[Sample] =
    tree match {
      case XML.Elem(Markup(EntryMarkup, properties), body) =>
        for {
          name <- Properties.get(properties, "name")
          success <- booleanProperty(properties, "success")
          count <- longProperty(properties, "count")
          if count > 0L
          elapsed <- longProperty(properties, "elapsed_us")
          cpu <- longProperty(properties, "cpu_us")
          gc <- longProperty(properties, "gc_us")
          minimum <- longProperty(properties, "min_elapsed_us")
          maximum <- longProperty(properties, "max_elapsed_us")
          histogram <- decodeHistogram(body)
          if histogram.values.sum == count
        } yield Sample(
          name = name,
          success = success,
          aggregate = Aggregate(
            count = count,
            timing = Timing(elapsed, cpu, gc),
            minElapsedMicros = minimum,
            maxElapsedMicros = maximum,
            histogram = histogram
          )
        )
      case _ => None
    }

  private def decodeHistogram(body: XML.Body): Option[Map[Int, Long]] = {
    val decoded = body.map {
      case XML.Elem(Markup(BucketMarkup, properties), Nil) =>
        for {
          bucket <- intProperty(properties, "bucket")
          if bucket >= 0
          count <- longProperty(properties, "count")
          if count > 0L
        } yield bucket -> count
      case _ => None
    }
    if (!decoded.forall(_.isDefined)) None
    else {
      val entries = decoded.flatten
      if (entries.map(_._1).distinct.length != entries.length) None
      else Some(entries.toMap)
    }
  }

  private def intProperty(properties: Properties.T, name: String): Option[Int] =
    Properties.get(properties, name).flatMap(Value.Int.unapply)

  private def longProperty(properties: Properties.T, name: String): Option[Long] =
    Properties.get(properties, name).flatMap(Value.Long.unapply)

  private def booleanProperty(
      properties: Properties.T,
      name: String
  ): Option[Boolean] =
    Properties.get(properties, name).flatMap(Value.Boolean.unapply)

  private def bucketUpperBoundMicros(bucket: Int): Long =
    if (bucket >= 62) Long.MaxValue
    else (1L << (bucket + 1)) - 1L
}
