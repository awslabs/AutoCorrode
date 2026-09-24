/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import scala.collection.mutable

import isabelle.Exn

object FineGrainedTimingHierarchy {
  sealed trait View
  case object Calls extends View
  case object Aggregate extends View

  final case class Signal(name: String, success: Boolean)

  final case class Command[A](
      value: A,
      order: Int,
      theory: String,
      proof: Option[String],
      invocations: Vector[FineGrainedTiming.Invocation]
  )

  final case class VisibleInvocation(
      index: Int,
      invocation: FineGrainedTiming.Invocation
  )

  final case class CommandData[A](
      command: Command[A],
      aggregate: FineGrainedTiming.Aggregate,
      invocations: Vector[VisibleInvocation]
  )

  final case class SignalData[A](
      signal: Signal,
      aggregate: FineGrainedTiming.Aggregate,
      commands: Vector[CommandData[A]]
  )

  final case class Index[A](signals: Vector[SignalData[A]])

  def build[A](
      commands: Vector[Command[A]],
      view: View,
      nameFilter: String,
      showSuccess: Boolean,
      showFailure: Boolean
  ): Index[A] = {
    val bySignal =
      mutable.LinkedHashMap.empty[Signal, mutable.ArrayBuffer[CommandData[A]]]
    val normalizedFilter = nameFilter.trim.toLowerCase(java.util.Locale.ROOT)

    def signalEnabled(signal: Signal): Boolean =
      (if (signal.success) showSuccess else showFailure) &&
        (normalizedFilter.isEmpty ||
          signal.name.toLowerCase(java.util.Locale.ROOT)
            .contains(normalizedFilter))

    def add(signal: Signal, data: CommandData[A]): Unit =
      if (signalEnabled(signal)) {
        bySignal.getOrElseUpdate(signal, mutable.ArrayBuffer.empty) += data
      }

    commands.foreach { command =>
      Exn.Interrupt.expose()
      view match {
        case Calls =>
          command.invocations.zipWithIndex
            .groupBy { case (invocation, _) =>
              Signal(invocation.method, invocation.success)
            }
            .foreach { case (signal, indexedInvocations) =>
              val aggregate =
                indexedInvocations.iterator
                  .flatMap { case (invocation, _) =>
                    invocation.samples.iterator.map(_.aggregate)
                  }
                  .reduceOption(_ + _)
                  .getOrElse(EmptyAggregate)
              add(
                signal,
                CommandData(
                  command,
                  aggregate,
                  indexedInvocations.iterator.map {
                    case (invocation, index) =>
                      VisibleInvocation(index, invocation)
                  }.toVector
                )
              )
            }

        case Aggregate =>
          FineGrainedTiming.aggregate(command.invocations)
            .foreach { case (key, aggregate) =>
              add(
                Signal(key.name, key.success),
                CommandData(
                  command,
                  aggregate,
                  Vector.empty
                )
              )
            }
      }
    }

    val signals =
      bySignal.iterator.flatMap { case (signal, commandBuffer) =>
        val signalCommands = commandBuffer.toVector.sortBy(_.command.order)
        merge(signalCommands.iterator.map(_.aggregate))
          .map(SignalData(signal, _, signalCommands))
      }.toVector.sortBy(data => -data.aggregate.timing.elapsedMicros)

    Index(signals)
  }

  def mergeIndexes[A](indexes: Vector[Index[A]]): Index[A] = {
    val bySignal =
      mutable.LinkedHashMap.empty[
        Signal,
        (FineGrainedTiming.Aggregate, mutable.ArrayBuffer[CommandData[A]])
      ]
    indexes.foreach { index =>
      index.signals.foreach { signalData =>
        bySignal.get(signalData.signal) match {
          case Some((aggregate, commands)) =>
            commands ++= signalData.commands
            bySignal.update(
              signalData.signal,
              (aggregate + signalData.aggregate, commands)
            )
          case None =>
            bySignal.update(
              signalData.signal,
              (
                signalData.aggregate,
                mutable.ArrayBuffer.from(signalData.commands)
              )
            )
        }
      }
    }
    Index(
      bySignal.iterator.map { case (signal, (aggregate, commands)) =>
        SignalData(signal, aggregate, commands.toVector)
      }.toVector.sortBy(data => -data.aggregate.timing.elapsedMicros)
    )
  }

  def merge(
      aggregates: Iterator[FineGrainedTiming.Aggregate]
  ): Option[FineGrainedTiming.Aggregate] =
    aggregates.reduceOption(_ + _)

  private val EmptyAggregate =
    FineGrainedTiming.Aggregate(
      count = 0L,
      timing = FineGrainedTiming.Timing(0L, 0L, 0L),
      minElapsedMicros = 0L,
      maxElapsedMicros = 0L,
      histogram = Map.empty
    )
}
