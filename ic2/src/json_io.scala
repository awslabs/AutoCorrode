/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/json_io.scala

Newline-delimited JSON over a Unix-domain socket channel, with a pluggable
fallback sink that absorbs writes once the channel is broken.

Each side writes one JSON value per line (UTF-8). A single dedicated reader
thread parses incoming lines and hands them to consumers via a queue, so reads
can be either blocking (`read()`) or bounded (`read(timeout_ms)`) without the
SO_TIMEOUT machinery that AF_UNIX channels don't offer. Writes are serialised
through the instance monitor.

Callers need not care whether the channel is still alive: `write(...)` either
lands on the wire or — once the wire is dead (a failed write, or a `close()`)
— flows into the configured `Sink`. After the first failure the dead channel
is never retried; every later write is a pure sink-call. See `write` below.
*/

package isabelle.ic2

import isabelle._

import java.io.{BufferedReader, IOException, InputStreamReader,
  OutputStreamWriter, PrintWriter}
import java.nio.channels.{Channels, SocketChannel}
import java.nio.charset.StandardCharsets
import java.util.concurrent.{LinkedBlockingQueue, TimeUnit}


object JSON_IO {

  /** What to do with events when the channel can't take them. */
  trait Sink {
    /** Called once with the JSON value that the network rejected.
     *  `reason` describes why ("closed", "broken pipe", etc.). */
    def absorb(value: JSON.T, reason: String): Unit
  }

  /** Default — silently drop. */
  object Drop_Sink extends Sink {
    def absorb(value: JSON.T, reason: String): Unit = ()
  }

  /** Mirror absorbed events to stderr (or another `PrintWriter`-friendly
   *  stream). Useful for `-vv` mode: shows status updates that lost their
   *  client. */
  class Stderr_Sink(label: => String, stream: java.io.PrintStream = System.err)
    extends Sink {
    def absorb(value: JSON.T, reason: String): Unit = {
      // Best-effort, single-shot — never throws.
      try {
        stream.println("[" + label + " ⇒ " + reason + "] " + JSON.Format(value))
        stream.flush()
      } catch { case _: Throwable => }
    }
  }

  /** Outcome of a bounded read. `Timeout` means the deadline passed with no
   *  value; `EOF` means the channel closed. Both are sticky: once the channel
   *  is at EOF every later read returns `EOF`. */
  sealed trait Read
  final case class Value(get: JSON.T) extends Read
  case object EOF extends Read
  case object Timeout extends Read

  def apply(channel: SocketChannel, sink: Sink = Drop_Sink): JSON_IO =
    new JSON_IO(channel, sink)
}

class JSON_IO private(channel: SocketChannel, sink: JSON_IO.Sink) extends AutoCloseable {
  private val in =
    new BufferedReader(new InputStreamReader(Channels.newInputStream(channel), StandardCharsets.UTF_8))
  private val out =
    new PrintWriter(
      new OutputStreamWriter(Channels.newOutputStream(channel), StandardCharsets.UTF_8), false)

  /* incoming queue, fed by the reader thread */

  private sealed trait Incoming
  private case class In_Value(t: JSON.T) extends Incoming
  private case object In_EOF extends Incoming
  private case class In_Error(e: Throwable) extends Incoming

  private val incoming = new LinkedBlockingQueue[Incoming]()

  private val reader: Thread = {
    val t = new Thread(() => read_loop(), "json-io-reader")
    t.setDaemon(true)
    t
  }
  reader.start()

  private def read_loop(): Unit = {
    try {
      var go = true
      while (go) {
        val line = in.readLine()
        if (line == null) { incoming.put(In_EOF); go = false }
        else
          try incoming.put(In_Value(JSON.parse(line, strict = false)))
          catch { case e: Throwable => incoming.put(In_Error(e)); go = false }
      }
    } catch {
      // close() / peer reset / IO error: the channel is done — signal EOF.
      case _: Throwable => incoming.put(In_EOF)
    }
  }

  /** Turn a queued item into a `Read`, keeping terminal states sticky so that
   *  repeated reads after EOF (or a parse error) keep reporting EOF. */
  private def decode(item: Incoming): JSON_IO.Read =
    item match {
      case In_Value(t) => JSON_IO.Value(t)
      case In_EOF => incoming.put(In_EOF); JSON_IO.EOF
      case In_Error(e) => incoming.put(In_EOF); throw e
    }

  /** Read the next JSON value, blocking. Returns `None` on EOF. Throws on
   *  malformed JSON (once; the channel is then treated as at EOF). */
  def read(): Option[JSON.T] =
    decode(incoming.take()) match {
      case JSON_IO.Value(t) => Some(t)
      case _ => None
    }

  /** Read the next JSON value, waiting at most `timeout_ms`. */
  def read(timeout_ms: Long): JSON_IO.Read = {
    val item = incoming.poll(timeout_ms, TimeUnit.MILLISECONDS)
    if (item == null) JSON_IO.Timeout else decode(item)
  }

  /* write side */

  /** Channel state: once `dead`, all writes go to the sink. */
  @volatile private var _dead: Boolean = false
  @volatile private var _dead_reason: String = ""

  private def kill(reason: String): Unit = {
    if (!_dead) { _dead = true; _dead_reason = reason }
  }

  /** Write one JSON value. Always succeeds from the caller's perspective:
   *  if the channel is dead (or dies during this write), the value is
   *  forwarded to the configured `Sink`. Synchronised — safe from any
   *  thread, ordering is preserved. */
  def write(value: JSON.T): Unit = synchronized {
    if (_dead) {
      sink.absorb(value, _dead_reason)
      return
    }
    try {
      out.print(JSON.Format(value))
      out.print('\n')
      out.flush()
      if (out.checkError()) {
        kill("broken pipe")
        sink.absorb(value, _dead_reason)
      }
    } catch {
      case e: IOException =>
        kill(e.getMessage match {
          case null | "" => e.getClass.getSimpleName
          case m => m
        })
        sink.absorb(value, _dead_reason)
    }
  }

  /** Channel is "live" iff no failed write has occurred and it isn't closed. */
  def is_alive: Boolean = !_dead && channel.isOpen
  def is_dead: Boolean  = !is_alive

  override def close(): Unit = {
    kill("closed")
    try { channel.close() } catch { case _: Throwable => }
  }
}
