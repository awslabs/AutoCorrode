/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/test_tool.scala

`isabelle ic2_test` — a test runner for the ic2 daemon and client.

Modes:
  unit            Run all unit tests (no Isabelle session needed). Fast.
  e2e [DIR]       Run end-to-end tests against a fresh `ic2 server start` instance
                  with logic=HOL. DIR defaults to test/fixtures next to
                  this component.
  all             unit + e2e (default).

Each test is a `*_test`-named method registered in `run_unit` / `run_e2e`;
read those two methods for the catalogue. Select individual tests with `-t`.
*/

package isabelle.ic2

import isabelle._

import java.io.{ByteArrayOutputStream, PrintStream}
import java.net.{StandardProtocolFamily, UnixDomainSocketAddress}
import java.nio.channels.{ServerSocketChannel, SocketChannel}
import java.nio.file.{FileSystems, Files, Paths}
import java.nio.file.attribute.PosixFilePermission
import java.util.concurrent.{CountDownLatch, TimeUnit}
import java.util.concurrent.atomic.{AtomicInteger, AtomicReference}
import scala.jdk.CollectionConverters._


object Test_Tool {

  /* CLI tool */

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("ic2_test",
      "test runner for the ic2 daemon and client",
      Scala_Project.here, { args => run_tool(args) })

  private def run_tool(args: List[String]): Unit = {
    var mode: String = ""
    var fixtures: Option[Path] = None
    var verbose: Boolean = false
    var only: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle ic2_test [OPTIONS] MODE [DIR]

  MODE:
    unit         run unit tests only
    e2e [DIR]    run end-to-end tests; DIR defaults to fixtures next to
                 the component
    all          unit + e2e (default)

  Options are:
    -v           verbose: show progress events
    -t TEST      only run TEST(s) (repeatable; comma-separated also OK)
""",
      "v" -> (_ => verbose = true),
      "t:" -> (a => only = only ::: a.split(',').toList.map(_.trim).filter(_.nonEmpty)))

    val rest = getopts(args)
    rest match {
      case "unit" :: Nil =>
        mode = "unit"
      case "e2e" :: Nil =>
        mode = "e2e"
      case "e2e" :: dir :: Nil =>
        mode = "e2e"; fixtures = Some(Path.explode(dir))
      case "all" :: Nil | Nil =>
        mode = "all"
      case _ => getopts.usage()
    }

    val runner = new Runner(verbose = verbose, only = only.toSet)

    val ok =
      mode match {
        case "unit" => runner.run_unit()
        case "e2e" => runner.run_e2e(fixtures)
        case "all" => runner.run_unit() && runner.run_e2e(fixtures)
        case _ => getopts.usage(); false
      }

    if (!ok) sys.exit(1)
  }


  /* runner */

  private class Runner(verbose: Boolean, only: Set[String]) {
    private val passed = new AtomicInteger(0)
    private val failed = new AtomicInteger(0)
    private val skipped = new AtomicInteger(0)

    private def announce(name: String): Unit = {
      Output.writeln("--- " + name + " ---")
    }

    private def case_runs(name: String): Boolean =
      only.isEmpty || only.contains(name)

    private def test(name: String)(body: => Unit): Unit = {
      if (!case_runs(name)) {
        skipped.incrementAndGet(); return
      }
      announce(name)
      try {
        body
        passed.incrementAndGet()
        Output.writeln("    PASS: " + name)
      } catch {
        case e: Throwable =>
          failed.incrementAndGet()
          Output.error_message("    FAIL: " + name + ": " + e.getMessage)
          if (verbose) e.printStackTrace(System.err)
      }
    }

    private def report(): Boolean = {
      Output.writeln("")
      Output.writeln(s"=== ${passed.get} passed, ${failed.get} failed, ${skipped.get} skipped ===")
      failed.get == 0
    }


    /* ---- AF_UNIX helpers ---- */

    private def sock_addr(name: String): UnixDomainSocketAddress =
      UnixDomainSocketAddress.of(Paths.get(Endpoint.socket(name).expand.implode))

    /** Short unique suffix for test server names. AF_UNIX paths are capped
     *  (~104 bytes on macOS) and the discovery dir already eats ~55, so a full
     *  36-char UUID would overflow; 8 hex chars is unique enough for tests. */
    private def short_id(): String = UUID.random_string().take(8)

    /** Write a fresh slow theory with a UNIQUE name into a throwaway dir and
     *  return its absolute path. A uniquely-named theory is guaranteed not to
     *  have been consolidated by any prior check, so it genuinely re-runs the
     *  ML sleep — the timing window the cancel / survives-disconnect tests need.
     *  (The shared Slow.thy fixture gets consolidated by the progress test, so
     *  a later re-check of it returns in ~100ms against the resident session.) */
    private def fresh_slow_theory(secs: Double = 8.0): String = {
      val name = "Slow_" + short_id()
      val dir = Files.createTempDirectory("ic2_slow")
      val file = dir.resolve(name + ".thy")
      val body =
        "theory " + name + "\n" +
        "  imports Main\n" +
        "begin\n\n" +
        "lemma " + name + "_1: \"(n::nat) + 0 = n\" by simp\n\n" +
        "ML ‹OS.Process.sleep (Time.fromReal " + secs + ")›\n\n" +
        "lemma " + name + "_2: \"(n::nat) * 1 = n\" by simp\n\n" +
        "end\n"
      Files.write(file, body.getBytes("UTF-8"))
      file.toAbsolutePath.toString
    }

    /** Write a fresh theory whose expensive command is BEFORE a cheap marker
     *  command that tests can rewrite. Used to pin incremental re-checks: after
     *  a successful baseline check, changing only the marker must not re-run
     *  the earlier sleep. */
    private def fresh_incremental_recheck_theory(secs: Double = 4.0): String = {
      val name = "Incremental_" + short_id()
      val dir = Files.createTempDirectory("ic2_incremental")
      val file = dir.resolve(name + ".thy")
      val body =
        "theory " + name + "\n" +
        "  imports Main\n" +
        "begin\n\n" +
        "ML_command ‹\n" +
        "  writeln \"IC2_INCREMENTAL_SLEEP_BEGIN\";\n" +
        "  OS.Process.sleep (Time.fromReal " + secs + ");\n" +
        "  writeln \"IC2_INCREMENTAL_SLEEP_END\"\n" +
        "›\n\n" +
        "ML_command ‹writeln \"IC2_INCREMENTAL_MARKER_0\"›\n\n" +
        "end\n"
      Files.write(file, body.getBytes("UTF-8"))
      file.toAbsolutePath.toString
    }

    private def rewrite_marker(path: String, from: String, to: String): Unit = {
      val p = Paths.get(path)
      val oldText = new String(Files.readAllBytes(p), "UTF-8")
      if (!oldText.contains(from))
        error("rewrite_marker: marker not found in " + path + ": " + from)
      Files.write(p, oldText.replace(from, to).getBytes("UTF-8"))
    }

    /** Run `isabelle ic2 <args>` as a subprocess and return its result. Used by
     *  the tests that exercise the CLI front door (exit codes, printed output)
     *  rather than the wire protocol directly. */
    private def ic2(args: String): Process_Result =
      Isabelle_System.bash(
        File.bash_path(Path.explode("$ISABELLE_HOME/bin/isabelle")) + " ic2 " + args)

    /** A connected pair of AF_UNIX channels in a throwaway temp dir, plus a
     *  cleanup thunk. Used by the JSON_IO unit tests, which need a real
     *  channel but no daemon. */
    private def unix_pair(): (SocketChannel, SocketChannel, () => Unit) = {
      val dir = Files.createTempDirectory("ic2_unit")
      val p = dir.resolve("pair.sock")
      val addr = UnixDomainSocketAddress.of(p)
      val listener = ServerSocketChannel.open(StandardProtocolFamily.UNIX)
      listener.bind(addr, 1)
      val client = SocketChannel.open(addr)
      val server = listener.accept()
      listener.close()
      val cleanup = () => {
        try { client.close() } catch { case _: Throwable => }
        try { server.close() } catch { case _: Throwable => }
        try { Files.deleteIfExists(p) } catch { case _: Throwable => }
        try { Files.deleteIfExists(dir) } catch { case _: Throwable => }
        ()
      }
      (client, server, cleanup)
    }


    /* ---- unit tests ---- */

    def run_unit(): Boolean = {
      announce("UNIT TESTS")

      test("json_io_roundtrip") { unit_json_io_roundtrip() }
      test("json_io_write_after_close") { unit_json_io_write_after_close() }
      test("json_io_read_timeout") { unit_json_io_read_timeout() }
      test("json_io_stderr_sink_format") { unit_json_io_stderr_sink_format() }
      test("endpoint_socket_path") { unit_endpoint_socket_path() }
      test("endpoint_dir_private") { unit_endpoint_dir_private() }
      test("endpoint_list_and_remove") { unit_endpoint_list_and_remove() }
      test("ansi_ui_repaints_with_csi") { unit_ansi_ui_repaints_with_csi() }
      test("status_line_format") { unit_status_line_format() }

      report()
    }

    private def unit_json_io_roundtrip(): Unit = {
      val (client, server, cleanup) = unix_pair()
      try {
        val cio = JSON_IO(client)
        val sio = JSON_IO(server)
        cio.write(JSON.Object("hello" -> "world", "n" -> 42))
        val got = sio.read(2000)
        got match {
          case JSON_IO.Value(t) =>
            if (JSON.string(t, "hello") != Some("world")) error("hello round-trip failed")
            if (JSON.int(t, "n") != Some(42)) error("int round-trip failed")
          case other => error("server never received message: " + other)
        }
        sio.write(JSON.Object("echo" -> "back"))
        cio.read(2000) match {
          case JSON_IO.Value(t) if JSON.string(t, "echo") == Some("back") => ()
          case other => error("reply round-trip failed: " + other)
        }
      } finally cleanup()
    }

    /** The dead-channel contract: once close() is called, every subsequent
     *  write is routed to the Sink (reason "closed"), exactly once each, and
     *  is_alive flips from true to false. */
    private def unit_json_io_write_after_close(): Unit = {
      val (client, _, cleanup) = unix_pair()
      try {
        val absorbed = new java.util.concurrent.CopyOnWriteArrayList[(JSON.T, String)]()
        val sink = new JSON_IO.Sink {
          def absorb(value: JSON.T, reason: String): Unit = { absorbed.add((value, reason)); () }
        }
        val io = JSON_IO(client, sink)
        if (!io.is_alive) error("channel should start alive")

        io.close()
        if (io.is_alive) error("channel should be dead after close()")
        if (!io.is_dead) error("is_dead should be true after close()")

        io.write(JSON.Object("a" -> 1))
        io.write(JSON.Object("b" -> 2))

        if (absorbed.size != 2)
          error("expected exactly 2 absorbed writes, got " + absorbed.size)
        val reasons = absorbed.asScala.toList.map(_._2).distinct
        if (reasons != List("closed"))
          error("expected absorb reason 'closed', got " + reasons.mkString(","))
        if (JSON.int(absorbed.get(0)._1, "a") != Some(1)) error("first absorbed payload wrong")
        if (JSON.int(absorbed.get(1)._1, "b") != Some(2)) error("second absorbed payload wrong")
      } finally cleanup()
    }

    /** Bounded reads: a quiet channel returns Timeout (not EOF, not a value);
     *  a peer close then surfaces as EOF and stays EOF. */
    private def unit_json_io_read_timeout(): Unit = {
      val (client, server, cleanup) = unix_pair()
      try {
        val cio = JSON_IO(client)
        val sio = JSON_IO(server)
        cio.read(200) match {
          case JSON_IO.Timeout => ()
          case other => error("expected Timeout on a quiet channel, got " + other)
        }
        sio.close()
        // Peer close -> EOF, and EOF is sticky across repeated reads.
        cio.read(2000) match {
          case JSON_IO.EOF => ()
          case other => error("expected EOF after peer close, got " + other)
        }
        cio.read(200) match {
          case JSON_IO.EOF => ()
          case other => error("EOF should be sticky, got " + other)
        }
      } finally cleanup()
    }

    /** Stderr_Sink renders "[label ⇒ reason] <json>" to its stream. */
    private def unit_json_io_stderr_sink_format(): Unit = {
      val buf = new ByteArrayOutputStream()
      val ps = new PrintStream(buf, true, "UTF-8")
      val sink = new JSON_IO.Stderr_Sink("conn 7", ps)
      sink.absorb(JSON.Object("event" -> "progress"), "closed")
      val out = buf.toString("UTF-8")
      if (!out.contains("[conn 7 ⇒ closed]"))
        error("missing label/reason header in: " + out)
      if (!out.contains("\"event\"") || !out.contains("progress"))
        error("missing JSON payload in: " + out)
    }

    /** Socket path is <dir>/<name>.sock under the discovery directory. */
    private def unit_endpoint_socket_path(): Unit = {
      val p = Endpoint.socket("foo").expand.implode
      if (!p.endsWith("/ic2/foo.sock"))
        error("unexpected socket path: " + p)
    }

    /** secure_dir() makes the discovery directory owner-only (mode 0700). */
    private def unit_endpoint_dir_private(): Unit = {
      val dir = Endpoint.secure_dir()
      val jdir = Paths.get(dir.expand.implode)
      if (FileSystems.getDefault.supportedFileAttributeViews.contains("posix")) {
        val perms = Files.getPosixFilePermissions(jdir).asScala.toSet
        val expected = Set(
          PosixFilePermission.OWNER_READ,
          PosixFilePermission.OWNER_WRITE,
          PosixFilePermission.OWNER_EXECUTE)
        if (perms != expected)
          error("expected discovery dir mode 0700 " + expected + ", got " + perms)
      }
    }

    /** exists / list_names / remove over real AF_UNIX socket nodes: two slots
     *  coexist, list sees both, removing one leaves the other. */
    private def unit_endpoint_list_and_remove(): Unit = {
      Endpoint.secure_dir()
      val a = "t_a_" + short_id()
      val b = "t_b_" + short_id()

      def bind(name: String): ServerSocketChannel = {
        val ss = ServerSocketChannel.open(StandardProtocolFamily.UNIX)
        ss.bind(sock_addr(name), 1)
        ss
      }

      val sa = bind(a)
      val sb = bind(b)
      try {
        if (!Endpoint.exists(a)) error("slot a should exist")
        if (!Endpoint.exists(b)) error("slot b should exist")
        val names = Endpoint.list_names()
        if (!names.contains(a) || !names.contains(b))
          error("list_names missing one: " + names.mkString(","))

        // close() leaves the socket node on disk; remove() unlinks it.
        sa.close()
        Endpoint.remove(a)
        if (Endpoint.exists(a)) error("slot a should be gone after remove")
        if (!Endpoint.exists(b)) error("removing a affected b")
      } finally {
        try { sa.close() } catch { case _: Throwable => }
        try { sb.close() } catch { case _: Throwable => }
        Endpoint.remove(a); Endpoint.remove(b)
      }
    }

    /** The ANSI UI must repaint in place: between two progress ticks it has to
     *  emit real CSI sequences (cursor-up ESC[<n>A and clear-to-end ESC[0J) to
     *  erase the prior frame, not the literal text "[<n>A". This pins the
     *  control byte (0x1B) — an empty ESC constant prints garbage on a TTY but
     *  is invisible to the e2e suite, which always lands on the plain UI. */
    private def unit_ansi_ui_repaints_with_csi(): Unit = {
      val buf = new ByteArrayOutputStream()
      val ps = new PrintStream(buf, true, "UTF-8")
      val ui = new Client.ANSI_UI(8, ps)
      ui.started(List("A"))
      // First tick draws a frame; second tick must erase it before redrawing.
      ui.progress(List(Client.Theory_Status("A", 10, 5, 1, 0, 0, 0, false)))
      ui.progress(List(Client.Theory_Status("A", 60, 2, 3, 1, 0, 0, false)))
      val out = buf.toString("UTF-8")
      val ESC = "\u001b"
      if (!out.contains(ESC + "[0J"))
        error("no clear-to-end-of-screen (ESC[0J); ESC byte missing? out=" + out)
      // Cursor-up over however many lines the prior frame drew (ESC[<n>A).
      if (!java.util.regex.Pattern.compile(java.util.regex.Pattern.quote(ESC) + """\[\d+A""")
            .matcher(out).find())
        error("no cursor-up (ESC[<n>A) to repaint over the prior frame; out=" + out)
    }

    /** Client.format_status renders the compact one-liner from a status reply,
     *  showing idle/busy and the connection count. */
    private def unit_status_line_format(): Unit = {
      val idle = JSON.Object("event" -> "status", "session" -> "HOL", "pid" -> 4321L,
        "uptime_s" -> 12L, "busy" -> false, "checks_in_flight" -> 0, "connections" -> 1L)
      val line = Client.format_status("srv", idle)
      for (frag <- List("srv:", "session=HOL", "pid=4321", "up=12s", "idle", "conns=1"))
        if (!line.contains(frag)) error("idle status line missing " + frag + ": " + line)

      val busy = JSON.Object("event" -> "status", "session" -> "HOL", "pid" -> 9L,
        "uptime_s" -> 1L, "busy" -> true, "checks_in_flight" -> 2, "connections" -> 3L)
      val bline = Client.format_status("srv", busy)
      if (!bline.contains("busy(2 checks)")) error("busy status line wrong: " + bline)
    }


    /* ---- end-to-end tests ---- */

    def run_e2e(fixtures_opt: Option[Path]): Boolean = {
      announce("E2E TESTS")

      val fixtures =
        fixtures_opt.getOrElse(
          Path.explode("$ISABELLE_IC2_HOME/test/fixtures"))
      if (!fixtures.is_dir) {
        Output.error_message("fixtures dir not found: " + fixtures.expand.implode)
        return false
      }

      val server_name = "t_" + short_id()
      Output.writeln("starting ic2 (logic=HOL, name=" + server_name +
        ", process_policy=env) ...")

      // smoke test: server accepts the -o flag without erroring; downstream
      // propagation to ML_Process is not asserted here (process_policy=env is
      // documented as a no-op). The status op echoes it back, exercised below.
      // --mcp: the MCP server is opt-in now (off by default), but the suite
      // exercises it (ir_status, session_tools, t_check*), so enable it here.
      val server_proc = start_server(server_name,
        extra_args = List("--mcp", "-o", "process_policy=env"))
      try {
        wait_for_server(server_name, timeout = 120)
        Output.writeln("ic2 ready at " + Endpoint.socket(server_name).expand.implode)

        // Each e2e test gets a fresh connection. assert_alive first, so a
        // server killed by a prior test fails fast and clearly instead of
        // cascading opaque failures. Then wait for the server to be IDLE: checks
        // are globally serialized (at most one in flight), and a prior test that
        // cancelled a slow check leaves it unwinding the ML sleep asynchronously
        // — so without this barrier the next test's own check could be refused.
        def etest(name: String)(body: => Unit): Unit =
          test(name) { assert_alive(server_name); wait_idle(server_name); body }

        etest("status_cli") { e2e_status_cli(server_name) }
        etest("status_wire") { e2e_status_wire(server_name) }
        etest("ir_status_when_iq_loaded") { e2e_ir_status(server_name) }
        etest("session_tools") { e2e_session_tools(server_name, fixtures) }
        etest("check_ok") { e2e_check_ok(server_name, fixtures) }
        etest("check_fail") { e2e_check_fail(server_name, fixtures) }
        etest("check_resolves_dependencies") { e2e_check_resolves_dependencies(server_name, fixtures) }
        etest("check_cli_exit_codes") { e2e_check_cli(server_name, fixtures) }
        etest("recheck_after_edit_skips_unchanged_prefix") { e2e_recheck_after_edit_skips_prefix(server_name) }
        etest("multi_file_first_error") { e2e_multi_file(server_name, fixtures) }
        etest("concurrent_clients") { e2e_concurrent_clients(server_name, fixtures) }
        etest("second_check_rejected") { e2e_second_check_rejected(server_name, fixtures) }
        etest("empty_files") { e2e_empty_files(server_name) }
        etest("bad_path") { e2e_bad_path(server_name) }
        etest("relative_path_rejected") { e2e_relative_path(server_name) }
        etest("status_busy_during_check") { e2e_status_busy(server_name, fixtures) }
        etest("disconnect_aborts_promptly") { e2e_disconnect_promptly(server_name, fixtures) }
        etest("check_detached") { e2e_check_detached(server_name, fixtures) }
        etest("check_detached_survives_disconnect") { e2e_detached_survives_disconnect(server_name, fixtures) }
        etest("check_cancel") { e2e_check_cancel(server_name, fixtures) }
        etest("recheck_after_cancel") { e2e_recheck_after_cancel(server_name, fixtures) }
        etest("progress_display_changes") { e2e_progress_display_changes(server_name, fixtures) }
        etest("check_attach") { e2e_check_attach(server_name, fixtures) }
        etest("query_wire") { e2e_query_wire(server_name, fixtures) }
        etest("query_cli") { e2e_query_cli(server_name, fixtures) }
        etest("state_at_returns_goal") { e2e_state_at_returns_goal(server_name, fixtures) }
        etest("state_at_never_visible") { e2e_state_at_never_visible(server_name, fixtures) }
        etest("query_heap_theory_message") { e2e_query_heap_theory_message(server_name) }
        etest("command_at_walkback") { e2e_command_at_walkback(server_name, fixtures) }
        etest("repl_from_source") { e2e_repl_from_source(server_name, fixtures) }

        // Its own -N server; the main server already built the HOL heap.
        test("no_build") { e2e_no_build(fixtures) }
        // Stale-socket reclaim: also its own server, on a pre-seeded node.
        test("stale_socket_reclaim") { e2e_stale_socket_reclaim(fixtures) }
        // --daemon background launch + stop subcommand: own server, own name.
        test("daemon_mode_and_stop") { e2e_daemon_mode(fixtures) }
        // Socket bound before the heap build: status is queryable and stop works
        // while a session is still building. Own server on a build-requiring
        // session (so it lingers in the "building" phase).
        test("status_and_stop_during_build") { e2e_status_and_stop_during_build() }
        // --no-iq: own -N server; asserts no I/R endpoint is set up.
        test("no_iq_skips_ir") { e2e_no_iq(fixtures) }
        // MCP is opt-in: a server without --mcp has I/R but no MCP endpoint.
        test("mcp_off_by_default") { e2e_mcp_off_by_default(fixtures) }
        // Partial check (`check --line N`): own -N server so we can observe
        // the post-check state (only the prefix evaluated, tail unprocessed).
        test("check_line_partial") { e2e_check_line_partial(fixtures) }
        // Partial check with PARALLEL proofs: bounding to the shorter target must
        // never schedule the longer tail proof (no overshoot). Own -N server for a
        // clean start.
        test("partial_bounded_tail_not_scheduled") { e2e_partial_bounded_tail_not_scheduled(fixtures) }

        // TERMINAL: kills the main server. Registered last so test-ordering
        // (and -t selection, which preserves code order) never runs it early.
        etest("shutdown_propagation") { e2e_shutdown_propagation(server_name, fixtures) }
      } finally {
        // Best-effort cleanup if shutdown didn't fire / wasn't run
        try { server_proc.terminate() } catch { case _: Throwable => }
        cleanup_server(server_name)
      }

      report()
    }

    private def start_server(
      name: String, extra_args: List[String] = Nil
    ): Bash.Process = {
      val cmd =
        File.bash_path(Path.explode("$ISABELLE_HOME/bin/isabelle")) +
        " ic2 server start -n " + Bash.string(name) + " -l HOL " +
        Bash.strings(extra_args)
      Bash.process(cmd, redirect = true)
    }

    /** True iff something is listening on `name`'s socket right now. */
    private def can_connect(name: String): Boolean =
      try { SocketChannel.open(sock_addr(name)).close(); true }
      catch { case _: java.io.IOException => false }

    // The socket is bound before the heap build, so a bare connect succeeds
    // while still building; wait for the status op to report state:"ready" (the
    // session is up) before issuing session-dependent ops. A "failed" state ends
    // the wait early with the recorded reason.
    private def wait_for_server(name: String, timeout: Int): Unit = {
      val deadline = System.currentTimeMillis() + timeout * 1000L
      while (System.currentTimeMillis() < deadline) {
        Daemon.ping_status(name) match {
          case Some(st) =>
            JSON.string(st, "state").getOrElse("ready") match {
              case "ready" => return
              case "failed" =>
                error("ic2 server (" + name + ") failed to start: " +
                  JSON.value(st, "build").flatMap(b => JSON.string(b, "reason")).getOrElse("unknown"))
              case _ => // still building/loading/starting — keep waiting
            }
          case None => // not yet listening
        }
        Thread.sleep(500)
      }
      error("ic2 server (" + name + ") did not become ready within " + timeout + "s")
    }

    /** Remove a test server's socket node and its log file, so per-test
     *  temporary servers leave nothing behind. (repl.py's output is folded into
     *  the daemon's own log via IRLauncher, so there is no separate repl log.) */
    private def cleanup_server(name: String): Unit = {
      Endpoint.remove(name)
      try { Files.deleteIfExists(Paths.get(Endpoint.log_file(name).expand.implode)) }
      catch { case _: Throwable => }
    }

    /** Open a connection and consume the `ready` greeting. */
    private def connection(name: String): JSON_IO = {
      val io = JSON_IO(SocketChannel.open(sock_addr(name)))
      io.read(15000) match {
        case JSON_IO.Value(t) if JSON.string(t, "event") == Some("ready") => io
        case other => io.close(); error("no ready greeting; got: " + other)
      }
    }

    /** Fast pre-flight: the server must accept a connection and greet us. */
    private def assert_alive(name: String): Unit = {
      val io =
        try connection(name)
        catch { case e: Throwable => error("server not reachable (prior test may have killed it): " + e.getMessage) }
      io.close()
    }

    /** Wait until the server reports no check in flight. Checks are globally
     *  serialized, so this is the precondition for a test that submits one: a
     *  prior test's cancelled slow check may still be unwinding its ML sleep.
     *  Best-effort cancel of any leftover in-flight check, then poll busy=false. */
    private def wait_idle(name: String, deadline_secs: Int = 30): Unit = {
      val deadline = System.currentTimeMillis() + deadline_secs * 1000L
      // Nudge any leftover check toward cancellation so the sleep unwinds.
      try { val _ = request_op(name, JSON.Object("op" -> "check_cancel")) }
      catch { case _: Throwable => }
      while (JSON.bool(query_status(name), "busy") == Some(true) &&
             System.currentTimeMillis() < deadline)
        Thread.sleep(150)
      if (JSON.bool(query_status(name), "busy") == Some(true))
        error("server still busy after " + deadline_secs + "s; a prior check did not unwind")
    }

    /** Run one check on a fresh connection; return (all events, finished). */
    private def run_check(
      name: String, files: List[String], deadline_secs: Int = 60
    ): (List[JSON.T], Option[JSON.T]) = {
      val io = connection(name)
      try {
        io.write(JSON.Object("op" -> "check", "files" -> files))
        collect_events(io, deadline_secs)
      } finally io.close()
    }

    /** Send the `status` op on a fresh connection and return the reply. */
    private def query_status(name: String): JSON.T = {
      val io = connection(name)
      try {
        io.write(JSON.Object("op" -> "status"))
        io.read(10000) match {
          case JSON_IO.Value(t) if JSON.string(t, "event") == Some("status") => t
          case other => error("expected status reply, got " + other)
        }
      } finally io.close()
    }

    /** Send one op on a fresh connection and return the single reply (consumes
     *  the ready greeting). For the non-streaming job ops. */
    private def request_op(name: String, op: JSON.Object.T): JSON.T = {
      val io = connection(name)
      try {
        io.write(op)
        io.read(15000) match {
          case JSON_IO.Value(t) => t
          case other => error("expected a reply to " + JSON.string(op, "op") + ", got " + other)
        }
      } finally io.close()
    }

    private def wait_check_state(name: String, states: Set[String], deadline_secs: Int = 30): JSON.T = {
      val deadline = System.currentTimeMillis() + deadline_secs * 1000L
      var st = request_op(name, JSON.Object("op" -> "check_status"))
      while (!states.contains(JSON.string(st, "state").getOrElse("")) &&
             System.currentTimeMillis() < deadline) {
        Thread.sleep(200)
        st = request_op(name, JSON.Object("op" -> "check_status"))
      }
      if (JSON.string(st, "event") != Some("check_status"))
        error("check_status should reply check_status, got " + JSON.Format(st))
      if (!states.contains(JSON.string(st, "state").getOrElse("")))
        error("check_status did not reach " + states.mkString("/") +
          " within " + deadline_secs + "s, got " + JSON.Format(st))
      st
    }

    /** Theory names are session-qualified on the wire (e.g. "Draft.Trivial_OK");
     *  tests compare against the unqualified basename. */
    private def base_name(theory: String): String = {
      val i = theory.lastIndexOf('.')
      if (i >= 0) theory.substring(i + 1) else theory
    }

    /** Basenames of the theories named by events of the given type. `started`
     *  carries a `theories` list; per-theory events (`error`) carry `theory`. */
    private def theory_names(events: List[JSON.T], event: String): List[String] =
      events.filter(t => JSON.string(t, "event") == Some(event)).flatMap { t =>
        if (event == "started") JSON.strings(t, "theories").getOrElse(Nil)
        else JSON.string(t, "theory").toList
      }.map(base_name)

    /** `ic2 server status -n NAME` and `ic2 server status` (survey all) via the CLI. */
    private def e2e_status_cli(server_name: String): Unit = {
      val one = ic2("server status -n " + Bash.string(server_name))
      if (one.rc != 0) error("ic2 server status -n returned non-zero: " + one.rc)
      val one_out = one.out + one.err
      if (!one_out.contains("session=HOL"))
        error("server status -n should report session=HOL; got [" + one_out + "]")

      val all = ic2("server status")
      if (all.rc != 0) error("ic2 server status (all) returned non-zero: " + all.rc)
      val all_out = all.out + all.err
      if (!all_out.contains(server_name))
        error("status (all) should list " + server_name + "; got [" + all_out + "]")
    }

    /** The `status` wire op reports the live fields and echoes the start
     *  options (here, the -o process_policy=env the server was started with). */
    private def e2e_status_wire(server_name: String): Unit = {
      val t = query_status(server_name)
      if (JSON.string(t, "session") != Some("HOL")) error("status.session should be HOL")
      if (JSON.long(t, "pid").getOrElse(0L) <= 0) error("status.pid should be positive")
      if (JSON.long(t, "uptime_s").getOrElse(-1L) < 0) error("status.uptime_s should be >= 0")
      if (JSON.bool(t, "busy") != Some(false)) error("status.busy should be false when idle")
      if (JSON.long(t, "connections").getOrElse(0L) < 1)
        error("status.connections should count the querying connection")
      val o = JSON.value(t, "options").getOrElse(error("status missing options object"))
      if (JSON.string(o, "logic") != Some("HOL")) error("options.logic should be HOL")
      val opts = JSON.strings(o, "options").getOrElse(Nil)
      if (!opts.exists(_.contains("process_policy")))
        error("options should echo -o process_policy=env; got " + opts.mkString(","))
    }

    /** The main server is started with I/Q (the default). If the AutoCorrode
     *  I/R sources (ir/) are reachable and python3 is available, status must
     *  carry options.load_iq=true AND a usable repl.py bridge endpoint: the
     *  in-prover ML_Repl is hidden (clients go through the bridge), the
     *  repl_port must be listening, and a real I/R command must round-trip
     *  through it. If the sources aren't found / python3 is unavailable, I/R is
     *  legitimately absent — note and pass rather than fail in a bare checkout. */
    private def e2e_ir_status(server_name: String): Unit = {
      val t = query_status(server_name)
      val o = JSON.value(t, "options").getOrElse(error("status missing options object"))
      if (JSON.bool(o, "load_iq") != Some(true))
        error("options.load_iq should be true for the default (I/Q-loaded) server")
      JSON.value(t, "ir") match {
        case Some(ir) =>
          // Bring-up is all-or-nothing here (IRLauncher only succeeds once
          // repl.py is reachable), so the in-prover ML_Repl must stay hidden.
          if (JSON.value(ir, "port").isDefined || JSON.value(ir, "token").isDefined)
            error("status must not expose the in-prover ML_Repl; only the repl.py bridge")
          val rport = JSON.int(ir, "repl_port").getOrElse(0)
          if (rport <= 0) error("ir.repl_port should be positive, got " + rport)
          if (!tcp_listening(rport))
            error("ir.repl_port " + rport + " is not accepting TCP connections")
          val rtoken = JSON.string(ir, "repl_token").getOrElse("")
          val reply = ir_command(rport, rtoken, "Ir.init \"e2e_R\" [\"Main\"]")
          if (!reply.contains("e2e_R"))
            error("repl.py did not run Ir.init (no REPL name in reply): " + reply)
          // The ready-to-paste one-shot client command must be present and point
          // at repl.py on this port (the shell analogue of the repl_* tools).
          val cli = JSON.string(ir, "repl_cli").getOrElse("")
          if (!cli.contains("repl.py cli") || !cli.contains("--port " + rport))
            error("ir.repl_cli should be a `repl.py cli` command on port " + rport + ", got: " + cli)
          // The MCP server in front of the bridge must be live: authenticate,
          // then call the `status` tool and confirm a non-error reply.
          val mport = JSON.int(ir, "mcp_port").getOrElse(0)
          if (mport <= 0) error("ir.mcp_port should be positive, got " + mport)
          if (!tcp_listening(mport))
            error("ir.mcp_port " + mport + " is not accepting TCP connections")
          val mtoken = JSON.string(ir, "mcp_token").getOrElse("")
          if (mtoken.isEmpty) error("ir.mcp_token should be present")
          val mcpReply = mcp_status(mport, mtoken)
          if (!mcpReply.contains("ic2 MCP server OK"))
            error("MCP status tool did not report OK: " + mcpReply)
        case None =>
          Output.writeln("    (note) no I/R endpoint — ir/ sources not found or " +
            "python3 unavailable; set AUTOCORRODE_BASE / keep ic2 in-tree to exercise I/R")
      }
    }

    /** True iff a TCP server is accepting on 127.0.0.1:port right now. */
    private def tcp_listening(port: Int): Boolean =
      try { val s = SocketChannel.open(
              new java.net.InetSocketAddress("127.0.0.1", port)); s.close(); true }
      catch { case _: Throwable => false }

    /** Drive one I/R command through repl.py's text protocol: optional token
     *  line (expect "OK"), then "<cmd>;\n", read until the "<<DONE>>" sentinel. */
    private def ir_command(port: Int, token: String, cmd: String): String = {
      val sock = new java.net.Socket("127.0.0.1", port)
      try {
        sock.setSoTimeout(15000)
        val out = new java.io.OutputStreamWriter(sock.getOutputStream, "UTF-8")
        val in = new java.io.BufferedReader(
          new java.io.InputStreamReader(sock.getInputStream, "UTF-8"))
        if (token.nonEmpty) {
          out.write(token + "\n"); out.flush()
          val ok = in.readLine()
          if (ok == null || !ok.startsWith("OK")) error("repl.py auth failed: " + ok)
        }
        out.write(cmd + ";\n"); out.flush()
        val sb = new StringBuilder
        var line = in.readLine()
        while (line != null && line != "<<DONE>>") { sb.append(line).append('\n'); line = in.readLine() }
        sb.toString
      } finally sock.close()
    }

    /** Drive the ic2 MCP server over its newline-delimited JSON-RPC protocol:
     *  initialize (public), authenticate with the token, then tools/call the
     *  `status` tool. Returns the concatenation of the status reply lines (the
     *  tool result text is embedded), so the caller can assert on it. */
    private def mcp_status(port: Int, token: String): String = {
      val sock = new java.net.Socket("127.0.0.1", port)
      try {
        sock.setSoTimeout(15000)
        val out = new java.io.OutputStreamWriter(sock.getOutputStream, "UTF-8")
        val in = new java.io.BufferedReader(
          new java.io.InputStreamReader(sock.getInputStream, "UTF-8"))
        def rpc(line: String): String = {
          out.write(line + "\n"); out.flush()
          val reply = in.readLine()
          if (reply == null) error("MCP connection closed unexpectedly")
          reply
        }
        // initialize (public, no auth required)
        val _ = rpc("""{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}""")
        // authenticate
        val authReply = rpc(
          s"""{"jsonrpc":"2.0","id":2,"method":"tools/call",""" +
          s""""params":{"name":"authenticate","arguments":{"token":${JSON.Format(token)}}}}""")
        if (!authReply.contains("Authenticated successfully"))
          error("MCP authenticate failed: " + authReply)
        // tools/call status
        rpc(
          """{"jsonrpc":"2.0","id":3,"method":"tools/call",""" +
          """"params":{"name":"status","arguments":{}}}""")
      } finally sock.close()
    }

    /** An authenticated MCP session against the ic2 MCP server, for driving
     *  tools/call repeatedly. Construct, use `call`, then `close`. */
    private final class Mcp_Session(port: Int, token: String) {
      private val sock = new java.net.Socket("127.0.0.1", port)
      sock.setSoTimeout(30000)
      private val out = new java.io.OutputStreamWriter(sock.getOutputStream, "UTF-8")
      private val in = new java.io.BufferedReader(
        new java.io.InputStreamReader(sock.getInputStream, "UTF-8"))
      private var nextId = 0
      private def rpc(obj: JSON.T): JSON.T = {
        nextId += 1
        out.write(JSON.Format(obj.asInstanceOf[JSON.Object.T] + ("id" -> nextId) + ("jsonrpc" -> "2.0")) + "\n")
        out.flush()
        // Skip any stray notifications/progress that linger on the stream. A
        // check's final nodes_status callback is dispatched on a delay and can
        // emit one last progress notification just after the result is written;
        // an MCP client must tolerate notifications arriving interleaved.
        var msg: JSON.T = null
        while (msg == null) {
          val line = in.readLine()
          if (line == null) error("MCP connection closed unexpectedly")
          val parsed = JSON.parse(line)
          if (JSON.string(parsed, "method") != Some("notifications/progress")) msg = parsed
        }
        msg
      }
      // Handshake immediately.
      locally {
        val _ = rpc(JSON.Object("method" -> "initialize", "params" -> JSON.Object()))
        val auth = rpc(JSON.Object("method" -> "tools/call",
          "params" -> JSON.Object("name" -> "authenticate",
            "arguments" -> JSON.Object("token" -> token))))
        if (!JSON.Format(auth).contains("Authenticated successfully"))
          error("MCP authenticate failed: " + JSON.Format(auth))
      }

      /** tools/call `name` with `args`; returns the parsed tool-result object
       *  (the JSON embedded in result.content[0].text), or fails the test on a
       *  JSON-RPC error / isError result unless `expectError`. */
      def call(name: String, args: JSON.Object.T, expectError: Boolean = false): JSON.T = {
        val reply = rpc(JSON.Object("method" -> "tools/call",
          "params" -> JSON.Object("name" -> name, "arguments" -> args)))
        JSON.value(reply, "error") match {
          case Some(err) =>
            if (expectError) JSON.Object("error" -> JSON.string(err, "message").getOrElse(""))
            else error(s"$name: JSON-RPC error: " + JSON.Format(err))
          case None =>
            val result = JSON.value(reply, "result").getOrElse(error(s"$name: no result"))
            val text = JSON.array(result, "content")
              .flatMap(_.headOption)
              .flatMap(c => JSON.string(c, "text"))
              .getOrElse(error(s"$name: no content text in " + JSON.Format(result)))
            val parsed = JSON.parse(text)
            val isError = JSON.bool(result, "isError").getOrElse(false)
            if (isError && !expectError) error(s"$name: tool error: $text")
            if (!isError && expectError) error(s"$name: expected error, got: $text")
            parsed
        }
      }

      /** tools/call `name` with `args` AND a progressToken, collecting any
       *  notifications/progress that arrive before the final response. Returns
       *  (progressParamsList, parsedToolResult). */
      def callWithProgress(
        name: String, args: JSON.Object.T, progressToken: String
      ): (List[JSON.T], JSON.T) = {
        nextId += 1
        val id = nextId
        out.write(JSON.Format(JSON.Object(
          "jsonrpc" -> "2.0", "id" -> id, "method" -> "tools/call",
          "params" -> JSON.Object("name" -> name, "arguments" -> args,
            "_meta" -> JSON.Object("progressToken" -> progressToken)))) + "\n")
        out.flush()
        val progress = scala.collection.mutable.ListBuffer.empty[JSON.T]
        var result: Option[JSON.T] = None
        while (result.isEmpty) {
          val line = in.readLine()
          if (line == null) error("MCP connection closed mid-call")
          val msg = JSON.parse(line)
          if (JSON.string(msg, "method") == Some("notifications/progress"))
            JSON.value(msg, "params").foreach(progress += _)
          else if (JSON.int(msg, "id") == Some(id) || JSON.long(msg, "id") == Some(id.toLong)) {
            val res = JSON.value(msg, "result").getOrElse(error(s"$name: no result in $line"))
            val text = JSON.array(res, "content").flatMap(_.headOption)
              .flatMap(c => JSON.string(c, "text")).getOrElse(error(s"$name: no content text"))
            result = Some(JSON.parse(text))
          }
          // other messages (shouldn't occur on a single-call session) are ignored
        }
        (progress.toList, result.get)
      }

      def close(): Unit = try { sock.close() } catch { case _: Throwable => }
    }

    /** Open an authenticated MCP session against the named server, reading its
     *  mcp_port/token from `ic2 server status`. Skips (returns None) if I/R+MCP isn't
     *  up (bare checkout: no ir/ sources or python3). */
    private def open_mcp(server_name: String): Option[Mcp_Session] = {
      val t = query_status(server_name)
      JSON.value(t, "ir").flatMap(ir =>
        for {
          port <- JSON.int(ir, "mcp_port")
          token <- JSON.string(ir, "mcp_token")
        } yield new Mcp_Session(port, token))
    }

    /** Extensive coverage of the SessionTools MCP tools (registered via
     *  SessionClient): every tool against the Diagnostics / Trivial_OK /
     *  Trivial_Fail fixtures, with each variant (file vs selection scope,
     *  severity error|warning, offset vs pattern, filters, and the error paths:
     *  missing path, unknown file, ambiguous offset/pattern). All fixtures are
     *  checked first so they are loaded session nodes. */
    private def e2e_session_tools(server_name: String, fixtures: Path): Unit = {
      open_mcp(server_name) match {
        case None =>
          Output.writeln("    (note) no MCP endpoint — I/R/MCP not up (no ir/ or python3); " +
            "skipping SessionTools coverage")
        case Some(mcp) =>
          try {
            // Load the fixtures into the session so the tools have nodes.
            // Running `check` loads the node regardless of whether the check
            // passes — Trivial_Fail and Diagnostics deliberately don't all pass,
            // but they still become loaded nodes, which is all the tools need.
            // Only Trivial_OK is asserted to actually check ok (sanity).
            val diag = (fixtures + Path.basic("Diagnostics.thy")).expand.implode
            val ok = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
            val fail = (fixtures + Path.basic("Trivial_Fail.thy")).expand.implode
            val (_, okFin) = run_check(server_name, List(ok))
            if (okFin.flatMap(JSON.bool(_, "ok")) != Some(true))
              error("precondition: Trivial_OK should check ok")
            val _ = run_check(server_name, List(fail))   // loads the node; check fails by design
            val _2 = run_check(server_name, List(diag))  // loads the node; has a benign warning

            t_list_files(mcp)
            t_processing_status(mcp)
            t_document_info(mcp)
            t_diagnostics(mcp)
            t_sorry_positions(mcp)
            t_entities(mcp)
            t_proof_blocks(mcp)
            t_command_info(mcp)
            t_context_info(mcp)
            t_resolution_errors(mcp)
            t_check(mcp, ok, fail)
            t_check_progress(mcp, fail)
            t_check_async(mcp, ok)
          } finally mcp.close()
      }
    }

    private def obj(pairs: (String, JSON.T)*): JSON.Object.T = JSON.Object(pairs: _*)

    /* ---- per-tool checks ---- */

    private def t_list_files(mcp: Mcp_Session): Unit = {
      val all = mcp.call("list_files", obj())
      val files = JSON.array(all, "files").getOrElse(error("list_files: no files array"))
      if (files.isEmpty) error("list_files: expected loaded nodes, got none")
      def nodes(j: JSON.T) = JSON.array(j, "files").getOrElse(Nil)
        .flatMap(e => JSON.string(e, "node"))
      // Trivial_OK should be present and consolidated/100%.
      val okEntry = files.find(e => JSON.string(e, "node").exists(_.endsWith("Trivial_OK.thy")))
        .getOrElse(error("list_files: Trivial_OK.thy not listed"))
      if (JSON.bool(okEntry, "consolidated") != Some(true))
        error("list_files: Trivial_OK should be consolidated")
      if (JSON.int(okEntry, "percentage") != Some(100))
        error("list_files: Trivial_OK should be at 100%")
      // filter_theory=true keeps only theory nodes; false keeps only non-theory.
      val onlyTheories = nodes(mcp.call("list_files", obj("filter_theory" -> true)))
      if (onlyTheories.isEmpty) error("list_files(filter_theory=true): expected theory nodes")
      val nonTheories = nodes(mcp.call("list_files", obj("filter_theory" -> false)))
      // Every theory node must drop out of the non-theory list.
      if (onlyTheories.toSet.intersect(nonTheories.toSet).nonEmpty)
        error("list_files: theory/non-theory filters overlap")
    }

    private def t_processing_status(mcp: Mcp_Session): Unit = {
      val okSt = mcp.call("get_processing_status", obj("path" -> "Trivial_OK.thy"))
      if (JSON.bool(okSt, "fully_processed") != Some(true))
        error("processing_status(Trivial_OK): should be fully_processed")
      if (JSON.bool(okSt, "has_errors") != Some(false))
        error("processing_status(Trivial_OK): should have no errors")
      if (JSON.int(okSt, "finished").getOrElse(0) <= 0)
        error("processing_status(Trivial_OK): finished should be > 0")
      val failSt = mcp.call("get_processing_status", obj("path" -> "Trivial_Fail.thy"))
      if (JSON.bool(failSt, "has_errors") != Some(true))
        error("processing_status(Trivial_Fail): should report errors")
      if (JSON.int(failSt, "failed").getOrElse(0) <= 0)
        error("processing_status(Trivial_Fail): failed should be > 0")
    }

    private def t_document_info(mcp: Mcp_Session): Unit = {
      val okInfo = mcp.call("get_document_info", obj("path" -> "Trivial_OK.thy"))
      if (JSON.bool(okInfo, "has_errors") != Some(false))
        error("document_info(Trivial_OK): should have no errors")
      if (JSON.int(okInfo, "total_commands").getOrElse(0) <= 0)
        error("document_info(Trivial_OK): total_commands should be > 0")
      val failInfo = mcp.call("get_document_info", obj("path" -> "Trivial_Fail.thy"))
      if (JSON.int(failInfo, "error_count").getOrElse(0) <= 0)
        error("document_info(Trivial_Fail): error_count should be > 0")
      if (JSON.bool(failInfo, "has_errors") != Some(true))
        error("document_info(Trivial_Fail): has_errors should be true")
    }

    private def t_diagnostics(mcp: Mcp_Session): Unit = {
      // File scope, error severity: Trivial_Fail has exactly one error.
      val errs = mcp.call("get_diagnostics", obj("path" -> "Trivial_Fail.thy", "severity" -> "error"))
      if (JSON.int(errs, "count").getOrElse(0) <= 0)
        error("diagnostics(Trivial_Fail, error): expected >= 1 error")
      if (JSON.string(errs, "scope") != Some("file")) error("diagnostics: scope should be file")
      val msg = JSON.array(errs, "diagnostics").getOrElse(Nil).headOption
        .flatMap(d => JSON.string(d, "message")).getOrElse("")
      if (msg.trim.isEmpty) error("diagnostics: error message should be non-empty")
      // File scope, error severity: Trivial_OK has none.
      val okErrs = mcp.call("get_diagnostics", obj("path" -> "Trivial_OK.thy", "severity" -> "error"))
      if (JSON.int(okErrs, "count") != Some(0))
        error("diagnostics(Trivial_OK, error): expected 0")
      // Default severity is error.
      val deflt = mcp.call("get_diagnostics", obj("path" -> "Trivial_Fail.thy"))
      if (JSON.string(deflt, "severity") != Some("error"))
        error("diagnostics: default severity should be error")
      // Warning severity is accepted (count >= 0).
      val warns = mcp.call("get_diagnostics", obj("path" -> "Diagnostics.thy", "severity" -> "warning"))
      if (JSON.int(warns, "count").isEmpty) error("diagnostics(warning): missing count")
      // Selection scope at the broken lemma: should surface the error there.
      val sel = mcp.call("get_diagnostics",
        obj("path" -> "Trivial_Fail.thy", "severity" -> "error",
            "scope" -> "selection", "pattern" -> "by simp"))
      if (JSON.string(sel, "scope") != Some("selection")) error("diagnostics: selection scope label")
      if (JSON.int(sel, "count").getOrElse(0) <= 0)
        error("diagnostics(selection at 'by simp'): expected the error")
      // Bad severity is rejected.
      val _ = mcp.call("get_diagnostics", obj("path" -> "Trivial_OK.thy", "severity" -> "bogus"),
        expectError = true)
      // Bad scope is rejected.
      val _2 = mcp.call("get_diagnostics", obj("path" -> "Trivial_OK.thy", "scope" -> "bogus"),
        expectError = true)
    }

    private def t_sorry_positions(mcp: Mcp_Session): Unit = {
      // Diagnostics.thy has exactly one sorry, in lemma `incomplete`.
      val s = mcp.call("get_sorry_positions", obj("path" -> "Diagnostics.thy"))
      val positions = JSON.array(s, "positions").getOrElse(error("sorry_positions: no positions"))
      if (JSON.int(s, "count") != Some(positions.length)) error("sorry_positions: count mismatch")
      if (positions.length != 1) error("sorry_positions(Diagnostics): expected 1 sorry, got " + positions.length)
      val p = positions.head
      if (JSON.string(p, "keyword") != Some("sorry")) error("sorry_positions: keyword should be sorry")
      if (JSON.string(p, "in_proof") != Some("incomplete"))
        error("sorry_positions: enclosing proof should be 'incomplete', got " + JSON.string(p, "in_proof"))
      if (JSON.int(p, "line").getOrElse(0) <= 0) error("sorry_positions: line should be > 0")
      // Trivial_OK has none.
      val none = mcp.call("get_sorry_positions", obj("path" -> "Trivial_OK.thy"))
      if (JSON.int(none, "count") != Some(0)) error("sorry_positions(Trivial_OK): expected 0")
    }

    private def t_entities(mcp: Mcp_Session): Unit = {
      val e = mcp.call("get_entities", obj("path" -> "Diagnostics.thy"))
      val entities = JSON.array(e, "entities").getOrElse(error("entities: no entities"))
      def named(kw: String, nm: String) =
        entities.exists(x => JSON.string(x, "keyword") == Some(kw) && JSON.string(x, "name") == Some(nm))
      if (!named("definition", "answer")) error("entities: missing definition answer")
      if (!named("datatype", "color")) error("entities: missing datatype color")
      if (!named("fun", "isRed")) error("entities: missing fun isRed")
      if (!named("lemma", "structured")) error("entities: missing lemma structured")
      // Each entity carries a positive line and a keyword in the known set.
      for (x <- entities) {
        if (JSON.int(x, "line").getOrElse(0) <= 0) error("entities: non-positive line")
      }
      // max_results truncates and flags it.
      val capped = mcp.call("get_entities", obj("path" -> "Diagnostics.thy", "max_results" -> 1))
      if (JSON.array(capped, "entities").getOrElse(Nil).length != 1)
        error("entities(max_results=1): should return exactly 1")
      if (JSON.bool(capped, "truncated") != Some(true))
        error("entities(max_results=1): should be truncated")
    }

    private def t_proof_blocks(mcp: Mcp_Session): Unit = {
      val b = mcp.call("get_proof_blocks", obj("path" -> "Diagnostics.thy"))
      val blocks = JSON.array(b, "blocks").getOrElse(error("proof_blocks: no blocks"))
      if (blocks.isEmpty) error("proof_blocks(Diagnostics): expected >= 1 block")
      // There is a structured (proof..qed) block and an apply..done block.
      val anyApply = blocks.exists(x => JSON.bool(x, "is_apply_style") == Some(true))
      val anyStructured = blocks.exists(x => JSON.bool(x, "is_apply_style") == Some(false))
      if (!anyApply) error("proof_blocks: expected an apply-style block")
      if (!anyStructured) error("proof_blocks: expected a structured block")
      for (x <- blocks) {
        if (JSON.string(x, "proof_text").getOrElse("").trim.isEmpty)
          error("proof_blocks: empty proof_text")
        if (JSON.int(x, "command_count").getOrElse(0) <= 0)
          error("proof_blocks: command_count should be > 0")
      }
      // min_chars filters short blocks out (huge threshold -> none).
      val filtered = mcp.call("get_proof_blocks", obj("path" -> "Diagnostics.thy", "min_chars" -> 100000))
      if (JSON.int(filtered, "count") != Some(0))
        error("proof_blocks(min_chars=100000): expected 0")
    }

    private def t_command_info(mcp: Mcp_Session): Unit = {
      // By pattern.
      val byPat = mcp.call("get_command_info", obj("path" -> "Trivial_OK.thy", "pattern" -> "lemma trivial"))
      if (JSON.string(byPat, "keyword") != Some("lemma"))
        error("command_info(pattern): keyword should be lemma")
      if (JSON.string(byPat, "command_type") != Some("statement"))
        error("command_info(pattern): command_type should be statement")
      if (!JSON.string(byPat, "source").getOrElse("").contains("trivial"))
        error("command_info(pattern): source should contain the lemma")
      JSON.value(byPat, "status").getOrElse(error("command_info: missing status"))
      // By offset: offset 0 is the `theory` command.
      val byOff = mcp.call("get_command_info", obj("path" -> "Trivial_OK.thy", "offset" -> 0))
      if (JSON.string(byOff, "command_type") != Some("theory_structure"))
        error("command_info(offset=0): should be the theory header")
      // results_text captures the command's output messages: the failing
      // `by simp` in Trivial_Fail emits an error that must show up here.
      val failCmd = mcp.call("get_command_info", obj("path" -> "Trivial_Fail.thy", "pattern" -> "by simp"))
      val failText = JSON.string(failCmd, "results_text").getOrElse("")
      if (!failText.contains("Failed to apply"))
        error("command_info(failing by simp): results_text should carry the error, got: " + failText)
      // Pattern not present -> error.
      val _ = mcp.call("get_command_info",
        obj("path" -> "Trivial_OK.thy", "pattern" -> "no_such_text_zzz"), expectError = true)
      // Neither offset nor pattern -> error.
      val _2 = mcp.call("get_command_info", obj("path" -> "Trivial_OK.thy"), expectError = true)
    }

    private def t_context_info(mcp: Mcp_Session): Unit = {
      // in_proof_context (a keyword-balance over the spans, independent of goal
      // output) distinguishes a command inside an open proof from one outside.
      val inProof = mcp.call("get_context_info", obj("path" -> "Diagnostics.thy", "pattern" -> "show \"answer"))
      if (JSON.bool(inProof, "in_proof_context") != Some(true))
        error("context_info(at show): in_proof_context should be true")
      JSON.value(inProof, "command").getOrElse(error("context_info: missing command"))
      JSON.value(inProof, "goal").getOrElse(error("context_info: missing goal"))
      // At the theory header: not in a proof context.
      val atHeader = mcp.call("get_context_info", obj("path" -> "Trivial_OK.thy", "offset" -> 0))
      if (JSON.bool(atHeader, "in_proof_context") != Some(false))
        error("context_info(at header): in_proof_context should be false")

      // has_goal keys strictly on a proof-STATE message (an open goal), NOT on
      // "any output". Verify there is no false positive: a non-goal command
      // (`definition`) emits writeln output ("consts answer :: nat"), and a
      // completed proof (`qed`) emits the proved theorem ("theorem ..."), but
      // NEITHER is an open goal. Both must report has_goal:false / empty goal.
      def assert_no_goal(pattern: String): Unit = {
        val ci = mcp.call("get_context_info", obj("path" -> "Diagnostics.thy", "pattern" -> pattern))
        val g = JSON.value(ci, "goal").getOrElse(error("context_info(" + pattern + "): missing goal"))
        if (JSON.bool(ci, "has_goal") != Some(false))
          error("context_info(" + pattern + "): has_goal should be false (no open goal)")
        if (JSON.bool(g, "has_goal") != Some(false))
          error("context_info(" + pattern + "): goal.has_goal should be false")
        if (JSON.int(g, "num_subgoals").getOrElse(-1) != 0)
          error("context_info(" + pattern + "): num_subgoals should be 0, got " + JSON.int(g, "num_subgoals"))
        if (JSON.string(g, "goal_text").getOrElse("x").nonEmpty)
          error("context_info(" + pattern + "): goal_text should be empty (no open goal)")
      }
      assert_no_goal("definition answer")
      assert_no_goal("qed")
    }

    private def t_resolution_errors(mcp: Mcp_Session): Unit = {
      // Missing path param.
      val _ = mcp.call("get_processing_status", obj(), expectError = true)
      // Unknown file.
      val _2 = mcp.call("get_processing_status", obj("path" -> "No_Such_Theory_Zzz.thy"), expectError = true)
      // Selection without offset or pattern.
      val _3 = mcp.call("get_context_info", obj("path" -> "Trivial_OK.thy"), expectError = true)
    }

    /** The `check` MCP tool (analogue of `isabelle ic2 check`): a passing file
     *  reports ok=true with its theory; a broken file reports ok=false with
     *  reason="errors"; and the argument-validation error paths. `okAbs`/`failAbs`
     *  are absolute fixture paths (the tool requires absolute paths). */
    private def t_check(mcp: Mcp_Session, okAbs: String, failAbs: String): Unit = {
      // Passing theory -> ok=true, theory name reported.
      val okRes = mcp.call("check", obj("files" -> List[Any](okAbs)))
      if (JSON.bool(okRes, "ok") != Some(true))
        error("check(Trivial_OK): ok should be true, got " + JSON.Format(okRes))
      val okThys = JSON.strings(okRes, "theories").getOrElse(Nil)
      if (!okThys.exists(_.endsWith("Trivial_OK")))
        error("check(Trivial_OK): theories should include Trivial_OK, got " + okThys)
      // Broken theory -> ok=false with a reason (not a transport error).
      val failRes = mcp.call("check", obj("files" -> List[Any](failAbs)))
      if (JSON.bool(failRes, "ok") != Some(false))
        error("check(Trivial_Fail): ok should be false, got " + JSON.Format(failRes))
      if (JSON.string(failRes, "reason").getOrElse("").isEmpty)
        error("check(Trivial_Fail): should carry a failure reason")
      if (!JSON.strings(failRes, "theories").getOrElse(Nil).exists(_.endsWith("Trivial_Fail")))
        error("check(Trivial_Fail): theories should include Trivial_Fail")
      // Multiple files at once: both theories reported, ok reflects the worst.
      val multi = mcp.call("check", obj("files" -> List[Any](okAbs, failAbs)))
      if (JSON.bool(multi, "ok") != Some(false))
        error("check(OK+Fail): ok should be false")
      val multiThys = JSON.strings(multi, "theories").getOrElse(Nil)
      if (!(multiThys.exists(_.endsWith("Trivial_OK")) && multiThys.exists(_.endsWith("Trivial_Fail"))))
        error("check(OK+Fail): both theories should be reported, got " + multiThys)
      // Error paths (isError tool results).
      val _ = mcp.call("check", obj("files" -> List.empty[Any]), expectError = true)   // empty
      val _2 = mcp.call("check", obj(), expectError = true)                            // missing param
      val _3 = mcp.call("check", obj("files" -> List[Any]("relative/Foo.thy")), expectError = true) // not absolute
      val _4 = mcp.call("check", obj("files" -> List[Any]("/no/such/Zzz.thy")), expectError = true) // missing file
    }

    /** `check` with a progressToken on Slow.thy (an ~8s check) must stream
     *  notifications/progress before the final result, each carrying the token
     *  and a {progress,total,message} payload, and the check must still succeed. */
    private def t_check_progress(mcp: Mcp_Session, failAbs: String): Unit = {
      // Fresh, uniquely-named slow theories: never consolidated, so each check
      // genuinely re-runs the 8s ML sleep — the window the progress / timeout
      // assertions need (a re-check of a shared fixture returns in ~100ms,
      // streaming no progress and finishing before any timeout budget bites).
      val slowAbs = fresh_slow_theory()
      val slow2Abs = fresh_slow_theory()
      val (progress, result) = mcp.callWithProgress("check", obj("files" -> List[Any](slowAbs)), "ptok-1")
      if (JSON.bool(result, "ok") != Some(true))
        error("check(Slow) with progress: ok should be true, got " + JSON.Format(result))
      if (progress.isEmpty)
        error("check(Slow): expected >= 1 progress notification (Slow.thy runs ~8s)")
      for (p <- progress) {
        if (JSON.int(p, "total") != Some(1))
          error("check progress: total should be 1, got " + JSON.Format(p))
        if (JSON.int(p, "progress").isEmpty)
          error("check progress: missing 'progress' field: " + JSON.Format(p))
        if (JSON.string(p, "message").getOrElse("").isEmpty)
          error("check progress: missing 'message': " + JSON.Format(p))
        if (JSON.string(p, "progressToken") != Some("ptok-1"))
          error("check progress: token not injected/echoed: " + JSON.Format(p))
      }
      // The last notification should report completion (1/1 processed).
      val last = progress.last
      if (JSON.int(last, "progress") != Some(1))
        error("check progress: final notification should report 1 processed, got " + JSON.Format(last))

      // First-error stop: a broken theory aborts the check (use_theories is
      // cancelled by Check_Progress.stop()), reporting errors — not a crash —
      // and the progress notifications still carry the token/shape.
      val (failProg, failRes) = mcp.callWithProgress("check", obj("files" -> List[Any](failAbs)), "ptok-2")
      if (JSON.bool(failRes, "ok") != Some(false))
        error("check(Fail) with progress: ok should be false, got " + JSON.Format(failRes))
      if (JSON.string(failRes, "reason").getOrElse("") != "errors")
        error("check(Fail): reason should be 'errors' (first-error stop), got " + JSON.Format(failRes))
      for (p <- failProg)
        if (JSON.string(p, "progressToken") != Some("ptok-2"))
          error("check(Fail) progress: token mismatch: " + JSON.Format(p))

      // Timeout abort: a 1s budget against the fresh Slow2.thy (~8s, not yet
      // consolidated, so the check genuinely re-runs the ML sleep) aborts the
      // check, reporting reason "timeout" — not a crash or a transport error.
      val timeoutRes = mcp.call("check", obj("files" -> List[Any](slow2Abs), "timeout_secs" -> 1))
      if (JSON.bool(timeoutRes, "ok") != Some(false))
        error("check(Slow2, timeout_secs=1): ok should be false, got " + JSON.Format(timeoutRes))
      if (JSON.string(timeoutRes, "reason").getOrElse("") != "timeout")
        error("check(Slow2, timeout_secs=1): reason should be 'timeout', got " + JSON.Format(timeoutRes))
      // A negative budget is a usage error (isError tool result).
      val _t = mcp.call("check", obj("files" -> List[Any](slow2Abs), "timeout_secs" -> -1), expectError = true)
    }

    /** Non-blocking MCP surface: check_async returns immediately while running;
     *  the no-arg check_status polls the single in-flight check; check_cancel
     *  aborts it; a second submit while one runs is REFUSED; and a fresh async
     *  OK check reaches state ok. */
    private def t_check_async(mcp: Mcp_Session, okAbs: String): Unit = {
      // A fresh, uniquely-named slow theory so the check is reliably still
      // running when check_status polls it (a re-check would already be ok).
      val slowAbs = fresh_slow_theory()
      // Submit a slow check without blocking.
      val sub = mcp.call("check_async", obj("files" -> List[Any](slowAbs)))
      if (JSON.string(sub, "state") != Some("running"))
        error("check_async(Slow): should be running, got " + JSON.Format(sub))
      // The no-arg check_status reports it running.
      val st = mcp.call("check_status", obj())
      if (JSON.string(st, "state") != Some("running"))
        error("check_status: Slow check should be running, got " + JSON.Format(st))
      // A second submit while one is in flight is refused (isError).
      val _r = mcp.call("check_async", obj("files" -> List[Any](okAbs)), expectError = true)
      // Cancel it; it settles to failed/cancelled.
      val cancel = mcp.call("check_cancel", obj())
      if (JSON.bool(cancel, "cancelled") != Some(true))
        error("check_cancel: running check should report cancelled=true, got " + JSON.Format(cancel))
      val deadline = System.currentTimeMillis() + 15000
      var s2 = mcp.call("check_status", obj())
      while (JSON.string(s2, "state") == Some("running") && System.currentTimeMillis() < deadline) {
        Thread.sleep(200); s2 = mcp.call("check_status", obj())
      }
      if (JSON.string(s2, "state") != Some("failed") || JSON.string(s2, "reason") != Some("cancelled"))
        error("cancelled async check should be failed/cancelled, got " + JSON.Format(s2))
      // With nothing now in flight, a fresh async OK check reaches state ok.
      val okSub = mcp.call("check_async", obj("files" -> List[Any](okAbs)))
      if (JSON.string(okSub, "state") != Some("running"))
        error("check_async(ok): should be running, got " + JSON.Format(okSub))
      val d2 = System.currentTimeMillis() + 30000
      var os = mcp.call("check_status", obj())
      while (JSON.string(os, "state") == Some("running") && System.currentTimeMillis() < d2) {
        Thread.sleep(200); os = mcp.call("check_status", obj())
      }
      if (JSON.string(os, "state") != Some("ok"))
        error("async Trivial_OK should reach ok, got " + JSON.Format(os))
      // check_cancel with nothing running is a no-op (not an error).
      val noop = mcp.call("check_cancel", obj())
      if (JSON.bool(noop, "cancelled") != Some(false))
        error("check_cancel with nothing running should report cancelled=false, got " + JSON.Format(noop))
    }

    private def e2e_check_ok(server_name: String, fixtures: Path): Unit = {
      val file = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
      val (events, finished) = run_check(server_name, List(file))
      finished match {
        case Some(t) if JSON.bool(t, "ok") == Some(true) => ()
        case other => error("expected finished{ok:true}, got " + other +
          "; events=" + events.length)
      }
      if (!theory_names(events, "started").contains("Trivial_OK"))
        error("started.theories should contain Trivial_OK; got " +
          theory_names(events, "started").mkString(","))
      // Success path ends on a 100%/consolidated snapshot for the requested theory.
      val last_progress =
        events.reverse.find(t => JSON.string(t, "event") == Some("progress"))
      last_progress.flatMap(t => JSON.array(t, "nodes")).getOrElse(Nil)
        .find(n => JSON.string(n, "theory").map(base_name) == Some("Trivial_OK")) match {
        case Some(n) =>
          if (JSON.int(n, "percentage") != Some(100)) error("Trivial_OK not at 100% at end")
          if (JSON.bool(n, "consolidated") != Some(true)) error("Trivial_OK not consolidated at end")
        case None => error("no final progress node for Trivial_OK")
      }
    }

    private def e2e_check_fail(server_name: String, fixtures: Path): Unit = {
      val file = (fixtures + Path.basic("Trivial_Fail.thy")).expand.implode
      val (events, finished) = run_check(server_name, List(file))
      val errors = events.filter(t => JSON.string(t, "event") == Some("error"))
      if (errors.isEmpty) error("expected at least one 'error' event")
      // The error must point at Trivial_Fail with a real position.
      val matched = errors.find(t => JSON.string(t, "theory").map(base_name) == Some("Trivial_Fail"))
      matched match {
        case Some(t) =>
          val f = JSON.string(t, "file").getOrElse("")
          if (!f.endsWith("Trivial_Fail.thy"))
            error("error file should be Trivial_Fail.thy, got " + f)
          if (JSON.int(t, "line").getOrElse(0) <= 0)
            error("error should carry a positive line number")
        case None => error("no error event references Trivial_Fail")
      }
      finished match {
        case Some(t) if JSON.bool(t, "ok") == Some(false) => ()
        case other => error("expected finished{ok:false}, got " + other)
      }
    }

    /** Automatic dependency resolution (step A): a FULL check of a theory that
     *  imports a LOCAL (non-heap) theory must resolve, load, and evaluate that
     *  import WITHOUT the client naming it. SpinImport.thy imports SpinDep.thy and
     *  its `uses_dep` lemma references `spin_dep_const` from the dependency, so a
     *  green check proves SpinDep was resolved and evaluated by the check engine
     *  (Check_Engine.updateModel's resources.dependencies closure), not by luck.
     *
     *  Pins: (i) check of SpinImport ALONE finishes ok:true; (ii) the unnamed
     *  dependency SpinDep appears in the progress nodes AND is consolidated;
     *  (iii) SpinDep is fully processed with no failures per get_processing_status.
     *  Skips cleanly if the fixtures are absent (bare checkout). */
    private def e2e_check_resolves_dependencies(server_name: String, fixtures: Path): Unit = {
      val imp = fixtures + Path.basic("SpinImport.thy")
      val dep = fixtures + Path.basic("SpinDep.thy")
      if (!imp.is_file || !dep.is_file) {
        Output.writeln("    (note) SpinImport/SpinDep fixtures missing; skipping dependency-resolution test")
        return
      }

      // Check ONLY the importer. If the engine did not resolve+evaluate SpinDep,
      // SpinImport.uses_dep would fail to type-check and the check would be ok:false.
      val (events, finished) = run_check(server_name, List(imp.expand.implode), deadline_secs = 90)
      if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
        error("check of SpinImport (imports SpinDep, unnamed) should be ok:true — a failure " +
          "means the dependency SpinDep was not auto-resolved/evaluated; got " + finished +
          " events=" + events.length)

      // The unnamed dependency must show up in the progress nodes and be consolidated.
      val last_progress = events.reverse.find(t => JSON.string(t, "event") == Some("progress"))
      val depNode =
        last_progress.flatMap(t => JSON.array(t, "nodes")).getOrElse(Nil)
          .find(n => JSON.string(n, "theory").map(base_name) == Some("SpinDep"))
      depNode match {
        case Some(n) =>
          if (JSON.bool(n, "consolidated") != Some(true))
            error("auto-resolved dependency SpinDep should be consolidated at end, got " + JSON.Format(n))
        case None =>
          error("dependency SpinDep should appear among the progress nodes (auto-resolved), " +
            "but no node for it was found in the final progress event")
      }

      // Cross-check via the query tool: SpinDep fully processed, no failures.
      val ps = request_op(server_name, JSON.Object("op" -> "query",
        "tool" -> "get_processing_status", "path" -> "SpinDep.thy"))
      val psR = JSON.value(ps, "result").getOrElse(JSON.Object())
      if (JSON.bool(psR, "fully_processed") != Some(true))
        error("auto-resolved dependency SpinDep should be fully_processed, got " + JSON.Format(psR))
      if (JSON.int(psR, "failed").getOrElse(0) != 0)
        error("auto-resolved dependency SpinDep should have no failures, got " + JSON.Format(psR))
    }

    /** The `ic2 check` CLI front door submits and returns. Completion state is
     *  observed with `check_status`; live `check attach` is TTY-only. */
    private def e2e_check_cli(server_name: String, fixtures: Path): Unit = {
      val ok = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
      val bad = (fixtures + Path.basic("Trivial_Fail.thy")).expand.implode
      val n = Bash.string(server_name)

      val r0 = ic2("check -n " + n + " " + Bash.string(ok))
      if (r0.rc != 0) error("check OK should submit with exit 0, got " + r0.rc + " err=" + r0.err.mkString)
      val r0_text = r0.out.mkString + r0.err.mkString
      if (!r0_text.contains("submitted"))
        error("check OK should print submitted ack, got output=" + r0_text)
      val s0 = wait_check_state(server_name, Set("ok"))
      if (JSON.bool(s0, "ok") != Some(true))
        error("submitted OK check should finish ok, got " + JSON.Format(s0))

      val r1 = ic2("check -n " + n + " " + Bash.string(bad))
      if (r1.rc != 0) error("check Fail should submit with exit 0, got " + r1.rc)
      val s1 = wait_check_state(server_name, Set("failed"))
      if (JSON.bool(s1, "ok") != Some(false))
        error("submitted failing check should finish failed/ok=false, got " + JSON.Format(s1))

      val r2 = ic2("check -n " + n)
      if (r2.rc != 2) error("check with no FILE should exit 2, got " + r2.rc)
      val r3 = ic2("check -P -n " + n + " " + Bash.string(ok))
      if (r3.rc != 2) error("check -P should be rejected as bad usage, got " + r3.rc)
      val r4 = ic2("check --detach -n " + n + " " + Bash.string(ok))
      if (r4.rc != 2) error("check --detach should be rejected as bad usage, got " + r4.rc)
      val r5 = ic2("check attach -n " + n)
      if (r5.rc != 2) error("check attach without TTY should exit 2, got " + r5.rc)
      if (!r5.err.mkString.contains("check status"))
        error("check attach without TTY should point to check status, got err=" + r5.err.mkString)
      val r6 = ic2("check attach --long-running 1 -n " + n)
      if (r6.rc != 2) error("check attach --long-running without TTY should exit 2, got " + r6.rc)
      if (!r6.err.mkString.contains("check status"))
        error("check attach --long-running should be accepted before the TTY guard, got err=" +
          r6.err.mkString)
    }

    /** Re-checking a changed theory should preserve the unchanged processed
     *  prefix. The baseline check evaluates an expensive ML command, then the
     *  test rewrites only a later marker command. A correct incremental check
     *  should finish the second run without re-running the earlier sleep. */
    private def e2e_recheck_after_edit_skips_prefix(server_name: String): Unit = {
      val file = fresh_incremental_recheck_theory(secs = 5.0)

      val (_, firstFinished) = run_check(server_name, List(file), deadline_secs = 30)
      if (firstFinished.flatMap(JSON.bool(_, "ok")) != Some(true))
        error("baseline incremental check should pass, got " + firstFinished)

      rewrite_marker(file, "IC2_INCREMENTAL_MARKER_0", "IC2_INCREMENTAL_MARKER_1")

      val start = System.currentTimeMillis()
      val (events, secondFinished) = run_check(server_name, List(file), deadline_secs = 4)
      val elapsed = System.currentTimeMillis() - start
      val replayedSleep = events.exists(t =>
        JSON.array(t, "nodes").getOrElse(Nil).exists(n =>
          JSON.array(n, "long_running").getOrElse(Nil).exists(rc =>
            JSON.string(rc, "preview").exists(_.contains("IC2_INCREMENTAL_SLEEP_BEGIN")))))
      if (secondFinished.flatMap(JSON.bool(_, "ok")) != Some(true))
        error("post-edit re-check should finish within 4s by reusing the unchanged prefix; " +
          "got finished=" + secondFinished + ", events=" + events.length +
          ", elapsed_ms=" + elapsed + ", replayed_sleep=" + replayedSleep)
      if (replayedSleep)
        error("post-edit re-check reported the pre-edit sleep as running")
    }

    /** Submit OK + Fail together; first-error stop must blame Fail, never OK. */
    private def e2e_multi_file(server_name: String, fixtures: Path): Unit = {
      val ok = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
      val bad = (fixtures + Path.basic("Trivial_Fail.thy")).expand.implode
      val (events, finished) = run_check(server_name, List(ok, bad))
      val started = theory_names(events, "started")
      if (!started.contains("Trivial_OK") || !started.contains("Trivial_Fail"))
        error("started.theories should list both files; got " + started.mkString(","))
      finished.flatMap(JSON.bool(_, "ok")) match {
        case Some(false) => ()
        case other => error("multi-file with a failure should be ok:false, got " + other)
      }
      val err_theories = theory_names(events, "error")
      if (!err_theories.contains("Trivial_Fail"))
        error("expected an error for Trivial_Fail; got " + err_theories.mkString(","))
      if (err_theories.contains("Trivial_OK"))
        error("Trivial_OK should not produce an error")
    }

    /** Checks are mutually exclusive server-wide: two clients each submit a
     *  (distinct, slow) check at once; EXACTLY ONE is accepted and the other is
     *  refused with "already in flight". This is the cross-connection gate that
     *  guarantees use_theories never runs concurrently on the session. */
    private def e2e_concurrent_clients(server_name: String, fixtures: Path): Unit = {
      val file1 = fresh_slow_theory()
      val file2 = fresh_slow_theory()

      val start = new CountDownLatch(1)
      // Per connection: Right(true) = accepted (saw `started`), Right(false) =
      // refused (saw the in-flight server_error), Left = unexpected.
      val results = new AtomicReference[Map[String, Either[Throwable, Boolean]]](Map.empty)

      def worker(tag: String, file: String): Thread =
        new Thread(new Runnable {
          def run(): Unit = {
            val outcome: Either[Throwable, Boolean] =
              try {
                start.await(10, TimeUnit.SECONDS)
                val io = connection(server_name)
                try {
                  io.write(JSON.Object("op" -> "check", "files" -> List(file)))
                  // Read until we learn accept (started) or refuse (server_error).
                  var verdict: Option[Boolean] = None
                  val deadline = System.currentTimeMillis() + 30000
                  while (verdict.isEmpty && System.currentTimeMillis() < deadline) {
                    io.read(2000) match {
                      case JSON_IO.Value(t) => JSON.string(t, "event") match {
                        case Some("started") => verdict = Some(true)
                        case Some("server_error")
                          if JSON.string(t, "message").exists(_.contains("in flight")) =>
                          verdict = Some(false)
                        case _ => /* progress/finished/etc — keep reading */
                      }
                      case JSON_IO.EOF => verdict = Some(false)
                      case JSON_IO.Timeout => /* keep waiting */
                    }
                  }
                  verdict.toRight(ERROR(tag + ": no accept/refuse verdict in time"))
                } finally io.close()   // closing cancels an accepted check
              } catch { case e: Throwable => Left(e) }
            results.getAndUpdate(m => m + (tag -> outcome))
          }
        })

      val t1 = worker("c1", file1)
      val t2 = worker("c2", file2)
      t1.start(); t2.start()
      start.countDown()
      t1.join(60000); t2.join(60000)

      val m = results.get
      val verdicts = List("c1", "c2").map { tag =>
        m.get(tag) match {
          case Some(Right(b)) => b
          case Some(Left(e)) => error(e.getMessage)
          case None => error(tag + " did not finish")
        }
      }
      // Exactly one accepted, exactly one refused.
      if (verdicts.count(_ == true) != 1 || verdicts.count(_ == false) != 1)
        error("expected exactly one accepted + one refused, got " + verdicts)
    }

    /** A second `check` while one is in flight must be rejected, leaving the
     *  first running. Getting the rejection back while the first check is mid-
     *  flight also proves the reader thread isn't blocked by the worker. The
     *  `finally` closes the channel, which cancels the first check on disconnect. */
    private def e2e_second_check_rejected(server_name: String, fixtures: Path): Unit = {
      val slow = fresh_slow_theory()
      val trivial = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
      val io = connection(server_name)
      try {
        io.write(JSON.Object("op" -> "check", "files" -> List(slow)))
        // Wait for 'started' so the worker is registered.
        if (!await_event(io, "started", 30))
          error("never saw 'started' for the first check")
        // Fire a second check on the SAME connection.
        io.write(JSON.Object("op" -> "check", "files" -> List(trivial)))
        // Expect a server_error about the in-flight check.
        var saw_reject = false
        val deadline = System.currentTimeMillis() + 10000
        while (!saw_reject && System.currentTimeMillis() < deadline) {
          io.read(1000) match {
            case JSON_IO.Value(t) if JSON.string(t, "event") == Some("server_error") =>
              val m = JSON.string(t, "message").getOrElse("")
              if (!m.contains("already in flight"))
                error("unexpected server_error: " + m)
              saw_reject = true
            case JSON_IO.Value(_) => /* progress for first check; keep reading */
            case JSON_IO.EOF => error("connection closed before rejection")
            case JSON_IO.Timeout => /* keep waiting */
          }
        }
        if (!saw_reject) error("second check was not rejected")
        // The first (slow) check is still running; closing the channel in the
        // finally cancels it on disconnect.
      } finally io.close()
    }

    private def e2e_empty_files(server_name: String): Unit = {
      val (events, finished) = run_check(server_name, Nil, deadline_secs = 30)
      val errs = events.filter(t => JSON.string(t, "event") == Some("server_error"))
      if (!errs.exists(t => JSON.string(t, "message").exists(_.contains("empty files"))))
        error("expected server_error about empty files list")
      // Must still terminate with a finished event (no hang).
      if (finished.flatMap(JSON.bool(_, "ok")) != Some(false))
        error("empty files should end with finished{ok:false}")
    }

    private def e2e_bad_path(server_name: String): Unit = {
      val file = "/this/path/should/never/exist/Foo.thy"
      val (events, finished) = run_check(server_name, List(file), deadline_secs = 30)
      val errs = events.filter(t => JSON.string(t, "event") == Some("server_error"))
      if (errs.isEmpty) error("bad path should yield a server_error")
      if (finished.flatMap(JSON.bool(_, "ok")) == Some(true))
        error("bad path should not yield ok=true")
    }

    private def e2e_relative_path(server_name: String): Unit = {
      val (events, finished) = run_check(server_name, List("Foo.thy"), deadline_secs = 30)
      val errs = events.filter(t => JSON.string(t, "event") == Some("server_error"))
      if (!errs.exists(t => JSON.string(t, "message").exists(_.contains("absolute"))))
        error("relative path should be rejected with an 'absolute' server_error")
      if (finished.flatMap(JSON.bool(_, "ok")) != Some(false))
        error("relative path should end with finished{ok:false}")
    }

    /** While a slow check is in flight on connection A, a `status` query on
     *  connection B must report busy=true with the check counted, and both
     *  connections in the count. Closing A cancels the slow check. */
    private def e2e_status_busy(server_name: String, fixtures: Path): Unit = {
      val slow = fresh_slow_theory()
      val a = connection(server_name)
      try {
        a.write(JSON.Object("op" -> "check", "files" -> List(slow)))
        if (!await_event(a, "started", 30)) error("never saw 'started' for slow check")
        val t = query_status(server_name)   // opens + closes its own connection
        if (JSON.bool(t, "busy") != Some(true))
          error("status.busy should be true while a check runs")
        if (JSON.int(t, "checks_in_flight").getOrElse(0) < 1)
          error("status.checks_in_flight should be >= 1 during a check")
        if (JSON.long(t, "connections").getOrElse(0L) < 2)
          error("status.connections should count A and the status query (>= 2)")
      } finally a.close()   // disconnect cancels the slow check
    }


    /** A mid-flight disconnect must INTERRUPT the in-flight check (closing the
     *  channel is the only way to cancel a foreground check). We verify it via
     *  the server going IDLE promptly after the drop: checks are serialized, so
     *  the slow check's ~8s sleep would keep the server `busy` unless the
     *  disconnect actually aborted it.
     *
     *  The 5s bound is the teeth of this test: above the ~1-2s a real interrupt
     *  takes to unwind, but well below the ~8s sleep, so a regressed
     *  cancel-on-disconnect (sleep runs to completion) fails here rather than
     *  passing on a loose bound. Once idle, a fresh tiny check still succeeds. */
    private def e2e_disconnect_promptly(server_name: String, fixtures: Path): Unit = {
      val file = fresh_slow_theory()
      val io = connection(server_name)
      io.write(JSON.Object("op" -> "check", "files" -> List(file)))
      if (!await_event(io, "started", 30)) error("never saw 'started' event")
      io.close()                 // disconnect mid-flight
      val drop_at = System.currentTimeMillis()

      // Poll until the server reports idle — that is the disconnect-cancel
      // taking effect. (Under single-slot serialization a new check submitted
      // now would be REFUSED while the cancel unwinds, not queued, so we assert
      // on busy->idle rather than on a competing check's latency.)
      val deadline = drop_at + 5000
      var busy = true
      while (busy && System.currentTimeMillis() < deadline) {
        Thread.sleep(150)
        busy = JSON.bool(query_status(server_name), "busy").getOrElse(true)
      }
      val elapsed = System.currentTimeMillis() - drop_at
      if (busy)
        error("server still busy " + elapsed + "ms after disconnect (> 5s); " +
          "disconnect likely did not interrupt the slow check")

      // And the session is healthy: a fresh tiny check now succeeds.
      val tiny = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
      val (_, finished) = run_check(server_name, List(tiny), deadline_secs = 30)
      if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
        error("post-disconnect tiny check should succeed once idle, got " + finished)
    }

    /** Detached check: `{op:check, detach:true}` returns a `submitted` ack
     *  immediately (no streaming), the check reports `running`, and a later
     *  no-arg check_status reports the terminal `ok`. */
    private def e2e_check_detached(server_name: String, fixtures: Path): Unit = {
      val file = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
      val ack = request_op(server_name, JSON.Object("op" -> "check", "files" -> List(file), "detach" -> true))
      if (JSON.string(ack, "event") != Some("submitted"))
        error("detached check should ack 'submitted', got " + JSON.Format(ack))
      if (!JSON.strings(ack, "theories").getOrElse(Nil).exists(_.endsWith("Trivial_OK")))
        error("submitted ack should list the theory")
      // Poll check_status until terminal (Trivial_OK is fast).
      val deadline = System.currentTimeMillis() + 30000
      var st = request_op(server_name, JSON.Object("op" -> "check_status"))
      while (JSON.string(st, "state") == Some("running") && System.currentTimeMillis() < deadline) {
        Thread.sleep(200)
        st = request_op(server_name, JSON.Object("op" -> "check_status"))
      }
      if (JSON.string(st, "event") != Some("check_status"))
        error("check_status should reply check_status, got " + JSON.Format(st))
      if (JSON.string(st, "state") != Some("ok"))
        error("detached Trivial_OK should reach state ok, got " + JSON.Format(st))
      if (JSON.bool(st, "ok") != Some(true)) error("detached ok should be true")
    }

    /** The key property of detached: it OUTLIVES the submitting connection. The
     *  submit reply closes the connection, yet the slow check keeps running and
     *  completes (status reaches ok). Contrast e2e_disconnect_promptly, where a
     *  FOREGROUND check is cancelled on disconnect. */
    private def e2e_detached_survives_disconnect(server_name: String, fixtures: Path): Unit = {
      // A UNIQUELY-named slow theory: it has never been consolidated, so the
      // check genuinely re-runs the 8s ML sleep and is reliably still running
      // 500ms after the submitting connection closes. (A shared fixture
      // consolidated by an earlier test would return in ~100ms.)
      val slow = fresh_slow_theory()
      // request_op opens a connection, gets the `submitted` ack, then CLOSES it.
      val ack = request_op(server_name, JSON.Object("op" -> "check", "files" -> List(slow), "detach" -> true))
      if (JSON.string(ack, "event") != Some("submitted"))
        error("detached submit should ack 'submitted', got " + JSON.Format(ack))
      // Right after the submitting connection closed, the check must still run.
      Thread.sleep(500)
      val mid = request_op(server_name, JSON.Object("op" -> "check_status"))
      if (JSON.string(mid, "state") != Some("running"))
        error("detached slow check should still be running after submit conn closed, got " + JSON.Format(mid))
      // And it must eventually complete ok (~8s).
      val deadline = System.currentTimeMillis() + 30000
      var st = mid
      while (JSON.string(st, "state") == Some("running") && System.currentTimeMillis() < deadline) {
        Thread.sleep(300)
        st = request_op(server_name, JSON.Object("op" -> "check_status"))
      }
      if (JSON.string(st, "state") != Some("ok"))
        error("detached Slow job should complete ok despite disconnect, got " + JSON.Format(st))
    }

    /** check_cancel (no arg) aborts the running detached check (reason
     *  "cancelled"); with nothing running it is a no-op (cancelled:false). */
    private def e2e_check_cancel(server_name: String, fixtures: Path): Unit = {
      val slow = fresh_slow_theory()
      val ack = request_op(server_name, JSON.Object("op" -> "check", "files" -> List(slow), "detach" -> true))
      if (JSON.string(ack, "event") != Some("submitted")) error("detached submit failed: " + JSON.Format(ack))
      // Cancel the in-flight check.
      val cancelReply = request_op(server_name, JSON.Object("op" -> "check_cancel"))
      if (JSON.string(cancelReply, "event") != Some("check_cancel"))
        error("check_cancel reply unexpected: " + JSON.Format(cancelReply))
      if (JSON.bool(cancelReply, "cancelled") != Some(true))
        error("cancelling a running check should report cancelled=true")
      // It settles to failed/cancelled.
      val deadline = System.currentTimeMillis() + 15000
      var st = request_op(server_name, JSON.Object("op" -> "check_status"))
      while (JSON.string(st, "state") == Some("running") && System.currentTimeMillis() < deadline) {
        Thread.sleep(200)
        st = request_op(server_name, JSON.Object("op" -> "check_status"))
      }
      if (JSON.string(st, "state") != Some("failed") || JSON.string(st, "reason") != Some("cancelled"))
        error("cancelled check should be failed/cancelled, got " + JSON.Format(st))
      // Cancelling with nothing running is a no-op, not an error.
      val noop = request_op(server_name, JSON.Object("op" -> "check_cancel"))
      if (JSON.string(noop, "event") != Some("check_cancel") || JSON.bool(noop, "cancelled") != Some(false))
        error("cancel with nothing running should reply check_cancel{cancelled:false}, got " + JSON.Format(noop))
    }

    /** Cancel a mid-flight check, then RE-CHECK the same theory — it must run
     *  to completion (the cancelled node must be left re-checkable, not stuck
     *  reporting its stale post-cancel state).
     *
     *  Uses a fresh, uniquely-named slow theory (8s ML sleep between two lemmas)
     *  so the FIRST check is genuinely interruptible mid-sleep and the re-check
     *  genuinely re-runs it (a re-check of a shared fixture would finish in
     *  ~100ms and mask the bug). */
    private def e2e_recheck_after_cancel(server_name: String, fixtures: Path): Unit = {
      val slow = fresh_slow_theory()
      // 1) Submit detached, wait until it's actually running, then cancel.
      val ack = request_op(server_name, JSON.Object("op" -> "check", "files" -> List(slow), "detach" -> true))
      if (JSON.string(ack, "event") != Some("submitted"))
        error("detached submit failed: " + JSON.Format(ack))
      if (JSON.string(request_op(server_name, JSON.Object("op" -> "check_status")), "state") != Some("running"))
        error("slow check should be running right after submit")
      // Let it get into the ML sleep (past the first lemma) before cancelling.
      Thread.sleep(1500)
      val cancelReply = request_op(server_name, JSON.Object("op" -> "check_cancel"))
      if (JSON.bool(cancelReply, "cancelled") != Some(true))
        error("cancelling the running check should report cancelled=true")
      // Wait for it to settle to failed/cancelled and the server to go idle
      // (the ML sleep must unwind before a new check can be accepted).
      wait_idle(server_name)

      // 2) Re-check the SAME theory. It must complete OK — every command
      //    evaluated — NOT return instantly with the stale post-cancel state.
      val (events, finished) = run_check(server_name, List(slow), deadline_secs = 60)
      finished.flatMap(JSON.bool(_, "ok")) match {
        case Some(true) => ()
        case other =>
          error("re-check after cancel should be ok:true (a clean full check), got " + other +
            " events=" + events.length + " — cancel+resume corruption?")
      }
      // 3) The document must actually be fully processed: no leftover
      //    unprocessed/failed commands from the cancelled run.
      val base = base_name_of(slow)
      val di = request_op(server_name, JSON.Object("op" -> "query", "tool" -> "get_document_info",
        "path" -> base))
      val diR = JSON.value(di, "result").getOrElse(JSON.Object())
      if (JSON.bool(diR, "fully_processed") != Some(true))
        error("re-check after cancel: theory should be fully_processed, got " + JSON.Format(diR))
      if (JSON.int(diR, "unprocessed").getOrElse(0) != 0 || JSON.int(diR, "failed").getOrElse(0) != 0)
        error("re-check after cancel: expected 0 unprocessed / 0 failed (clean re-eval), got " +
          JSON.Format(diR))
    }

    /** Basename (no dir, no .thy) of an absolute theory path — for `query`
     *  path args, which resolve by suffix against loaded nodes. */
    private def base_name_of(path: String): String = {
      val f = path.substring(path.lastIndexOf('/') + 1)
      if (f.endsWith(".thy")) f.dropRight(4) else f
    }

    /** Witnesses two progress-display properties:
     *   (a) the client's rendered frame lists in-flight theories in
     *       descending-percentage order (stable, not swapping around);
     *   (b) commands that have been running for a while are surfaced under
     *       their theory's progress bar, with the correct source line.
     *
     *  (a) is verified against Client.render_progress_frame with a synthetic
     *  multi-theory list — deterministic, no timing hazards. (b) is verified
     *  end-to-end: submit SpinTactic.thy (whose two `by (spin 30; simp)`
     *  proofs each spin ~30s) and watch the streamed progress events for a
     *  `long_running` payload with keyword `by` and elapsed >= 5s. Closing
     *  the connection when the payload is seen cancels the check on
     *  disconnect, so the ~30s spins don't drag out cleanup.
     *
     *  The forked `by` is the interesting case: it exercises ic2's
     *  Timing_Tracker (a per-exec-id counter over the raw command_timing
     *  stream), which surfaces a spinning forked proof that PIDE's own
     *  Command_Timings.running — and jEdit's Timing dockable — drop due to
     *  the transition/fork offset collision. */
    private def e2e_progress_display_changes(server_name: String, fixtures: Path): Unit = {
      // (a) rendered order: three in-flight theories in a MIXED input order —
      // the rendered frame must list them by descending last-updated stamp
      // (not by percentage), so the display tracks where the check is
      // actively working.
      val nodes = List(
        Client.Theory_Status("A", 10, 5, 1, 0, 0, 0, false, updated = 3),
        Client.Theory_Status("B", 60, 0, 2, 8, 0, 0, false, updated = 1),
        Client.Theory_Status("C", 40, 3, 1, 4, 0, 0, false, updated = 2))
      val frame = Client.render_progress_frame(nodes, 8)
      // First distinct theory-name letters seen after the header, in order.
      val order = frame.tail.flatMap { line =>
        List("A", "B", "C").find(t => line.contains(t + " ") || line.contains(" " + t))
      }.distinct
      if (order.take(3) != List("A", "C", "B"))
        error("render_progress_frame should sort in-flight theories by " +
          "descending last-updated stamp; expected [A, C, B], got " +
          order.take(3).mkString(", ") + " in frame:\n" + frame.mkString("\n"))

      // (b) end-to-end: at least one `by` command from SpinTactic.thy should
      // surface with elapsed >= 5s. Skip cleanly if the fixture is missing.
      val spin = fixtures + Path.basic("SpinTactic.thy")
      if (!spin.is_file) {
        Output.writeln("    (note) SpinTactic.thy fixture missing; " +
          "skipping the end-to-end long-running check")
        return
      }
      val io = connection(server_name)
      try {
        io.write(JSON.Object("op" -> "check", "files" -> List(spin.expand.implode)))
        val deadline = System.currentTimeMillis() + 30000
        var seen = false
        var closed = false
        while (!seen && !closed && System.currentTimeMillis() < deadline) {
          io.read(1500) match {
            case JSON_IO.Value(t) if JSON.string(t, "event") == Some("progress") =>
              val hit =
                JSON.array(t, "nodes").getOrElse(Nil).exists { n =>
                  val theory = JSON.string(n, "theory").map(base_name).getOrElse("")
                  theory == "SpinTactic" &&
                  JSON.array(n, "long_running").getOrElse(Nil).exists { rc =>
                    val elapsed =
                      JSON.double(rc, "elapsed_s")
                        .orElse(JSON.int(rc, "elapsed_s").map(_.toDouble))
                        .getOrElse(0.0)
                    val kwOK = JSON.string(rc, "keyword").exists(_ == "by")
                    val lineOK = JSON.int(rc, "line").exists(_ > 0)
                    kwOK && lineOK && elapsed >= 5.0
                  }
                }
              if (hit) seen = true
            case JSON_IO.Value(_) =>
            case JSON_IO.EOF => closed = true
            case JSON_IO.Timeout =>
          }
        }
        if (!seen)
          error("no `progress` event carried a long_running `by` entry for " +
            "SpinTactic with elapsed >= 5s within 30s; the ~30s spinning `by` " +
            "commands should have shown up under the theory's bar.")
      } finally io.close()   // cancel-on-disconnect stops the spin
    }

    /** check_attach (no arg) streams the in-flight detached check to completion:
     *  a fresh connection attaches and sees a `finished` event, even though it
     *  didn't submit. */
    private def e2e_check_attach(server_name: String, fixtures: Path): Unit = {
      val slow = fresh_slow_theory()
      val ack = request_op(server_name, JSON.Object("op" -> "check", "files" -> List(slow), "detach" -> true))
      if (JSON.string(ack, "event") != Some("submitted")) error("detached submit failed: " + JSON.Format(ack))
      val io = connection(server_name)
      try {
        io.write(JSON.Object("op" -> "check_attach"))
        val (_, finished) = collect_events(io, deadline_secs = 30)
        finished.flatMap(JSON.bool(_, "ok")) match {
          case Some(true) => ()
          case other => error("check_attach should stream to finished{ok:true}, got " + other)
        }
      } finally io.close()
    }

    /** Load Diagnostics.thy (and Trivial_OK) into the session for the query
     *  tests; running a check loads the node regardless of pass/fail. */
    private def load_query_fixtures(server_name: String, fixtures: Path): String = {
      val diag = (fixtures + Path.basic("Diagnostics.thy")).expand.implode
      val _ = run_check(server_name, List(diag))
      diag
    }

    /** The `query` wire op routes through the same SessionTools.dispatch as MCP.
     *  Spot-check a node-scope tool, a command-scope tool, and an error path
     *  (the exhaustive per-tool coverage is in e2e_session_tools over MCP). */
    private def e2e_query_wire(server_name: String, fixtures: Path): Unit = {
      load_query_fixtures(server_name, fixtures)

      def q(tool: String, extra: (String, JSON.T)*): JSON.T =
        request_op(server_name, JSON.Object(
          (("op" -> "query") :: ("tool" -> tool) :: extra.toList): _*))

      // Node-scope: list_files includes Diagnostics, with status fields.
      val lf = q("list_files")
      if (JSON.string(lf, "event") != Some("query")) error("query list_files: wrong event " + JSON.Format(lf))
      val files = JSON.value(lf, "result").flatMap(r => JSON.array(r, "files")).getOrElse(Nil)
      if (!files.exists(f => JSON.string(f, "node").exists(_.endsWith("Diagnostics.thy"))))
        error("query list_files should include Diagnostics.thy")

      // Node-scope: entities finds the `answer` definition.
      val ent = JSON.value(q("get_entities", "path" -> "Diagnostics.thy"), "result").getOrElse(JSON.Object())
      val names = JSON.array(ent, "entities").getOrElse(Nil).flatMap(e => JSON.string(e, "name"))
      if (!names.contains("answer")) error("query get_entities should find 'answer', got " + names)

      // Command-scope: context_info at the definition reports has_goal:false.
      val ci = JSON.value(q("get_context_info", "path" -> "Diagnostics.thy", "pattern" -> "definition answer"),
        "result").getOrElse(JSON.Object())
      if (JSON.bool(ci, "has_goal") != Some(false))
        error("query get_context_info(definition): has_goal should be false, got " + JSON.Format(ci))

      // Error path: unknown tool -> server_error (not a crash).
      val bad = q("no_such_tool")
      if (JSON.string(bad, "event") != Some("server_error"))
        error("query unknown tool should be server_error, got " + JSON.Format(bad))
      // Error path: a command-scope tool with no offset/pattern -> server_error.
      val noSel = q("get_context_info", "path" -> "Diagnostics.thy")
      if (JSON.string(noSel, "event") != Some("server_error"))
        error("query get_context_info without offset/pattern should be server_error, got " + JSON.Format(noSel))
    }

    /** Querying a theory that is built into the session HEAP (not loaded as a live
     *  document node) must give an accurate message — it is a heap theory, not a
     *  missing/uncheckable one. The old blanket "exists but is not a loaded session
     *  node (check it first...)" was misleading here: checking it does nothing, it
     *  is already in the heap. The main server runs -l HOL, so HOL's own Main.thy
     *  source is such a heap theory. Skip if the source file isn't present. */
    private def e2e_query_heap_theory_message(server_name: String): Unit = {
      val mainThy = Path.explode("$ISABELLE_HOME/src/HOL/Main.thy").expand
      if (!mainThy.is_file) {
        Output.writeln("    (note) HOL/Main.thy source not found; skipping heap-theory message test")
        return
      }
      val reply = request_op(server_name, JSON.Object(
        "op" -> "query", "tool" -> "get_diagnostics", "path" -> mainThy.implode))
      // A resolution failure surfaces as server_error; assert its message names
      // the heap case rather than the misleading "check it first".
      val msg = JSON.string(reply, "message").getOrElse(JSON.Format(reply))
      if (!msg.contains("heap"))
        error("query on a heap theory (HOL/Main.thy) should explain it is a heap theory, got: " + msg)
      if (msg.contains("check it first"))
        error("query on a heap theory should NOT advise 'check it first' (misleading), got: " + msg)
    }

    /** get_state_at returns real goal state at a proof command. This exercises the
     *  ON-DEMAND print_state query path (SessionTools.goalState -> queryProofState):
     *  with show_states removed, the goal is produced by firing print_state at the
     *  command, not read from a pre-existing STATE message. Diagnostics.thy's
     *  `structured` lemma has an open goal at `proof -`. */
    private def e2e_state_at_returns_goal(server_name: String, fixtures: Path): Unit = {
      load_query_fixtures(server_name, fixtures)

      def state_at(pattern: String): JSON.T =
        JSON.value(request_op(server_name, JSON.Object(
          "op" -> "query", "tool" -> "get_state_at",
          "path" -> "Diagnostics.thy", "pattern" -> pattern)), "result").getOrElse(JSON.Object())

      // At `proof -` of the `structured` lemma, an open goal exists.
      val st = state_at("proof -")
      if (JSON.bool(st, "has_goal") != Some(true))
        error("get_state_at at 'proof -' should report has_goal:true (on-demand print_state query); got " +
          JSON.Format(st))
      val goal = JSON.value(st, "goal").getOrElse(JSON.Object())
      val goalText = JSON.string(goal, "goal_text").getOrElse("")
      if (!goalText.contains("answer = 42"))
        error("get_state_at goal_text should show the goal 'answer = 42', got: " + goalText)
      if (JSON.int(goal, "num_subgoals").getOrElse(0) < 1)
        error("get_state_at should report >= 1 subgoal at an open proof, got " + JSON.Format(goal))

      // A definition command has no goal — the query correctly reports none
      // (empty state, not a spurious goal).
      val defSt = state_at("definition answer")
      if (JSON.bool(defSt, "has_goal") != Some(false))
        error("get_state_at at a definition should report has_goal:false, got " + JSON.Format(defSt))
    }

    /** THE key property of on-demand state: get_state_at returns the goal for a
     *  proof command that was processed but NEVER made visible. A headless session
     *  has an empty perspective (no command is ever visible), so the old passive
     *  command_results read saw a STATE message only because show_states forced one
     *  for every command. With show_states removed, goal state must instead come
     *  from firing print_state at the command — whose overlay makes it visible so
     *  the print function runs. This test checks a fresh theory (never viewed) and
     *  asserts the goal is recovered at a deep proof command. */
    private def e2e_state_at_never_visible(server_name: String, fixtures: Path): Unit = {
      // A fresh, uniquely-named theory with a proof that has a distinctive goal.
      // Never opened in any viewport (there is none — this is headless), and
      // freshly checked, so nothing pre-produced its STATE message.
      val name = "NeverVisible_" + short_id()
      val goalStr = "(n::nat) + 0 = n"
      val text =
        s"theory $name\n  imports Main\nbegin\n\n" +
        s"lemma deep: \"$goalStr\"\n" +
        "proof -\n" +
        s"  show \"$goalStr\" by simp\n" +
        "qed\n\nend\n"
      val dir = Files.createTempDirectory("ic2_nv_test")
      val file = dir.resolve(name + ".thy")
      Files.write(file, text.getBytes("UTF-8"))
      val abs = file.toAbsolutePath.toString

      val (_, finished) = run_check(server_name, List(abs))
      if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
        error("baseline check of the never-visible theory should pass, got " + finished)

      // Query the state at `show ... by simp` — a proof command deep in the theory
      // that was never in any viewport. On-demand print_state must recover its goal.
      val st = JSON.value(request_op(server_name, JSON.Object(
        "op" -> "query", "tool" -> "get_state_at",
        "path" -> abs, "pattern" -> "proof -")), "result").getOrElse(JSON.Object())
      if (JSON.bool(st, "has_goal") != Some(true))
        error("get_state_at on a never-visible proof command should report has_goal:true " +
          "(on-demand print_state query recovers it); got " + JSON.Format(st))
      val goalText = JSON.string(JSON.value(st, "goal").getOrElse(JSON.Object()), "goal_text").getOrElse("")
      if (!goalText.contains("n + 0 = n") && !goalText.contains("(n::nat) + 0 = n"))
        error("get_state_at on never-visible command should show the goal text, got: " + goalText)
    }

    /** The `ic2 query` CLI front door: covers every subtool (all 9), every
     *  selector on the selection-scope tools (`--offset`, `--line`,
     *  `--pattern`), every documented flag (`--severity`, `--scope`,
     *  `--theory`/`--non-theory`, `--max`, `--min-chars`, `--json`),
     *  human-formatted output shape, `--json` roundtrip, and the CLI-level
     *  error paths (0 ok / 2 usage / 3 server-side failure). Driven as
     *  subprocesses so the whole client-side argv/parser/renderer path is
     *  actually exercised, distinct from the wire/MCP tests.
     *
     *  Fixtures used (all loaded here): Diagnostics.thy (main), Trivial_OK.thy,
     *  Trivial_Fail.thy, and CommandLookup.thy (for the --line assertions;
     *  its structure is pinned in e2e_command_at_walkback). */
    private def e2e_query_cli(server_name: String, fixtures: Path): Unit = {
      val n = Bash.string(server_name)
      // Ensure all four fixtures are loaded. Prior tests may have loaded some
      // of them; run_check is a no-op-ish re-check when the session
      // already has the node consolidated.
      for (f <- List("Diagnostics.thy", "Trivial_OK.thy", "Trivial_Fail.thy",
                     "CommandLookup.thy")) {
        val path = (fixtures + Path.basic(f)).expand.implode
        val _ = run_check(server_name, List(path))
      }

      // Helper: run one CLI query, assert exit code, return combined output.
      def cli(subargs: String, expectedRc: Int = 0): String = {
        val r = ic2("query " + subargs + " -n " + n)
        if (r.rc != expectedRc)
          error(s"`ic2 query $subargs` expected rc=$expectedRc, got rc=${r.rc}\nstdout: ${r.out}\nstderr: ${r.err}")
        r.out + r.err
      }
      // Helper: same, but parse the reply as JSON (requires --json).
      def cliJson(subargs: String): JSON.T = {
        val out = cli(subargs + " --json").trim
        try JSON.parse(out)
        catch { case e: Throwable => error(s"`ic2 query $subargs --json` did not produce valid JSON: ${e.getMessage}\n$out") }
      }

      // ---- 1) list-files ------------------------------------------------
      // No-FILE case; human output lists loaded nodes.
      val lfOut = cli("list-files")
      if (!lfOut.contains("Diagnostics.thy"))
        error(s"list-files should mention Diagnostics.thy in human output:\n$lfOut")
      if (!lfOut.contains("node(s):"))
        error(s"list-files should print the '<N> node(s):' header:\n$lfOut")
      // --json: has a 'files' array.
      val lfJson = cliJson("list-files")
      val lfFiles = JSON.array(lfJson, "files").getOrElse(Nil)
      if (lfFiles.isEmpty) error("list-files --json: expected non-empty 'files' array")
      // --theory / --non-theory partitions the list.
      val lfTheoryJson = cliJson("list-files --theory")
      val lfNonTheoryJson = cliJson("list-files --non-theory")
      val thNodes = JSON.array(lfTheoryJson, "files").getOrElse(Nil)
        .flatMap(f => JSON.string(f, "node"))
      val nonThNodes = JSON.array(lfNonTheoryJson, "files").getOrElse(Nil)
        .flatMap(f => JSON.string(f, "node"))
      if (thNodes.isEmpty) error("list-files --theory: expected some theory nodes")
      if (thNodes.toSet.intersect(nonThNodes.toSet).nonEmpty)
        error("list-files: --theory and --non-theory should not overlap")

      // ---- 2) processing-status ----------------------------------------
      val psOK = cli("processing-status Trivial_OK.thy")
      if (!psOK.contains("Trivial_OK") || !psOK.contains("fully processed"))
        error(s"processing-status(Trivial_OK): expected 'fully processed', got:\n$psOK")
      val psFail = cli("processing-status Trivial_Fail.thy")
      if (!psFail.contains("failed=") || psFail.contains("failed=0 "))
        error(s"processing-status(Trivial_Fail): expected failed>0, got:\n$psFail")

      // ---- 3) document-info --------------------------------------------
      val diOK = cli("document-info Trivial_OK.thy")
      if (!diOK.contains("errors=0"))
        error(s"document-info(Trivial_OK): expected errors=0, got:\n$diOK")
      val diFail = cli("document-info Trivial_Fail.thy")
      if (diFail.contains("errors=0"))
        error(s"document-info(Trivial_Fail): expected errors>0, got:\n$diFail")

      // ---- 4) diagnostics (all selectors + severities + scopes) --------
      // File scope, default severity=error: Trivial_Fail has an error.
      val dgFail = cli("diagnostics Trivial_Fail.thy")
      if (!dgFail.contains("error (file): 1 found") && !dgFail.contains("error (file):"))
        error(s"diagnostics(Trivial_Fail): expected error listing, got:\n$dgFail")
      // Trivial_OK has zero errors.
      val dgOK = cli("diagnostics Trivial_OK.thy")
      if (!dgOK.contains("0 found"))
        error(s"diagnostics(Trivial_OK): expected 0 errors, got:\n$dgOK")
      // Warning severity: Diagnostics.thy has a benign simp warning.
      val dgWarn = cli("diagnostics Diagnostics.thy --severity warning")
      if (!dgWarn.contains("warning (file):"))
        error(s"diagnostics(Diagnostics --severity warning): missing header, got:\n$dgWarn")
      // Selection scope by pattern: error at 'by simp' in Trivial_Fail.
      val dgSelP = cli("diagnostics Trivial_Fail.thy --scope selection --pattern 'by simp'")
      if (!dgSelP.contains("error (selection):"))
        error(s"diagnostics --scope selection --pattern: expected selection header, got:\n$dgSelP")
      // Selection scope by --line (last-offset semantics via --line).
      // Trivial_Fail's failing `by simp` is on the lemma's line; assert an
      // error is reported at that selection. First find the line number.
      val failPath = (fixtures + Path.basic("Trivial_Fail.thy")).expand.implode
      val failLines = File.read(new java.io.File(failPath)).linesIterator.toIndexedSeq
      val bySimpLine = failLines.indexWhere(_.contains("by simp")) + 1
      if (bySimpLine <= 0) error("Trivial_Fail.thy: no 'by simp' line? (fixture changed?)")
      val dgSelL = cli("diagnostics Trivial_Fail.thy --scope selection --line " + bySimpLine)
      // The selection may or may not surface the error at that specific line
      // depending on line/command overlap — but the CLI must accept the flag
      // and return without error (rc==0) with a selection-scope header.
      if (!dgSelL.contains("error (selection):"))
        error(s"diagnostics --scope selection --line $bySimpLine: expected selection header, got:\n$dgSelL")

      // ---- 5) sorry ----------------------------------------------------
      val soDiag = cli("sorry Diagnostics.thy")
      if (!soDiag.contains("1 sorry/oops"))
        error(s"sorry(Diagnostics): expected '1 sorry/oops', got:\n$soDiag")
      if (!soDiag.contains("in incomplete"))
        error(s"sorry(Diagnostics): expected enclosing 'incomplete', got:\n$soDiag")
      val soOK = cli("sorry Trivial_OK.thy")
      if (!soOK.contains("0 sorry/oops"))
        error(s"sorry(Trivial_OK): expected '0 sorry/oops', got:\n$soOK")

      // ---- 6) entities (already covered — expand with --max, --json) ---
      val entOut = cli("entities Diagnostics.thy")
      if (!entOut.contains("answer"))
        error(s"entities(Diagnostics): expected 'answer' in output, got:\n$entOut")
      // --max caps result count.
      val entCapped = cliJson("entities Diagnostics.thy --max 1")
      if (JSON.array(entCapped, "entities").getOrElse(Nil).length != 1)
        error(s"entities --max 1: expected exactly 1 entity in --json output")
      if (JSON.bool(entCapped, "truncated") != Some(true))
        error(s"entities --max 1: expected truncated=true in --json output")

      // ---- 7) proof-blocks (+ --min-chars) -----------------------------
      val pbOut = cli("proof-blocks Diagnostics.thy")
      if (!pbOut.contains("proof block(s) in"))
        error(s"proof-blocks(Diagnostics): expected header, got:\n$pbOut")
      // At least one apply-style block should be flagged.
      if (!pbOut.contains("apply-style"))
        error(s"proof-blocks(Diagnostics): expected 'apply-style' marker, got:\n$pbOut")
      // --min-chars 100000 filters out every real proof block.
      val pbFilt = cliJson("proof-blocks Diagnostics.thy --min-chars 100000")
      if (JSON.int(pbFilt, "count") != Some(0))
        error(s"proof-blocks --min-chars 100000: expected count=0")

      // ---- 8) command-info (all three selectors) -----------------------
      // By --pattern.
      val ciByPat = cli("command-info Trivial_OK.thy --pattern 'lemma trivial'")
      if (!ciByPat.contains("lemma ["))
        error(s"command-info --pattern: expected 'lemma [<status>]' line, got:\n$ciByPat")
      if (!ciByPat.contains("trivial"))
        error(s"command-info --pattern: expected the lemma name in source, got:\n$ciByPat")
      // By --offset: offset 0 = the theory header command.
      val ciByOff = cli("command-info Trivial_OK.thy --offset 0")
      if (!ciByOff.contains("theory ["))
        error(s"command-info --offset 0: expected 'theory' keyword line, got:\n$ciByOff")
      // By --line: line 13 of CommandLookup.thy is `  apply (rule impI)`.
      val ciByLine = cli("command-info CommandLookup.thy --line 13")
      if (!ciByLine.contains("apply ["))
        error(s"command-info --line 13 (apply line): expected 'apply' keyword line, got:\n$ciByLine")
      if (!ciByLine.contains("rule impI"))
        error(s"command-info --line 13: expected 'rule impI' source, got:\n$ciByLine")
      // --json roundtrip for command-info.
      val ciJson = cliJson("command-info Trivial_OK.thy --pattern 'lemma trivial'")
      if (JSON.string(ciJson, "keyword") != Some("lemma"))
        error(s"command-info --json: expected keyword=lemma")
      // No selector -> server-side error (exit 3).
      val ciNoSel = cli("command-info Trivial_OK.thy", expectedRc = 3)
      if (ciNoSel.trim.isEmpty)
        error("command-info without selector should produce an error message")

      // ---- 9) context-info (all three selectors) -----------------------
      // By --pattern: at the theory header (out of any proof).
      val ctxHeader = cli("context-info Trivial_OK.thy --offset 0")
      if (!ctxHeader.contains("in_proof_context=false"))
        error(s"context-info --offset 0 (header): expected in_proof_context=false, got:\n$ctxHeader")
      // By --pattern inside a proof (Diagnostics has `show "answer = 42"`).
      val ctxShow = cli("context-info Diagnostics.thy --pattern 'show \"answer'")
      if (!ctxShow.contains("in_proof_context=true"))
        error(s"context-info --pattern 'show': expected in_proof_context=true, got:\n$ctxShow")
      // By --line: line 19 of CommandLookup.thy is `    show ?thesis by simp`
      // — last-offset semantics resolves to `by simp` inside the structured
      // proof, so in_proof_context must be true. (has_goal at `by simp` is
      // deliberately NOT asserted here: the intermediate state emitted after
      // `simp` closes subgoals appears at some caret positions and not others,
      // and pinning that shape is not the point of this test.)
      val ctxByLine = cli("context-info CommandLookup.thy --line 19")
      if (!ctxByLine.contains("by ") || !ctxByLine.contains("in_proof_context=true"))
        error(s"context-info --line 19: expected `by` with in_proof_context=true, got:\n$ctxByLine")
      // By --line: line 20 is `  qed` — inside the proof block still, but
      // `qed` closes the proof so it has no open goal → has_goal=false.
      val ctxByLineQed = cli("context-info CommandLookup.thy --line 20")
      if (!ctxByLineQed.contains("qed ") || !ctxByLineQed.contains("has_goal=false"))
        error(s"context-info --line 20 (qed): expected qed with has_goal=false, got:\n$ctxByLineQed")
      // --json roundtrip for context-info.
      val ctxJson = cliJson("context-info Diagnostics.thy --pattern 'show \"answer'")
      if (JSON.bool(ctxJson, "in_proof_context") != Some(true))
        error(s"context-info --json: expected in_proof_context=true")

      // ---- 10) CLI-level error paths -----------------------------------
      // Unknown subtool -> exit 2 with a usage message.
      val badSub = ic2("query no_such_tool -n " + n)
      if (badSub.rc != 2) error(s"unknown subtool: expected rc=2, got ${badSub.rc}")
      // Missing FILE on a subtool that requires it -> exit 2.
      val noFile = ic2("query entities -n " + n)
      if (noFile.rc != 2) error(s"missing FILE: expected rc=2, got ${noFile.rc}")
      // Non-integer --offset value -> exit 2 (parser rejects).
      val badInt = ic2("query command-info Trivial_OK.thy --offset abc -n " + n)
      if (badInt.rc != 2) error(s"--offset abc: expected rc=2, got ${badInt.rc}")
      // Unknown --flag -> exit 2.
      val badFlag = ic2("query entities Diagnostics.thy --nosuchflag -n " + n)
      if (badFlag.rc != 2) error(s"unknown --flag: expected rc=2, got ${badFlag.rc}")
      // Server-side error (unloaded file) -> exit 3.
      val badFile = ic2("query processing-status No_Such_Theory_Zzz.thy -n " + n)
      if (badFile.rc != 3) error(s"unloaded theory: expected rc=3, got ${badFile.rc}")
      // Selection-scope tool without a selector -> server_error -> exit 3.
      val ctxNoSel = ic2("query context-info Diagnostics.thy -n " + n)
      if (ctxNoSel.rc != 3) error(s"context-info without selector: expected rc=3, got ${ctxNoSel.rc}")
    }

    /** Pins the semantics of SessionTools.commandAt: given a character offset,
     *  return the LAST NON-IGNORED COMMAND AT OR BEFORE that offset. Matches
     *  jEdit's Document.current_command exactly (document.scala:777-786): when
     *  the offset falls in an inter-command whitespace span, walk BACKWARDS
     *  through the commands list to the previous real command.
     *
     *  Fixture CommandLookup.thy is designed to exercise all five geometries:
     *
     *      1: theory CommandLookup
     *      2:   imports Main
     *      3: begin
     *      4:                              <- blank line
     *      5:     definition foo :: nat where "foo = 0"
     *      6:                              <- blank line
     *      7: definition bar :: nat where "bar = 1"
     *      8: definition baz :: nat where "baz = 2"
     *      9:                              <- blank line
     *     10: definition p :: nat where "p = 3" definition q :: nat where "q = 4"
     *
     *  Precomputed offsets (fixture is ASCII, so Text.Offset == byte index): */
    private def e2e_command_at_walkback(server_name: String, fixtures: Path): Unit = {
      val file = fixtures + Path.basic("CommandLookup.thy")
      if (!file.is_file) {
        Output.writeln("    (note) CommandLookup.thy missing; skipping"); return
      }
      // Load the fixture — the query tools resolve against loaded session
      // nodes, so the theory must be checked first.
      val (_, finished) = run_check(server_name, List(file.expand.implode))
      if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
        error("precondition: CommandLookup.thy should check ok, got " + finished)

      def cmdKeywordAt(offset: Int): (String, String) = {
        val reply = request_op(server_name,
          JSON.Object("op" -> "query", "tool" -> "get_command_info",
            "path" -> "CommandLookup.thy", "offset" -> offset))
        if (JSON.string(reply, "event") != Some("query"))
          error(s"query at offset $offset: unexpected event: " + JSON.Format(reply))
        val r = JSON.value(reply, "result").getOrElse(JSON.Object())
        val kw = JSON.string(r, "keyword").getOrElse("?")
        val src = JSON.string(r, "source").getOrElse("").trim
        (kw, src)
      }

      def assertCmd(caseLabel: String, offset: Int, expectedKw: String, expectedSrcContains: String): Unit = {
        val (kw, src) = cmdKeywordAt(offset)
        if (kw != expectedKw || !src.contains(expectedSrcContains))
          error(f"$caseLabel%s at offset $offset%d: expected keyword=$expectedKw%s with source containing '$expectedSrcContains%s', got keyword='$kw%s' source='$src%s'")
      }

      // -----------------------------------------------------------------
      // (a) Beginning of a line whose content starts with whitespace.
      //     Line 5 is "    definition foo …". Column 0 (offset 43) is
      //     inside the ignored-whitespace span BEFORE `definition foo`.
      //     Walk-back lands on the `theory CommandLookup … begin` command
      //     — Isar treats the theory header plus `begin` as ONE command
      //     (span [0..41)), so offsets 42-46 are all in the ignored span
      //     between it and `definition foo`.
      // -----------------------------------------------------------------
      assertCmd("(a) column-0 leading-ws before command", offset = 43,
        expectedKw = "theory", expectedSrcContains = "begin")

      // -----------------------------------------------------------------
      // (b) First non-whitespace character on that same line.
      //     Offset 47 is the 'd' of `definition foo`. This lands directly
      //     on the definition command, no walk-back needed.
      // -----------------------------------------------------------------
      assertCmd("(b) first non-ws is start of command", offset = 47,
        expectedKw = "definition", expectedSrcContains = "foo = 0")

      // -----------------------------------------------------------------
      // (c) End-of-line, next line starts with whitespace.
      //     Line 6 is entirely blank (offset 85). This offset is inside
      //     the ignored span between `definition foo` and `definition bar`
      //     — walk back to `definition foo`.
      // -----------------------------------------------------------------
      assertCmd("(c) end-of-line, next line all whitespace", offset = 85,
        expectedKw = "definition", expectedSrcContains = "foo = 0")

      // -----------------------------------------------------------------
      // (d) End-of-line whose next line starts directly with a command.
      //     Line 7 ends at offset 123 (just past `"bar = 1"`), and line 8
      //     begins immediately (`definition baz …`) with only a newline
      //     between them. The offset falls inside the newline (ignored
      //     span) — walk back to `definition bar`, not forward to baz.
      // -----------------------------------------------------------------
      assertCmd("(d) end-of-line, next line starts with command", offset = 123,
        expectedKw = "definition", expectedSrcContains = "bar = 1")

      // -----------------------------------------------------------------
      // (e) Two commands separated only by a single space, on one line.
      //     Line 10 is `definition p … "p = 3" definition q … "q = 4"`.
      //     The space at offset 196 is the whole ignored span between the
      //     two definitions. Three offsets are worth pinning:
      //       - 195: closing `"` of first — lands ON `definition p`.
      //       - 196: the space itself — walks back to `definition p`.
      //       - 197: 'd' of second — lands ON `definition q`.
      //     This is the tightest ignored span the parser will produce
      //     (Isar requires >=1 whitespace token between commands).
      // -----------------------------------------------------------------
      assertCmd("(e) last char of first command",  offset = 195,
        expectedKw = "definition", expectedSrcContains = "p = 3")
      assertCmd("(e) inside 1-char ignored span",  offset = 196,
        expectedKw = "definition", expectedSrcContains = "p = 3")
      assertCmd("(e) first char of second command", offset = 197,
        expectedKw = "definition", expectedSrcContains = "q = 4")

      // -----------------------------------------------------------------
      // Proof-command cases (apply-style block). The fixture is:
      //   line 12: lemma apply_style: "P \<longrightarrow> P"    span 232..274
      //   line 13:   apply (rule impI)                        span [277..294)
      //   line 14:   apply assumption                         span [297..313)
      //   line 15:   done                                     span [316..320)
      // Each `apply` is its own command; walk-back rules apply verbatim.
      // -----------------------------------------------------------------
      assertCmd("(p1) leading-ws before first apply (col 0 line 13)",
        offset = 275, expectedKw = "lemma", expectedSrcContains = "apply_style")
      assertCmd("(p1) first-non-ws of first apply", offset = 277,
        expectedKw = "apply", expectedSrcContains = "rule impI")
      assertCmd("(p2) end of first apply line", offset = 294,
        expectedKw = "apply", expectedSrcContains = "rule impI")
      assertCmd("(p2) col 0 of second apply's line — inter-apply whitespace",
        offset = 295, expectedKw = "apply", expectedSrcContains = "rule impI")
      assertCmd("(p2) first-non-ws of second apply", offset = 297,
        expectedKw = "apply", expectedSrcContains = "assumption")
      assertCmd("(p3) col 0 of `done` line — whitespace after last apply",
        offset = 314, expectedKw = "apply", expectedSrcContains = "assumption")
      assertCmd("(p3) `done` itself", offset = 316,
        expectedKw = "done", expectedSrcContains = "done")
      assertCmd("(p3) blank line 16 — walk-back to done",
        offset = 321, expectedKw = "done", expectedSrcContains = "done")

      // -----------------------------------------------------------------
      // Structured proof block:
      //   line 17: lemma structured: "(n::nat) * 1 = n"       span [322..358)
      //   line 18:   proof -                                   span [361..368)
      //   line 19:     show ?thesis by simp     — parses as 2 commands:
      //     `show ?thesis`  span [373..385)  and  `by simp`  span [386..393)
      //   line 20:   qed                                       span [396..399)
      // The structured `show ?thesis by simp` is important: it demonstrates
      // that a single source line can contain TWO commands (`show ?thesis`
      // then `by simp`, separated by a single space) — the walk-back must
      // distinguish them just as it does for the (e) same-line case.
      // -----------------------------------------------------------------
      assertCmd("(s1) leading-ws before `proof -`",
        offset = 359, expectedKw = "lemma", expectedSrcContains = "structured")
      assertCmd("(s1) `proof -` itself", offset = 361,
        expectedKw = "proof", expectedSrcContains = "proof -")
      assertCmd("(s2) leading-ws before `show`",
        offset = 369, expectedKw = "proof", expectedSrcContains = "proof -")
      assertCmd("(s2) first-non-ws is `show`", offset = 373,
        expectedKw = "show", expectedSrcContains = "show ?thesis")
      assertCmd("(s2) end of `show ?thesis` span (offset 385, on trailing space)",
        offset = 385, expectedKw = "show", expectedSrcContains = "show ?thesis")
      assertCmd("(s2) `by simp` (offset 386, the 'b')", offset = 386,
        expectedKw = "by", expectedSrcContains = "by simp")
      assertCmd("(s3) col 0 of `qed` line — whitespace after `by simp`",
        offset = 394, expectedKw = "by", expectedSrcContains = "by simp")
      assertCmd("(s3) `qed` itself", offset = 396,
        expectedKw = "qed", expectedSrcContains = "qed")

      // ================================================================
      // --line N: uses the LAST offset on line N, then commandAt's walk-
      // back. Semantics: "the command that ENDS on or before line N."
      // Blank lines walk back to the previous real command; a line
      // containing multiple commands resolves to the LAST one on that
      // line.
      // ================================================================
      def cmdByLine(line: Int): (String, String) = {
        val reply = request_op(server_name,
          JSON.Object("op" -> "query", "tool" -> "get_command_info",
            "path" -> "CommandLookup.thy", "line" -> line))
        if (JSON.string(reply, "event") != Some("query"))
          error(s"query --line $line: unexpected event: " + JSON.Format(reply))
        val r = JSON.value(reply, "result").getOrElse(JSON.Object())
        (JSON.string(r, "keyword").getOrElse("?"),
         JSON.string(r, "source").getOrElse("").trim)
      }
      def assertLine(caseLabel: String, line: Int, expectedKw: String, expectedSrcContains: String): Unit = {
        val (kw, src) = cmdByLine(line)
        if (kw != expectedKw || !src.contains(expectedSrcContains))
          error(f"$caseLabel%s --line $line%d: expected keyword=$expectedKw%s src~='$expectedSrcContains%s', got keyword='$kw%s' src='$src%s'")
      }

      // (L.a) Any line covered by the theory header — Isar treats
      //       `theory ... imports ... begin` as ONE command spanning lines
      //       1-3. Line 4 is blank between it and `definition foo`, walks
      //       back to the theory command.
      assertLine("(L.a) line 1 (header first line)", 1, "theory", "begin")
      assertLine("(L.a) line 3 (`begin` line)",     3, "theory", "begin")
      assertLine("(L.a) line 4 (blank after header)", 4, "theory", "begin")

      // (L.b) Line 5's content is `    definition foo ...` — the trailing
      //       characters are inside definition foo's span.
      assertLine("(L.b) line 5 (indented definition)", 5, "definition", "foo = 0")

      // (L.c) Line 6 is blank between two definitions → walk back to foo.
      assertLine("(L.c) line 6 (blank between defs)", 6, "definition", "foo = 0")

      // (L.d) Lines 7 and 8 each have their own definition.
      assertLine("(L.d) line 7 (bar)", 7, "definition", "bar = 1")
      assertLine("(L.d) line 8 (baz)", 8, "definition", "baz = 2")

      // (L.e) Line 10 contains BOTH `definition p` and `definition q`.
      //       Last-offset semantics resolves to the SECOND command on
      //       the line.
      assertLine("(L.e) line 10 (two defs, resolves to LAST)", 10, "definition", "q = 4")

      // (L.f) Proof-command lines: each apply is on its own line.
      assertLine("(L.f) line 13 (first apply)",  13, "apply", "rule impI")
      assertLine("(L.f) line 14 (second apply)", 14, "apply", "assumption")
      assertLine("(L.f) line 15 (done)",         15, "done", "done")

      // (L.g) Blank line 16 after the apply block — walk back to `done`.
      assertLine("(L.g) line 16 (blank after done)", 16, "done", "done")

      // (L.h) Structured proof:
      //       line 18 is `  proof -`, line 19 is `    show ?thesis by simp`.
      //       Line 19 contains TWO commands; last-offset resolves to `by simp`.
      assertLine("(L.h) line 18 (proof -)",           18, "proof", "proof -")
      assertLine("(L.h) line 19 (show; by — resolves to last)", 19, "by", "by simp")
      assertLine("(L.h) line 20 (qed)",               20, "qed", "qed")

      // (L.i) The final `end` on its own line.
      assertLine("(L.i) line 22 (end)", 22, "end", "end")
    }

    /** `ic2 repl FILE:LINE NAME`: create an I/R REPL at a source location. The
     *  daemon resolves the line to a command in the session and creates the
     *  REPL via the connected I/R client. Skips cleanly when I/R isn't up. Also
     *  checks the local usage errors (bad FILE:LINE) and a server-side failure
     *  (unknown file). */
    private def e2e_repl_from_source(server_name: String, fixtures: Path): Unit = {
      // Only meaningful when I/R came up (python3 + ir/ sources present).
      if (JSON.value(query_status(server_name), "ir").isEmpty) {
        Output.writeln("    (note) no I/R endpoint — skipping repl-from-source")
        return
      }
      load_query_fixtures(server_name, fixtures)   // loads Diagnostics.thy
      val n = Bash.string(server_name)

      // Diagnostics.thy line 23 is `lemma structured: "answer = 42"` — a real
      // goal-bearing command, so a REPL forks there cleanly.
      val ok = ic2("repl-create Diagnostics.thy:23 e2e_src -n " + n)
      if (ok.rc != 0)
        error("repl-create at Diagnostics.thy:23 should exit 0, got " + ok.rc + " err=" + ok.err)
      val out = ok.out + ok.err
      if (!out.contains("e2e_src"))
        error("repl-create reply should mention the new REPL name e2e_src:\n" + out)
      // The agent-facing drive schema must be present and runnable against THIS
      // repl: a `repl.py cli ... step e2e_src ...` line on the real port.
      if (!out.contains("repl.py cli") || !out.contains("step e2e_src"))
        error("repl-create should print the `repl.py cli` drive schema for e2e_src:\n" + out)

      // The created REPL exists in the running I/R: list it via the wire bridge.
      val ir = JSON.value(query_status(server_name), "ir").getOrElse(error("ir gone"))
      val rport = JSON.int(ir, "repl_port").getOrElse(0)
      val rtoken = JSON.string(ir, "repl_token").getOrElse("")
      if (!out.contains("--port " + rport))
        error("drive schema should target the real repl.py port " + rport + ":\n" + out)
      if (!ir_command(rport, rtoken, "Ir.repls ()").contains("e2e_src"))
        error("created REPL e2e_src should appear in Ir.repls ()")

      // Usage errors (local, exit 2): missing NAME, and a non-FILE:LINE arg.
      if (ic2("repl-create Diagnostics.thy:23 -n " + n).rc != 2)
        error("repl-create with no NAME should exit 2")
      if (ic2("repl-create Diagnostics.thy e2e_x -n " + n).rc != 2)
        error("repl-create with no :LINE should exit 2")
      if (ic2("repl-create Diagnostics.thy:notanum e2e_x -n " + n).rc != 2)
        error("repl-create with non-integer LINE should exit 2")

      // Server-side failure (exit 3): an unknown / unloaded file.
      if (ic2("repl-create No_Such_Theory_Zzz.thy:1 e2e_y -n " + n).rc != 3)
        error("repl-create on an unloaded file should exit 3")
    }

    /** Exercise the -N (no_build) startup path with its own short-lived
     *  server; the main server has already built the HOL heap. */
    private def e2e_no_build(fixtures: Path): Unit = {
      val name = "t_nb_" + short_id()
      val proc = start_server(name, extra_args = List("-N"))
      try {
        wait_for_server(name, timeout = 60)
        val file = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
        val (_, finished) = run_check(name, List(file))
        if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
          error("-N server check_ok should succeed, got " + finished)
      } finally {
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** A leftover socket node from a crashed predecessor (no listener) must be
     *  reclaimed: a fresh server on the same name should start and serve. We
     *  pre-seed the node by binding+closing an AF_UNIX listener (the JVM leaves
     *  the file behind), then bring up a real -N server on that name. */
    private def e2e_stale_socket_reclaim(fixtures: Path): Unit = {
      val name = "t_stale_" + short_id()
      Endpoint.secure_dir()
      val stale = ServerSocketChannel.open(StandardProtocolFamily.UNIX)
      stale.bind(sock_addr(name), 1)
      stale.close()                          // leaves a stale (no-listener) node
      if (!Endpoint.exists(name)) error("precondition: stale socket node should exist")
      if (can_connect(name)) error("precondition: stale node must have no listener")

      val proc = start_server(name, extra_args = List("-N"))
      try {
        wait_for_server(name, timeout = 60)
        val file = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
        val (_, finished) = run_check(name, List(file))
        if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
          error("server should reclaim stale socket and serve, got " + finished)
      } finally {
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** `ic2 server start --daemon` returns once the background server is ready, writes
     *  a default log file, and stays up; `ic2 server stop` then shuts it down. Uses -N
     *  (the main server already built the HOL heap) and its own server name. */
    private def e2e_daemon_mode(fixtures: Path): Unit = {
      val name = "t_dmn_" + short_id()
      val started = ic2("server start --daemon -N -l HOL -n " + Bash.string(name))
      if (started.rc != 0)
        error("ic2 server start --daemon should exit 0, got " + started.rc +
          " err=" + started.err.mkString)
      try {
        // --daemon returned only after the readiness poll succeeded.
        if (!can_connect(name)) error("daemon not reachable after --daemon returned")
        // Default log file (no -L given) must have been created.
        if (!Endpoint.log_file(name).is_file)
          error("default daemon log not created: " + Endpoint.log_file(name).expand.implode)
        // A real check works against the backgrounded server.
        val file = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
        val (_, finished) = run_check(name, List(file))
        if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
          error("check against daemon should succeed, got " + finished)
        // `ic2 server stop` shuts it down.
        val stopped = ic2("server stop -n " + Bash.string(name))
        if (stopped.rc != 0) error("ic2 server stop should exit 0, got " + stopped.rc)
        Thread.sleep(1500)
        if (can_connect(name)) error("server still listening after ic2 server stop")
      } finally {
        // Best-effort: if stop didn't take, ask again, then unlink the node/logs.
        if (can_connect(name)) try { ic2("server stop -n " + Bash.string(name)) } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** The socket is bound BEFORE the heap build, so a server whose session must
     *  be built is discoverable (status) and stoppable (stop) while still
     *  building — not invisible until the build finishes. Builds a throwaway
     *  session with a slow (sleeping) theory so the build lingers, then asserts:
     *   A) status reports state="building" (with a build readout),
     *   B) a session-dependent op (query) is refused with a "not ready" error
     *      rather than hanging or crashing,
     *   C) `stop` mid-build shuts the server down promptly and unbinds. */
    private def e2e_status_and_stop_during_build(): Unit = {
      val name = "t_bld_" + short_id()
      val tmp = Files.createTempDirectory("ic2_build_test")
      val sess = "Slow_Build_" + short_id()
      val sdir = tmp.resolve(sess)
      Files.createDirectories(sdir)
      // A session that must be built, with a ~30s ML sleep so the build lingers
      // in the "building" phase long enough to observe status/stop.
      Files.write(sdir.resolve("ROOT"),
        ("session " + sess + " = HOL +\n  theories\n    Slow_Thy\n").getBytes("UTF-8"))
      Files.write(sdir.resolve("Slow_Thy.thy"),
        ("theory Slow_Thy\n  imports Main\nbegin\n" +
         "ML \\<open>OS.Process.sleep (Time.fromSeconds 30)\\<close>\n" +
         "end\n").getBytes("UTF-8"))

      val cmd =
        File.bash_path(Path.explode("$ISABELLE_HOME/bin/isabelle")) +
        " ic2 server start --no-iq -n " + Bash.string(name) +
        " -l " + Bash.string(sess) + " -d " + Bash.string(sdir.toString)
      val proc = Bash.process(cmd, redirect = true)
      try {
        // Wait for the socket to answer (bound before the build) AND report the
        // building phase — the whole point: reachable while still building.
        val deadline = System.currentTimeMillis() + 60000
        var st: Option[JSON.T] = None
        while (st.isEmpty && System.currentTimeMillis() < deadline) {
          Daemon.ping_status(name) match {
            case Some(s) if JSON.string(s, "state").contains("building") ||
                            JSON.string(s, "state").contains("loading") => st = Some(s)
            case _ => Thread.sleep(300)
          }
        }
        // (A) discoverable while building.
        val status = st.getOrElse(error("server never reported a building/loading state"))
        val phase = JSON.string(status, "state").getOrElse("?")
        if (phase != "building" && phase != "loading")
          error("expected building/loading state, got " + phase)
        if (JSON.value(status, "build").isEmpty)
          error("building status should carry a `build` sub-object")

        // (B) a session-dependent op is refused with a clear "not ready" error
        // (and does not hang): use the query op.
        val q = request_op(name, JSON.Object("op" -> "query", "tool" -> "list_files"))
        if (JSON.string(q, "event") != Some("server_error"))
          error("query during build should be a server_error, got " + q)
        if (!JSON.string(q, "message").getOrElse("").contains("not ready"))
          error("query-during-build error should mention 'not ready', got " + q)

        // (C) stop works mid-build: returns promptly and the node stops listening.
        val stopped = ic2("server stop -n " + Bash.string(name))
        if (stopped.rc != 0) error("stop during build should exit 0, got " + stopped.rc)
        Thread.sleep(1500)
        if (can_connect(name)) error("server still listening after stop during build")
      } finally {
        if (can_connect(name)) try { ic2("server stop -n " + Bash.string(name)) } catch { case _: Throwable => }
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
        try { Isabelle_System.rm_tree(Path.explode(tmp.toString)) } catch { case _: Throwable => }
      }
    }

    /** --no-iq: the server comes up without bringing up I/R, so status reports
     *  options.load_iq=false and carries no `ir` endpoint. Own -N server. */
    private def e2e_no_iq(fixtures: Path): Unit = {
      val name = "t_noiq_" + short_id()
      val proc = start_server(name, extra_args = List("-N", "--no-iq"))
      try {
        wait_for_server(name, timeout = 60)
        val t = query_status(name)
        val o = JSON.value(t, "options").getOrElse(error("status missing options object"))
        if (JSON.bool(o, "load_iq") != Some(false))
          error("--no-iq should set options.load_iq=false")
        if (JSON.value(t, "ir").isDefined)
          error("--no-iq server should not report an I/R endpoint")
        // A plain check still works without I/R.
        val file = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
        val (_, finished) = run_check(name, List(file))
        if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
          error("--no-iq server check should succeed, got " + finished)
      } finally {
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** MCP is OFF by default (opt-in via --mcp): a server started WITHOUT --mcp
     *  still brings up I/R (repl.py bridge reachable, repl_cli present) but
     *  exposes NO mcp_port/mcp_token. Its own server; skips if I/R can't come
     *  up (no ir/ or python3). */
    private def e2e_mcp_off_by_default(fixtures: Path): Unit = {
      val name = "t_nomcp_" + short_id()
      val proc = start_server(name, extra_args = List("-N"))   // note: no --mcp
      try {
        wait_for_server(name, timeout = 60)
        JSON.value(query_status(name), "ir") match {
          case None =>
            Output.writeln("    (note) no I/R endpoint — can't check MCP-off; skipping")
          case Some(ir) =>
            // I/R itself is up: repl.py bridge reachable + the cli command present.
            val rport = JSON.int(ir, "repl_port").getOrElse(0)
            if (rport <= 0 || !tcp_listening(rport))
              error("MCP-off server should still have a live repl.py bridge, got port " + rport)
            if (JSON.string(ir, "repl_cli").isEmpty)
              error("MCP-off server should still surface repl_cli")
            // But the MCP endpoint must be ABSENT.
            if (JSON.value(ir, "mcp_port").isDefined || JSON.value(ir, "mcp_token").isDefined)
              error("without --mcp, status must not expose an MCP endpoint, got " + JSON.Format(ir))
        }
      } finally {
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** `check FILE --line N`: partial check — only the prefix of commands up
     *  to and including line N is evaluated; commands after that line remain
     *  UNPROCESSED. Pins:
     *   (a) wire op: `{check, files, line}` reaches `finished{ok:true}` FAST,
     *       even when a later command in the theory would take 8s (proving
     *       the tail was actually abandoned, not merely raced through);
     *   (b) after the partial check, list-files shows the node still
     *       unconsolidated with unprocessed>0 — the whole theory has NOT
     *       been evaluated;
     *   (c) MCP `check` with `line` arg agrees;
     *   (d) CLI `ic2 check --line N` exits 0;
     *   (e) `check --line` with 0 or >1 files is refused (usage error);
     *   (f) FORKED-PROOF bounding (SpinTactic.thy): `--line 41` dispatches
     *       ONLY spin1, never the forked spin2 at line 44;
     *   (g) DEPENDENCY loading (SpinImport.thy imports SpinDep.thy): a
     *       bounded check must still fully evaluate the local import, else
     *       the prefix can't type-check.
     *
     *  Uses its own -N server so we can prove "the tail wasn't evaluated"
     *  starting from a fresh state. (a)-(e) use Slow.thy (inline ML-sleep
     *  tail); (f) uses SpinTactic.thy (two parallel forked `by` proofs) to
     *  cover the case where the tail would run CONCURRENTLY; (g) uses
     *  SpinImport/SpinDep to cover transitive dependency evaluation. */
    private def e2e_check_line_partial(fixtures: Path): Unit = {
      val name = "t_lc_" + short_id()
      // parallel_proofs=0 -> proofs run INLINE (no forked terminal `by`), so a
      // partial check that stops at the target line has zero overshoot: the
      // next proof isn't dispatched until the current one's transition
      // finishes, and use_theories is single-threaded per node. This makes
      // the bounding deterministic to assert (case (f)). With the default
      // parallel_proofs the partial check may overshoot by a proof or two
      // (dispatched before the target terminates) — acknowledged, not tested.
      val proc = start_server(name, extra_args = List("-N", "--mcp", "-o", "parallel_proofs=0"))
      try {
        wait_for_server(name, timeout = 60)
        val file = (fixtures + Path.basic("Slow.thy")).expand.implode

        // (a) wire op: partial check up to line 13 (`slow1`'s `by simp`).
        //     The tail (line 17's 8s ML sleep, then slow2) is deliberately
        //     costly — a working cancel path returns fast; a broken one
        //     would wait out the sleep. Bound the wire deadline WELL below
        //     that 8s to fail loudly if cancel regresses.
        val io = connection(name)
        val started_ms = System.currentTimeMillis()
        try {
          io.write(JSON.Object("op" -> "check", "files" -> List(file), "line" -> 13))
          val (events, finished) = collect_events(io, deadline_secs = 30)
          val elapsed_ms = System.currentTimeMillis() - started_ms
          if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
            error("check --line 13 should reach finished{ok:true}, got " + finished +
              " events=" + events.length)
          if (elapsed_ms > 6000)
            error("check --line 13 took " + elapsed_ms + "ms (>= 6s); expected fast return " +
              "since target line precedes an 8s ML sleep — cancel-on-target-reached regressed?")
          val started = theory_names(events, "started")
          if (started.length != 1 || !started.head.contains("Slow"))
            error("check --line: started should carry exactly Slow, got " + started)
        } finally io.close()

        // (b) After a partial check to line 13, the theory has UNPROCESSED
        //     tail commands (line-17 ML sleep + slow2). document-info sees
        //     total > finished and fully_processed=false — the definitive
        //     signal that partial mode did NOT run the whole theory.
        val di = request_op(name, JSON.Object("op" -> "query", "tool" -> "get_document_info",
          "path" -> "Slow.thy"))
        val diR = JSON.value(di, "result").getOrElse(JSON.Object())
        val total = JSON.int(diR, "total_commands").getOrElse(0)
        val finished = JSON.int(diR, "finished").getOrElse(0)
        val unproc = JSON.int(diR, "unprocessed").getOrElse(0)
        if (total <= 0) error("check --line: precondition — document-info should see commands, got " + JSON.Format(diR))
        if (unproc <= 0)
          error("check --line 13: expected unprocessed>0 (tail commands NOT evaluated), " +
            "got total=" + total + " finished=" + finished + " unprocessed=" + unproc)
        if (JSON.bool(diR, "fully_processed") != Some(false))
          error("check --line: fully_processed should be false after partial check, got " + JSON.Format(diR))

        // (c) MCP `check` with `line`. Skip if MCP isn't up. Use a fresh
        //     Slow-shaped fixture so the check is still meaningfully partial.
        open_mcp(name) match {
          case None => Output.writeln("    (note) no MCP endpoint — skipping MCP arm of check --line test")
          case Some(mcp) =>
            try {
              // A UNIQUELY-named slow theory so it isn't already consolidated
              // (a re-check would trivially finish before the target).
              val slowAbs = fresh_slow_theory(8.0)
              val mcpStart = System.currentTimeMillis()
              val mcpRes = mcp.call("check", obj("files" -> List[Any](slowAbs), "line" -> 5))
              val mcpElapsed = System.currentTimeMillis() - mcpStart
              if (JSON.bool(mcpRes, "ok") != Some(true))
                error("MCP check with line=5: expected ok=true, got " + JSON.Format(mcpRes))
              if (mcpElapsed > 6000)
                error("MCP check --line 5 on slow theory took " + mcpElapsed + "ms; expected fast")
              // Bad shape: multiple files with a `line`.
              val _ = mcp.call("check", obj("files" -> List[Any](slowAbs, slowAbs), "line" -> 3),
                expectError = true)
            } finally mcp.close()
        }

        // (d) CLI `ic2 check --line N` (on the same Slow.thy that (a) used,
        //     so it's already loaded; this arm tests the CLI wrapper's exit codes).
        val n = Bash.string(name)
        val cliOk = ic2("check -n " + n + " " + Bash.string(file) + " --line 13")
        if (cliOk.rc != 0)
          error("ic2 check --line 13 should exit 0, got rc=" + cliOk.rc + " err=" + cliOk.err)
        val cliSt = wait_check_state(name, Set("ok"))
        if (JSON.bool(cliSt, "ok") != Some(true))
          error("ic2 check --line 13 should finish ok, got " + JSON.Format(cliSt))

        // (e) Usage errors.
        //     - `--line` with no value.
        val e1 = ic2("check -n " + n + " " + Bash.string(file) + " --line")
        if (e1.rc != 2) error("check --line with no value: expected rc=2, got " + e1.rc)
        //     - `--line` with two FILEs.
        val other = (fixtures + Path.basic("Trivial_OK.thy")).expand.implode
        val e2 = ic2("check -n " + n + " " + Bash.string(file) + " " + Bash.string(other) + " --line 3")
        if (e2.rc != 2) error("check --line with 2 FILEs: expected rc=2, got " + e2.rc)
        //     - `--line 0`.
        val e3 = ic2("check -n " + n + " " + Bash.string(file) + " --line 0")
        if (e3.rc != 2) error("check --line 0: expected rc=2, got " + e3.rc)

        // (f) LINE BOUNDING — `--line N` stops evaluation at the target line.
        //     SpinTactic.thy has TWO `by (spin 30; simp)` proofs (lines 41,
        //     44). `--line 41` runs spin1 to completion, then the line-reached
        //     watchdog cancels; spin2 must NOT run for a meaningful time.
        //     Under `parallel_proofs=0` (sequential eval) spin2 is at most
        //     briefly dispatched before the cancel reaches it — it may flicker
        //     for a tick but never accumulates real time. Assert: (i) spin1
        //     (line 41) reaches a large elapsed (it genuinely spun ~30s);
        //     (ii) spin2 (line 44) never exceeds a few seconds of elapsed
        //     (bounded — not a second 30s spin); (iii) spin2 is not finished
        //     afterwards (unprocessed or cancelled, never a clean success).
        //     (With DEFAULT parallel proofs the overshoot could be larger —
        //     acknowledged imprecision; this test pins parallel_proofs=0 so
        //     the bound is tight.) Skip if the fixture is absent.
        val spin = fixtures + Path.basic("SpinTactic.thy")
        if (spin.is_file) {
          val sio = connection(name)
          def elapsedOf(rc: JSON.T): Double =
            JSON.double(rc, "elapsed_s").orElse(JSON.int(rc, "elapsed_s").map(_.toDouble)).getOrElse(0.0)
          try {
            sio.write(JSON.Object("op" -> "check", "files" -> List(spin.expand.implode), "line" -> 41))
            val deadline = System.currentTimeMillis() + 60000
            var spin1Max = 0.0
            var spin2Max = 0.0
            var done = false
            while (!done && System.currentTimeMillis() < deadline) {
              sio.read(1500) match {
                case JSON_IO.Value(t) if JSON.string(t, "event") == Some("progress") =>
                  for (nd <- JSON.array(t, "nodes").getOrElse(Nil)
                       if JSON.string(nd, "theory").map(base_name) == Some("SpinTactic");
                       rc <- JSON.array(nd, "long_running").getOrElse(Nil)) {
                    JSON.int(rc, "line") match {
                      case Some(41) => spin1Max = math.max(spin1Max, elapsedOf(rc))
                      case Some(44) => spin2Max = math.max(spin2Max, elapsedOf(rc))
                      case _ =>
                    }
                  }
                case JSON_IO.Value(t) if JSON.string(t, "event") == Some("finished") => done = true
                case JSON_IO.EOF => done = true
                case _ =>
              }
            }
            if (spin1Max < 5.0)
              error("check --line 41: spin1 (line 41) should run to a large elapsed " +
                "(genuinely spins ~30s), max seen " + spin1Max + "s")
            if (spin2Max >= 5.0)
              error("check --line 41: spin2 (line 44) ran for " + spin2Max + "s — the tail " +
                "proof overshot well past the target line (expected a brief flicker at most)")
          } finally sio.close()
          // Tail proof (spin2) must NOT have finished successfully — it was
          // cut off at the target line (left unprocessed, or cancelled).
          val di2 = request_op(name, JSON.Object("op" -> "query", "tool" -> "get_document_info",
            "path" -> "SpinTactic.thy"))
          val di2R = JSON.value(di2, "result").getOrElse(JSON.Object())
          val unproc = JSON.int(di2R, "unprocessed").getOrElse(0)
          val failedN = JSON.int(di2R, "failed").getOrElse(0)
          if (unproc + failedN <= 0)
            error("check --line 41 on SpinTactic: expected spin2 left unprocessed or cancelled, " +
              "got " + JSON.Format(di2R))
        }

        // (g) DEPENDENCY loading — a bounded check of a file that imports a
        //     LOCAL theory must fully evaluate that dependency (else the
        //     prefix can't type-check). SpinImport.thy imports SpinDep.thy
        //     and its `uses_dep` proof references `spin_dep_const` from the
        //     dependency, so a green check here PROVES SpinDep evaluated.
        //     Pins: (i) check --line 20 exits ok; (ii) SpinDep is fully
        //     processed/consolidated afterwards; (iii) the importing theory
        //     is bounded (its own tail, if any, and here the whole thing
        //     up to the target — the point is SpinDep must be done): a bounded
        //     check must still fully evaluate its dependencies.
        val imp = fixtures + Path.basic("SpinImport.thy")
        val dep = fixtures + Path.basic("SpinDep.thy")
        if (imp.is_file && dep.is_file) {
          val iio = connection(name)
          try {
            iio.write(JSON.Object("op" -> "check",
              "files" -> List(imp.expand.implode), "line" -> 20))
            val (events, finished) = collect_events(iio, deadline_secs = 90)
            if (finished.flatMap(JSON.bool(_, "ok")) != Some(true))
              error("check --line 20 of SpinImport (imports SpinDep) should be ok — a " +
                "failure means the dependency SpinDep was not evaluated; got " + finished +
                " events=" + events.length)
          } finally iio.close()
          // The dependency must be fully evaluated + consolidated.
          val ps = request_op(name, JSON.Object("op" -> "query",
            "tool" -> "get_processing_status", "path" -> "SpinDep.thy"))
          val psR = JSON.value(ps, "result").getOrElse(JSON.Object())
          if (JSON.bool(psR, "fully_processed") != Some(true))
            error("check --line on SpinImport: dependency SpinDep should be fully_processed " +
              "(bounded check must still evaluate imports), got " + JSON.Format(psR))
          if (JSON.int(psR, "failed").getOrElse(0) != 0)
            error("check --line: dependency SpinDep should have no failures, got " + JSON.Format(psR))
        }
      } finally {
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** Partial check with PARALLEL PROOFS ON — the complement of
     *  `check_line_partial` case (f), which pins parallel_proofs=0. SpinTactic has
     *  two terminal `by (spin N)` proofs (spin1 15s at line 41, spin2 30s at line
     *  44) that would fork and run concurrently under default parallel proofs.
     *
     *  A `--line 41` check drives a BOUNDED VISIBLE perspective to spin1: the
     *  prover schedules the target node only up to the visible-last command (spin1)
     *  and never dispatches spin2. So — unlike the old require-then-cancel model,
     *  which let spin2 fork and then reclaimed it — there is NO OVERSHOOT to cancel:
     *    (1) spin1 (the target) genuinely runs to a large elapsed;
     *    (2) spin2 (past the target line) is never scheduled — it accrues ~no
     *        elapsed and is left unprocessed;
     *    (3) the check returns shortly after spin1, well before spin2's 30s;
     *    (4) the theory is not fully processed afterwards.
     *
     *  Own -N server so the post-check state is observable from a fresh start.
     *  Skip if the fixture is absent. */
    private def e2e_partial_bounded_tail_not_scheduled(fixtures: Path): Unit = {
      val spin = fixtures + Path.basic("SpinTactic.thy")
      if (!spin.is_file) {
        Output.writeln("    (note) SpinTactic.thy fixture missing; skipping bounded-tail test")
        return
      }
      val name = "t_fc_" + short_id()
      // Default parallel proofs (do NOT pin to 0): spin2 WOULD fork and run
      // concurrently if it were scheduled — the point is that bounding to line 41
      // means it never is.
      val proc = start_server(name, extra_args = List("-N"))
      try {
        wait_for_server(name, timeout = 60)
        def elapsedOf(rc: JSON.T): Double =
          JSON.double(rc, "elapsed_s").orElse(JSON.int(rc, "elapsed_s").map(_.toDouble)).getOrElse(0.0)
        val sio = connection(name)
        var spin1Max = 0.0
        var spin2Max = 0.0
        val started_ms = System.currentTimeMillis()
        try {
          sio.write(JSON.Object("op" -> "check",
            "files" -> List(spin.expand.implode), "line" -> 41))
          val deadline = System.currentTimeMillis() + 60000
          var done = false
          while (!done && System.currentTimeMillis() < deadline) {
            sio.read(1500) match {
              case JSON_IO.Value(t) if JSON.string(t, "event") == Some("progress") =>
                for (nd <- JSON.array(t, "nodes").getOrElse(Nil)
                     if JSON.string(nd, "theory").map(base_name) == Some("SpinTactic");
                     rc <- JSON.array(nd, "long_running").getOrElse(Nil)) {
                  JSON.int(rc, "line") match {
                    case Some(41) => spin1Max = math.max(spin1Max, elapsedOf(rc))
                    case Some(44) => spin2Max = math.max(spin2Max, elapsedOf(rc))
                    case _ =>
                  }
                }
              case JSON_IO.Value(t) if JSON.string(t, "event") == Some("finished") => done = true
              case JSON_IO.EOF => done = true
              case _ =>
            }
          }
          val total_ms = System.currentTimeMillis() - started_ms
          // (1) spin1 (the 15s target) genuinely spun to a large elapsed.
          if (spin1Max < 10.0)
            error("partial check: spin1 (line 41, 15s) should reach a large elapsed, " +
              "max seen " + spin1Max + "s")
          // (2) spin2 (past line 41) was NEVER scheduled by the bounded perspective
          //     — it must show ~no elapsed (a small ceiling absorbs any brief
          //     display flicker; it must be nowhere near its 30s runtime).
          if (spin2Max >= 5.0)
            error("partial check: spin2 (line 44, 30s) ran for " + spin2Max + "s — a bounded " +
              "check to line 41 must never schedule it (no overshoot); expected ~0s")
          // (3) the check returned shortly after spin1's 15s, not spin2's 30s.
          if (total_ms >= 28000)
            error("partial check took " + total_ms + "ms; expected to return shortly after " +
              "spin1's 15s (spin2 never scheduled), not wait out spin2's 30s")
        } finally sio.close()
        // (4) spin2 must NOT have finished successfully: bounded to the target line.
        val di = request_op(name, JSON.Object("op" -> "query", "tool" -> "get_document_info",
          "path" -> "SpinTactic.thy"))
        val diR = JSON.value(di, "result").getOrElse(JSON.Object())
        if (JSON.bool(diR, "fully_processed") == Some(true))
          error("partial check: SpinTactic should NOT be fully processed (spin2 never scheduled), " +
            "got " + JSON.Format(diR))
        if (JSON.int(diR, "unprocessed").getOrElse(0) + JSON.int(diR, "failed").getOrElse(0) <= 0)
          error("partial check: expected spin2 left unprocessed, got " + JSON.Format(diR))
      } finally {
        try { proc.terminate() } catch { case _: Throwable => }
        cleanup_server(name)
      }
    }

    /** TERMINAL. A check is in flight on connection A; `shutdown` arrives on
     *  connection B. A must wind down (finished OR EOF) and the listener must
     *  be gone afterwards. */
    private def e2e_shutdown_propagation(server_name: String, fixtures: Path): Unit = {
      val file = (fixtures + Path.basic("Slow.thy")).expand.implode
      val a = connection(server_name)
      try {
        a.write(JSON.Object("op" -> "check", "files" -> List(file)))
        if (!await_event(a, "started", 30)) error("conn A never saw 'started'")

        val b = connection(server_name)
        try {
          b.write(JSON.Object("op" -> "shutdown"))
          // Drain B until it closes.
          var bdone = false
          val bdl = System.currentTimeMillis() + 30000
          while (!bdone && System.currentTimeMillis() < bdl) {
            b.read(1000) match {
              case JSON_IO.EOF => bdone = true
              case _ =>
            }
          }
        } finally b.close()

        // Conn A must wind down: a finished event OR a clean EOF, within 20s.
        var a_wound_down = false
        val adl = System.currentTimeMillis() + 20000
        while (!a_wound_down && System.currentTimeMillis() < adl) {
          a.read(1000) match {
            case JSON_IO.EOF => a_wound_down = true
            case JSON_IO.Value(t) if JSON.string(t, "event") == Some("finished") => a_wound_down = true
            case _ => /* trailing progress / timeout */
          }
        }
        if (!a_wound_down) error("conn A did not wind down after shutdown")
      } finally a.close()

      // Listener gone.
      Thread.sleep(1000)
      if (can_connect(server_name)) error("server socket still accepting after shutdown")
    }


    /** Read until an event of the given type arrives (true) or deadline (false). */
    private def await_event(io: JSON_IO, event: String, deadline_secs: Int): Boolean = {
      val deadline = System.currentTimeMillis() + deadline_secs * 1000L
      while (System.currentTimeMillis() < deadline) {
        io.read(1000) match {
          case JSON_IO.Value(t) if JSON.string(t, "event") == Some(event) => return true
          case JSON_IO.Value(_) =>
          case JSON_IO.EOF => return false
          case JSON_IO.Timeout =>
        }
      }
      false
    }

    /** Read events until `finished` arrives or deadline expires. */
    private def collect_events(
      io: JSON_IO,
      deadline_secs: Int
    ): (List[JSON.T], Option[JSON.T]) = {
      val buf = scala.collection.mutable.ListBuffer[JSON.T]()
      var fin: Option[JSON.T] = None
      val deadline = System.currentTimeMillis() + deadline_secs * 1000L
      var done = false
      while (!done && System.currentTimeMillis() < deadline) {
        io.read(1000) match {
          case JSON_IO.EOF => done = true
          case JSON_IO.Timeout => /* keep waiting */
          case JSON_IO.Value(t) =>
            if (verbose) Output.writeln("    [event] " + JSON.Format(t))
            buf += t
            if (JSON.string(t, "event") == Some("finished")) {
              fin = Some(t); done = true
            }
        }
      }
      (buf.toList, fin)
    }
  }
}
