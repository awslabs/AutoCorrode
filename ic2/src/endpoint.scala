/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/endpoint.scala

Endpoint discovery for the Unix-domain-socket daemon: maps a server name to a
socket path, so `ic2 check` / `ic2 server status` find a running `ic2 server start` without
flags.

Layout: $ISABELLE_HOME_USER/ic2/<name>.sock  (and <name>.log for daemons)

Access control is the *directory*, not the socket node: the JVM creates the
AF_UNIX socket file world-traversable (rwxr-xr-x), so the only gate is a private
parent directory (mode 0700). With that in place no other OS user can reach the
socket, and there is no auth token to manage. Caveats: the mode is set just after
the directory is created, not atomically (a brief create->chmod window), and is
skipped on Windows (no POSIX permissions), where the directory is not a boundary.
The threat model is same-OS-user trust; see the README "Access control" section.

Multiple servers can coexist by passing -n <name>.
*/

package isabelle.ic2

import isabelle._

import java.nio.file.{Files, Paths}
import java.nio.file.attribute.PosixFilePermission


object Endpoint {
  /** The discovery directory. Created mode 0700 by `secure_dir()`. */
  def dir: Path = Path.explode("$ISABELLE_HOME_USER/ic2")

  /** Socket path for the named server. */
  def socket(name: String): Path = dir + Path.basic(name + ".sock")

  /** Default log path for a `--daemon` server (overridable with -L). */
  def log_file(name: String): Path = dir + Path.basic(name + ".log")

  private def jpath(p: Path): java.nio.file.Path = Paths.get(p.expand.implode)

  /** Ensure the discovery directory exists and is private (owner-only, 0700).
   *  Re-tightens the mode on every call, so a pre-existing loose directory is
   *  fixed rather than trusted. Returns the directory path. */
  def secure_dir(): Path = {
    Isabelle_System.make_directory(dir)
    try {
      Files.setPosixFilePermissions(jpath(dir),
        java.util.EnumSet.of(
          PosixFilePermission.OWNER_READ,
          PosixFilePermission.OWNER_WRITE,
          PosixFilePermission.OWNER_EXECUTE))
    } catch { case _: UnsupportedOperationException => /* Windows */ }
    dir
  }

  /** True iff a socket node exists for `name` (no liveness implied). AF_UNIX
   *  nodes aren't regular files, so probe the raw path rather than `is_file`. */
  def exists(name: String): Boolean = Files.exists(jpath(socket(name)))

  /** Delete the socket node for `name`, if present. */
  def remove(name: String): Unit =
    try { Files.deleteIfExists(jpath(socket(name))) }
    catch { case _: java.io.IOException => /* swallow */ }

  /** Names of all servers with a socket node (sorted). Used both to hint the
   *  user when a requested name isn't found and to enumerate servers for
   *  `ic2 server status` without a name. */
  def list_names(): List[String] = {
    val d = Paths.get(dir.expand.implode).toFile
    if (!d.isDirectory) Nil
    else d.listFiles().toList
      .map(_.getName)
      .filter(_.endsWith(".sock"))
      .map(_.stripSuffix(".sock"))
      .sorted
  }
}
