/*  Title:      ic2/src/ic2_use_theories.scala

IC2-local copy of the relevant `Headless.Session.use_theories` /
`Headless.Resources.load_theories` machinery from Isabelle2025-2
`Pure/PIDE/headless.scala`.

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The copy is intentionally narrow: IC2 does not use upstream's `commit` callback
path, so this keeps only the no-commit checking path. The key IC2 modification
is in `Theory.node_edits`: upstream uses a whole-file `Text.Edit.replace(0, old,
new)` for changed files; IC2 computes a common-prefix/common-suffix replacement
so PIDE can preserve unchanged command identities across repeated CLI checks.
*/

package isabelle.ic2

import isabelle._

import scala.annotation.tailrec


object IC2_Use_Theories {
  private def stable_snapshot(
    state: Document.State,
    version: Document.Version,
    name: Document.Node.Name
  ): Document.Snapshot = {
    val snapshot = state.snapshot(name)
    assert(version.id == snapshot.version.id)
    snapshot
  }

  final class Result private[IC2_Use_Theories](
    val state: Document.State,
    val version: Document.Version,
    val nodes: List[(Document.Node.Name, Document_Status.Node_Status)]
  ) {
    def snapshot(name: Document.Node.Name): Document.Snapshot =
      stable_snapshot(state, version, name)

    def ok: Boolean = nodes.iterator.forall({ case (_, st) => st.ok })
  }


  /* loader state: copied from Headless.Resources.State, with IC2 edits */

  private object Loader {
    private val states =
      new java.util.WeakHashMap[Headless.Session, Synchronized[State]]

    private def state_for(session: Headless.Session): Synchronized[State] =
      states.synchronized {
        var state = states.get(session)
        if (state == null) {
          state = Synchronized(State())
          states.put(session, state)
        }
        state
      }

    private final case class Theory(
      node_name: Document.Node.Name,
      node_header: Document.Node.Header,
      text: String,
      node_required: Boolean
    ) {
      def node_perspective: Document.Node.Perspective_Text.T =
        Document.Node.Perspective(node_required, Text.Perspective.empty, Document.Node.Overlays.empty)

      def make_edits(text_edits: List[Text.Edit]): List[Document.Edit_Text] =
        List(
          node_name -> Document.Node.Deps(node_header),
          node_name -> Document.Node.Edits(text_edits),
          node_name -> node_perspective)

      def node_edits(session: Headless.Session, old: Option[Theory]): List[Document.Edit_Text] = {
        val old_text =
          old match {
            case Some(t) => t.text
            case None => SessionTools.nodeText(session, node_name)
          }
        val old_required = old.map(_.node_required).getOrElse(false)
        val text_edits =
          if (old.isEmpty && old_text.isEmpty) Text.Edit.inserts(0, text)
          else Theory.minimal_replace(old_text, text)

        if (text_edits.isEmpty && node_required == old_required) Nil
        else make_edits(text_edits)
      }

      def set_required(required: Boolean): Theory =
        if (required == node_required) this
        else copy(node_required = required)
    }

    private object Theory {
      /* IC2 deviation from Headless.Resources.Theory.node_edits:
       * upstream uses Text.Edit.replace(0, old, new), which expands to a
       * whole-file remove+insert. That removes unchanged prefix Command objects
       * before Thy_Syntax.reparse_spans can preserve them, so a tiny edit near
       * EOF can re-run an expensive command near BOF. This common-prefix /
       * common-suffix edit preserves unchanged command identities and lets PIDE
       * invalidate only the affected command range. */
      private def minimal_replace(old_text: String, new_text: String): List[Text.Edit] = {
        if (old_text == new_text) Nil
        else {
          val old_len = old_text.length
          val new_len = new_text.length
          var start = 0
          while (start < old_len && start < new_len &&
                 old_text.charAt(start) == new_text.charAt(start)) {
            start += 1
          }

          var old_stop = old_len
          var new_stop = new_len
          while (old_stop > start && new_stop > start &&
                 old_text.charAt(old_stop - 1) == new_text.charAt(new_stop - 1)) {
            old_stop -= 1
            new_stop -= 1
          }

          Text.Edit.removes(start, old_text.substring(start, old_stop)) :::
            Text.Edit.inserts(start, new_text.substring(start, new_stop))
        }
      }
    }

    private final case class State(
      blobs: Map[Document.Node.Name, Document.Blobs.Item] = Map.empty,
      theories: Map[Document.Node.Name, Theory] = Map.empty,
      required: Multi_Map[Document.Node.Name, UUID.T] = Multi_Map.empty
    ) {
      def doc_blobs: Document.Blobs = Document.Blobs(blobs)

      def update_blobs(names: List[Document.Node.Name]): (Document.Blobs, State) = {
        val new_blobs =
          names.flatMap { name =>
            val bytes = Bytes.read(name.path)
            blobs.get(name) match {
              case Some(blob) if blob.bytes == bytes => None
              case _ =>
                val text = bytes.text
                val blob = Document.Blobs.Item(bytes, text, Symbol.Text_Chunk(text), changed = true)
                Some(name -> blob)
            }
          }
        val blobs1 = new_blobs.foldLeft(blobs)(_ + _)
        val blobs2 = new_blobs.foldLeft(blobs) { case (map, (a, b)) => map + (a -> b.unchanged) }
        (Document.Blobs(blobs1), copy(blobs = blobs2))
      }

      def blob_edits(
        name: Document.Node.Name,
        old_blob: Option[Document.Blobs.Item]
      ): List[Document.Edit_Text] = {
        val blob = blobs.getOrElse(name, error("Missing blob " + quote(name.toString)))
        val text_edits =
          old_blob match {
            case None => List(Text.Edit.insert(0, blob.source))
            case Some(blob0) => Text.Edit.replace(0, blob0.source, blob.source)
          }
        if (text_edits.isEmpty) Nil
        else List(name -> Document.Node.Blob(blob), name -> Document.Node.Edits(text_edits))
      }

      def is_required(name: Document.Node.Name): Boolean = required.isDefinedAt(name)

      def insert_required(id: UUID.T, names: List[Document.Node.Name]): State =
        copy(required = names.foldLeft(required)(_.insert(_, id)))

      def remove_required(id: UUID.T, names: List[Document.Node.Name]): State =
        copy(required = names.foldLeft(required)(_.remove(_, id)))

      def update_theories(update: List[Theory]): State =
        copy(theories =
          update.foldLeft(theories) {
            case (thys, thy) =>
              thys.get(thy.node_name) match {
                case Some(thy1) if thy1 == thy => thys
                case _ => thys + (thy.node_name -> thy)
              }
          })

      def unload_theories(
        session: Headless.Session,
        id: UUID.T,
        names: List[Document.Node.Name]
      ): (List[Document.Edit_Text], State) = {
        val st1 = remove_required(id, names)
        val theory_edits =
          for {
            node_name <- names
            theory <- st1.theories.get(node_name)
          }
          yield {
            val theory1 = theory.set_required(st1.is_required(node_name))
            val edits = theory1.node_edits(session, Some(theory))
            (theory1, edits)
          }
        (theory_edits.flatMap(_._2), st1.update_theories(theory_edits.map(_._1)))
      }
    }

    def load_theories(
      session: Headless.Session,
      resources: Headless.Resources,
      id: UUID.T,
      theories: List[Document.Node.Name],
      files: List[Document.Node.Name],
      unicode_symbols: Boolean,
      progress: Progress
    ): Unit = {
      val loaded_theories =
        for (node_name <- theories)
        yield {
          val path = node_name.path
          if (!node_name.is_theory) error("Not a theory file: " + path)

          progress.expose_interrupt()
          val text = Symbol.output(unicode_symbols, File.read(path))
          val node_header = resources.check_thy(node_name, Scan.char_reader(text))
          Theory(node_name, node_header, text, true)
        }

      val loaded = loaded_theories.length
      if (loaded > 1) progress.echo("Loading " + loaded + " theories ...")

      state_for(session).change { st =>
        val (doc_blobs1, st1) = st.insert_required(id, theories).update_blobs(files)
        val theory_edits =
          for (theory <- loaded_theories)
          yield {
            val node_name = theory.node_name
            val old_theory = st.theories.get(node_name)
            val theory1 = theory.set_required(st1.is_required(node_name))
            val edits = theory1.node_edits(session, old_theory)
            (theory1, edits)
          }
        val file_edits =
          for { node_name <- files if doc_blobs1.changed(node_name) }
          yield st1.blob_edits(node_name, st.blobs.get(node_name))

        session.update(doc_blobs1, theory_edits.flatMap(_._2) ::: file_edits.flatten)
        st1.update_theories(theory_edits.map(_._1))
      }
    }

    def unload_theories(
      session: Headless.Session,
      id: UUID.T,
      theories: List[Document.Node.Name]
    ): Unit = {
      state_for(session).change { st =>
        val (edits, st1) = st.unload_theories(session, id, theories)
        session.update(st.doc_blobs, edits)
        st1
      }
    }
  }


  /* use_theories copy, no upstream commit callback path */

  private object Load_State {
    def finished: Load_State = Load_State(Nil, Nil, Space.zero)

    def count_file(resources: Headless.Resources)(name: Document.Node.Name): Long =
      if (resources.loaded_theory(name)) 0 else File.size(name.path)
  }

  private final case class Load_State(
    pending: List[Document.Node.Name],
    rest: List[Document.Node.Name],
    load_limit: Space
  ) {
    def next(
      resources: Headless.Resources,
      dep_graph: Document.Node.Name.Graph[Unit],
      consolidated: Document.Node.Name => Boolean
    ): (List[Document.Node.Name], Load_State) = {
      def load_requirements(
        pending1: List[Document.Node.Name],
        rest1: List[Document.Node.Name]
      ): (List[Document.Node.Name], Load_State) = {
        val load_theories = dep_graph.all_preds_rev(pending1)
        (load_theories, Load_State(pending1, rest1, load_limit))
      }

      if (!pending.forall(consolidated)) (Nil, this)
      else if (rest.isEmpty) (Nil, Load_State.finished)
      else if (!load_limit.is_proper) load_requirements(rest, Nil)
      else {
        val reachable =
          dep_graph.reachable_limit(
            load_limit.bytes, Load_State.count_file(resources), dep_graph.imm_preds, rest)
        val (pending1, rest1) = rest.partition(reachable)
        load_requirements(pending1, rest1)
      }
    }
  }

  private final case class Use_Theories_State(
    resources: Headless.Resources,
    dep_graph: Document.Node.Name.Graph[Unit],
    load_state: Load_State,
    watchdog_timeout: Time,
    last_update: Date = Date.now(),
    nodes_status: Document_Status.Nodes_Status = Document_Status.Nodes_Status.empty,
    changed_nodes: Set[Document.Node.Name] = Set.empty,
    changed_assignment: Boolean = false,
    result: Option[Exn.Result[Result]] = None
  ) {
    def nodes_status_update(
      state: Document.State,
      version: Document.Version,
      domain: Option[Set[Document.Node.Name]] = None,
      trim: Boolean = false
    ): (Boolean, Use_Theories_State) = {
      val now = Date.now()
      val nodes_status1 =
        nodes_status.update_nodes(now, resources, state, version, domain = domain, trim = trim)
      val st1 = copy(last_update = now, nodes_status = nodes_status1)
      (nodes_status1 != nodes_status, st1)
    }

    def changed(
      nodes: IterableOnce[Document.Node.Name],
      assignment: Boolean
    ): Use_Theories_State =
      copy(
        changed_nodes = changed_nodes ++ nodes,
        changed_assignment = changed_assignment || assignment)

    def reset_changed: Use_Theories_State =
      if (changed_nodes.isEmpty && !changed_assignment) this
      else copy(changed_nodes = Set.empty, changed_assignment = false)

    def watchdog: Boolean =
      watchdog_timeout > Time.zero && Date.now() - last_update > watchdog_timeout

    def finished_result: Boolean = result.isDefined

    def join_result: Option[(Exn.Result[Result], Use_Theories_State)] =
      if (finished_result) Some((result.get, this)) else None

    def cancel_result: Use_Theories_State =
      if (finished_result) this else copy(result = Some(Exn.Exn(Exn.Interrupt())))

    private def consolidated(
      state: Document.State,
      version: Document.Version,
      name: Document.Node.Name
    ): Boolean =
      resources.loaded_theory(name) ||
        nodes_status.quasi_consolidated(name) ||
        state.node_consolidated(version, name)

    def check(
      state: Document.State,
      version: Document.Version,
      beyond_limit: Boolean
    ): (List[Document.Node.Name], Use_Theories_State) = {
      val (load_theories0, load_state1) =
        load_state.next(resources, dep_graph, consolidated(state, version, _))
      val load_theories = load_theories0.filterNot(resources.loaded_theory)

      val result1 = {
        val stopped = beyond_limit || watchdog
        if (!finished_result && load_theories.isEmpty &&
            (stopped || dep_graph.keys_iterator.forall(consolidated(state, version, _)))) {
          val now = Date.now()

          @tailrec def make_nodes(
            input: List[Document.Node.Name],
            output: List[(Document.Node.Name, Document_Status.Node_Status)]
          ): Option[List[(Document.Node.Name, Document_Status.Node_Status)]] = {
            input match {
              case name :: rest =>
                if (resources.loaded_theory(name)) make_nodes(rest, output)
                else {
                  val status = Document_Status.Node_Status.make(now, state, version, name)
                  if (stopped || status.consolidated) make_nodes(rest, (name -> status) :: output)
                  else None
                }
              case Nil => Some(output)
            }
          }

          for (nodes <- make_nodes(dep_graph.topological_order.reverse, Nil))
            yield Exn.Res(new Result(state, version, nodes))
        }
        else result
      }

      (load_theories, copy(result = result1, load_state = load_state1))
    }
  }

  def use_theories(
    session: Headless.Session,
    resources: Headless.Resources,
    theories: List[String],
    qualifier: String = Sessions.DRAFT,
    master_dir: String = "",
    unicode_symbols: Boolean = false,
    check_delay: Time,
    check_limit: Int,
    watchdog_timeout: Time,
    nodes_status_delay: Time,
    id: UUID.T = UUID.random(),
    progress: Progress = new Progress
  ): Result = {
    val dependencies = {
      val import_names =
        theories.map(thy =>
          resources.import_name(qualifier, session.master_directory(master_dir), thy) -> Position.none)
      resources.dependencies(import_names, progress = progress).check_errors
    }
    val dep_theories = dependencies.theories
    val dep_theories_set = dep_theories.toSet
    val dep_files = dependencies.loaded_files

    val use_theories_state = {
      val dep_graph = dependencies.theory_graph
      val maximals = dep_graph.maximals
      val rest =
        if (maximals.isEmpty || maximals.tail.isEmpty) maximals
        else {
          val depth = dep_graph.node_depth(Load_State.count_file(resources))
          maximals.sortBy(node => - depth(node))
        }
      Synchronized(
        Use_Theories_State(
          resources, dep_graph, Load_State(Nil, rest, Space.zero), watchdog_timeout))
    }

    def check_state(
      beyond_limit: Boolean = false,
      state: Document.State = session.get_state()
    ): Unit = {
      for {
        version <- state.stable_tip_version
        load_theories = use_theories_state.change_result(_.check(state, version, beyond_limit))
        if load_theories.nonEmpty
      } Loader.load_theories(session, resources, id, load_theories, dep_files, unicode_symbols, progress)
    }

    lazy val check_progress = {
      var check_count = 0
      Event_Timer.request(Time.now(), repeat = Some(check_delay)) {
        if (progress.stopped) use_theories_state.change(_.cancel_result)
        else {
          check_count += 1
          check_state(check_limit > 0 && check_count > check_limit)
        }
      }
    }

    val consumer = {
      val delay_nodes_status =
        Delay.first(nodes_status_delay max Time.zero) {
          val st = use_theories_state.value
          val now = progress.now()
          progress.nodes_status(
            Progress.Nodes_Status(now, st.dep_graph.topological_order, st.nodes_status))
        }

      isabelle.Session.Consumer[isabelle.Session.Commands_Changed](getClass.getName) { changed =>
        val state = session.get_state()

        def apply_changed(st: Use_Theories_State): Use_Theories_State =
          st.changed(changed.nodes.iterator.filter(dep_theories_set), changed.assignment)

        state.stable_tip_version match {
          case None => use_theories_state.change(apply_changed)
          case Some(version) =>
            val theory_progress =
              use_theories_state.change_result { st =>
                val changed_st = apply_changed(st)
                val domain =
                  if (st.nodes_status.is_empty) dep_theories_set
                  else changed_st.changed_nodes

                val (nodes_status_changed, st1) =
                  st.reset_changed.nodes_status_update(
                    state, version, domain = Some(domain), trim = changed_st.changed_assignment)

                if (nodes_status_delay >= Time.zero && nodes_status_changed)
                  delay_nodes_status.invoke()

                val theory_progress =
                  (for {
                    name <- st1.dep_graph.topological_order.iterator
                    node_status = st1.nodes_status(name)
                    if !node_status.is_empty && changed_st.changed_nodes(name)
                    p1 = node_status.percentage
                    if p1 > 0 && !st.nodes_status.get(name).map(_.percentage).contains(p1)
                  } yield Progress.Theory(name.theory, percentage = Some(p1))).toList

                (theory_progress, st1)
              }

            theory_progress.foreach(progress.theory)
            check_state(state = state)
        }
      }
    }

    try {
      session.commands_changed += consumer
      check_progress
      use_theories_state.guarded_access(_.join_result)
      check_progress.cancel()
    }
    finally {
      session.commands_changed -= consumer
      Loader.unload_theories(session, id, dep_theories)
    }

    Exn.release(use_theories_state.guarded_access(_.join_result))
  }
}
