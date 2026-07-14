/* Original Copyright (c) 1986-2025,
            University of Cambridge,
            Technische Universitaet Muenchen,
            and contributors
   under the ISABELLE COPYRIGHT LICENSE

   Modifications Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
*/

/* Adaptation of src/Pure/PIDE/query_operation.scala:

   - Allow query to run at arbitrary command, not only the current one
   - Capture error output sent to special overlay file
   - Generic over an `isabelle.Session` (works for the live PIDE session in
     Isabelle/jEdit and a headless `Headless.Session` alike). The few
     host-specific capabilities a query operation needs — mutate the node
     perspective/overlays, flush pending edits, and marshal work onto the host's
     document thread — are abstracted behind `Extended_Query_Operation.Host`.
     jEdit supplies a Host backed by its `Editor`; a headless caller supplies one
     backed by `session.update`.

   The caret-driven entry points of the original (`apply_query` against the
   current command, `locate_query` via a GUI hyperlink) are intentionally NOT
   here: they are editor-specific. Callers resolve the target command themselves
   (any way they like) and drive `apply_query_at_command`. In `package isabelle`
   so it is shareable into `package isabelle.ic2`. */

package isabelle

object Extended_Query_Operation {
  enum Status { case inactive, failed, waiting, running, finished }

  object State {
    val empty: State = State()

    def make(command: Command, query: List[String]): State =
      State(instance = Document_ID.make().toString,
        location = Some(command),
        query = query,
        status = Status.waiting)
  }

  sealed case class State(
    instance: String = Document_ID.none.toString,
    location: Option[Command] = None,
    query: List[String] = Nil,
    update_pending: Boolean = false,
    output: List[XML.Tree] = Nil,
    status: Status = Status.inactive,
    exec_id: Document_ID.Exec = Document_ID.none)

  /** The host-specific capabilities a query operation needs, beyond the generic
    * `Session`. jEdit backs these with its `Editor` / `Document_Model` (so overlay
    * edits ride jEdit's own perspective flushes); a headless host backs them with
    * direct `session.update` calls.
    *
    *   - `insert_overlay` / `remove_overlay`: add/drop the print-function overlay on
    *     a command (a node perspective mutation). Inserting an overlay also makes
    *     the command visible, so the print function runs even off-screen / headless
    *     (Thy_Syntax.command_perspective folds overlay-bearing commands into the
    *     visible set).
    *   - `flush`: push pending perspective/overlay edits to the prover.
    *   - `require_dispatcher` / `send_dispatcher`: run a body on the host's document
    *     thread. jEdit requires the GUI thread; a headless host can run inline. */
  trait Host {
    def insert_overlay(command: Command, fn: String, args: List[String]): Unit
    def remove_overlay(command: Command, fn: String, args: List[String]): Unit
    def flush(): Unit
    def require_dispatcher[A](body: => A): A
    def send_dispatcher(body: => Unit): Unit
  }
}

class Extended_Query_Operation(
  session: Session,
  host: Extended_Query_Operation.Host,
  operation_name: String,
  consume_status: Extended_Query_Operation.Status => Unit,
  consume_output: (Document.Snapshot, Command.Results, List[XML.Elem]) => Unit,
) {
  private val print_function = operation_name + "_query"

  // Expose print_function for checking if it has changed
  def get_print_function: String = print_function


  /* implicit state -- owned by the host dispatcher */

  private val current_state = Synchronized(Extended_Query_Operation.State.empty)

  def get_location: Option[Command] = current_state.value.location

  private def remove_overlay(): Unit = {
    val state = current_state.value
    for (command <- state.location) {
      host.remove_overlay(command, print_function, state.instance :: state.query)
    }
  }


  /* content update */

  private def content_update(): Unit = {
    host.require_dispatcher {}

    /* snapshot */

    val state0 = current_state.value

    val (snapshot, command_results, results, errors, removed) =
      state0.location match {
        case Some(cmd) =>
          val snapshot = session.snapshot(node_name = cmd.node_name)
          val command_results = snapshot.command_results(cmd)

          val results = (for {
            case (_, elem @ XML.Elem(Markup(markup_name, props), _)) <- command_results.iterator
              if (props.contains((Markup.INSTANCE, state0.instance)) ||
                  props.contains((Markup.FILE, s"overlay_instance(${state0.instance})")))
          } yield elem).toList

          val errors = (for {
            case (_, elem @ XML.Elem(Markup(markup_name, props), _)) <- command_results.iterator
              if markup_name == Markup.ERROR_MESSAGE
          } yield elem).toList

          val removed = !snapshot.get_node(cmd.node_name).commands.contains(cmd)
          (snapshot, command_results, results, errors, removed)
        case None =>
          (Document.Snapshot.init, Command.Results.empty, Nil, Nil, true)
      }



    /* resolve sendback: static command id */

    def resolve_sendback(body: XML.Body): XML.Body = {
      state0.location match {
        case None => body
        case Some(command) =>
          def resolve(body: XML.Body): XML.Body =
            body map {
              case XML.Wrapped_Elem(m, b1, b2) => XML.Wrapped_Elem(m, resolve(b1), resolve(b2))
              case XML.Elem(Markup(Markup.SENDBACK, props), b) =>
                val props1 =
                  props.map({
                    case (Markup.ID, Value.Long(id)) if id == state0.exec_id =>
                      (Markup.ID, Value.Long(command.id))
                    case p => p
                  })
                XML.Elem(Markup(Markup.SENDBACK, props1), resolve(b))
              case XML.Elem(m, b) => XML.Elem(m, resolve(b))
              case t => t
            }
          resolve(body)
      }
    }


    /* output */

    val new_output =
      (for {
        case XML.Elem(_, List(XML.Elem(markup, body))) <- results
        if Markup.messages.contains(markup.name)
        body1 = resolve_sendback(body)
      } yield Protocol.make_message(body1, markup.name, props = markup.properties)) ++
      (for {
        case elem @ XML.Elem(Markup(markup_name, props), body) <- results
        if markup_name == Markup.ERROR_MESSAGE || markup_name == Markup.WARNING_MESSAGE
        body1 = resolve_sendback(body)
      } yield Protocol.make_message(body1, markup_name, props = props))


    /* status */

    def get_status(name: String, status: Extended_Query_Operation.Status): Option[Extended_Query_Operation.Status] =
      results.collectFirst({ case XML.Elem(_, List(elem: XML.Elem)) if elem.name == name => status })

    val new_status =
      if (removed) Extended_Query_Operation.Status.finished
      else {
        // Check for missing print function error
        val hasMissingPrintFunction = errors.exists { elem =>
          val content = XML.content(elem)
          content.contains(s"Missing print function \"$print_function\"")
        }

        if (hasMissingPrintFunction) Extended_Query_Operation.Status.failed
        else
          get_status(Markup.FINISHED, Extended_Query_Operation.Status.finished) orElse
          get_status(Markup.RUNNING, Extended_Query_Operation.Status.running) getOrElse
          Extended_Query_Operation.Status.waiting
      }

    /* state update */

    if (new_status == Extended_Query_Operation.Status.running)
      results.collectFirst(
      {
        case XML.Elem(Markup(_, Position.Id(id)), List(elem: XML.Elem))
        if elem.name == Markup.RUNNING => id
      }).foreach(id => current_state.change(_.copy(exec_id = id)))

    if (state0.output != new_output || state0.status != new_status) {
      if (snapshot.is_outdated)
        current_state.change(_.copy(update_pending = true))
      else {
        current_state.change(_.copy(update_pending = false))
        if (state0.output != new_output && !removed) {
          current_state.change(_.copy(output = new_output))
          consume_output(snapshot, command_results, new_output)
        }
        if (state0.status != new_status) {
          current_state.change(_.copy(status = new_status))
          consume_status(new_status)
          if (new_status == Extended_Query_Operation.Status.finished ||
              new_status == Extended_Query_Operation.Status.failed)
            remove_overlay()
        }
      }
    }
  }


  /* query operations */

  def cancel_query(): Unit =
    host.require_dispatcher { session.cancel_exec(current_state.value.exec_id) }

  // Run the query against an explicitly-resolved command. Inserting the overlay
  // makes that command visible, so the print function runs regardless of viewport
  // or (headless) empty perspective.
  def apply_query_at_command(command: Command, query: List[String]): Unit = {
    host.require_dispatcher {}

    cleanup_state()

    val state = Extended_Query_Operation.State.make(command, query)
    current_state.change(_ => state)
    host.insert_overlay(command, print_function, state.instance :: query)

    consume_status(current_state.value.status)
    host.flush()
  }

  // Helper method for cleanup
  private def cleanup_state(): Unit = {
    remove_overlay()
    current_state.change(_ => Extended_Query_Operation.State.empty)
    consume_output(Document.Snapshot.init, Command.Results.empty, Nil)
    consume_status(Extended_Query_Operation.Status.inactive)
  }


  /* main */

  private val main =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      case changed =>
        val state = current_state.value
        state.location match {
          case Some(command)
          if state.update_pending ||
            (state.status != Extended_Query_Operation.Status.finished &&
              state.status != Extended_Query_Operation.Status.failed &&
              changed.commands.contains(command)) =>
            host.send_dispatcher { content_update() }
          case _ =>
        }
    }

  def activate(): Unit = {
    session.commands_changed += main
  }

  def deactivate(): Unit = {
    session.commands_changed -= main
    cleanup_state()
  }
}
