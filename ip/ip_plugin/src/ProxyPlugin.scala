/* Proxy Plugin: entry point, protocol handler, shared state.

   Registers a PIDE protocol handler that recognizes two message types
   injected by ml_proxy.py into the ML→Scala message stream:

     ("function", "proxy_log")    — body text appended to the log panel
     ("function", "proxy_status") — properties: host, mbps
*/

import isabelle._
import isabelle.jedit.PIDE

import org.gjt.sp.jedit.{EBMessage, EBPlugin, jEdit}


/* Shared mutable state between protocol handler and UI components. */
object ProxyState {
  case class Status(host: String = "", mbps: Double = 0.0)

  @volatile var status: Status = Status()
  @volatile private var activated: Boolean = false

  private var statusListeners: List[Status => Unit] = Nil
  private var logListeners: List[String => Unit] = Nil

  def addStatusListener(f: Status => Unit): Unit = synchronized { statusListeners ::= f }
  def removeStatusListener(f: Status => Unit): Unit = synchronized {
    statusListeners = statusListeners.filterNot(_ eq f)
  }

  def addLogListener(f: String => Unit): Unit = synchronized { logListeners ::= f }
  def removeLogListener(f: String => Unit): Unit = synchronized {
    logListeners = logListeners.filterNot(_ eq f)
  }

  /* On first proxy_status, append proxy-status at the end (keep ml-status). */
  private def activateStatusBar(): Unit = {
    if (activated) return
    synchronized {
      if (activated) return
      activated = true
    }
    GUI_Thread.later {
      val key = "view.status"
      var current = jEdit.getProperty(key, "")
      if (!current.contains("proxy-status"))
        current = current + " proxy-status"
      jEdit.setProperty(key, current)
      var view = jEdit.getFirstView()
      while (view != null) {
        view.getStatus.propertiesChanged()
        view = view.getNext
      }
    }
  }

  def notifyStatus(s: Status): Unit = {
    activateStatusBar()
    status = s
    val ls = synchronized { statusListeners }
    GUI_Thread.later { ls.foreach(_(s)) }
  }

  def notifyLog(text: String): Unit = {
    val ls = synchronized { logListeners }
    GUI_Thread.later { ls.foreach(_(text)) }
  }
}


/* PIDE protocol handler. */
class ProxyProtocolHandler extends Session.Protocol_Handler {
  private var session: Session = null

  override def init(session: Session): Unit = { this.session = session }

  private def handle_log(msg: Prover.Protocol_Output): Boolean = {
    ProxyState.notifyLog(msg.text)
    true
  }

  private def handle_status(msg: Prover.Protocol_Output): Boolean = {
    val host = Properties.get(msg.properties, "host").getOrElse("")
    val mbps = Properties.get(msg.properties, "mbps").flatMap(s =>
      try { Some(s.toDouble) } catch { case _: NumberFormatException => None }
    ).getOrElse(0.0)
    ProxyState.notifyStatus(ProxyState.Status(host, mbps))
    true
  }

  private def handle_ml_stats(msg: Prover.Protocol_Output): Boolean = {
    if (session != null) {
      val props = space_explode(',', msg.text).flatMap(Properties.Eq.unapply)
      if (props.nonEmpty) {
        val props1 = session.cache.props(props ::: Java_Statistics.jvm_statistics())
        session.runtime_statistics.post(Session.Runtime_Statistics(props1))
      }
    }
    true
  }

  override val functions: Session.Protocol_Functions =
    List("proxy_log" -> handle_log,
         "proxy_status" -> handle_status,
         "proxy_ml_stats" -> handle_ml_stats)
}


/* jEdit plugin lifecycle. */
class ProxyPlugin extends EBPlugin {
  override def start(): Unit = {
    /* Register protocol handler once PIDE session is available. */
    Isabelle_Thread.fork(name = "ip_plugin_init") {
      var registered = false
      while (!registered) {
        try {
          PIDE.session.init_protocol_handler(new ProxyProtocolHandler)
          registered = true
        } catch {
          case _: Throwable =>
            Time.seconds(0.5).sleep()
        }
      }
    }
  }
  override def stop(): Unit = {
    val key = "view.status"
    val current = jEdit.getProperty(key, "")
    if (current.contains("proxy-status")) {
      jEdit.setProperty(key, current.replace("proxy-status", "").replaceAll("  +", " ").trim)
    }
  }
  override def handleMessage(message: EBMessage): Unit = {}
}
