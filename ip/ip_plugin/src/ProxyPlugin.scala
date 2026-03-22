/* Proxy Plugin: entry point, protocol handler, proxy detection.

   Detects proxy usage from process_policy option at startup.
   If active, adds a status bar widget that polls a proxy-stats file
   written by ml_proxy.py (modeled after Status_Widget.Java_GUI).

   Also registers a PIDE protocol handler for:
     ("function", "proxy_log")      — acknowledged (no-op)
     ("function", "proxy_ml_stats") — remote ML statistics forwarding
*/

import isabelle._
import isabelle.jedit.PIDE

import org.gjt.sp.jedit.{EBMessage, EBPlugin, jEdit}


/* Shared state: proxy stats file path and host. */
object ProxyState {
  /* Set once at startup; empty if no proxy detected. */
  @volatile var stats_file: String = ""
  @volatile var proxy_host: String = ""
}


/* PIDE protocol handler (proxy_log + proxy_ml_stats). */
class ProxyProtocolHandler extends Session.Protocol_Handler {
  private var session: Session = null

  override def init(session: Session): Unit = { this.session = session }

  private def handle_log(msg: Prover.Protocol_Output): Boolean = true

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
         "proxy_ml_stats" -> handle_ml_stats)
}


/* jEdit plugin lifecycle. */
class ProxyPlugin extends EBPlugin {
  override def start(): Unit = {
    Isabelle_Thread.fork(name = "ip_plugin_init") {
      /* Register protocol handler once PIDE session is available. */
      var registered = false
      while (!registered) {
        try {
          PIDE.session.init_protocol_handler(new ProxyProtocolHandler)
          registered = true
        } catch {
          case _: Throwable => Time.seconds(0.5).sleep()
        }
      }
      /* Detect proxy from process_policy; set up stats file path and widget. */
      try {
        val policy = PIDE.options.string("process_policy")
        if (policy.contains("ml_proxy")) {
          val host = "--host\\s+(\\S+)".r.findFirstMatchIn(policy).map(_.group(1)).getOrElse("")
          val bare_host = if (host.contains("@")) host.split("@", 2)(1) else host
          ProxyState.proxy_host = host

          val tmp_prefix = Isabelle_System.getenv("ISABELLE_TMP_PREFIX")
          if (tmp_prefix.nonEmpty) {
            ProxyState.stats_file = tmp_prefix + "/proxy-stats-" + bare_host
          }

          GUI_Thread.later {
            val key = "view.status"
            var current = jEdit.getProperty(key, "")
            if (!current.contains("proxy-status"))
              current = current + " proxy-status"
            jEdit.setProperty(key, current)
            val suffix = " [PROXY: " + bare_host + "]"
            var view = jEdit.getFirstView()
            while (view != null) {
              view.getStatus.propertiesChanged()
              view = view.getNext
            }
          }
        }
      } catch { case _: Throwable => }
    }
  }

  override def stop(): Unit = {
    val key = "view.status"
    val current = jEdit.getProperty(key, "")
    if (current.contains("proxy-status")) {
      jEdit.setProperty(key, current.replace("proxy-status", "").replaceAll("  +", " ").trim)
    }
  }

  /* Re-apply proxy suffix after Isabelle resets the title. */
  override def handleMessage(message: EBMessage): Unit = {
    val host = ProxyState.proxy_host
    if (host.nonEmpty) {
      val bare = if (host.contains("@")) host.split("@", 2)(1) else host
      val suffix = " [PROXY: " + bare + "]"
      message match {
        case _: org.gjt.sp.jedit.msg.EditPaneUpdate |
             _: org.gjt.sp.jedit.msg.ViewUpdate |
             _: org.gjt.sp.jedit.msg.EditorStarted =>
          /* Delay to run after Isabelle's init_title in the same EDT cycle. */
          javax.swing.SwingUtilities.invokeLater(() => {
            var view = jEdit.getFirstView()
            while (view != null) {
              val cfg = view.getViewConfig.title
              if (cfg != null && !cfg.contains("[PROXY:")) {
                view.setUserTitle(cfg + suffix)
              }
              view = view.getNext
            }
          })
        case _ =>
      }
    }
  }
}
