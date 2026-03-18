/* Proxy status bar widget: shows "Proxy: host  X.X MB/s" with progress bar.

   Polls proxy-stats-{host} file on a 500ms timer, modeled after
   Status_Widget.Java_GUI which polls JVM heap via a Swing Timer.
*/

import isabelle._

import java.awt.{Color, Dimension, Graphics, Graphics2D, Insets, RenderingHints}
import java.awt.event.{ActionEvent, ActionListener}
import java.awt.font.FontRenderContext
import java.io.File
import java.nio.file.Files
import javax.swing.{JComponent, Timer}

import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.gui.statusbar.{StatusWidgetFactory, Widget}


class ProxyStatusWidget(view: View) extends JComponent {
  private val MAX_MBPS = 25.0

  private val template = "Proxy: 999.999.999.999  99.9 MB/s"

  setFont(GUI.copy_font(GUI.label_font()))

  private val frc = new FontRenderContext(null, true, false)
  private val lineMetrics = getFont.getLineMetrics(template, frc)

  {
    val bounds = getFont.getStringBounds(template, frc)
    val dim = new Dimension(bounds.getWidth.toInt + 12, bounds.getHeight.toInt)
    setPreferredSize(dim)
    setMaximumSize(dim)
  }

  setForeground(jEdit.getColorProperty("view.status.foreground"))
  setBackground(jEdit.getColorProperty("view.status.background"))

  private def progressFg: Color = jEdit.getColorProperty("view.status.memory.foreground")
  private def progressBg: Color = jEdit.getColorProperty("view.status.memory.background")

  /* Component state — owned by GUI thread. */
  private var currentHost: String = ""
  private var currentMbps: Double = 0.0

  /* Timer polls the stats file every 500ms, like Java_GUI. */
  private val timer = new Timer(500, new ActionListener {
    override def actionPerformed(e: ActionEvent): Unit = {
      val path = ProxyState.stats_file
      if (path.nonEmpty) {
        try {
          val f = new File(path)
          if (f.isFile) {
            val lines = new String(Files.readAllBytes(f.toPath), "UTF-8")
            var host = ""
            var mbps = 0.0
            for (line <- lines.split('\n')) {
              val eq = line.indexOf('=')
              if (eq > 0) {
                val key = line.substring(0, eq)
                val value = line.substring(eq + 1)
                if (key == "host") host = value
                else if (key == "mbps")
                  try { mbps = value.toDouble } catch { case _: NumberFormatException => }
              }
            }
            if (host != currentHost || mbps != currentMbps) {
              currentHost = host
              currentMbps = mbps
              repaint()
            }
          }
        } catch { case _: Exception => }
      } else if (currentHost.isEmpty) {
        /* No stats file yet; show host from process_policy if available. */
        val h = ProxyState.proxy_host
        if (h.nonEmpty && h != currentHost) {
          currentHost = h
          repaint()
        }
      }
    }
  })

  override def addNotify(): Unit = {
    super.addNotify()
    timer.start()
  }

  override def removeNotify(): Unit = {
    super.removeNotify()
    timer.stop()
  }

  override def paintComponent(gfx: Graphics): Unit = {
    super.paintComponent(gfx)
    if (currentHost.isEmpty) return

    val host = if (currentHost.contains("@")) currentHost.split("@", 2)(1) else currentHost
    val text = f"Proxy: $host  ${currentMbps}%.1f MB/s"
    val fraction = math.min(currentMbps / MAX_MBPS, 1.0)

    val insets = new Insets(0, 0, 0, 0)
    val width = getWidth - insets.left - insets.right
    val height = getHeight - insets.top - insets.bottom - 1
    val barWidth = (width * fraction).toInt

    val textBounds = gfx.getFont.getStringBounds(text, frc)
    val textX = insets.left + ((width - textBounds.getWidth.toInt) / 2)
    val textY = lineMetrics.getAscent.toInt

    val g2 = gfx.asInstanceOf[Graphics2D]
    g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,
                        RenderingHints.VALUE_TEXT_ANTIALIAS_ON)

    /* Progress bar background. */
    gfx.setColor(progressBg)
    gfx.fillRect(insets.left, insets.top, barWidth, height)

    /* Text over the bar portion. */
    gfx.setColor(progressFg)
    gfx.setClip(insets.left, insets.top, barWidth, height)
    gfx.drawString(text, textX, textY)

    /* Text over the empty portion. */
    gfx.setColor(getForeground)
    gfx.setClip(insets.left + barWidth, insets.top, width - barWidth, height)
    gfx.drawString(text, textX, textY)

    gfx.setClip(null)
  }

  setToolTipText("Remote ML prover throughput")
}


class ProxyStatusWidgetFactory extends StatusWidgetFactory {
  override def getWidget(view: View): Widget =
    new Widget { override def getComponent: JComponent = new ProxyStatusWidget(view) }
}
