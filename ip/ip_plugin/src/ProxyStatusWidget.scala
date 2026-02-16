/* Proxy status bar widget: shows "Proxy: host  X.X MB/s" with progress bar.

   Modeled after Status_Widget.ML_GUI / Java_GUI.
   Registered via services.xml as "proxy-status".
*/

import isabelle._

import java.awt.{Color, Dimension, Graphics, Graphics2D, Insets, RenderingHints}
import java.awt.font.FontRenderContext
import javax.swing.JComponent

import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.gui.statusbar.{StatusWidgetFactory, Widget}


class ProxyStatusWidget(view: View) extends JComponent {
  /* The progress bar scales to this ceiling (MB/s). */
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

  @volatile private var currentStatus = ProxyState.Status()

  private val listener: ProxyState.Status => Unit = { s =>
    if (s != currentStatus) { currentStatus = s; repaint() }
  }

  override def addNotify(): Unit = {
    super.addNotify()
    ProxyState.addStatusListener(listener)
    listener(ProxyState.status)
  }

  override def removeNotify(): Unit = {
    super.removeNotify()
    ProxyState.removeStatusListener(listener)
  }

  override def paintComponent(gfx: Graphics): Unit = {
    super.paintComponent(gfx)
    val s = currentStatus
    if (s.host.isEmpty) return

    val host = if (s.host.contains("@")) s.host.split("@", 2)(1) else s.host
    val text = f"Proxy: $host  ${s.mbps}%.1f MB/s"
    val fraction = math.min(s.mbps / MAX_MBPS, 1.0)

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
