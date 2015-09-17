package edu.cmu.cs.ls.keymaerax.launcher

import java.net.URL
import javax.swing.JOptionPane

/**
 * Created by nfulton on 9/17/15.
 */
object SystemWebBrowser {
  /** @note location is not a URL/URI because it could be stuff like about:config or whatever... */
  def apply(location: String) = {
    // Try opening the web browser appropriately
    try {
      if (!java.awt.GraphicsEnvironment.isHeadless() &&
        java.awt.Desktop.isDesktopSupported() &&
        java.awt.Desktop.getDesktop().isSupported(java.awt.Desktop.Action.BROWSE))
      {
        java.awt.Desktop.getDesktop().browse(new java.net.URI(location))
      }
      else if (!java.awt.GraphicsEnvironment.isHeadless()) {
        JOptionPane.showMessageDialog(null, s"Point your browser to ${location}")
      }
      else {
        println("Launching server in headless mode.")
      }
    } catch {
      case exc: java.awt.HeadlessException =>
      case exc: java.lang.ClassNotFoundException =>
      case exc: java.lang.NoSuchMethodError =>
      case exc: Exception =>
    }
  }

}
