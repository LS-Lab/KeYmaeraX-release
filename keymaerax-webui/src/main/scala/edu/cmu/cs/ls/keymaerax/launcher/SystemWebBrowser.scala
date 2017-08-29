package edu.cmu.cs.ls.keymaerax.launcher

import javax.swing.{JLabel, JOptionPane}
import java.awt.GraphicsEnvironment._
import java.awt.Desktop._
import java.util.Locale

/**
 * Opens the default web browser pointed to the KeYmaera X URL.
 * Created by nfulton on 9/17/15.
 */
object SystemWebBrowser {
  /** @note location is not a URL/URI because it could be stuff like about:config or whatever... */
  def apply(location: String): Unit = {
    // Try opening the web browser appropriately
    try {
      val os = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
      if (os != "linux" && !isHeadless && isDesktopSupported && getDesktop.isSupported(Action.BROWSE)) {
        getDesktop.browse(new java.net.URI(location))
      } else if (os == "linux" && !isHeadless) {
        //@todo Runtime.exec open default browser
        JOptionPane.showMessageDialog(null, new JLabel(s"""<html>Point your browser to <a href="$location">$location</a></html>"""))
      } else if (!isHeadless) {
        JOptionPane.showMessageDialog(null, new JLabel(s"""<html>Point your browser to <a href="$location">$location</a></html>"""))
      } else {
        println(s"Launching server in headless mode.\nPoint your browser to $location")
      }
    } catch {
      case _: java.awt.HeadlessException =>
      case _: java.lang.ClassNotFoundException =>
      case _: java.lang.NoSuchMethodError =>
      case _: Exception =>
    }
  }

}
