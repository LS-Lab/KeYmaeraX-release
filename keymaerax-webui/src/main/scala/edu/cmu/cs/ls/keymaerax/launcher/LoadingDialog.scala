package edu.cmu.cs.ls.keymaerax.launcher

import java.awt.GridLayout
import javax.swing.{JWindow, JLabel, JProgressBar}
import edu.cmu.cs.ls.keymaerax.core

/**
  * @author Nathan Fulton
  */
trait LoadingDialog {
  val msg: String
  def addToStatus(x :  Int) : Unit
  def hide() : Unit
  def dispose() : Unit
}

/**
  * Obtain lightweight splash screens or command line status messages about KeYmaera X loading
  */
object LoadingDialogFactory {
  var theDialog : Option[LoadingDialog] = None

  def apply() = {
    if (theDialog.isEmpty) {
      theDialog =
        if (java.awt.GraphicsEnvironment.isHeadless) Some(new CLILoadingDialog())
        else Some(new GraphicalLoadingDialog())
    }
    theDialog.get
  }

  def closed() = {theDialog = None}
}

class CLILoadingDialog() extends LoadingDialog {
  private var status : Int = 0
  override val msg = "Headless KeYmaera X Server " + core.VERSION + " is Loading... "

  override def addToStatus(x: Int): Unit = {
    status = status + x
    if(status >= 100) hide()
    else println(s"$msg ($status% complete)")
  }

  override def hide(): Unit = {
    println("Loading Complete!")
    LoadingDialogFactory.closed()
  }

  override def dispose() = ()
}

/**
  * Splash screen indicator that the user interface is in the process of loading.
  */
class GraphicalLoadingDialog() extends LoadingDialog {
  println("Starting GUI Loading Dialog.")
  override val msg = "KeYmaera X User Interface " + core.VERSION + " is Loading..."

  private val progressBar = new JProgressBar()
  //  val progressMonitor = new ProgressMonitor(progressBar, "Initializing HyDRA..", "Binding port 8090", 0, 100)
  private val label = new JLabel(msg)
  //@todo only show on first launch
  private val firstLaunch = new JLabel("The first two starts might take a while to populate the local lemma database.")

  private var window = new JWindow()
  window.setLayout(new GridLayout(3,1))
  window.getContentPane.add(label)
  window.getContentPane.add(firstLaunch)
  window.getContentPane.add(progressBar)
  window.setSize(500,100)
  window.setLocationRelativeTo(null) //needs java 1.4 or newer
  window.setVisible(true)

  override def addToStatus(x : Int) = {
    val newValue = progressBar.getValue + x
    progressBar.setValue(newValue)
    //    progressMonitor.setProgress(newValue)
    progressBar.repaint()
    if (progressBar.getValue >= 100) hide()
  }

  override def hide():Unit = {
    if (window != null) {
      window.setVisible(false)
//      window.dispose()  //@note might exit the JVM if no other window is showing up yet

    }
  }

  override def dispose() = {
    LoadingDialogFactory.closed()
    window.dispose()
    window = null
  }
}
