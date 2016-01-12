package edu.cmu.cs.ls.keymaerax.launcher

import java.awt.GridLayout
import javax.swing.{JWindow, JLabel, JProgressBar}

/**
  * @author Nathan Fulton
  */
trait LoadingDialog {
  val msg: String
  def addToStatus(x :  Int) : Unit
  def close() : Unit
}

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

  def closed() = theDialog = None
}

class CLILoadingDialog() extends LoadingDialog {
  private var status : Int = 0
  override val msg = "Headless KeYmaera X Server is Loading... "

  override def addToStatus(x: Int): Unit = {
    status = status + x
    if(status >= 100) close()
    else println(s"$msg ($status% complete)")
  }

  override def close(): Unit = {
    println("Loading Complete!")
    LoadingDialogFactory.closed()
  }
}

class GraphicalLoadingDialog() extends LoadingDialog {
  println("Staring GUI Loading Dialog.")
  override val msg = "KeYmaera X User Interface is Loading..."

  private val progressBar = new JProgressBar()
  //  val progressMonitor = new ProgressMonitor(progressBar, "Initializing HyDRA..", "Binding port 8090", 0, 100)
  private val label = new JLabel(msg)

  private var window = new JWindow()
  window.setLayout(new GridLayout(2,1))
  window.getContentPane.add(label)
  window.getContentPane.add(progressBar)
  window.setSize(500,100)
  window.setLocationRelativeTo(null) //needs java 1.4 or newer
  window.setVisible(true)

  override def addToStatus(x : Int) = {
    val newValue = progressBar.getValue + x
    progressBar.setValue(newValue)
    //    progressMonitor.setProgress(newValue)
    progressBar.repaint()
    if (progressBar.getValue >= 100) close()
  }

  override def close() = {
    if (window != null) {
      window.setVisible(false)
      window = null
      LoadingDialogFactory.closed()
    }
  }
}
