package edu.cmu.cs.ls.keymaerax.launcher

import java.awt.GridLayout
import javax.swing.{JLabel, JProgressBar, JWindow}

import edu.cmu.cs.ls.keymaerax.core
import org.apache.logging.log4j.scala.Logging

/**
  * @author Nathan Fulton
  */
trait LoadingDialog {
  /** The initial message displayed in the dialog. */
  val initialMsg: String

  /** Updates the status with a `progress` indicator and a message `msg`. */
  def addToStatus(progress: Int, msg: Option[String]): Unit

  /** Closes the dialog. */
  def close(): Unit
}

/**
  * Obtain lightweight splash screens or command line status messages about KeYmaera X loading
  */
object LoadingDialogFactory {
  var theDialog : Option[LoadingDialog] = None

  def apply(): LoadingDialog = {
    if (theDialog.isEmpty) {
      theDialog =
        if (java.awt.GraphicsEnvironment.isHeadless) Some(new CLILoadingDialog())
        else Some(new GraphicalLoadingDialog())
    }
    theDialog.get
  }

  def close(): Unit = theDialog = None
}

class CLILoadingDialog() extends LoadingDialog with Logging {
  private var status: Int = 0
  override val initialMsg: String = "Headless KeYmaera X Server " + core.VERSION + " is Loading... "

  override def addToStatus(x: Int, msg: Option[String]): Unit = {
    status = status + x
    if (status >= 100) close()
    else logger.info(s"${msg.getOrElse(initialMsg)} ($status% complete)")
  }

  override def close(): Unit = {
    logger.info("Loading Complete!")
    LoadingDialogFactory.close()
  }
}

/**
  * Splash screen indicator that the user interface is in the process of loading.
  */
class GraphicalLoadingDialog() extends LoadingDialog {
  private val titleMsg: String = "KeYmaera X " + core.VERSION
  override val initialMsg: String = "Loading..."

  private val progressBar = new JProgressBar()
  private val titleLabel = new JLabel(titleMsg)
  private val progressLabel = new JLabel(initialMsg)
  //@todo only show on first launch
  private val firstLaunch = new JLabel("The first two starts might take a while to populate the local lemma database.")

  private var window = new JWindow()
  window.setLayout(new GridLayout(4,1))
  window.getContentPane.add(titleLabel)
  window.getContentPane.add(progressLabel)
  window.getContentPane.add(firstLaunch)
  window.getContentPane.add(progressBar)
  window.setSize(500,100)
  window.setLocationRelativeTo(null) //needs java 1.4 or newer
  window.setVisible(true)

  override def addToStatus(x : Int, msg: Option[String]): Unit = {
    progressLabel.setText(msg.getOrElse(initialMsg))
    val newValue = progressBar.getValue + x
    progressBar.setValue(newValue)
    //    progressMonitor.setProgress(newValue)
    progressBar.repaint()
    if (progressBar.getValue >= 100) close()
  }

  override def close(): Unit = {
    if (window != null) {
      window.setVisible(false)
      //window.dispose()  //@note might exit the JVM if no other window is showing up yet
      window = null
      LoadingDialogFactory.close()
    }
  }
}
