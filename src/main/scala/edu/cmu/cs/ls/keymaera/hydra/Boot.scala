package edu.cmu.cs.ls.keymaera.hydra

import java.awt.event.{ActionEvent, ActionListener}
import java.awt.{GridLayout, Label, BorderLayout}
import java.util.EventListener
import javax.swing._

import akka.actor.{ActorSystem, Props}
import akka.io.IO
import edu.cmu.cs.ls.keymaera.api.ComponentConfig
import spray.can.Http

import scala.concurrent.duration.FiniteDuration

class LoadingDialog {
  val progressBar = new JProgressBar()
//  val progressMonitor = new ProgressMonitor(progressBar, "Initializing HyDRA..", "Binding port 8090", 0, 100)
  val label = new JLabel("KeYmaeraX is Loading...")

  var window = new JWindow()
  window.setLayout(new GridLayout(2,1))
  window.getContentPane.add(label)
  window.getContentPane.add(progressBar)
  window.setSize(500,100)
  window.setLocationRelativeTo(null) //needs java 1.4 or newer
  window.setVisible(true)

  def addToStatus(x : Int) = {
    val newValue = progressBar.getValue() + x
    progressBar.setValue(newValue)
//    progressMonitor.setProgress(newValue)
    progressBar.repaint()
    if(progressBar.getValue >= 100) {
      if(window != null) {
        window.setVisible(false)
        window = null
        JOptionPane.showMessageDialog(null, "Open a browser to http://localhost:8090 to access KeYmaera X.\n The server will continue running in the background until it is manually shutdown using the power button in the Web UI.")
      }
//        label.setText("KeYmaeraX is running at http://localhost:8090")
//      label.repaint()
//      window.remove(progressBar)
//      progressBar.repaint()
//      val button = new java.awt.Button("Shutdown KeYmaeraX") {
//        this.addActionListener(new ActionListener {
//          override def actionPerformed(e: ActionEvent): Unit = JOptionPane.showMessageDialog(null, "To exit KeYmaeraX, login to the web UI and press the power button.")
//        })
//      }
//      window.getContentPane.add(button)
//      button.repaint()
    }
  }
}

object Boot extends App {
  def restart(): Unit = {
    this.system.shutdown();
    this.system.awaitTermination();

    //Re-initialize the server
    this.system = ActorSystem("on-spray-can")
    var service = system.actorOf(Props[RestApiActor], "hydra")
    ComponentConfig.keymaeraInitializer.initialize()
    IO(Http) ! Http.Bind(service, interface = host, port = port)
  }

  // we need an ActorSystem to host our application in
  implicit var system = ActorSystem("on-spray-can")

  // create and start our service actor
  var service = system.actorOf(Props[RestApiActor], "hydra")

  // spawn dependency injection framework
  ComponentConfig.keymaeraInitializer.initialize()

  val database = DBAbstractionObj.defaultDatabase
  val config = database.getAllConfigurations.filter(_.name.equals("serverconfig")).headOption
  val (isHosted:Boolean, host:String, port:Int) = config match {
    case Some(c) => (c.config("isHosted").equals("true"), c.config("host"), Integer.parseInt(c.config("port")))
    case None => (false, "localhost", 8090)
  }


  // start a new HTTP server on port 8080 with our service actor as the handler
  val io = IO(Http)
  val bind = Http.Bind(service, interface = host, port = port)

  io ! bind

  val dialog = new LoadingDialog;

  {
    import scala.concurrent.ExecutionContext.Implicits.global

    def someTime(x:Int) = new FiniteDuration(x, scala.concurrent.duration.SECONDS)
    this.system.scheduler.scheduleOnce(someTime(1))(dialog.addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(2))(dialog.addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(3))(dialog.addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(4))(dialog.addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(4))(onLoad())
  }

  def onLoad() : Unit = {
    // Finally, print a message indicating that the server was started.
    println(
      "**********************************************************\n" +
        "****                   KeYmaera X                     ****\n" +
        "****                                                  ****\n" +
        "**** OPEN YOUR WEB BROWSER AT  http://"+host+":"+port+"/ ****\n" +
        "****                                                  ****\n" +
        "**** THE BROWSER MAY NEED RELOADS TILL THE PAGE SHOWS ****\n" +
        "**********************************************************\n"
    )

    // Try opening the web browser appropriately
    try {
      if (!java.awt.GraphicsEnvironment.isHeadless() &&
        java.awt.Desktop.isDesktopSupported() &&
        java.awt.Desktop.getDesktop().isSupported(java.awt.Desktop.Action.BROWSE))
      {
        java.awt.Desktop.getDesktop().browse(new java.net.URI("http://localhost:8090/"))
      }
      else if(!java.awt.GraphicsEnvironment.isHeadless() && java.awt.Desktop.isDesktopSupported()) {
        JOptionPane.showMessageDialog(null, "Point your browser to http://localhost:8090/")

      }
      else {
        println("Launching server in headless mode.")
      }
    } catch {
      case exc: java.awt.HeadlessException =>
      case exc: java.lang.ClassNotFoundException =>
      case exc: Exception =>
    }
  }

}
