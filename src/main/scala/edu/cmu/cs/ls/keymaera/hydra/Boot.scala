package edu.cmu.cs.ls.keymaera.hydra

import javax.swing.JOptionPane

import akka.actor.{ActorSystem, Props}
import akka.io.IO
import edu.cmu.cs.ls.keymaera.api.ComponentConfig
import spray.can.Http

import scala.concurrent.duration.FiniteDuration

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

  //Sorry, couldn't find a better method than this for the moment.
  {
    import scala.concurrent.ExecutionContext.Implicits.global
    val someTime = new FiniteDuration(4, scala.concurrent.duration.SECONDS)
    this.system.scheduler.scheduleOnce(someTime)(onLoad)
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
