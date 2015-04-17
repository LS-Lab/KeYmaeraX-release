package edu.cmu.cs.ls.keymaera.hydra

import akka.actor.{ActorSystem, Props}
import akka.io.IO
import edu.cmu.cs.ls.keymaera.api.ComponentConfig
import spray.can.Http

object Boot extends App {
  def restart(): Unit = {
    this.system.shutdown();
    this.system.awaitTermination();

    //Re-initialize the server
    this.system = ActorSystem("on-spray-can")
    var service = system.actorOf(Props[RestApiActor], "hydra")
    ComponentConfig.keymaeraInitializer.initialize()
    IO(Http) ! Http.Bind(service, interface = "localhost", port = 8090)
  }
  // we need an ActorSystem to host our application in
  implicit var system = ActorSystem("on-spray-can")

  // create and start our service actor
  var service = system.actorOf(Props[RestApiActor], "hydra")

  // spawn dependency injection framework
  ComponentConfig.keymaeraInitializer.initialize()

  // start a new HTTP server on port 8080 with our service actor as the handler
  IO(Http) ! Http.Bind(service, interface = "localhost", port = 8090)

  // Finally, print a message indicating that the server was started.
  println(
    "**********************************************************\n" +
    "****                   KeYmaera X                     ****\n" +
    "****                                                  ****\n" +
    "**** POINT YOUR WEB BROWSER TO http://localhost:8090/ ****\n" +
    "****                                                  ****\n" +
    "**********************************************************\n"
  )

}
