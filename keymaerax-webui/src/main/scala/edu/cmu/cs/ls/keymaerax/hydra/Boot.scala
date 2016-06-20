/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerate, DerivedAxioms, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.launcher.{DefaultConfiguration, LoadingDialogFactory, SystemWebBrowser}
import edu.cmu.cs.ls.keymaerax.tools._
import akka.actor.{ActorSystem, Props}
import akka.io.IO
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program, QETool}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import spray.can.Http

import scala.concurrent.duration.FiniteDuration



object Boot extends App {
  private type OptionMap = Map[Symbol, Any]

  def restart(): Unit = {
    this.system.shutdown()
    this.system.awaitTermination()

    //Re-initialize the server
    this.system = ActorSystem("on-spray-can")
    val service = system.actorOf(Props[RestApiActor], "hydra")
    init()
    IO(Http) ! Http.Bind(service, interface = host, port = port)
  }

  def nextOption(map: OptionMap, list: List[String]): OptionMap = list match {
    case Nil => map
    case "-tool" :: value :: tail => nextOption(map ++ Map('tool -> value), tail)
    case option :: tail => println("[Error] Unknown option " + option + "\n\n" /*+ usage*/); sys.exit(1)
  }

  def init(): Unit = {
    val options = nextOption(Map('commandLine -> args.mkString(" ")), args.toList)

    //@note pretty printer setup must be first, otherwise derived axioms print wrong
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    // connect invariant generator to tactix library
    val generator = new ConfigurableGenerate[Formula]()
    TactixLibrary.invGenerator = generator
    KeYmaeraXParser.setAnnotationListener((p:Program,inv:Formula) => generator.products += (p->inv))

    val tool: Tool with QETool with DiffSolutionTool with CounterExampleTool = createTool(options)

    try {
      initFromDB(tool, database)
      assert(tool.isInitialized, "Mathematica should be initialized after init()")
    } catch {
      //@todo add e to log here and in other places
      case e:Throwable => println("===> WARNING: Failed to initialize Mathematica. " + e)
        println("You should configure settings in the UI and restart KeYmaera X.")
        println("Or specify the paths to the libraries for your system explicitly from command line by running\n" +
          "  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink")
        println("Current configuration:\n" + edu.cmu.cs.ls.keymaerax.tools.diagnostic)
        e.printStackTrace()
    }

    DerivedAxioms.qeTool = tool
    TactixLibrary.qeTool = tool
    TactixLibrary.odeTool = tool
    TactixLibrary.cexTool = tool
    try {
      DerivedAxioms.prepopulateDerivedLemmaDatabase()
    } catch {
      case e : Exception =>
        println("===> WARNING: Could not prepopulate the derived lemma database. This is a critical error -- the UI will fail to work! <===")
        println("You should configure settings in the UI and restart KeYmaera X")
        e.printStackTrace()
    }
  }

  // we need an ActorSystem to host our application in
  implicit var system = ActorSystem("on-spray-can")

  // create and start our service actor
  var service = system.actorOf(Props[RestApiActor], "hydra")

  val database = DBAbstractionObj.defaultDatabase
  val config = database.getAllConfigurations.find(_.name == "serverconfig")
  val (isHosted:Boolean, host:String, port:Int) = config match {
    case Some(c) => (c.config("isHosted").equals("true"), c.config("host"), Integer.parseInt(c.config("port")))
    case None => (false, "127.0.0.1", 8090)
  }

  init()

  // start a new HTTP server on port 8080 with our service actor as the handler
  val io = IO(Http)
  val bind = Http.Bind(service, interface = host, port = port)

  io ! bind

  {
    import scala.concurrent.ExecutionContext.Implicits.global

    def someTime(x:Int) = new FiniteDuration(x, scala.concurrent.duration.SECONDS)

    this.system.scheduler.scheduleOnce(someTime(1))(LoadingDialogFactory().addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(2))(LoadingDialogFactory().addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(3))(LoadingDialogFactory().addToStatus(25))
    this.system.scheduler.scheduleOnce(someTime(4))(LoadingDialogFactory().addToStatus(20))
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
    SystemWebBrowser(s"http://$host:$port/")
    LoadingDialogFactory().close()
  }

  private def createTool(options: OptionMap): Tool with QETool with DiffSolutionTool with CounterExampleTool = {
    val tool: String = options.getOrElse('tool, "mathematica").toString
    tool.toLowerCase() match {
      case "mathematica" => new Mathematica()
      case "z3" => new Z3()
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  private def initFromDB(tool: Tool, db: DBAbstraction) = tool match {
    case t: Mathematica => initMathematicaFromDB(t, db)
    case t: Z3 => t.init(Map.empty)
  }

  private def initMathematicaFromDB(mathematica: Mathematica, db: DBAbstraction) = {
    getMathematicaLinkName(db) match {
      case Some(l) => getMathematicaLibDir(db) match {
        case Some(libDir) => mathematica.init(Map("linkName" -> l, "libDir" -> libDir))
        case None => mathematica.init(Map("linkName" -> l))
      }
      case None => mathematica.init(DefaultConfiguration.defaultMathematicaConfig)
    }
  }

  private def getMathematicaLinkName(db: DBAbstraction): Option[String] = {
    db.getConfiguration("mathematica").config.get("linkName")
  }

  private def getMathematicaLibDir(db: DBAbstraction): Option[String] = {
    val config = db.getConfiguration("mathematica").config
    if (config.contains("jlinkLibDir")) Some(config.get("jlinkLibDir").get)
    else None
  }
}
