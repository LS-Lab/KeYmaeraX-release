/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import akka.actor.{Actor, ActorSystem, Props}
import akka.io.IO
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleInterpreter, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.hydra.HyDRAServerConfig.{host, port}
import edu.cmu.cs.ls.keymaerax.launcher.{DefaultConfiguration, LoadingDialogFactory, SystemWebBrowser}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import spray.can.Http

/**
  * Creates a HyDRA server listening on a host and port specified in the database's config file under the configurations serverconfig.host and serverconfig.port.
  * Uses localhost and 8090 by default.
  *
  * @note The HyDRA_SSL environmental variable needs to be set properly because it is used in application.conf.
  *       Main.startServer should so the correct thing based upon the current value of that flag. However, from within
  *       IntelliJ, you may want to modify application.conf directly and comment out the assertion at the top of this object.
  *
  * @see [[SSLBoot]] for SSL-enabled deployments.
  * @author Nathan Fulton
  */
object NonSSLBoot extends App {
  /** Actor notified when binding is finished */
  class BindingFinishedActor extends Actor {
    def receive: Actor.Receive = {
      case _: Http.Bound =>
        LoadingDialogFactory().addToStatus(15, Some("Finished loading"))

        // Finally, print a message indicating that the server was started.
        println(
          "**********************************************************\n" +
            "****                   KeYmaera X                     ****\n" +
            "****                                                  ****\n" +
            "**** OPEN YOUR WEB BROWSER AT  http://" + host + ":" + port + "/ ****\n" +
            "****                                                  ****\n" +
            "**** THE BROWSER MAY NEED RELOADS TILL THE PAGE SHOWS ****\n" +
            "**********************************************************\n"
        )

        LoadingDialogFactory().close()
        SystemWebBrowser(s"http://$host:$port/")
      case _ =>
        LoadingDialogFactory().addToStatus(0, Some("Loading failed..."))
        System.exit(1)
    }
  }

  LoadingDialogFactory() //@note show if not already started through Main.scala

  assert(!System.getenv().containsKey("HyDRA_SSL") || System.getenv("HyDRA_SSL").equals("off"),
    "A non-SSL server can only be booted when the environment var HyDRA_SSL is unset or is set to 'off'")

  import HyDRAServerConfig._
  val config = ConfigFactory.load()
    .withValue("akka.loglevel", ConfigValueFactory.fromAnyRef("OFF"))
    .withValue("akka.stdout-loglevel", ConfigValueFactory.fromAnyRef("OFF"))
  implicit var system = ActorSystem("on-spray-can", config)

  HyDRAInitializer(args, database)

  val bindingFinished = system.actorOf(Props[BindingFinishedActor], "hydraloader")
  IO(Http).tell(Http.Bind(service, interface = host, port = port), bindingFinished)
}

/**
  * Boots a server with SSL enabled.
  *
  * Booting from SSL requires a KeyStore.jks file in the keymaerax-webui/src/main/resources directory.
  * The password for this key strong should be stored in the config table of the production database under the configuration key serverconfig.jks.
  *
  * @note The HyDRA_SSL environmental variable needs to be set properly because it is used in application.conf.
  *       Main.startServer should so the correct thing based upon the current value of that flag. However, from within
  *       IntelliJ, you may want to modify application.conf directly and comment out the assertion at the top of this object.
  *
  * @see [[NonSSLBoot]] is better if you are binding to localhost or only exposing your server to trusted clients (i.e., not on the internet or a semi-public intranet.)
  * @author Nathan Fulton
  */
object SSLBoot extends App with KyxSslConfiguration {
  //@note when booting from IntelliJ, you will want to set HyDRA_SSL and then boot IntelliJ. Setting HyDRA_SSL in a separate terminal once IntelliJ is running won't work.
  //Alternatively, you can comment out these assertions and then change application.conf to just say ssl-encryption = on.
  assert(System.getenv().containsKey("HyDRA_SSL"),
    s"An SSL server can only be booted when the environment var HyDRA_SSL is set to 'on', but it is currently not set. (Current Environemnt: ${System.getenv.keySet().toArray().toList.mkString(", ")}).")
  assert(System.getenv("HyDRA_SSL").equals("on"),
    s"An SSL server can only be booted when the environment var HyDRA_SSL is set to 'on', but it is currently set to ${System.getenv("HyDRA_SSL")}")

  import HyDRAServerConfig._
  implicit var system = ActorSystem("on-spray-can")

  assert(database.getConfiguration("serverconfig").config.get("jks").isDefined,
    "ERROR: Cannot start an SSL server without a password for the KeyStore.jks file stored in the the serverconfig.jks configuration.")

  if(host != "0.0.0.0")
    println("WARNING: Expecting host 0.0.0.0 in SSL mode.")

  //@todo Should also check that the .aks file actually exists.

  println(s"SSL BOOT: Attempting to listen on $host:$port. SSL requests only!")
  println("NOTE: No browser instance will open because we assume SSL-hosted servers are headless (i.e., SSL mode is for production deployments only -- if hosting locally, use NonSSLBoot!)")

  HyDRAInitializer(args, database)
  IO(Http) ! Http.Bind(service, interface = host, port = port)
}

/**
  * Initializes the HyDRA server.
  * @author Nathan Fulton
  */
object HyDRAInitializer {
  private type OptionMap = Map[Symbol, Any]

  def apply(args : Array[String], database: DBAbstraction): Unit = {
    val options = nextOption(Map('commandLine -> args.mkString(" ")), args.toList)

    //@note setup interpreter
    BelleInterpreter.setInterpreter(SequentialInterpreter())
    //@note pretty printer setup must be first, otherwise derived axioms print wrong
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    // connect invariant generator to tactix library
    val generator = new ConfigurableGenerator[Formula]()
    TactixLibrary.invGenerator = generator
    KeYmaeraXParser.setAnnotationListener((p:Program,inv:Formula) => generator.products += (p->inv))

    LoadingDialogFactory().addToStatus(15, Some("Connecting to arithmetic tools..."))

    try {
      val preferredTool = preferredToolFromDB(database)
      val config = configFromDB(options, database, preferredTool)
      createTool(options, config, preferredTool)
    } catch {
      //@todo add e to log here and in other places
      case e:Throwable => println("===> WARNING: Failed to initialize Mathematica. " + e)
        println("You should configure settings in the UI and restart KeYmaera X.")
        println("Or specify the paths to the libraries for your system explicitly from command line by running\n" +
          "  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink")
        println("Current configuration:\n" + edu.cmu.cs.ls.keymaerax.tools.diagnostic)
        e.printStackTrace()
    }

    LoadingDialogFactory().addToStatus(5, Some("Updating lemma caches..."))

    try {
      //Delete the lemma database if KeYmaera X has been updated since the last time the database was populated.
      val cacheVersion = LemmaDBFactory.lemmaDB.version()
      if(StringToVersion(cacheVersion) < StringToVersion(edu.cmu.cs.ls.keymaerax.core.VERSION))
        LemmaDBFactory.lemmaDB.deleteDatabase()
      //Populate the derived axioms database.
      DerivedAxioms.prepopulateDerivedLemmaDatabase()
    } catch {
      case e : Exception =>
        println("===> WARNING: Could not prepopulate the derived lemma database. This is a critical error -- the UI will fail to work! <===")
        println("You should configure settings in the UI and restart KeYmaera X")
        e.printStackTrace()
    }
  }

  def nextOption(map: OptionMap, list: List[String]): OptionMap = list match {
    case Nil => map
    case "-tool" :: value :: tail => nextOption(map ++ Map('tool -> value), tail)
    case "-ui" :: tail => nextOption(map, tail)
    case "-launch" :: tail => nextOption(map, tail)
    case option :: tail => println("[Warning] Unknown option " + option + "\n\n" /*+ usage*/); nextOption(map, tail)
  }

  private def createTool(options: OptionMap, config: ToolProvider.Configuration, preferredTool: String): Unit = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    val provider = tool.toLowerCase() match {
      case "mathematica" => new MathematicaToolProvider(config)
      case "z3" => new Z3ToolProvider
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
    ToolProvider.setProvider(provider)
    assert(provider.tools().forall(_.isInitialized), "Tools should be initialized after init()")
  }

  private def configFromDB(options: OptionMap, db: DBAbstraction, preferredTool: String): ToolProvider.Configuration = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    tool.toLowerCase() match {
      case "mathematica" => mathematicaConfigFromDB(db)
      case "z3" => Map.empty
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  private def preferredToolFromDB(db: DBAbstraction): String = {
    db.getConfiguration("tool").config.getOrElse("qe", throw new Exception("No preferred tool"))
  }

  def mathematicaConfigFromDB(db: DBAbstraction): ToolProvider.Configuration = {
    getMathematicaLinkName(db) match {
      case Some(l) => getMathematicaLibDir(db) match {
        case Some(libDir) => Map("linkName" -> l, "libDir" -> libDir)
        case None => Map("linkName" -> l)
      }
      case None => DefaultConfiguration.defaultMathematicaConfig
    }
  }

  private def getMathematicaLinkName(db: DBAbstraction): Option[String] = {
    db.getConfiguration("mathematica").config.get("linkName")
  }

  private def getMathematicaLibDir(db: DBAbstraction): Option[String] = {
    val config = db.getConfiguration("mathematica").config
    if (config.contains("jlinkLibDir")) Some(config("jlinkLibDir"))
    else None
  }
}

/** Config vars needed for server setup. */
object HyDRAServerConfig {
  // we need an ActorSystem to host our application in
  var system = ActorSystem("on-spray-can")
  val database = DBAbstractionObj.defaultDatabase
  var service = system.actorOf(Props[RestApiActor], "hydra")

  val databaserServerConfig = database.getAllConfigurations.find(_.name == "serverconfig")

  val (isHosted:Boolean, host:String, port:Int) = databaserServerConfig match {
    case Some(c) =>
      assert(c.config.keySet.contains("host"), "If serverconfig configuration exists then it should have a 'host' key.")
      assert(c.config.keySet.contains("port"), "If serverconfig configuration exists then it should have a 'port' key.")
      val isHosted = c.config.get("isHosted") match {
        case Some(s) => s.equals("true")
        case None => false
      }
      (isHosted, c.config("host"), Integer.parseInt(c.config("port")))
    case None => (false, "127.0.0.1", 8090) //default values.
  }

  assert(isHosted || host == "127.0.0.1" || host == "localhost",
    "Either isHosted should be set or else the host should be localhost. This is crucial -- isHosted is used in security-critical ways.")
}