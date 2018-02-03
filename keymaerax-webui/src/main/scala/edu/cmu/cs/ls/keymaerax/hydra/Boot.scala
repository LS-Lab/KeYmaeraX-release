/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import akka.actor.{Actor, ActorSystem, Props}
import akka.io.IO
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleInterpreter, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.hydra.HyDRAServerConfig.{host, port}
import edu.cmu.cs.ls.keymaerax.launcher.{DefaultConfiguration, LoadingDialogFactory, SystemWebBrowser}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import org.apache.logging.log4j.scala.Logging
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
object NonSSLBoot extends App with Logging {
  /** Actor notified when binding is finished */
  class BindingFinishedActor extends Actor {
    def receive: Actor.Receive = {
      case _: Http.Bound =>
        LoadingDialogFactory().addToStatus(15, Some("Finished loading"))

        // Finally, print a message indicating that the server was started.
        logger.info(
          "\n**********************************************************\n" +
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
object SSLBoot extends App with KyxSslConfiguration with Logging {
  //@note when booting from IntelliJ, you will want to set HyDRA_SSL and then boot IntelliJ. Setting HyDRA_SSL in a separate terminal once IntelliJ is running won't work.
  //Alternatively, you can comment out these assertions and then change application.conf to just say ssl-encryption = on.
  assert(System.getenv().containsKey("HyDRA_SSL"),
    s"An SSL server can only be booted when the environment var HyDRA_SSL is set to 'on', but it is currently not set. (Current Environemnt: ${System.getenv.keySet().toArray().toList.mkString(", ")}).")
  assert(System.getenv("HyDRA_SSL").equals("on"),
    s"An SSL server can only be booted when the environment var HyDRA_SSL is set to 'on', but it is currently set to ${System.getenv("HyDRA_SSL")}")

  import HyDRAServerConfig._
  implicit var system = ActorSystem("on-spray-can")

  assert(Configuration.getOption(Configuration.Keys.JKS).isDefined,
    "ERROR: Cannot start an SSL server without a password for the KeyStore.jks file stored in the the serverconfig.jks configuration.")

  if(host != "0.0.0.0")
    logger.warn("WARNING: Expecting host 0.0.0.0 in SSL mode.")

  //@todo Should also check that the .aks file actually exists.

  logger.info(s"SSL BOOT: Attempting to listen on $host:$port. SSL requests only!")
  logger.info("NOTE: No browser instance will open because we assume SSL-hosted servers are headless (i.e., SSL mode is for production deployments only -- if hosting locally, use NonSSLBoot!)")

  HyDRAInitializer(args, database)
  IO(Http) ! Http.Bind(service, interface = host, port = port)
}

/**
  * Initializes the HyDRA server.
  * @author Nathan Fulton
  */
object HyDRAInitializer extends Logging {
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
      val preferredTool = preferredToolFromConfig
      val config = configFromDB(options, database, preferredTool)
      createTool(options, config, preferredTool)
    } catch {
      case e: Throwable =>
        val msg =
          s"""===> WARNING: Failed to initialize Mathematica.
            |You should configure settings in the UI and restart KeYmaera X.
            |Or specify the paths to the libraries for your system explicitly from command line by running
            |  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink
            |Current configuration:
            |${edu.cmu.cs.ls.keymaerax.tools.diagnostic}
          """.stripMargin
        logger.warn(msg, e)
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
      case e: Exception =>
        val msg =
          """===> WARNING: Could not prepopulate the derived lemma database. This is a critical error -- the UI will fail to work! <===
            |You should configure settings in the UI and restart KeYmaera X
          """.stripMargin
        logger.warn(msg, e)
    }
  }

  def nextOption(map: OptionMap, list: List[String]): OptionMap = list match {
    case Nil => map
    case "-tool" :: value :: tail => nextOption(map ++ Map('tool -> value), tail)
    case "-ui" :: tail => nextOption(map, tail)
    case "-launch" :: tail => nextOption(map, tail)
    case option :: tail => logger.warn("[Warning] Unknown option " + option + "\n\n" /*+ usage*/); nextOption(map, tail)
  }

  private def createTool(options: OptionMap, config: ToolProvider.Configuration, preferredTool: String): Unit = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    val provider = tool.toLowerCase() match {
      case "mathematica" =>
        try {
          val p = new MathematicaToolProvider(config)
          if (!p.tools().forall(_.isInitialized)) {
            val msg =
              """Unable to connect to Mathematica, switching to Z3
                |Please check your Mathematica configuration in Help->Tools
              """.stripMargin
            logger.info(msg)
            new Z3ToolProvider
          } else p
        } catch {
          case ex: Throwable =>
            val msg =
              """Unable to connect to Mathematica, switching to Z3
                |Please check your Mathematica configuration in Help->Tools
                |Mathematica initialization failed with the error below
              """.stripMargin
            logger.warn(msg, ex)
            logger.info("Starting with Z3 since Mathematica initialization failed")
            new Z3ToolProvider
        }
      case "z3" => new Z3ToolProvider
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
    ToolProvider.setProvider(provider)
    assert(provider.tools().forall(_.isInitialized), "Tools should be initialized after init()")
  }

  private def configFromDB(options: OptionMap, db: DBAbstraction, preferredTool: String): ToolProvider.Configuration = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    tool.toLowerCase() match {
      case "mathematica" => mathematicaConfig
      case "z3" => Map.empty
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  private def preferredToolFromConfig: String = {
    Configuration.getOption(Configuration.Keys.QE_TOOL).getOrElse(throw new Exception("No preferred tool"))
  }

  def mathematicaConfig: ToolProvider.Configuration = {
    getMathematicaLinkName match {
      case Some(l) => getMathematicaLibDir match {
        case Some(libDir) => Map("linkName" -> l, "libDir" -> libDir)
        case None => Map("linkName" -> l)
      }
      case None => DefaultConfiguration.defaultMathematicaConfig
    }
  }

  private def getMathematicaLinkName: Option[String] = {
    Configuration.getOption(Configuration.Keys.MATHEMATICA_LINK_NAME)
  }

  private def getMathematicaLibDir: Option[String] = {
    Configuration.getOption(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
  }
}

/** Config vars needed for server setup. */
object HyDRAServerConfig {
  // we need an ActorSystem to host our application in
  var system = ActorSystem("on-spray-can")
  val database = DBAbstractionObj.defaultDatabase
  var service = system.actorOf(Props[RestApiActor], "hydra")

  val (isHosted: Boolean, host: String, port: Int) =
    (Configuration(Configuration.Keys.IS_HOSTED) == "true",
      Configuration(Configuration.Keys.HOST),
      Integer.parseInt(Configuration(Configuration.Keys.PORT)))

  assert(isHosted || host == "127.0.0.1" || host == "localhost",
    "Either isHosted should be set or else the host should be localhost. This is crucial -- isHosted is used in security-critical ways.")
}