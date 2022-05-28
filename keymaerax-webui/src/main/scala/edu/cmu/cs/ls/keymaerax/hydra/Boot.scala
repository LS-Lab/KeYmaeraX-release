/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import akka.actor.ActorSystem
import akka.http.scaladsl.{ConnectionContext, Http, HttpsConnectionContext}
import akka.stream.ActorMaterializer
import akka.util.Timeout
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration, KeYmaeraXStartup, Logging}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.launcher.{KeYmaeraX, LoadingDialogFactory, SystemWebBrowser}

import scala.concurrent.duration._
import akka.http.scaladsl.server.Route
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

import scala.concurrent.ExecutionContextExecutor
import scala.language.postfixOps

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
  assert(!System.getenv().containsKey("HyDRA_SSL") || System.getenv("HyDRA_SSL").equals("off"),
    "A non-SSL server can only be booted when the environment var HyDRA_SSL is unset or is set to 'off'")

  Configuration.setConfiguration(FileConfiguration)

  //Initialize all tools.
  val url = HyDRAInitializer(args, HyDRAServerConfig.database)

  //Some boilerplate code that I don't understand.
  implicit val system: ActorSystem = ActorSystem("hydraloader") //Not sure what the significance of this name is?
  implicit val materializer: ActorMaterializer = ActorMaterializer()
  implicit val executionContext: ExecutionContextExecutor = system.dispatcher
  implicit val timeout: Timeout = Timeout(10 seconds) //@note this might need to be much higher.
  val config = ConfigFactory.load()
    .withValue("akka.loglevel", ConfigValueFactory.fromAnyRef("OFF"))
    .withValue("akka.stdout-loglevel", ConfigValueFactory.fromAnyRef("OFF"))

  val api = routes

  def routes : Route = RestApi.api

  //Do the KeYmaera X initialization GUI stuff...
  LoadingDialogFactory() //@note show if not already started through Main.scala
  Http().bindAndHandle(handler = api, interface = HyDRAServerConfig.host, port = HyDRAServerConfig.port) map {
    _ => {
      // Finally, print a message indicating that the server was started.
      LoadingDialogFactory().addToStatus(10, Some("Finished loading"))
      logger.info(
        "\n**********************************************************\n" +
          "****                   KeYmaera X                     ****\n" +
          "****                                                  ****\n" +
          "**** OPEN YOUR WEB BROWSER AT  http://" + HyDRAServerConfig.host + ":" + HyDRAServerConfig.port + "/ ****\n" +
          "****                                                  ****\n" +
          "**** THE BROWSER MAY NEED RELOADS TILL THE PAGE SHOWS ****\n" +
          "**********************************************************\n"
      )
      LoadingDialogFactory().close()
      SystemWebBrowser(s"http://${HyDRAServerConfig.host}:${HyDRAServerConfig.port}/" + url)
    }
  } recover {
    case _ =>
      LoadingDialogFactory().addToStatus(0, Some("Loading failed..."))
      System.exit(1)
  }
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
object SSLBoot extends App with Logging {
  //@note when booting from IntelliJ, you will want to set HyDRA_SSL and then boot IntelliJ. Setting HyDRA_SSL in a separate terminal once IntelliJ is running won't work.
  //Alternatively, you can comment out these assertions and then change application.conf to just say ssl-encryption = on.
  assert(System.getenv().containsKey("HyDRA_SSL"),
    s"An SSL server can only be booted when the environment var HyDRA_SSL is set to 'on', but it is currently not set. (Current Environemnt: ${System.getenv.keySet().toArray().toList.mkString(", ")}).")
  assert(System.getenv("HyDRA_SSL").equals("on"),
    s"An SSL server can only be booted when the environment var HyDRA_SSL is set to 'on', but it is currently set to ${System.getenv("HyDRA_SSL")}")

  Configuration.setConfiguration(FileConfiguration)

  //Initialize all tools.
  HyDRAInitializer(args, HyDRAServerConfig.database)

  assert(Configuration.getString(Configuration.Keys.JKS).isDefined,
    "ERROR: Cannot start an SSL server without a password for the KeyStore.jks file stored in the the serverconfig.jks configuration.")
  if (HyDRAServerConfig.host != "0.0.0.0")
    logger.warn("WARNING: Expecting host 0.0.0.0 in SSL mode.")

  //Some boilerplate code that I don't understand.
  implicit val system: ActorSystem = ActorSystem("hydraloader") //Not sure what the significance of this name is?
//  val sslConfig = AkkaSSLConfig()
  implicit val materializer: ActorMaterializer = ActorMaterializer()
  implicit val executionContext: ExecutionContextExecutor = system.dispatcher
  implicit val timeout: Timeout = Timeout(10 seconds) //@note this might need to be much higher.
  val config = ConfigFactory.load()
    .withValue("akka.loglevel", ConfigValueFactory.fromAnyRef("OFF"))
    .withValue("akka.stdout-loglevel", ConfigValueFactory.fromAnyRef("OFF"))

  val api = routes

  def routes : Route = RestApi.api

  val https: HttpsConnectionContext = ConnectionContext.https(KyxSslConfiguration.sslContext)
  Http().setDefaultServerHttpContext(https)
  Http().bindAndHandle(handler = api, interface = HyDRAServerConfig.host, port = HyDRAServerConfig.port, connectionContext = https) map {
    _ => {
      // Finally, print a message indicating that the server was started.
      logger.info(s"SSL BOOT: Attempting to listen on ${HyDRAServerConfig.host}:${HyDRAServerConfig.port}. SSL requests only!")
      logger.info("NOTE: No browser instance will open because we assume SSL-hosted servers are headless (i.e., SSL mode is for production deployments only -- if hosting locally, use NonSSLBoot!)")
    }
  } recover {
    case ex =>
      println(s"Failed to start an SSL server. ${ex.getMessage}")
      logger.error(s"Failed to start an SSL server. ${ex.getMessage}")
      System.exit(1)
  }
}

/**
  * Initializes the HyDRA server.
  * @author Nathan Fulton
  */
object HyDRAInitializer extends Logging {
  private type OptionMap = Map[Symbol, Any]

  /** Initializes the server using arguments `args` and `database`. Returns the page to open. */
  def apply(args: Array[String], database: DBAbstraction): String = {
    val options = KeYmaeraX.nextOption(Map('commandLine -> args.mkString(" ")), args.toList)

    LoadingDialogFactory().addToStatus(10, Some("Connecting to arithmetic tools ..."))

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

    LoadingDialogFactory().addToStatus(15, Some("Updating lemma caches..."))

    KeYmaeraXStartup.initLemmaCache((msg: String, ex: Throwable) => {
      System.err.println(msg)
      ex.printStackTrace(System.err)
      logger.error(msg, ex)
    })

    def proofUrl(userId: String, proofId: Int): String = {
      database.getUser(userId) match {
        case Some(u) =>
          SessionManager.defaultUserTokenKey = Some(SessionManager.add(u))
          "dashboard.html?#/proofs/" + proofId
        case None => ""
      }
    }

    options.get('open) match {
      case None => "" //@note start with model list
      case Some(archive) =>
        if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true")) {
          Configuration.getString(Configuration.Keys.DEFAULT_USER) match {
            case None =>
              logger.warn("Unable to import archive: no default user configured")
              ""
            case Some(user) =>
              LoadingDialogFactory().addToStatus(15, Some("Importing archive..."))
              val result = DatabasePopulator.importKya(database, user, archive.toString, prove = false, List.empty)
              result.succeeded.headOption match {
                case Some((_, id)) =>
                  database.getProofsForModel(id).headOption match {
                    case Some(p) => proofUrl(user, p.proofId)
                    case None => proofUrl(user, database.createProofForModel(id, "", "", "", None))
                  }
                case None => ""
              }
          }
        } else ""
    }
  }

  private def createTool(options: OptionMap, config: ToolProvider.Configuration, preferredTool: String): Unit = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    val provider = tool.toLowerCase() match {
      case "mathematica" => ToolProvider.initFallbackZ3(MathematicaToolProvider(config), "Mathematica")
      case "wolframengine" => ToolProvider.initFallbackZ3(WolframEngineToolProvider(config), "Wolfram Engine")
      case "wolframscript" => ToolProvider.initFallbackZ3(WolframScriptToolProvider(config), "Wolfram Script")
      case "z3" => new Z3ToolProvider
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
    ToolProvider.setProvider(provider)
    assert(provider.tools().forall(_.isInitialized), "Tools should be initialized after init()")
  }

  private def configFromDB(options: OptionMap, db: DBAbstraction, preferredTool: String): ToolProvider.Configuration = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    ToolConfiguration.config(tool.toLowerCase)
  }

  private def preferredToolFromConfig: String = {
    Configuration.getString(Configuration.Keys.QE_TOOL).getOrElse(throw new Exception("No preferred tool"))
  }
}

/** Config vars needed for server setup. */
object HyDRAServerConfig {
  // we need an ActorSystem to host our application in
  val system: ActorSystem = ActorSystem("on-spray-can")
  val database: DBAbstraction = DBAbstractionObj.defaultDatabase

  val (isHosted: Boolean, host: String, port: Int) =
    (Configuration(Configuration.Keys.IS_HOSTED) == "true",
      Configuration(Configuration.Keys.HOST),
      Integer.parseInt(Configuration(Configuration.Keys.PORT)))
}