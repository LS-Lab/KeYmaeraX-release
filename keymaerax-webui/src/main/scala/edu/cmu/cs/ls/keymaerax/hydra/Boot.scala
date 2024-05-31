/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.Route
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.cli.Options
import edu.cmu.cs.ls.keymaerax.launcher.{LoadingDialogFactory, SystemWebBrowser}
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration, KeYmaeraXStartup, Logging}

import scala.concurrent.ExecutionContextExecutor
import scala.language.postfixOps

/**
 * Creates a HyDRA server listening on a host and port specified in the database's config file under the configurations
 * serverconfig.host and serverconfig.port. Uses localhost and 8090 by default.
 *
 * @author
 *   Nathan Fulton
 */
object NonSSLBoot extends Logging {
  def run(options: Options) = {
    Configuration.setConfiguration(FileConfiguration)

    // Initialize all tools.
    val url = HyDRAInitializer.run(options, HyDRAServerConfig.database)

    // Some boilerplate code that I don't understand.
    implicit val system: ActorSystem = ActorSystem("hydraloader") // Not sure what the significance of this name is?
    implicit val executionContext: ExecutionContextExecutor = system.dispatcher

    def routes: Route = RestApi.api
    val api = routes

    // Do the KeYmaera X initialization GUI stuff...
    LoadingDialogFactory() // @note show if not already started through Main.scala
    Http().newServerAt(interface = HyDRAServerConfig.host, port = HyDRAServerConfig.port).bindFlow(api) map { _ =>
      // Finally, print a message indicating that the server was started.
      LoadingDialogFactory().addToStatus(10, Some("Finished loading"))
      logger.info(s"Open your web browser at http://${HyDRAServerConfig.host}:${HyDRAServerConfig.port}/")
      LoadingDialogFactory().close()
      SystemWebBrowser(s"http://${HyDRAServerConfig.host}:${HyDRAServerConfig.port}/" + url)
    } recover { _ =>
      LoadingDialogFactory().addToStatus(0, Some("Loading failed..."))
      System.exit(1)
    }
  }
}

/**
 * Initializes the HyDRA server.
 * @author
 *   Nathan Fulton
 */
object HyDRAInitializer extends Logging {

  /** Initializes the server using arguments `args` and `database`. Returns the page to open. */
  def run(options: Options, database: DBAbstraction): String = {
    LoadingDialogFactory().addToStatus(10, Some("Connecting to arithmetic tools ..."))

    try {
      val preferredTool = preferredToolFromConfig
      val config = toolConfig(options, preferredTool)
      createTool(options, config, preferredTool)
    } catch {
      case e: Throwable =>
        val msg = s"""===> WARNING: Failed to initialize Mathematica.
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

    options.open match {
      case None => "" // @note start with model list
      case Some(archive) =>
        if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true")) {
          Configuration.getString(Configuration.Keys.DEFAULT_USER) match {
            case None =>
              logger.warn("Unable to import archive: no default user configured")
              ""
            case Some(user) =>
              LoadingDialogFactory().addToStatus(15, Some("Importing archive..."))
              val result = DatabasePopulator.importKya(database, user, archive.toString, List.empty)
              result.succeeded.headOption match {
                case Some((_, id)) => database.getProofsForModel(id).headOption match {
                    case Some(p) => proofUrl(user, p.proofId)
                    case None => proofUrl(user, database.createProofForModel(id, "", "", "", None))
                  }
                case None => ""
              }
          }
        } else ""
    }
  }

  private def createTool(options: Options, config: ToolConfiguration, preferredTool: String): Unit = {
    val tool: String = options.tool.getOrElse(preferredTool)
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

  private def toolConfig(options: Options, preferredTool: String): ToolConfiguration = {
    val tool: String = options.tool.getOrElse(preferredTool)
    ToolConfiguration.config(tool.toLowerCase, options.toToolConfig)
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

  val (isHosted: Boolean, host: String, port: Int) = (
    Configuration(Configuration.Keys.IS_HOSTED) == "true",
    Configuration(Configuration.Keys.HOST),
    Integer.parseInt(Configuration(Configuration.Keys.PORT)),
  )
}
