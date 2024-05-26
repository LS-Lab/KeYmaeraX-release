/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.{
  MathematicaToolProvider,
  MultiToolProvider,
  NoneToolProvider,
  ToolProvider,
  WolframEngineToolProvider,
  WolframScriptToolProvider,
  Z3ToolProvider,
}
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.ToolConfigStatusResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, LocalhostOnlyRequest, Response, WriteRequest}
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

import scala.collection.immutable.{List, Map, Nil}

class SetToolRequest(db: DBAbstraction, tool: String) extends LocalhostOnlyRequest with WriteRequest {
  override def resultingResponses(): List[Response] = {
    // @todo more/different tools
    if (tool != "mathematica" && tool != "z3" && tool != "wolframengine" && tool != "wolframscript")
      new ErrorResponse("Unknown tool " + tool + ", expected either 'mathematica' or 'z3' or 'wolframengine'") :: Nil
    else {
      assert(
        tool == "mathematica" || tool == "z3" || tool == "wolframengine" || tool == "wolframscript",
        "Expected either Mathematica or Z3 or Wolfram Engine tool",
      )
      ToolProvider.shutdown()
      val config = ToolConfiguration.config(tool)
      try {
        val (provider: Option[ToolProvider], saveToConfig: Boolean) = tool match {
          case "mathematica" =>
            if (
              new java.io.File(config.getOrElse("linkName", "")).exists &&
              new java.io.File(config.getOrElse("libDir", "")).exists
            ) {
              if (
                Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
                Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
              ) { (Some(MultiToolProvider(MathematicaToolProvider(config) :: Z3ToolProvider() :: Nil)), true) }
              else (None, false)
            } else { (Some(Z3ToolProvider()), false) }
          case "wolframengine" =>
            if (
              new java.io.File(config.getOrElse("linkName", "")).exists &&
              new java.io.File(config.getOrElse("libDir", "")).exists
            ) {
              if (
                Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
                Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) &&
                Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP)
              ) { (Some(MultiToolProvider(WolframEngineToolProvider(config) :: Z3ToolProvider() :: Nil)), true) }
              else (None, false)
            } else { (Some(Z3ToolProvider()), false) }
          case "wolframscript" =>
            (Some(MultiToolProvider(WolframScriptToolProvider(Map.empty) :: Z3ToolProvider() :: Nil)), true)
          case "z3" => (Some(Z3ToolProvider()), true)
          case _ => (Some(new NoneToolProvider), false)
        }
        provider match {
          case Some(p) =>
            if (saveToConfig) Configuration.set(Configuration.Keys.QE_TOOL, tool)
            ToolProvider.setProvider(p)
          case _ => // nothing to do
        }
        new ToolConfigStatusResponse(tool, provider.isDefined) :: Nil
      } catch {
        case ex: Throwable if tool == "mathematica" =>
          new ErrorResponse(
            "Error initializing " + tool +
              ". Please double-check the configuration paths and that the license is valid (e.g., start Mathematica and type $LicenseExpirationDate, check that license server is reachable, if used).",
            ex,
          ) :: Nil
        case ex: Throwable if tool == "wolframengine" =>
          new ErrorResponse(
            "Error initializing " + tool +
              ". Please double-check the configuration paths, that the license is valid and the computer is online for license checking. If Wolfram Engine remains unavailable and/or keeps crashing KeYmaera X, please run Wolfram Engine to update the license information (check by running $LicenseExpirationDate in Wolfram Engine) prior to starting KeYmaera X.",
            ex,
          ) :: Nil
        case ex: Throwable =>
          new ErrorResponse("Error initializing " + tool + ". Please double-check the configuration paths.", ex) :: Nil
      }
    }
  }
}
