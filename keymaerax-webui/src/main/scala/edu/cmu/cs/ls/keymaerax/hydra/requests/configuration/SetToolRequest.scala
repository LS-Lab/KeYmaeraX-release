/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.{
  MathematicaToolProvider,
  MultiToolProvider,
  ToolProvider,
  WolframEngineToolProvider,
  WolframScriptToolProvider,
  Z3ToolProvider,
}
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.ToolConfigStatusResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, LocalhostOnlyRequest, Response, WriteRequest}
import edu.cmu.cs.ls.keymaerax.tools.ToolName
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

class SetToolRequest(db: DBAbstraction, toolStr: String) extends LocalhostOnlyRequest with WriteRequest {

  private val tool = ToolName.parse(toolStr)

  override def resultingResponse(): Response = {
    ToolProvider.shutdown()
    val config = ToolConfiguration.config(tool)
    try {
      val (provider: Option[ToolProvider], saveToConfig: Boolean) = tool match {
        case ToolName.Mathematica =>
          if (
            new java.io.File(config.mathKernel.getOrElse("")).exists &&
            new java.io.File(config.jlinkLibDir.getOrElse("")).exists
          ) {
            if (
              Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
              Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
            ) { (Some(MultiToolProvider(MathematicaToolProvider(config) :: Z3ToolProvider() :: Nil)), true) }
            else (None, false)
          } else { (Some(Z3ToolProvider()), false) }
        case ToolName.WolframEngine =>
          if (
            new java.io.File(config.mathKernel.getOrElse("")).exists &&
            new java.io.File(config.jlinkLibDir.getOrElse("")).exists
          ) {
            if (
              Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
              Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) &&
              Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP)
            ) { (Some(MultiToolProvider(WolframEngineToolProvider(config) :: Z3ToolProvider() :: Nil)), true) }
            else (None, false)
          } else { (Some(Z3ToolProvider()), false) }
        case ToolName.WolframScript =>
          (Some(MultiToolProvider(WolframScriptToolProvider(ToolConfiguration()) :: Z3ToolProvider() :: Nil)), true)
        case ToolName.Z3 => (Some(Z3ToolProvider()), true)
      }
      provider match {
        case Some(p) =>
          if (saveToConfig) Configuration.set(Configuration.Keys.QE_TOOL, tool.toString)
          ToolProvider.setProvider(p)
        case _ => // nothing to do
      }
      new ToolConfigStatusResponse(tool, provider.isDefined)
    } catch {
      case ex: Throwable if tool == ToolName.Mathematica =>
        new ErrorResponse(
          "Error initializing " + tool +
            ". Please double-check the configuration paths and that the license is valid (e.g., start Mathematica and type $LicenseExpirationDate, check that license server is reachable, if used).",
          ex,
        )
      case ex: Throwable if tool == ToolName.WolframEngine =>
        new ErrorResponse(
          "Error initializing " + tool +
            ". Please double-check the configuration paths, that the license is valid and the computer is online for license checking. If Wolfram Engine remains unavailable and/or keeps crashing KeYmaera X, please run Wolfram Engine to update the license information (check by running $LicenseExpirationDate in Wolfram Engine) prior to starting KeYmaera X.",
          ex,
        )
      case ex: Throwable =>
        new ErrorResponse("Error initializing " + tool + ". Please double-check the configuration paths.", ex)
    }
  }
}
