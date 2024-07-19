/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.hydra.responses.configuration.MathematicaConfigurationResponse
import org.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}
import org.keymaerax.info.{Os, OsType}
import org.keymaerax.tools.ToolName

import java.io.File

class GetMathematicaConfigurationRequest(db: DBAbstraction, toolName: ToolName.Value)
    extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    val jlinkLibFile = Os.Type match {
      case OsType.Windows => "JLinkNativeLibrary.dll"
      case OsType.Linux => "libJLinkNativeLibrary.so"
      case OsType.MacOs => "libJLinkNativeLibrary.jnilib"
      case OsType.Unknown => "Unknown"
    }
    toolName match {
      case ToolName.Mathematica
          if Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) =>
        new MathematicaConfigurationResponse(
          Configuration(Configuration.Keys.MATHEMATICA_LINK_NAME),
          Configuration(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) + File.separator + jlinkLibFile,
          Configuration.getString(Configuration.Keys.MATH_LINK_TCPIP).getOrElse(""),
        )
      case ToolName.WolframEngine
          if Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) =>
        new MathematicaConfigurationResponse(
          Configuration(Configuration.Keys.WOLFRAMENGINE_LINK_NAME),
          Configuration(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) + File.separator + jlinkLibFile,
          Configuration.getString(Configuration.Keys.WOLFRAMENGINE_TCPIP).getOrElse(""),
        )
      case _ => new MathematicaConfigurationResponse("", "", "")
    }
  }
}