/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.MathematicaConfigurationResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}

import java.io.File
import java.util.Locale
import scala.collection.immutable.{List, Nil}

class GetMathematicaConfigurationRequest(db: DBAbstraction, toolName: String)
    extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val jlinkLibFile = {
      if (osName.contains("win")) "JLinkNativeLibrary.dll"
      else if (osName.contains("mac")) "libJLinkNativeLibrary.jnilib"
      else if (osName.contains("nix") || osName.contains("nux") || osName.contains("aix")) "libJLinkNativeLibrary.so"
      else "Unknown"
    }
    toolName match {
      case "mathematica"
          if Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) =>
        new MathematicaConfigurationResponse(
          Configuration(Configuration.Keys.MATHEMATICA_LINK_NAME),
          Configuration(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) + File.separator + jlinkLibFile,
          Configuration.getString(Configuration.Keys.MATH_LINK_TCPIP).getOrElse(""),
        ) :: Nil
      case "wolframengine"
          if Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) =>
        new MathematicaConfigurationResponse(
          Configuration(Configuration.Keys.WOLFRAMENGINE_LINK_NAME),
          Configuration(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) + File.separator + jlinkLibFile,
          Configuration.getString(Configuration.Keys.WOLFRAMENGINE_TCPIP).getOrElse(""),
        ) :: Nil
      case _ => new MathematicaConfigurationResponse("", "", "") :: Nil
    }
  }
}
