/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.MathematicaConfigSuggestionResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.tools.ext.WolframScript
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

import scala.collection.immutable.{List, Nil}

class GetWolframScriptConfigSuggestionRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val os = System.getProperty("os.name")
    val jvmBits = System.getProperty("sun.arch.data.model")
    try {
      val we = new WolframScript()
      val version = we.getVersion
      we.shutdown()
      new MathematicaConfigSuggestionResponse(os, jvmBits, true,
        ToolConfiguration.ConfigSuggestion(version.major + "." + version.minor + "." + version.revision, "", "", "",
          ""), Nil) :: Nil
    } catch {
      case _: Throwable =>
        new MathematicaConfigSuggestionResponse(os, jvmBits, false,
          ToolConfiguration.ConfigSuggestion("", "", "", "", ""), Nil) :: Nil
    }
  }
}
