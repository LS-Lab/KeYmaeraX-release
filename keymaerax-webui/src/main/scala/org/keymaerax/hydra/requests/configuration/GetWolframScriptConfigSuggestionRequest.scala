/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.responses.configuration.MathematicaConfigSuggestionResponse
import org.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import org.keymaerax.info.Os
import org.keymaerax.tools.ToolPathFinder
import org.keymaerax.tools.ext.WolframScript

import java.nio.file.Paths

class GetWolframScriptConfigSuggestionRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    try {
      val we = new WolframScript()
      we.shutdown()
      new MathematicaConfigSuggestionResponse(
        Os.Name,
        true,
        ToolPathFinder.MathematicaPaths(mathKernel = Paths.get(""), jlinkLib = Paths.get("")),
      )
    } catch {
      case _: Throwable => new MathematicaConfigSuggestionResponse(
          Os.Name,
          false,
          ToolPathFinder.MathematicaPaths(mathKernel = Paths.get(""), jlinkLib = Paths.get("")),
        )
    }
  }
}
