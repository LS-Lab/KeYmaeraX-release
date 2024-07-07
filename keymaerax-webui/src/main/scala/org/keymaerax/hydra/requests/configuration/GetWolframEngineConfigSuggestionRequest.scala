/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.responses.configuration.MathematicaConfigSuggestionResponse
import org.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}
import org.keymaerax.info.Os
import org.keymaerax.tools.ToolPathFinder

import java.nio.file.Paths

class GetWolframEngineConfigSuggestionRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    val paths = ToolPathFinder.findWolframEngineInstallDir().flatMap(ToolPathFinder.findMathematicaPaths)

    val suggestionFound = paths.isDefined
    val suggestion = paths.getOrElse(
      ToolPathFinder
        .MathematicaPaths(mathKernel = Paths.get("path/to/MathKernel"), jlinkLib = Paths.get("path/to/jlinkLib"))
    )

    new MathematicaConfigSuggestionResponse(Os.Name, suggestionFound, suggestion)
  }
}
