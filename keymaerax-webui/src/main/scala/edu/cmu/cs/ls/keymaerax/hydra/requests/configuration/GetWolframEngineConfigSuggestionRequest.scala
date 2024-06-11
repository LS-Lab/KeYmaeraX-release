/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.MathematicaConfigSuggestionResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.info.Os
import edu.cmu.cs.ls.keymaerax.tools.ToolPathFinder

import java.nio.file.Paths

class GetWolframEngineConfigSuggestionRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    val paths = ToolPathFinder.findMathematicaInstallDir().flatMap(ToolPathFinder.findMathematicaPaths)

    val suggestionFound = paths.isDefined
    val suggestion = paths.getOrElse(
      ToolPathFinder
        .MathematicaPaths(mathKernel = Paths.get("path/to/MathKernel"), jlinkLib = Paths.get("path/to/jlinkLib"))
    )

    new MathematicaConfigSuggestionResponse(Os.Name, suggestionFound, suggestion)
  }
}
