/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.MathematicaConfigSuggestionResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.info.Os
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

import scala.collection.immutable.{List, Nil}

class GetWolframEngineConfigSuggestionRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val allSuggestions = ToolConfiguration.wolframEngineSuggestion()
    val (suggestionFound, suggestion) = allSuggestions.find(s =>
      new java.io.File(s.kernelPath + s.kernelName).exists && new java.io.File(s.jlinkPath + s.jlinkName).exists
    ) match {
      case Some(s) => (true, s)
      case None => (false, allSuggestions.head) // use the first configuration as suggestion when nothing else matches
    }

    new MathematicaConfigSuggestionResponse(Os.Name, suggestionFound, suggestion, allSuggestions) :: Nil
  }
}
