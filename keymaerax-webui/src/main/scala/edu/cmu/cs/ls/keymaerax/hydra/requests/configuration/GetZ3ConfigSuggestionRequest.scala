/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.Z3ConfigSuggestionResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.tools.install.Z3Installer

import scala.collection.immutable.{List, Nil}

class GetZ3ConfigSuggestionRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    new Z3ConfigSuggestionResponse(Z3Installer.defaultZ3Path) :: Nil
  }
}
