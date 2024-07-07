/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.responses.configuration.Z3ConfigSuggestionResponse
import org.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import org.keymaerax.tools.install.Z3Installer

class GetZ3ConfigSuggestionRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = new Z3ConfigSuggestionResponse(Z3Installer.defaultZ3Path)
}
