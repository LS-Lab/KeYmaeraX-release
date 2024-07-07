/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.responses.configuration.ToolConfigStatusResponse
import org.keymaerax.hydra.{ReadRequest, Request, Response}
import org.keymaerax.tools.ToolName

class Z3ConfigStatusRequest extends Request with ReadRequest {
  override def resultingResponse(): Response = new ToolConfigStatusResponse(ToolName.Z3, true)
}
