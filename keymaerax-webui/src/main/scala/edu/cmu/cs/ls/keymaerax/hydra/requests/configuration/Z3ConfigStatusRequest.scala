/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.ToolConfigStatusResponse
import edu.cmu.cs.ls.keymaerax.hydra.{ReadRequest, Request, Response}

class Z3ConfigStatusRequest extends Request with ReadRequest {
  override def resultingResponse(): Response = new ToolConfigStatusResponse("z3", true)
}
