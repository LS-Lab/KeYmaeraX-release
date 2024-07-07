/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.tools

import org.keymaerax.btactics.ToolProvider
import org.keymaerax.hydra.{BooleanResponse, ReadRequest, Request, Response}

//@todo Detect closed connections and request timeouts server-side
class CancelToolRequest() extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    val allCancelled = ToolProvider.tools().map(_.cancel()).reduce(_ && _)
    BooleanResponse(flag = allCancelled)
  }
}
