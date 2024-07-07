/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.{BooleanResponse, HyDRAServerConfig, ReadRequest, Request, Response}

class IsLocalInstanceRequest() extends Request with ReadRequest {
  override def resultingResponse(): Response = BooleanResponse(!HyDRAServerConfig.isHosted)
}
