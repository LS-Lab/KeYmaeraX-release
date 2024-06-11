/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, HyDRAServerConfig, ReadRequest, Request, Response}

class IsLocalInstanceRequest() extends Request with ReadRequest {
  override def resultingResponse(): Response = BooleanResponse(!HyDRAServerConfig.isHosted)
}
