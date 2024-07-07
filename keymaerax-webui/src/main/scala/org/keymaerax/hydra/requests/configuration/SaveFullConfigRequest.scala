/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.hydra.{BooleanResponse, LocalhostOnlyRequest, ReadRequest, Response}

class SaveFullConfigRequest(content: String) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    Configuration.overwrite(content)
    BooleanResponse(flag = true)
  }
}
