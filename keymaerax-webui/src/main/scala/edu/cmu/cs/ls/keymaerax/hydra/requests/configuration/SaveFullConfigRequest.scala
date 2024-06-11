/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, LocalhostOnlyRequest, ReadRequest, Response}

class SaveFullConfigRequest(content: String) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    Configuration.overwrite(content)
    BooleanResponse(flag = true)
  }
}
