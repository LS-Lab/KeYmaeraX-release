/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, LocalhostOnlyRequest, ReadRequest, Response}

import scala.collection.immutable.{List, Nil}

class SaveFullConfigRequest(content: String) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    Configuration.overwrite(content)
    BooleanResponse(flag = true) :: Nil
  }
}
