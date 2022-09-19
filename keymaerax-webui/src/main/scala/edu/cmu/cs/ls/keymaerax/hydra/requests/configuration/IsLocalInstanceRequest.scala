/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, HyDRAServerConfig, ReadRequest, Request, Response}

import scala.collection.immutable.{List, Nil}

class IsLocalInstanceRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = BooleanResponse(!HyDRAServerConfig.isHosted) :: Nil
}
