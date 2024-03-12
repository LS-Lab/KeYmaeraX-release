/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, ReadRequest, Request, Response}

import scala.collection.immutable.{List, Nil}

//@todo Detect closed connections and request timeouts server-side
class CancelToolRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val allCancelled = ToolProvider.tools().map(_.cancel()).reduce(_ && _)
    BooleanResponse(flag = allCancelled) :: Nil
  }
}
