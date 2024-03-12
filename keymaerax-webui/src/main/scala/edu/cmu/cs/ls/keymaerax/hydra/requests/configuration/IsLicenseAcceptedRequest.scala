/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, ReadRequest, Request, Response}

import scala.collection.immutable.{List, Nil}

class IsLicenseAcceptedRequest(db: DBAbstraction) extends Request with ReadRequest {
  def resultingResponses(): List[Response] = {
    BooleanResponse(
      db.getConfiguration("license").config.contains("accepted") &&
        db.getConfiguration("license").config("accepted") == "true"
    ) :: Nil
  }
}
