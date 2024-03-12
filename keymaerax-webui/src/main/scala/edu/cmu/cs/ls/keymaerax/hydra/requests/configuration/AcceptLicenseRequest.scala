/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{
  BooleanResponse,
  ConfigurationPOJO,
  DBAbstraction,
  Request,
  Response,
  WriteRequest,
}

import scala.collection.immutable.{List, Map, Nil}

class AcceptLicenseRequest(db: DBAbstraction) extends Request with WriteRequest {
  def resultingResponses(): List[Response] = {
    val newConfiguration = new ConfigurationPOJO("license", Map("accepted" -> "true"))
    db.updateConfiguration(newConfiguration)
    BooleanResponse(flag = true) :: Nil
  }
}
