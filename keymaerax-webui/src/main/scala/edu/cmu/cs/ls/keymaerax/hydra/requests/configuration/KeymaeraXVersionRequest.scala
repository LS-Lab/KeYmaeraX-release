/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.KeymaeraXVersionResponse
import edu.cmu.cs.ls.keymaerax.hydra.{ReadRequest, Request, Response}
import edu.cmu.cs.ls.keymaerax.{UpdateChecker, VersionNumber}

import scala.collection.immutable.{List, Nil}

class KeymaeraXVersionRequest extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    new KeymaeraXVersionResponse(
      VersionNumber.CURRENT.toString,
      UpdateChecker.upToDate,
      UpdateChecker.latestVersion.map(_.toString),
    ) :: Nil
  }
}
