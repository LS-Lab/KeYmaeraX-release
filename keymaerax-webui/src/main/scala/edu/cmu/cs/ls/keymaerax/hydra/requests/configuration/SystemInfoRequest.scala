/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.SystemInfoResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.info.Os

import scala.collection.immutable.{List, Nil}

class SystemInfoRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    new SystemInfoResponse(
      Os.Name,
      Os.Version,
      System.getProperty("java.home"),
      System.getProperty("java.vendor"),
      System.getProperty("java.version"),
      Os.JvmArchType,
    ) :: Nil
  }
}
