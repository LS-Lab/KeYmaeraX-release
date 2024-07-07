/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.hydra.responses.configuration.SystemInfoResponse
import org.keymaerax.hydra.{DBAbstraction, LocalhostOnlyRequest, ReadRequest, Response}
import org.keymaerax.info.Os

class SystemInfoRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    new SystemInfoResponse(
      Os.Name,
      Os.Version,
      System.getProperty("java.home"),
      System.getProperty("java.vendor"),
      System.getProperty("java.version"),
    )
  }
}
