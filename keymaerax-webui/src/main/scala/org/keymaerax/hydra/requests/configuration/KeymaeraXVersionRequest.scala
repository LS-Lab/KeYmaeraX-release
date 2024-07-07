/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.UpdateChecker
import org.keymaerax.hydra.responses.configuration.KeymaeraXVersionResponse
import org.keymaerax.hydra.{ReadRequest, Request, Response}
import org.keymaerax.info.Version

class KeymaeraXVersionRequest extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    new KeymaeraXVersionResponse(Version.toString, UpdateChecker.upToDate, UpdateChecker.latestVersion.map(_.toString))
  }
}
