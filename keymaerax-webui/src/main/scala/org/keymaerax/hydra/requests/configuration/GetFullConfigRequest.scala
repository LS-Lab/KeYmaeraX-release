/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.hydra.responses.configuration.FullConfigurationResponse
import org.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}

import java.io.{PrintWriter, StringWriter}

class GetFullConfigRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    val w = new StringWriter()
    Configuration.printConfig(new PrintWriter(w))
    new FullConfigurationResponse(w.toString)
  }
}
