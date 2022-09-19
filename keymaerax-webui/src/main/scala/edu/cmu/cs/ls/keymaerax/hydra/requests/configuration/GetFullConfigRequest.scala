/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.FullConfigurationResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}

import java.io.{PrintWriter, StringWriter}
import scala.collection.immutable.{List, Nil}

class GetFullConfigRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val w = new StringWriter()
    Configuration.printConfig(new PrintWriter(w))
    new FullConfigurationResponse(w.toString) :: Nil
  }
}
