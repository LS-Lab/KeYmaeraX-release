/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.Z3ConfigurationResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.tools.install.Z3Installer

import scala.collection.immutable.{List, Nil}

class GetZ3ConfigurationRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    new Z3ConfigurationResponse(Z3Installer.z3Path) :: Nil
  }
}
