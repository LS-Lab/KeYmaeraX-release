/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.{ToolProvider, Z3ToolProvider}
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.ConfigureZ3Response
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, Response, WriteRequest}
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

class ConfigureZ3Request(z3Path: String) extends LocalhostOnlyRequest with WriteRequest {
  private def isZ3PathCorrect(z3Path: java.io.File): Boolean = z3Path.getName == "z3" || z3Path.getName == "z3.exe"

  override def resultingResponse(): Response = {
    // check to make sure the indicated files exist and point to the correct files.
    val z3File = new java.io.File(z3Path)
    val z3Exists = isZ3PathCorrect(z3File)

    if (!z3Exists) { new ConfigureZ3Response("", false) }
    else {
      ToolProvider.shutdown()
      Configuration.set(Configuration.Keys.QE_TOOL, "z3")
      Configuration.set(Configuration.Keys.Z3_PATH, z3Path)
      ToolProvider.setProvider(Z3ToolProvider(ToolConfiguration(z3Path = Some(z3Path))))
      new ConfigureZ3Response(z3File.getAbsolutePath, true)
    }
  }
}
