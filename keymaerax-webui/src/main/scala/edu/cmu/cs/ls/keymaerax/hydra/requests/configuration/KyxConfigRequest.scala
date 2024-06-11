/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.KyxConfigResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.info.{Os, Version}

class KyxConfigRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponse(): Response = {
    val javaVersion = System.getProperty("java.runtime.version")
    val linkName = Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME)
    val jlinkLibDir = Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)

    val kyxConfig = s"""KeYmaera X version: $Version
                       |Java version: $javaVersion
                       |OS: ${Os.Name} ${Os.Version}
                       |LinkName: $linkName
                       |jlinkLibDir: $jlinkLibDir
                       |""".stripMargin

    new KyxConfigResponse(kyxConfig)
  }
}
