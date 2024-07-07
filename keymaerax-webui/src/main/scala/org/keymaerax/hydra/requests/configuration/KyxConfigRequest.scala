/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.hydra.responses.configuration.KyxConfigResponse
import org.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import org.keymaerax.info.{Os, Version}

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
