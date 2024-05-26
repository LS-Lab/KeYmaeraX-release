/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.KyxConfigResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}
import edu.cmu.cs.ls.keymaerax.info.{ArchType, Os, Version}

import scala.collection.immutable.{List, Nil}

class KyxConfigRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val javaVersion = System.getProperty("java.runtime.version")
    val javaBits = Os.JvmArchType match {
      case ArchType.Bit32 => "32"
      case ArchType.Bit64 => "64"
      case ArchType.Unknown => "unknown"
    }
    val linkName = Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME)
    val jlinkLibDir = Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)

    val kyxConfig = s"""KeYmaera X version: $Version
                       |Java version: $javaVersion with $javaBits bits
                       |OS: ${Os.Name} ${Os.Version}
                       |LinkName: $linkName
                       |jlinkLibDir: $jlinkLibDir
                       |""".stripMargin

    new KyxConfigResponse(kyxConfig) :: Nil
  }
}
