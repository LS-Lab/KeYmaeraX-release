/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core.VERSION
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.KyxConfigResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, ReadRequest, Response}

import scala.collection.immutable.{List, Nil}

class KyxConfigRequest extends LocalhostOnlyRequest with ReadRequest {
  val newline = "\n"
  override def resultingResponses(): List[Response] = {
    val kyxConfig =
      ("KeYmaera X version: " + VERSION + newline) +
        ("Java version: " + System.getProperty("java.runtime.version") + " with " +
          System.getProperty("sun.arch.data.model") + " bits" + newline) +
        ("OS: " + System.getProperty("os.name") + " " + System.getProperty("os.version") + newline) +
        ("LinkName: " + Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME) + newline) +
        ("jlinkLibDir: " + Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR))
    new KyxConfigResponse(kyxConfig) :: Nil
  }
}
