/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.{ToolConfigErrorResponse, ToolConfigStatusResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Request, Response}

import scala.collection.immutable.{List, Nil}

class WolframEngineConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool("wolframEngine") match {
      case Some(_) =>
        new ToolConfigStatusResponse(
          "wolframengine",
          Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) &&
            Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP),
        ) :: Nil
      case None =>
        new ToolConfigErrorResponse(
          "wolframengine",
          "Wolfram Engine could not be started; please double-check the configured paths and make sure you are online for license checking. Temporarily using " +
            ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.",
        ) :: Nil
    }

  }
}
