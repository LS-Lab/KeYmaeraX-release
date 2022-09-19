/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.{ToolConfigErrorResponse, ToolConfigStatusResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Request, Response}

import scala.collection.immutable.{List, Nil}

class MathematicaConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool("mathematica") match {
      case Some(_) =>
        new ToolConfigStatusResponse("mathematica",
          Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
            Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) &&
            ToolProvider.tool("mathematica").isDefined) :: Nil
      case None => new ToolConfigErrorResponse("mathematica", "Mathematica could not be started; please double-check the configured paths and make sure you have a valid license (if you use a license server, make sure it is reachable). Temporarily using " + ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.") :: Nil
    }
  }
}
