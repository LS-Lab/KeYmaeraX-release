/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, KvpResponse, LocalhostOnlyRequest, ReadRequest, Response}

import scala.collection.immutable.{List, Nil}

class GetToolRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    //@todo more/different tools
    val toolName = Configuration(Configuration.Keys.QE_TOOL)
    ToolProvider.tool(toolName) match {
      case Some(tool) =>
        val initialized = tool.isInitialized
        if (initialized) new KvpResponse("tool", toolName) :: Nil
        else new ErrorResponse(toolName + " is not initialized. Please double-check the configuration paths.") :: Nil
      case _ => new ErrorResponse(toolName + " failed to initialize. Please reselect the desired tool and double-check the configuration paths. Temporarily switched to fallback tools " + ToolProvider.tools().map(_.name).mkString(",")) :: Nil
    }
  }
}
