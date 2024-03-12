/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.hydra.{
  BooleanResponse,
  HyDRAServerConfig,
  LocalhostOnlyRequest,
  RegisteredOnlyRequest,
  Response,
}

import scala.collection.immutable.{List, Nil}

class ShutdownRequest() extends LocalhostOnlyRequest with RegisteredOnlyRequest {
  override def resultingResponses(): List[Response] = {
    new Thread() {
      override def run(): Unit = {
        try {
          // Tell all scheduled tactics to stop.
          // @todo figure out which of these are actually necessary.
          System.out.flush()
          System.err.flush()
          ToolProvider.shutdown()
          System.out.flush()
          System.err.flush()
          HyDRAServerConfig.system.terminate()
          System.out.flush()
          System.err.flush()
          this.synchronized { this.wait(4000) }
          System.out.flush()
          System.err.flush()
          System.exit(0) // should've already stopped the application by now.
        } catch { case _: Exception => System.exit(-1) }

      }
    }.start()

    BooleanResponse(flag = true) :: Nil
  }
}
