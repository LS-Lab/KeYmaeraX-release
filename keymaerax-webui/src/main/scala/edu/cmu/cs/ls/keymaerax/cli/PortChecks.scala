/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.info.FullName

import java.io.IOException
import java.net.ServerSocket
import javax.swing.JOptionPane

object PortChecks {

  /**
   * Check if KeYmaera X can bind to the port that the webui will later bind to. If it can't, notify the user and exit
   * (similar to [[GlobalLockChecks.acquireGlobalLockFileOrExit]]).
   *
   * Due to possible race conditions, this check alone is not enough and must always be combined with
   * [[GlobalLockChecks.acquireGlobalLockFileOrExit]]. It should be called after
   * [[GlobalLockChecks.acquireGlobalLockFileOrExit]] so the error messages make more sense to the user.
   */
  def ensureWebuiPortCanBeBoundOrExit(): Unit = {
    val port = Integer.parseInt(Configuration(Configuration.Keys.PORT))

    try { new ServerSocket(port).close() }
    catch {
      case e: IOException =>
        val msg = s"""$FullName can't bind to port $port: $e
                     |Please ensure no other program is currently bound to the port, then try again.
                     |""".stripMargin.stripLineEnd
        println(msg)
        JOptionPane.showMessageDialog(null, msg)
        sys.exit(1)
    }
  }
}
