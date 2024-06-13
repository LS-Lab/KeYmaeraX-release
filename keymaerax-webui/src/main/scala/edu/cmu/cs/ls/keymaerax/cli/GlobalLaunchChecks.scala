/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.info.FullName

import java.io.IOException
import java.net.ServerSocket
import java.nio.file.{FileAlreadyExistsException, Files, Paths}
import javax.swing.JOptionPane
import scala.sys.ShutdownHookThread

object GlobalLaunchChecks {

  /**
   * Try to atomically acquire a global lock file, notifying the user and exiting on failure. Uses both CLI and GUI
   * messages to notify the user so they see the message regardless of how they launched the jar.
   *
   * Running two instances of KeYmaera X concurrently can result in weird behavior, including during initialization.
   * Thus, this function must be called very early during any KeYmaera X startup sequence.
   */
  def acquireGlobalLockFileOrExit(): Unit = {
    val path = Paths.get(Configuration.KEYMAERAX_HOME_PATH).resolve("lockfile")

    try {
      Files.createDirectories(path.getParent)
      // Checking for the file's existence and creating it is a single atomic operation.
      val acquiredPath = Files.createFile(path)
      ShutdownHookThread { Files.delete(acquiredPath) }
    } catch {
      case _: FileAlreadyExistsException =>
        val msg = s"""There is already an instance of $FullName running on this machine.
                     |Multiple instances of $FullName can't run concurrently.
                     |
                     |If you are certain that no instances of $FullName are currently running,
                     |manually delete the lock file at the following path, then try again:
                     |$path
                     |""".stripMargin.stripLineEnd
        println(msg)
        JOptionPane.showMessageDialog(null, msg)
        sys.exit(1)
      case e: Throwable =>
        val msg = s"""$FullName failed to create its lock file: $e
                     |Please ensure $FullName has permissions to read from and write to the following path:
                     |$path
                     |""".stripMargin.stripLineEnd
        println(msg)
        JOptionPane.showMessageDialog(null, msg)
        sys.exit(1)
    }
  }

  /**
   * Check if KeYmaera X can bind to the port that the webui will later bind to. If it can't, notify the user and exit
   * (similar to [[acquireGlobalLockFileOrExit]]).
   *
   * Due to possible race conditions, this check alone is not enough and must always be combined with
   * [[acquireGlobalLockFileOrExit]]. It should be called after [[acquireGlobalLockFileOrExit]] so the error messages
   * make more sense to the user.
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
