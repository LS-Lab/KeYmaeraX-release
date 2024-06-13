/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.info.FullName

import java.nio.file.{FileAlreadyExistsException, Files, Paths}
import javax.swing.JOptionPane
import scala.sys.ShutdownHookThread

object GlobalLockChecks {

  /**
   * Try to atomically acquire a global lock file, notifying the user and exiting on failure. Uses both CLI and GUI
   * messages to notify the user so they see the message regardless of how they launched the jar.
   *
   * Running two instances of KeYmaera X concurrently can result in weird behavior, including during initialization.
   * Thus, this function must be called very early during any KeYmaera X startup sequence.
   */
  def acquireGlobalLockFileOrExit(graphical: Boolean = false): Unit = {
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
        if (graphical) JOptionPane.showMessageDialog(null, msg)
        sys.exit(1)
      case e: Throwable =>
        val msg = s"""$FullName failed to create its lock file: $e
                     |Please ensure $FullName has permissions to read from and write to the following path:
                     |$path
                     |""".stripMargin.stripLineEnd
        println(msg)
        if (graphical) JOptionPane.showMessageDialog(null, msg)
        sys.exit(1)
    }
  }
}
