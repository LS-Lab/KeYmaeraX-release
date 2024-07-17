/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.info.FullName

import scala.sys.process.Process

object Relauncher {
  private val ExtraJvmArgs = Seq("-Xss20M")

  private case class LaunchCommand(jvmCmd: String, jvmArgs: Seq[String], cliArgs: Seq[String])

  private def getLaunchCommand(cliArgs: Seq[String]): Option[LaunchCommand] = {
    import scala.jdk.OptionConverters._

    val info = ProcessHandle.current().info()
    val jvmCmd = info.command().toScala.getOrElse(return None)
    val allArgs = info.arguments().toScala.getOrElse(return None)
    val jvmArgs = if (allArgs.endsWith(cliArgs)) allArgs.dropRight(cliArgs.length) else return None

    Some(LaunchCommand(jvmCmd = jvmCmd, jvmArgs = jvmArgs.toSeq, cliArgs = cliArgs))
  }

  /**
   * Try to the current JVM process with more stack space, but otherwise identical arguments.
   *
   * @param cliArgs
   *   The arguments that were passed to the main function.
   */
  def relaunchOrExit(cliArgs: Seq[String]): Nothing = {
    println(s"Restarting $FullName with sufficient stack space.")

    val launchCmd = getLaunchCommand(cliArgs).getOrElse {
      println(s"Failed to restart $FullName because the launch arguments could not be determined.")
      println(s"Try starting $FullName with ${ExtraJvmArgs.mkString(" ")} and ${Options.LaunchFlag}.")
      sys.exit(1)
    }

    val relaunchCmd = launchCmd.jvmCmd
    val relaunchArgs = ExtraJvmArgs ++ launchCmd.jvmArgs ++ launchCmd.cliArgs :+ Options.LaunchFlag
    val exitValue = Process(relaunchCmd, relaunchArgs).run(connectInput = true).exitValue()
    sys.exit(exitValue)
  }
}
