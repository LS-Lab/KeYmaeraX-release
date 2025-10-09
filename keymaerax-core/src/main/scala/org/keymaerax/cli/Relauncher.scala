/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.Logging
import org.keymaerax.info.FullName

import java.lang.management.ManagementFactory
import java.nio.file.Path
import scala.sys.process.Process
import scala.util.boundary

object Relauncher extends Logging {
  private val ExtraJvmArgs = Seq("-Xss20M")

  private case class LaunchCommand(jvmCmd: String, allArgs: Seq[String])

  private def getLaunchCommand(cliArgs: Seq[String]): Option[LaunchCommand] = boundary {
    import scala.jdk.CollectionConverters.*
    import scala.jdk.OptionConverters.*

    val info = ProcessHandle.current().info()
    val jvmCmd = info.command().toScala.getOrElse(boundary.break(None))

    val allArgs = info
      .arguments()
      .toScala
      .map(_.toSeq)
      .getOrElse {
        // We're probably on Windows: https://bugs.openjdk.org/browse/JDK-8176725
        // Let's try piecing together our arguments from multiple sources.
        // https://stackoverflow.com/a/2541745
        // https://stackoverflow.com/a/320595 (though there's no need to round-trip through File)
        val jvmArgs = ManagementFactory.getRuntimeMXBean.getInputArguments.asScala.toSeq
        val jarPath = Path.of(this.getClass.getProtectionDomain.getCodeSource.getLocation.toURI).toString
        jvmArgs ++ Seq("-jar", jarPath) ++ cliArgs
      }

    Some(LaunchCommand(jvmCmd = jvmCmd, allArgs = allArgs))
  }

  /**
   * Try to the current JVM process with more stack space, but otherwise identical arguments.
   *
   * @param cliArgs The arguments that were passed to the main function.
   */
  def relaunchOrExit(cliArgs: Seq[String]): Nothing = {
    logger.info(s"Restarting $FullName with sufficient stack space.")

    val launchCmd = getLaunchCommand(cliArgs).getOrElse {
      logger.error(s"Failed to restart $FullName because the launch arguments could not be determined.")
      logger.error(s"Try starting $FullName with ${ExtraJvmArgs.mkString(" ")} and ${Options.LaunchFlag}.")
      sys.exit(1)
    }

    val relaunchCmd = launchCmd.jvmCmd
    val relaunchArgs = ExtraJvmArgs ++ launchCmd.allArgs :+ Options.LaunchFlag
    val exitValue = Process(relaunchCmd, relaunchArgs).run(connectInput = true).exitValue()
    sys.exit(exitValue)
  }
}
