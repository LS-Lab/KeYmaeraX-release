/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.cli.{Command, Options}
import edu.cmu.cs.ls.keymaerax.core.Ensures
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.info.{TechnicalName, Version, VersionNumber}
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration, UpdateChecker}
import spray.json.DefaultJsonProtocol._
import spray.json._

import java.io._
import javax.swing.JOptionPane
import scala.io.{Codec, Source}

/**
 * Prelauncher that restarts a big-stack JVM and then starts [[edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX]], the
 * aXiomatic Tactical Theorem Prover for Hybrid Systems and Hybrid Games.
 *
 * @todo
 *   move functionality directly into KeYmaeraX.scala?
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 * @since 4/17/15
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX]]
 */
object Main {
  def main(args: Array[String]): Unit = {
    val options = Options.parseArgs(s"$TechnicalName-webui", args)
    if (!options.launch) { Relauncher.relaunchOrExit(args) }

    Configuration.setConfiguration(FileConfiguration)

    if (options.command.getOrElse(Command.Ui) == Command.Ui) {
      edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.initializeConfig(options);
      // Initialize the loading dialog splash screen.
      LoadingDialogFactory()
      DatabaseChecks.exitIfDeprecated()

      LoadingDialogFactory().addToStatus(15, Some("Checking lemma caches..."))
      LemmaCacheChecks.clearCacheIfDeprecated()

      assert(options.launch)
      startServer(options)
      // @todo use command line arguments as the file to load. And preferably a second argument as the tactic file to run.
    } else { KeYmaeraX.main(args) }
  }

  def startServer(options: Options): Unit = {
    LoadingDialogFactory().addToStatus(10, Some("Obtaining locks..."))
    GlobalLaunchChecks.acquireGlobalLockFileOrExit()
    GlobalLaunchChecks.ensureWebuiPortCanBeBoundOrExit()

    launcherDebug(Options.LaunchFlag + " -- starting KeYmaera X Web UI server HyDRA.")
    edu.cmu.cs.ls.keymaerax.hydra.NonSSLBoot.run(options)
  }

  /** Print debug message `s`. */
  def launcherDebug(s: String): Unit = if (Configuration.getString(Configuration.Keys.DEBUG).contains("true")) {
    val prefix = "[launcherDebug] "
    println(prefix + s)
  }
}
