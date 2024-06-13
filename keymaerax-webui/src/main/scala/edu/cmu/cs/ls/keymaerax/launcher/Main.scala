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
      clearCacheIfDeprecated()

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

  /** Clears the cache if the cache was created by a previous version of KeYmaera X */
  private def clearCacheIfDeprecated(): Unit = {
    val cacheLocation = Configuration.path(Configuration.Keys.LEMMA_CACHE_PATH)
    val cacheDirectory = new File(cacheLocation)
    val cacheVersionFile = new File(cacheLocation + File.separator + "VERSION")

    if (!cacheDirectory.exists()) {
      if (!cacheDirectory.mkdirs()) {
        throw new Exception(
          s"Could not create the directory ${cacheDirectory.getAbsolutePath}. Please check your file system permissions."
        )
      }
    }

    if (!cacheVersionFile.exists()) {
      if (!cacheVersionFile.createNewFile()) throw new Exception(
        s"Could not create the file ${cacheVersionFile.getAbsolutePath}. Please check your file system permissions."
      )
      clearCache(new File(cacheLocation))
    } else {
      val source = scala.io.Source.fromFile(cacheVersionFile)
      val cacheVersion = source.mkString.replace("\n", "")
      source.reader().close() // Ensure that the associated reader is closed so that we can delete the file if need to.
      try {
        if (VersionNumber.parse(cacheVersion) != Version) {
          assert(
            cacheVersionFile.delete(),
            s"Could not delete the cache version file in ${cacheVersionFile.getAbsolutePath}",
          )
          clearCache(cacheDirectory)
        }
      } catch {
        case _: NumberFormatException =>
          println("WARNING: Could not parse the cache version file, cache contained: " + cacheVersion)
          cacheVersionFile.delete()
          clearCache(cacheDirectory)
      }
    }
  }

  /** Clears the cache and creates a new cache/VERSION file */
  private def clearCache(dir: File): Unit = {
    println("Clearing your cache because of an update.")
    if (dir.exists()) {
      if (!deleteDirectory(dir)) throw new Exception(s"Could not delete cache directory ${dir.getAbsolutePath}")
    }
    assert(!dir.exists(), s"Cache directory ${dir.getAbsolutePath} should not exist after being deleted.")
    if (!dir.mkdirs()) throw new Exception(
      s"Could not reinitialize cache because cache directory ${dir.getAbsolutePath} could not be created."
    )

    val versionFile = new File(dir.getAbsolutePath + File.separator + "VERSION")
    if (!versionFile.exists()) {
      if (!versionFile.createNewFile()) throw new Exception(s"Could not create ${versionFile.getAbsolutePath}")
    }
    assert(versionFile.exists())
    val fw = new FileWriter(versionFile)
    fw.write(Version.toString)
    fw.flush()
    fw.close()
  }

  /** Deletes the directory or file (recursively). Corresponds to rm -r */
  private def deleteDirectory(f: File): Boolean = {
    if (!f.isDirectory) {
      if (!f.delete()) {
        launcherLog(s"WARNING: could not delete ${f.getAbsolutePath}")
        false
      } else true
    } else if (f.list().isEmpty) {
      val result = f.delete()
      assert(result, s"Could not delete file ${f.getName} in: ${f.getAbsolutePath}")
      result
    } else {
      val recSuccess = f.listFiles().forall(deleteDirectory)
      if (recSuccess) f.delete() else false
    }
  } ensures (r => !r || !f.exists())

  /** Print message `s`. */
  def launcherLog(s: String, isError: Boolean = false): Unit = {
    val prefix = if (isError) "[launcher][ERROR] " else "[launcher] "
    println(prefix + s)
  }

  /** Print debug message `s`. */
  def launcherDebug(s: String): Unit = if (Configuration.getString(Configuration.Keys.DEBUG).contains("true")) {
    val prefix = "[launcherDebug] "
    println(prefix + s)
  }
}
