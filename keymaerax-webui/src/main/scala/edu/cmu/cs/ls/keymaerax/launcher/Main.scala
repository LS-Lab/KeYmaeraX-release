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

      exitIfDeprecated()

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

  /**
   * Kills the current process and shows an error message if the current database is deprecated.
   * @todo
   *   similar behavior for the cache
   */
  private def exitIfDeprecated(): Unit = {
    val dbVersion = SQLite.versionOf(SQLite.ProdDB)
    launcherLog(s"Database version: $dbVersion")

    cleanupGuestData()
    LoadingDialogFactory().addToStatus(25, Some("Checking database version..."))
    if (UpdateChecker.dbUpgradeRequired(dbVersion).getOrElse(false)) {
      // @todo maybe it makes more sense for the JSON file to associate each KeYmaera X version to a list of database and cache versions that work with that version.
      val backupPath = Configuration.path(Configuration.Keys.DB_PATH) + s"-$dbVersion-*"
      launcherLog("Backing up database to " + backupPath)
      val defaultName = new File(Configuration.path(Configuration.Keys.DB_PATH)).getName
      try {
        launcherLog("Upgrading database...")
        val upgradedDbVersion = upgradeDatabase(dbVersion)
        if (UpdateChecker.dbUpgradeRequired(upgradedDbVersion).getOrElse(false)) {
          val message = upgradeFailedMessage(defaultName, backupPath)
          launcherLog(message)
          JOptionPane.showMessageDialog(null, message)
          sys.exit(-1)
        } else {
          launcherLog(
            "Successful database upgrade to version: " + SQLite.ProdDB.getConfiguration("version").config("version")
          )
        }
      } catch {
        case e: Throwable =>
          val message = upgradeFailedMessage(defaultName, backupPath) + "\n\nInternal error details:"
          launcherLog(message)
          e.printStackTrace()
          JOptionPane.showMessageDialog(null, message)
          sys.exit(-1)
      }
    }
  }

  /** Error message printed when the database upgrade fails. */
  private def upgradeFailedMessage(defaultName: String, backupPath: String): String = {
    s"""
       |Your KeYmaera X database is not compatible with this version of KeYmaera X.
       |Automated upgrade failed and changes have been rolled back.
       |Additionally, a backup copy of your current database was placed at
       |$backupPath.
       |To upgrade KeYmaera X, please follow these steps:
       |1. Make a database backup by copying
       |   ~/.keymaerax/$defaultName
       |   and
       |   $backupPath
       |   to a safe place
       |2. Revert to your previous version of KeYmaera X
       |3. Export your models and proofs into an archive file (.kyx) using the Web UI
       |   model list page's "Export all (with proofs)" button and store the file in
       |   a safe place. If you want to export only select models and proofs, use the export
       |   buttons in the model list instead. If necessary, restore the backup database
       |   from $backupPath back to $defaultName before exporting
       |4. Delete the database ~/.keymaerax/$defaultName
       |5. Upgrade and start KeYmaera X. The models and proofs pages will now be empty.
       |6. Import the models and proofs from the .kyx file of step 3, using the Web UI
       |   model list page's upload functionality: "Select file" and then press "Upload"
       |   """.stripMargin
  }

  /** Stores a backup of the database, identifies the backup with `currentVersion` and the current system time. */
  private def backupDatabase(dbVersion: VersionNumber): Unit = {
    val src = new File(SQLite.ProdDB.dblocation)
    val dest = new File(s"${src.getAbsolutePath}-$dbVersion-${System.currentTimeMillis()}")
    new FileOutputStream(dest).getChannel.transferFrom(new FileInputStream(src).getChannel, 0, Long.MaxValue)
  }

  /**
   * Runs the upgrade script located at `scriptResourcePath`. Statements (separated by ;) in the script are run in batch
   * mode.
   */
  private def runUpgradeScript(scriptResourcePath: String): Unit = {
    val script = Source.fromResource(scriptResourcePath)(Codec.UTF8).mkString
    val statements = script.split(";")
    val session = SQLite.ProdDB.sqldb.createSession()
    val conn = session.conn
    conn.setAutoCommit(false)
    try {
      conn.rollback()
      val stmt = conn.createStatement()
      statements.foreach(stmt.addBatch)
      stmt.executeBatch()
      conn.commit()
    } catch { case e: Throwable => conn.rollback(); throw e }
    finally {
      conn.close()
      session.close()
    }
  }

  /** Runs auto-upgrades from the current version, returns the version after upgrade */
  private def upgradeDatabase(dbVersion: VersionNumber): VersionNumber = {
    backupDatabase(dbVersion)

    val upgrades = Source
      .fromResource("/sql/upgradescripts.json")(Codec.UTF8)
      .mkString
      .parseJson
      .asJsObject
      .fields("autoUpgrades")
      .convertTo[List[JsObject]]
      .filter(e => {
        val versionString = e.fields("upgradeFrom").convertTo[String]
        val version = VersionNumber.parse(versionString)
        version == dbVersion
      })

    val scripts = upgrades.flatMap(_.fields("scripts").convertTo[List[JsObject]]).map(_.fields("url").convertTo[String])

    for (script <- scripts) { runUpgradeScript(script) }

    SQLite.versionOf(SQLite.ProdDB)
  }

  /** Returns a list of outdated guest-user created models (literal model content comparison) */
  private def listOutdatedModels(): List[ModelPOJO] = {
    val db = DBAbstractionObj.defaultDatabase
    val tempUsers = db.getTempUsers
    val tempUrlsAndModels: List[(String, List[ModelPOJO])] = tempUsers.map(u => {
      launcherDebug("Updating guest " + u.userName + "...")
      val models = db.getModelList(u.userName)
      launcherDebug("...with " + models.size + " guest models")
      (u.userName, models)
    })

    tempUrlsAndModels.flatMap({ case (url, models) =>
      try {
        if (models.nonEmpty) {
          launcherDebug("Reading guest source " + url)
          val content = DatabasePopulator.readKyx(url)
          launcherDebug("Comparing cached and source content")
          models.flatMap(m =>
            content.find(_.name == m.name) match {
              case Some(DatabasePopulator.TutorialEntry(_, model, _, _, _, _, _)) if model == m.keyFile => None
              case Some(DatabasePopulator.TutorialEntry(_, model, _, _, _, _, _)) if model != m.keyFile => Some(m)
              case _ => /*@note model was deleted/renamed in original file, so delete*/ Some(m)
            }
          )
        } else List()
      } catch {
        case _: Throwable => List() // @note original file inaccessible, so keep temporary model
      }
    })
  }

  /** Deletes all outdated guest models and proofs from the database. */
  private def cleanupGuestData(): Unit = {
    LoadingDialogFactory().addToStatus(10, Some("Guest model updates ..."))
    launcherDebug("Cleaning up guest data...")
    val deleteModels = listOutdatedModels()
    val deleteModelsStatements = deleteModels.map("delete from models where _id = " + _.modelId)
    launcherDebug("...deleting " + deleteModels.size + " guest models")
    if (deleteModels.nonEmpty) {
      val session = SQLite.ProdDB.sqldb.createSession()
      val conn = session.conn
      conn.createStatement().executeUpdate("PRAGMA journal_mode = WAL")
      conn.createStatement().executeUpdate("PRAGMA foreign_keys = ON")
      conn.createStatement().executeUpdate("PRAGMA synchronous = NORMAL")
      conn.createStatement().executeUpdate("VACUUM")
      try {
        val stmt = conn.createStatement()
        deleteModelsStatements.foreach(stmt.addBatch)
        stmt.executeBatch()
      } catch { case e: Throwable => launcherLog("Error cleaning up guest data"); throw e }
      finally {
        conn.close()
        session.close()
      }
    }
    launcherDebug("done.")
  }

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
