/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.hydra.{DBAbstractionObj, DatabasePopulator, ModelPOJO, SQLite}
import org.keymaerax.info.VersionNumber
import org.keymaerax.{Configuration, UpdateChecker}
import spray.json.DefaultJsonProtocol._
import spray.json._

import java.io.{File, FileInputStream, FileOutputStream}
import javax.swing.JOptionPane
import scala.io.{Codec, Source}

object DatabaseChecks {
  private def printlnDebug(msg: String): Unit = {
    if (Configuration.getBoolean(Configuration.Keys.DEBUG).getOrElse(false)) println(msg)
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
       |""".stripMargin
  }

  /**
   * Kills the current process and shows an error message if the current database is deprecated.
   * @todo
   *   similar behavior for the cache
   */
  def exitIfDeprecated(): Unit = {
    val dbVersion = SQLite.versionOf(SQLite.ProdDB)
    println(s"Database version: $dbVersion")

    cleanupGuestData()
    LoadingDialogFactory().addToStatus(25, Some("Checking database version..."))
    if (UpdateChecker.dbUpgradeRequired(dbVersion).getOrElse(false)) {
      // @todo maybe it makes more sense for the JSON file to associate each KeYmaera X version to a list of database and cache versions that work with that version.
      val backupPath = Configuration.path(Configuration.Keys.DB_PATH) + s"-$dbVersion-*"
      println("Backing up database to " + backupPath)
      val defaultName = new File(Configuration.path(Configuration.Keys.DB_PATH)).getName
      try {
        println("Upgrading database...")
        val upgradedDbVersion = upgradeDatabase(dbVersion)
        if (UpdateChecker.dbUpgradeRequired(upgradedDbVersion).getOrElse(false)) {
          val message = upgradeFailedMessage(defaultName, backupPath)
          println(message)
          JOptionPane.showMessageDialog(null, message)
          sys.exit(-1)
        } else {
          println(
            "Successful database upgrade to version: " + SQLite.ProdDB.getConfiguration("version").config("version")
          )
        }
      } catch {
        case e: Throwable =>
          val message = upgradeFailedMessage(defaultName, backupPath) + "\n\nInternal error details:"
          println(message)
          e.printStackTrace()
          JOptionPane.showMessageDialog(null, message)
          sys.exit(-1)
      }
    }
  }

  /** Deletes all outdated guest models and proofs from the database. */
  private def cleanupGuestData(): Unit = {
    LoadingDialogFactory().addToStatus(10, Some("Guest model updates ..."))
    printlnDebug("Cleaning up guest data...")
    val deleteModels = listOutdatedModels()
    val deleteModelsStatements = deleteModels.map("delete from models where _id = " + _.modelId)
    printlnDebug("...deleting " + deleteModels.size + " guest models")
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
      } catch { case e: Throwable => println("Error cleaning up guest data"); throw e }
      finally {
        conn.close()
        session.close()
      }
    }
    printlnDebug("done.")
  }

  /** Returns a list of outdated guest-user created models (literal model content comparison) */
  private def listOutdatedModels(): List[ModelPOJO] = {
    val db = DBAbstractionObj.defaultDatabase
    val tempUsers = db.getTempUsers
    val tempUrlsAndModels: List[(String, List[ModelPOJO])] = tempUsers.map(u => {
      printlnDebug("Updating guest " + u.userName + "...")
      val models = db.getModelList(u.userName)
      printlnDebug("...with " + models.size + " guest models")
      (u.userName, models)
    })

    tempUrlsAndModels.flatMap({ case (url, models) =>
      try {
        if (models.nonEmpty) {
          printlnDebug("Reading guest source " + url)
          val content = DatabasePopulator.readKyx(url)
          printlnDebug("Comparing cached and source content")
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
}
