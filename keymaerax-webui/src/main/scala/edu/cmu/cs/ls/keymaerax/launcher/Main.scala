/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.cli.Command
import edu.cmu.cs.ls.keymaerax.core.{assertion, Ensures}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.info.{Version, VersionNumber}
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
 * Usage:
 * {{{
 *  java -jar keymaerax.jar
 *  java -Xss20M -jar keymaerax.jar -launch
 * }}}
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

  /** This flag is set to true iff this process does nothing but re-launch */
  var IS_RELAUNCH_PROCESS = false

  // @todo set via -log command line option
  private val logFile = false

  /** Command line flag to launch the prover in this JVM (if not set, spawns another JVM). */
  private val LAUNCH_FLAG = "-launch"

  /** Command line flags to display help. */
  private val HELP_FLAGS = List("-help", "--help", "-h", "-?")

  def main(args: Array[String]): Unit = {
    // prelaunch help without launching an extra JVM
    Configuration.setConfiguration(FileConfiguration)
    if (args.length > 0 && HELP_FLAGS.contains(args(0))) {
      println(s"KeYmaera X Prover $Version")
      println(KeYmaeraX.help)
      sys.exit(1)
    }

    // isFirstLaunch indicates that an extra big-stack JVM still has to be launched
    val isFirstLaunch = !args.contains(LAUNCH_FLAG)

    if (isFirstLaunch) {
      IS_RELAUNCH_PROCESS = true
      val java: String = javaLocation
      val keymaeraxjar: String = jarLocation

      val javaVersionCompatibility = javaVersion
      if (javaVersionCompatibility._1.contains(false)) {
        exitWith(
          "KeYmaera X requires at least Java Virtual Machine version 1.8.0_111. It was started with " +
            javaVersionCompatibility._2 + ". Please install compatible Java and restart KeYmaera X."
        )
      } else {
        if (javaVersionCompatibility._1.isEmpty) {
          println("WARNING: Unexpected Java Version not known to be compatible: " + javaVersionCompatibility._2)
        }
        var assertsEnabled = false
        assertion({
          assertsEnabled = true; assertsEnabled
        }) // intentional lazy side-effect of setting assertsEnabled to true if -ea
        // now assertsEnabled is set to the correct value (true if -ea, false if -da)
        val cmd =
          (java :: "-Xss20M" :: (if (assertsEnabled) "-ea" else "-da") :: "-jar" :: keymaeraxjar :: LAUNCH_FLAG ::
            Nil) ++ args ++
            (if (args.map(_.stripPrefix("-")).intersect(Command.FlagNames).isEmpty) Command.UiFlag :: Nil else Nil)
        launcherLog("Restarting KeYmaera X with sufficient stack space\n" + cmd.mkString(" "))
        runCmd(cmd)
      }
    } else if (args.contains(Command.UiFlag)) {
      // Initialize the loading dialog splash screen.
      LoadingDialogFactory()

      exitIfDeprecated()

      LoadingDialogFactory().addToStatus(15, Some("Checking lemma caches..."))
      clearCacheIfDeprecated()

      assert(args.contains(LAUNCH_FLAG))
      startServer(args.filter(_ != LAUNCH_FLAG))
      // @todo use command line arguments as the file to load. And preferably a second argument as the tactic file to run.
    } else { KeYmaeraX.main(args) }
  }

  def startServer(args: Array[String]): Unit = {
    LoadingDialogFactory().addToStatus(10, Some("Obtaining locks..."))
    KeYmaeraXLock.obtainLockOrExit()

    launcherDebug(LAUNCH_FLAG + " -- starting KeYmaera X Web UI server HyDRA.")
    edu.cmu.cs.ls.keymaerax.hydra.NonSSLBoot.run(args)
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

  /** Indicates whether the process `proc` is alive, similar to [[Process]] but catching all exceptions. */
  def processIsAlive(proc: Process): Boolean = {
    try {
      proc.exitValue()
      false
    } catch { case _: Exception => true }
  }

  /** Runs the command `cmd` in a new process. */
  private def runCmd(cmd: List[String]): Unit = {
    launcherDebug("Running command:\n" + cmd.mkString(" "))

    val pb = new ProcessBuilder(cmd: _*)
    var pollOnStd = false
    try {
      if (logFile) {
        // @todo not sure if it's really helpful to have separate error and output log. pb.redirectErrorStream(true)
        val errorLog = File.createTempFile("keymaerax-error-stream", ".txt")
        val outputLog = File.createTempFile("keymaerax-output-stream", ".txt")
        pb.redirectError(errorLog)
        System.err.println("Errors will be logged at " + errorLog.getPath)
        pb.redirectOutput(outputLog)
        System.err.println("Outputs will be logged at " + outputLog.getPath)
      } else {
        // @todo dump to console AND to logfile would be best
        pb.inheritIO()
      }
    } catch {
      // @note JDK<1.7
      case _: NoSuchMethodError => pollOnStd = true
    }
    val proc = pb.start()

    Runtime
      .getRuntime
      .addShutdownHook(new Thread() {
        override def run(): Unit = {
          if (!IS_RELAUNCH_PROCESS) KeYmaeraXLock.deleteLock()
          proc.destroy()
        }
      })

    if (pollOnStd) {
      val errReaderThread = new Thread() {
        override def run(): Unit = {
          try {
            val errReader = new BufferedReader(new InputStreamReader(proc.getErrorStream))
            while (processIsAlive(proc)) {
              val errLine = errReader.readLine()
              if (errLine != null) System.err.println(errLine)
            }
            errReader.close()
          } catch {
            case _: EOFException => System.err.println("Done with log output")
            case exc: IOException => System.err.println("Done with log output: " + exc)
          }
        }
      }
      val stdReaderThread = new Thread() {
        override def run(): Unit = {
          try {
            val reader = new BufferedReader(new InputStreamReader(proc.getInputStream))
            while (processIsAlive(proc)) {
              val line = reader.readLine()
              if (line != null) System.out.println(line)
            }
            reader.close()
          } catch {
            case _: EOFException => System.err.println("Done with log output")
            case exc: IOException => System.err.println("Done with log input: " + exc)
          }
        }
      }

      stdReaderThread.start()
      errReaderThread.start()
    }

    sys.exit(proc.waitFor())
  }

  /** Gracefully exit with an error message displayed to the user. */
  private def exitWith(err: String): Nothing = {
    val message =
      "ERROR in loader :: See http://keymaeraX.org/startup.html for trouble-shooting assistance (Message: " + err + ")"
    launcherLog(message)
    try { if (!java.awt.GraphicsEnvironment.isHeadless) { JOptionPane.showMessageDialog(null, message) } }
    catch {
      case _: java.awt.HeadlessException =>
      case _: java.lang.ClassNotFoundException =>
      case _: java.lang.NoSuchMethodError =>
      case _: Exception =>
    }
    sys.exit(-3)
  }

  /** The location of the Java Virtual Machine interpreter `java`. */
  lazy val javaLocation: String = {
    val javaHome = System.getProperty("java.home") + "/bin"
    val matchingFiles = new java.io.File(javaHome).listFiles(new FileFilter {
      override def accept(pathname: File): Boolean = pathname.canExecute &&
        (pathname.getName.equals("java") || pathname.getName.equals("java.exe"))
    })

    if (matchingFiles.length == 1) { matchingFiles.head.getAbsolutePath }
    else { exitWith("Could not find a Java executable in " + javaHome) }
  }

  /**
   * Assumes that the JAR was run from its containing directory (e.g., as happens when double-clicking). If this
   * assumption is violated, the launcher will fail.
   * @return
   *   The location of the .JAR file that's currently running.
   */
  lazy val jarLocation: String = {
    new File(Main.getClass.getProtectionDomain.getCodeSource.getLocation.toURI.getPath).toString
  }

  /**
   * Identify whether the running Java Version is compatible with KeYmaera X.
   * @return
   *   \- Some(true) if compatible, along with the version string
   *   - Some(false) if not compatible, along with the version string
   *   - None if compatibility unknown, along with the best guess of a version string
   */
  private def javaVersion: (Option[Boolean], String) = {
    val javaVersion: String =
      try { System.getProperty("java.version") }
      catch {
        case e: IllegalArgumentException =>
          println("Java does not reveal its version: " + e); return (None, "<unknown>")
        case e: NullPointerException => println("Java does not reveal its version: " + e); return (None, "<unknown>")
        case e: SecurityException =>
          println("Java does not reveal its version because a SecurityManager interfered: " + e);
          return (None, "<unknown>")
      }
    try {
      val javaMajorMinor :: legacyUpdateVersion :: Nil =
        if (javaVersion.contains("_")) javaVersion.split("_").toList else javaVersion :: "-1" :: Nil
      val _ :: javaMajor :: javaMinor :: updateVersion :: Nil = {
        val majorMinor: List[String] = javaMajorMinor.split("\\.").toList
        if (majorMinor.length == 1) "1" +: majorMinor :+ "0" :+ legacyUpdateVersion
        else if (majorMinor.length == 2) majorMinor :+ "0" :+ legacyUpdateVersion
        else if (Integer.parseInt(majorMinor.head) >= 9) "1" +:
          majorMinor // @note Java 9 onwards are of the shape 9.0.2
        else majorMinor.take(3) :+ legacyUpdateVersion
      }
      if (
        Integer.parseInt(javaMajor) < 8 ||
        (Integer.parseInt(javaMajor) == 8 && Integer.parseInt(javaMinor) == 0 && Integer.parseInt(updateVersion) < 111)
      ) { (Some(false), javaVersion) }
      else { (Some(true), javaVersion) }
    } catch {
      case _: MatchError => (None, javaVersion)
      case _: NumberFormatException => (None, javaVersion)
    }
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

  /**
   * A robust locking mechanism for ensures that there's only ever one instance of KeYmaera X running. Also displays GUI
   * messages when the lock cannot be obtained so that confused users don't have to wonder why KeYmaera X won't start.
   *
   * @todo
   *   decide if java.nio lock files are a better solution. Definitely keep port-based stale checking, though
   * @author
   *   Nathan Fulton
   */
  private object KeYmaeraXLock {

    /** Set to true when a lock is obtained. Determines if the lock file is deleted on shutdown. */
    private var lockObtained = false

    /**
     * Obtains a lock if the lock file does not exist and the desired port is not bound. Otherwise, shows a relevant
     * error message on GUI and STDOUT then exits with error code.
     */
    def obtainLockOrExit(): Unit = {
      require(!lockObtained, "ERROR: obtainLockOrExit was run more than once!")

      val bound = portIsBound()

      if (lockFile.exists() && bound) {
        val msg =
          "ERROR: There is already an instance of KeYmaera X running on this machine. Open your browser to http://127.0.0.1:8090"
        launcherLog(msg)
        JOptionPane.showMessageDialog(null, msg)
        SystemWebBrowser(s"http://127.0.0.1:${keymaeraxPort()}/")
        lockObtained = false
        sys.exit(-1)
      } else if (lockFile.exists() && !bound) {
        if (!lockIsNewborn) {
          // lock file exists, but there's no new instance of KeYmaera X and the port isn't bound. Proceed, but show message to the user just in case.
          val msg =
            "WARNING: A lock file exists but nothing is bound to the KeYmaera X web server's port.\nDeleting the lock file and starting KeYmaera X. If you experience errors, try killing all\ninstances of KeYmaera X from your system's task manager."
          forceDeleteLock()
          launcherLog(msg)
          if (!java.awt.GraphicsEnvironment.isHeadless) JOptionPane.showMessageDialog(null, msg)
        } else {
          // lock file exists but port isn't bound, so another instance of KeYmaera X probably *just* started. Don't even bother with a GUI message -- the user probably double-launched on accident.
          launcherLog(
            s"ERROR: Another instance of KeYmaera X just obtained a lock.\nIf the problem persists, kill all running versions of KeYmaera X and delete the following file if it exists:\n  ${lockFile.getAbsolutePath}"
          )
          lockObtained = false
          SystemWebBrowser(s"http://127.0.0.1:${keymaeraxPort()}/")
          sys.exit(-1)
        }
      } else if (!lockFile.exists() && bound) {
        val msg =
          s"WARNING: The KeYmaera X lock file does not exist.\nHowever, some service is running on the KeYmaera X port (${keymaeraxPort()}).\nPerhaps you're running another service on this port?\nExiting."
        launcherLog(msg)
        JOptionPane.showMessageDialog(null, msg)
        lockObtained = false
        SystemWebBrowser(s"http://127.0.0.1:${keymaeraxPort()}/")
        sys.exit(-1)
      }

      // This file is later destroyed in the shutdown hook.
      launcherDebug("Obtaining lock.")
      obtainLock()
    } ensures (_ => lockObtained && lockFile.exists())

    /** Obtains a KeYmaera X startup lock by creating a lock file that is automatically deleted on exit. */
    def obtainLock(): Unit = {
      require(!lockFile.exists(), "Cannot obtain a lock if the lock file exists.")
      lockObtained = true
      assert(
        lockFile.createNewFile(),
        "could not obtain lock file even though we just checked that the file does not exist.",
      )
      lockFile.deleteOnExit()
    } ensures (_ => lockObtained && lockFile.exists())

    /** Deletes the lock file regardless of whether this is the process that created the lock file. */
    private def forceDeleteLock(): Boolean = { lockFile.delete() } ensures (!lockFile.exists())

    /**
     * Deletes the lock file ONLY IF this process obtained the lock (i.e., lockObtained = true).
     * @note
     *   not strictly necessary as lont as File.deleteOnExit works properly.
     */
    def deleteLock(): Unit = {
      if (lockObtained) lockFile.delete()
      else launcherLog("refusing to delete lock because this process's most recent attempt to obtain a lock failed.")
    }

    /** Returns true iff the lock file is less than 30s old. */
    private def lockIsNewborn: Boolean = {
      val current = System.currentTimeMillis()
      val lastModified = lockFile.lastModified()
      val threshold = 30000

      current - lastModified < threshold
    }

    /**
     * Location of the KeYmaera X lock file. Choose a non-. file so that students can find it easily if they need to
     * delete it.
     */
    private def lockFile: java.io.File =
      new java.io.File(Configuration.KEYMAERAX_HOME_PATH + File.separator + "lockfile")

    /** Returns the assigned port from the database, or the default port if the database or config key DNE. */
    private def keymaeraxPort(): String = Configuration(Configuration.Keys.PORT)

    /**
     * Returns true iff the port is bound.
     * @note
     *   The port is a canary for determining whether there's an instance of KeYmaera X currently running. Running two
     *   instances can result in weird behavior, even during initialization. Merely checking and failing when we try to
     *   bind to the port for real is insufficient, because we need to run some initialization code before attempting to
     *   bind. That's why we perform this check instead of just catching exceptions when the actual binding fails.
     */
    private def portIsBound(): Boolean = {
      // Check if this port is bound by trying to bind to it and catching the SocketException.
      try {
        new java.net.ServerSocket(Integer.parseInt(keymaeraxPort())).close()
        false
      } catch {
        case e: java.net.BindException =>
          e.printStackTrace()
          true
        case t: Throwable =>
          t.printStackTrace()
          true // Probably other things could happen here as well, but we'll catch all errors and assume something's fishy.
      }
    }
  }
}
