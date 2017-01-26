/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.launcher

import java.io._
import javax.swing.JOptionPane

import edu.cmu.cs.ls.keymaerax.hydra.{SQLite, StringToVersion, UpdateChecker}
import spray.json.JsArray

import scala.collection.JavaConversions._

import spray.json._
import spray.json.DefaultJsonProtocol._

/**
 * Usage:
 *  java -jar KeYmaeraX.jar or else
 *  java -Xss20M -jar KeYmaeraX.jar
 * Created by nfulton on 4/17/15.
 * @todo move functionality directly into KeYmaeraX.scala?
 */
object Main {
  def startServer(args: Array[String]) : Unit = {
    launcherLog("-launch -- starting KeYmaera X Web UI server HyDRA.")
//    try {
////      throw new LemmbaDatabaseInitializationException("")
////      LemmaDatabaseInitializer.initializeFromJAR
//    }
//    catch {
//      case e: LemmbaDatabaseInitializationException => {
//        println("!!! ERROR: Could not initialize database !!!)")
//        e.printStackTrace()
//        println("!!! ERROR RECOVERY: Trying to generate the Lemma database by proving all derived axioms")
//        edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.prepopulateDerivedLemmaDatabase()
////        edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms.prepopulateDerivedLemmaDatabase()
//      }
//    }
    //@todo skip -ui -launch
    if(System.getenv().containsKey("HyDRA_SSL") && System.getenv("HyDRA_SSL").equals("on")) {
      edu.cmu.cs.ls.keymaerax.hydra.SSLBoot.main(args)
    }
    else {
      LoadingDialogFactory() //Intialize the loading dialog.
      edu.cmu.cs.ls.keymaerax.hydra.NonSSLBoot.main(args)
    }
  }


  //@todo set via -log command line option
  private var logFile = false
  def main(args : Array[String]) : Unit = {
    val isFirstLaunch = if (args.length >= 1) {
      !args.head.equals("-launch") || args.length>=2 && args(0)=="-ui" && args(1)=="-launch"
    } else true

    if (isFirstLaunch) {
      val java : String = javaLocation
      val keymaeraxjar : String = jarLocation
      println("Restarting KeYmaera X with sufficient stack space")
      runCmd((java :: "-Xss20M" :: "-jar" :: keymaeraxjar :: "-launch"  :: Nil) ++ args.toList ++ ("-ui" :: Nil))
    }
    else {
      exitIfDeprecated()
      clearCacheIfDeprecated()
      assert(args.head.equals("-launch"))
      startServer(args.tail)
      //@todo use command line argument -mathkernel and -jlink from KeYmaeraX.main
      //@todo use command line arguments as the file to load. And preferably a second argument as the tactic file to run.
    }
  }

  /** Clears the cache if the cache was created by a previous version of KeYmaera X */
  private def clearCacheIfDeprecated(): Unit = {
    val cacheLocation = System.getProperty("user.home") + File.separator + ".keymaerax" + File.separator + "cache"
    val cacheDirectory = new File(cacheLocation)
    val cacheVersionFile = new File(cacheLocation + File.separator + "VERSION")

    if (!cacheDirectory.exists()) {
      if (!cacheDirectory.mkdirs()) {
        throw new Exception(s"Could not create the directory ${cacheDirectory.getAbsolutePath}. Please check your file system permissions.")
      }
    }

    if (!cacheVersionFile.exists()) {
      if (!cacheVersionFile.createNewFile())
        throw new Exception(s"Could not create the file ${cacheVersionFile.getAbsolutePath}. Please check your file system permissions.")
      clearCache(new File(cacheLocation))
    }
    else {
      val cacheVersion = scala.io.Source.fromFile(cacheVersionFile).mkString.replace("\n", "")
      try {
        if (StringToVersion(cacheVersion) != StringToVersion(edu.cmu.cs.ls.keymaerax.core.VERSION)) {
          clearCache(cacheDirectory)
        }
      }
      catch {
        case e: NumberFormatException => {
          println("Warning: Could not parse the cache version file, cache contained: " + cacheVersion)
          clearCache(cacheDirectory)
        }
      }
    }
  }

  /** Clears the cache and creates a new cache/VERSION file */
  private def clearCache(dir: File) = {
    println("Clearing your cache because of an update.")
    if(dir.exists()) {
      if(!deleteDirectory(dir)) throw new Exception(s"Could not delete cache directory ${dir.getAbsolutePath}")
    }
    assert(!dir.exists(), s"Cache directory ${dir.getAbsolutePath} should not exist after being deleted.")
    if(!dir.mkdirs()) throw new Exception(s"Could not reinitialize cache because cache directory ${dir.getAbsolutePath} could not be created.")

    val versionFile = new File(dir.getAbsolutePath + File.separator + "VERSION")
    if(!versionFile.exists()) {
      if(!versionFile.createNewFile()) throw new Exception(s"Could not create ${versionFile.getAbsolutePath}")
    }
    assert(versionFile.exists())
    val fw = new FileWriter(versionFile)
    fw.write(edu.cmu.cs.ls.keymaerax.core.VERSION)
    fw.close()
  }

  /** Deletes the directory or file (recursively). Corresponds to rm -r */
  private def deleteDirectory(f : File) : Boolean = {
    if(!f.isDirectory) {
      if(!f.delete()) {
        println(s"Warning: could not delete ${f.getAbsolutePath}")
        false
      }
      else true
    }
    else if(f.list().length == 0) f.delete()
    else {
      val recSuccess = f.listFiles().forall(deleteDirectory)
      if(recSuccess) f.delete()
      else false
    }
  } ensuring(r => !r || !f.exists())

  /** Kills the current process and shows an error message if the current database is deprecated.
    * @todo similar behavior for the cache
    */
  private def exitIfDeprecated() = {
    val databaseVersion = SQLite.ProdDB.getConfiguration("version").config("version")
    println("Current database version: " + databaseVersion)
    if (UpdateChecker.upToDate().getOrElse(false) &&
        UpdateChecker.needDatabaseUpgrade(databaseVersion).getOrElse(false)) {
      //Exit if KeYmaera X is up to date but the production database belongs to a deprecated version of KeYmaera X.
      //@todo maybe it makes more sense for the JSON file to associate each KeYmaera X version to a list of database and cache versions that work with that version.
      try {
        upgradeDatabase(databaseVersion)
        println("Successful database upgrade to version: " + SQLite.ProdDB.getConfiguration("version").config("version"))
      } catch {
        case e: Throwable =>
          val backupPath = s"~/.keymaerax/keymaerax.sqlite-$databaseVersion-*"
          val defaultName = "keymaerax.sqlite"
          val message =
            s"""
              |Your KeYmaera X database is not compatible with this version of KeYmaera X.
              |Automated upgrade failed and changes have been rolled back.
              |Additionally, a backup copy of your current database was placed at $backupPath.
              |Please revert to an old version of KeYmaera X.
              |If necessary, restore the backup database from $backupPath back to $defaultName.
              |
              |Internal error details:
            """.stripMargin
          println(message)
          e.printStackTrace()
          JOptionPane.showMessageDialog(null, message)
          System.exit(-1)
      }
    }
    else {} //getOrElse(false) ignores cases where we couldn't download some needed information.
  }

  private def backupDatabase(currentVersion: String): Unit = {
    val src = new File(SQLite.ProdDB.dblocation)
    val dest = new File(src.getAbsolutePath + "-" + currentVersion + "-" + System.currentTimeMillis())
    new FileOutputStream(dest).getChannel.transferFrom(new FileInputStream(src).getChannel, 0, Long.MaxValue)
  }

  private def runUpgradeScript(scriptUrl: String): Unit = {
    val script = io.Source.fromInputStream(getClass.getResourceAsStream(scriptUrl)).mkString
    val statements = script.split(";")
    val conn = SQLite.ProdDB.sqldb.createConnection()
    conn.setAutoCommit(false)
    try {
      conn.rollback()
      val stmt = conn.createStatement()
      statements.foreach(stmt.addBatch)
      stmt.executeBatch()
      conn.commit()
    } catch {
      case e: Throwable => conn.rollback(); throw e
    } finally {
      conn.close()
    }
  }

  private def upgradeDatabase(currentVersion: String): Unit = {
    val upgradeScripts = io.Source.fromInputStream(getClass.getResourceAsStream("/sql/upgradescripts.json")).mkString
    val scripts = upgradeScripts.parseJson.asInstanceOf[JsArray]
    val currentScripts = scripts.elements.filter(_.asJsObject.fields("upgradeFrom").convertTo[String] == currentVersion)
    if (currentScripts.nonEmpty) {
      backupDatabase(currentVersion)
      currentScripts.map(_.asJsObject.fields("scripts").asInstanceOf[JsArray]).foreach(script =>
        script.elements.foreach(s => runUpgradeScript(s.asJsObject.fields("url").convertTo[String]))
      )
    }
  }

  def processIsAlive(proc : Process) = {
    try {
      proc.exitValue()
      false
    } catch {
      case e : Exception => true
    }
  }


  private def runCmd(cmd: List[String]) = {
    launcherLog("Running command:\n" + cmd.mkString(" "))

    val pb = new ProcessBuilder(cmd)
    var pollOnStd = false
    try {
      if (logFile) {
        //@todo not sure if it's really helpful to have separate error and output log. pb.redirectErrorStream(true)
        val errorLog = File.createTempFile("keymaerax-error-stream", ".txt")
        val outputLog = File.createTempFile("keymaerax-output-stream", ".txt")
        pb.redirectError(errorLog)
        System.err.println("Errors will be logged at " + errorLog.getPath)
        pb.redirectOutput(outputLog)
        System.err.println("Outputs will be logged at " + outputLog.getPath)
      } else {
        //@todo dump to console AND to logfile would be best
        pb.inheritIO()
      }
    } catch {
      //@note JDK<1.7
      case ex: NoSuchMethodError => pollOnStd = true
    }
    val proc = pb.start()

    Runtime.getRuntime.addShutdownHook(new Thread() {
      override def run(): Unit = {
        proc.destroy()
      }
    })

    if (pollOnStd) {
      val errReaderThread = new Thread() {
        override def run() = {
          try {
            val errReader = new BufferedReader(new InputStreamReader(proc.getErrorStream))
            while (processIsAlive(proc)) {
              val errLine = errReader.readLine()
              if (errLine != null) System.err.println(errLine)
            }
            errReader.close()
          } catch {
            case exc: EOFException => System.err.println("Done with log output")
            case exc: IOException => System.err.println("Done with log output: " + exc)
          }
        }
      }
      val stdReaderThread = new Thread() {
        override def run() = {
          try {
            val reader = new BufferedReader(new InputStreamReader(proc.getInputStream))
            while (processIsAlive(proc)) {
              val line = reader.readLine()
              if (line != null) System.out.println(line)
            }
            reader.close()
          } catch {
            case exc: EOFException => System.err.println("Done with log output")
            case exc: IOException => System.err.println("Done with log input: " + exc)
          }
        }
      }

      stdReaderThread.start()
      errReaderThread.start()
    }

    proc.waitFor()
    println("")
  }

  private def exitWith(err : String) = {
    val message = "ERROR in loader :: See http://keymaeraX.org/startup.html for trouble-shooting assistance (Message: " + err + ")"
    launcherLog(message)
    try {
      if (!java.awt.GraphicsEnvironment.isHeadless) {
        JOptionPane.showMessageDialog(null, message)
      }
    } catch {
        case exc: java.awt.HeadlessException =>
        case exc: java.lang.ClassNotFoundException =>
        case exc: java.lang.NoSuchMethodError =>
        case exc: Exception =>
    }
    System.exit(-1)
    ???
  }

  lazy val javaLocation : String = {
    val javaHome = System.getProperty("java.home") + "/bin"
    val matchingFiles = new java.io.File(javaHome).listFiles(new FileFilter {
      override def accept(pathname: File): Boolean = pathname.canExecute && (pathname.getName.equals("java") || pathname.getName.equals("java.exe"))
    })

    if(matchingFiles.length == 1) {
      matchingFiles.head.getAbsolutePath
    }
    else {
      exitWith("Could not find a Java executable in " + javaHome)
    }
  }

  /**
   * Assumes that the JAR was run from its containing directory (e.g., as happens when double-clicking).
   * If this assumption is violated, the launcher will fail.
   * @return The location of the .JAR file that's currently running.
   */
  lazy val jarLocation : String = {
      new File(Main.getClass.getProtectionDomain.getCodeSource.getLocation.toURI.getPath).toString
  }

  def launcherLog(s : String, isError:Boolean = false) = {
    val prefix = if(isError) "[launcher][ERROR] " else "[launcher] "
    println(prefix + s)
  }

}
