/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.launcher

import java.io.{InputStreamReader, BufferedReader, File, FileFilter,IOException,EOFException}
import javax.swing.JOptionPane
import edu.cmu.cs.ls.keymaerax.hydra.{SQLite, UpdateChecker}
import edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms

import scala.collection.JavaConversions._

/**
 * Usage:
 *  java -jar KeYmaeraX.jar or else
 *  java -Xss20M -jar KeYmaeraX.jar
 * Created by nfulton on 4/17/15.
 * @todo move functionality directly into KeYmaeraX.scala?
 */
object Main {
  def startServer() : Unit = {
    launcherLog("-launch -- starting KeYmaera X Web UI server HyDRA.")
    try {
      LemmaDatabaseInitializer.initializeFromJAR
    }
    catch {
      case e: LemmbaDatabaseInitializationException => {
        println("!!! ERROR: Could not initialize database !!!)")
        e.printStackTrace()
        println("!!! ERROR RECOVERY: Trying to generate the Lemma database by proving all derived axioms")
        DerivedAxioms.prepopulateDerivedLemmaDatabase()
      }
    }
    //@todo skip -ui -launch
    edu.cmu.cs.ls.keymaerax.hydra.Boot.main(Array[String]()) //@todo not sure.
  }


  //@todo set via -log command line option
  private var logFile = false
  def main(args : Array[String]) : Unit = {
    val isFirstLaunch = if(args.length >= 1) {
      !args.head.equals("-launch") || args.length>=2 && args(0)=="-ui" && args(1)=="-launch"
    } else true

    if(isFirstLaunch) {
      val java : String = javaLocation
      val keymaera : String = jarLocation
      println("Restarting KeYmaera X with sufficient stack space")
      runCmd(java :: "-Xss20M" :: "-jar" :: keymaera :: "-ui" :: "-launch" :: Nil)
    }
    else {
      exitIfDeprecated()
      startServer()
    }
  }

  /** Kills the current process and shows an error message if the current database is deprecated.
    * @todo similar behavior for the cache
    */
  private def exitIfDeprecated() = {
    if(UpdateChecker.upToDate().getOrElse(false) &&
       UpdateChecker.needDatabaseUpgrade(SQLite.ProdDB.getConfiguration("version").config("version")).getOrElse(false))
    {
      //Exit if KeYmaera X is up to date but the production database belongs to a deprecated version of KeYmaera X.
      //@todo maybe it makes more sense for the JSON file to associate each KeYmaera X version to a list of database and cache versions that work with that version.
      JOptionPane.showMessageDialog(null, "Your KeYmaera X database is not compatible with this version of KeYmaera X.\nPlease revert to an old version of KeYmaera X or else delete your current database (HOME/.keymaerax/keymaerax.sqlite)")
      System.exit(-1)
    }
    else {} //getOrElse(false) ignores cases where we couldn't download some needed information.
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
    launcherLog("Running command: " + cmd)

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
