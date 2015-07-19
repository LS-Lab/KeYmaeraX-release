/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.launcher

import java.io.{InputStreamReader, BufferedReader, File, FileFilter,IOException,EOFException}
import javax.swing.JOptionPane
import scala.collection.JavaConversions._

/**
 * Usage:
 *  java -jar KeYmaeraX.jar or else
 *  java -Xss20M -jar KeYmaeraX.jar
 * Created by nfulton on 4/17/15.
 */
object Main {
  def main(args : Array[String]) : Unit = {
    val isFirstLaunch = if(args.length >= 1) {
      !args.head.equals("LAUNCH") || args.length>=2 && args(0)=="-ui" && args(1)=="LAUNCH"
    } else true

    if(isFirstLaunch) {
      val java : String = javaLocation
      val keymaera : String = jarLocation
      println("Restarting KeYmaera X with sufficient stack space")
      runCmd(java :: "-Xss20M" :: "-jar" :: keymaera :: "-ui" :: "LAUNCH" :: Nil)
    }
    else {
      launcherLog("LAUNCH flag present -- starting KeYmaera X Web UI server HyDRA.")
      edu.cmu.cs.ls.keymaerax.hydra.Boot.main(Array[String]()) //@todo not sure.
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
    launcherLog("Running command: " + cmd)

    val pb = new ProcessBuilder(cmd)
    var pollOnStd = false
    try {
      val errorLog = File.createTempFile("keymaerax-error-stream", ".txt")
      val outputLog = File.createTempFile("keymaerax-output-stream", ".txt")
      pb.redirectError(errorLog)
      System.err.println("Errors will be logged at " + errorLog.getPath)
      pb.redirectOutput(outputLog)
      System.err.println("Outputs will be logged at " + outputLog.getPath)
    } catch {
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
