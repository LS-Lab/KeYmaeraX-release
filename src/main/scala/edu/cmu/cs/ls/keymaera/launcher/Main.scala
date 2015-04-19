package edu.cmu.cs.ls.keymaera.launcher

import java.io.{InputStreamReader, BufferedReader, File, FileFilter,IOException,EOFException}
import javax.swing.JOptionPane

/**
 * Usage:
 *  java -jar KeYmaeraX.jar or else
 *  java -Xss20M -jar KeYmaeraX.jar
 * Created by nfulton on 4/17/15.
 */
object Main {
  def main(args : Array[String]) : Unit = {
    val isFirstLaunch = if(args.length > 0) {
      !args.head.equals("LAUNCH")
    } else true

    if(isFirstLaunch) {
      val java : String = javaLocation
      val keymaera : String = jarLocation
      val cmd = java + " -Xss20M -jar " + keymaera + " LAUNCH"
      runCmd(cmd)
    }
    else {
      launcherLog("Detected LAUNCH flag -- starting HyDRA.")
      edu.cmu.cs.ls.keymaera.hydra.Boot.main(Array[String]()) //@todo not sure.
    }
  }



  def processIsAlive(proc : Process) = {
    try {
      proc.exitValue();
      false
    } catch {
      case e : Exception => true
    }
  }

  private def runCmd(cmd:String) = {
    launcherLog("Running command: " + cmd)
    //@todo As of 1.5, ProcessBuilder.start() is the preferred way to create a Process.
    val proc = Runtime.getRuntime.exec(cmd)

    Runtime.getRuntime().addShutdownHook(new Thread() {
      override def run(): Unit = {
        proc.destroy()
      }
    })

    val errReaderThread = new Thread() {
      override def run() = {
        try {
        val errReader = new BufferedReader(new InputStreamReader(proc.getErrorStream));
        var errLine = ""
        while((errLine = errReader.readLine()) != null && processIsAlive(proc)) {
//          errLine = errReader.readLine()
          if(errLine != null) System.err.println(errLine);
        }
        } catch {
          case exc: EOFException => System.err.println("Done with log output")
          case exc: IOException => System.err.println("Done with log output: " + exc)
        } 
      }
    }
    val stdReaderThread = new Thread() {
      override def run() = {
        try {
        val reader =
          new BufferedReader(new InputStreamReader(proc.getInputStream()));
        var line = ""
        while((line = reader.readLine()) != null && processIsAlive(proc)) {
          if(line != null) System.out.println(line);
        }
        } catch {
          case exc: EOFException => System.err.println("Done with log output")
          case exc: IOException => System.err.println("Done with log input: " + exc)
        } 
      }
    }

    stdReaderThread.start()
    errReaderThread.start()

    proc.waitFor();
    println("")
  }

  private def exitWith(err : String) = {
    val message = "ERROR in loader :: See http://keymaerax.org/startup.html for trouble-shooting assistance (Message: " + err + ")"
    launcherLog(message)
    JOptionPane.showMessageDialog(null, message)
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
    new File(Main.getClass().getProtectionDomain().getCodeSource().getLocation().toURI().getPath()).toString()
//    val execDir  = System.getProperty("user.dir")
//    val matchingFiles = new java.io.File(execDir).listFiles(new FileFilter {
//      override def accept(pathname: File): Boolean = pathname.getName.contains("keymaerax.jar") && pathname.getAbsolutePath.endsWith(".jar") //finds *marea*.jar$
//    })
//    if(matchingFiles.length == 1) matchingFiles.head.getAbsolutePath else exitWith("Could not find a KeYmaeraX JAR in " + execDir + " NOTE: the JAR file MUST be named keymaerax.jar!")
  }

  def launcherLog(s : String, isError:Boolean = false) = {
    val prefix = if(isError) "[launcher][ERROR] " else "[launcher] "
    println(prefix + s)
  }

}
