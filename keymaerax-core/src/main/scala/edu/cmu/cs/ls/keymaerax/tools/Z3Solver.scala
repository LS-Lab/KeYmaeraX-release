/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.io._
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, ParseException}

import scala.collection.immutable
import scala.concurrent._
import scala.sys.process._
import ExecutionContext.Implicits.global

/**
 * Created by ran on 3/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class Z3Solver(val converter: SMTConverter = DefaultSMTConverter) extends ToolOperationManagementBase with SMTSolver {
  private val DEBUG = Configuration(Configuration.Keys.DEBUG) == "true"

  /** Get the absolute path to Z3 executable
    * Copies Z3 out of the JAR if the KeYmaera X version has updated. */
  private val pathToZ3 : String = {
    val z3TempDir = Configuration.path(Configuration.Keys.Z3_PATH)
    if (!new File(z3TempDir).exists) new File(z3TempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)

    val z3AbsPath =
      if (needsUpdate(z3TempDir)) {
        copyToDisk(osName, z3TempDir)
      } else if (osName.contains("windows") && new File(z3TempDir+"z3.exe").exists()) {
        z3TempDir+"z3.exe"
      } else if (new File(z3TempDir+"z3").exists()) {
        z3TempDir+"z3"
      } else {
        copyToDisk(osName,z3TempDir)
      }

    assert(new File(z3AbsPath).exists())
    z3AbsPath
  }

  /** We store the last version of KeYmaera X that updated the Z3 binary, and copy over Z3 every time we notice
    * a new version of KeYmaera X is installed.
    * @todo We should probably check the Z3 version instead but... */
  private def versionFile(z3TempDir:String) = new File(z3TempDir + File.separator + "z3v")

  /** Returns the version of Z3 that the current system's JAR was updated from. */
  private def needsUpdate(z3TempDir: String) = {
    val versionWhenLastCopied =
      if(versionFile(z3TempDir).exists()) {
        val source = scala.io.Source.fromFile(versionFile(z3TempDir))
        val result = source.mkString
        source.close()
        result
      }
      else {
        "Not A Version Number" //Return an invalid version number, forcing Z3 to be copied to disk.
      }
    //Update if the version stroed in the version file does not equal the current version.
    val result = !versionWhenLastCopied.equals(edu.cmu.cs.ls.keymaerax.core.VERSION)
    if(result && DEBUG) println("Updating Z3 binary...")
    result
  }

  /** Copies Z3 to the disk. */
  private def copyToDisk(osName:String, z3TempDir:String) = {
    //Update the version number.
    new PrintWriter(versionFile(z3TempDir)) { write(edu.cmu.cs.ls.keymaerax.core.VERSION); close() }
    //Copy z3 binary to disk.
    scala.io.Source.fromFile(versionFile(z3TempDir))
    val osArch = System.getProperty("os.arch")
    var resource : InputStream = null
    if (osName.contains("mac")) {
      if(osArch.contains("64")) {
        resource = this.getClass.getResourceAsStream("/z3/mac64/z3")
      }
    } else if (osName.contains("windows")) {
      if(osArch.contains("64")) {
        resource = this.getClass.getResourceAsStream("/z3/windows64/z3.exe")
      } else {
        resource = this.getClass.getResourceAsStream("/z3/windows32/z3.exe")
      }
    } else if (osName.contains("linux")) {
      if(osArch.contains("64")) {
        resource = this.getClass.getResourceAsStream("/z3/ubuntu64/z3")
      } else {
        resource = this.getClass.getResourceAsStream("/z3/ubuntu32/z3")
      }
    } else if (osName.contains("freebsd")) {
      if(osArch.contains("64")) {
        resource = this.getClass.getResourceAsStream("/z3/freebsd64/z3")
      }
    } else {
      throw new Exception("Z3 solver is currently not supported in your operating system.")
    }
    if (resource == null)
      throw new Exception("Could not find Z3 in classpath jar bundle: " + System.getProperty("user.dir"))
    val z3Source = Channels.newChannel(resource)
    val z3Temp = {
      if (osName.contains("windows")) {
        new File(z3TempDir, "z3.exe")
      } else {
        new File(z3TempDir, "z3")
      }
    }

    // Get a stream to the script in the resources dir
    val z3Dest = new FileOutputStream(z3Temp)
    // Copy file to temporary directory
    z3Dest.getChannel.transferFrom(z3Source, 0, Long.MaxValue)
    val z3AbsPath = z3Temp.getAbsolutePath
    val permissionCmd =
      if (osName.contains("windows")) "icacls " + z3AbsPath + " /e /p Everyone:F"
      else "chmod u+x " + z3AbsPath
    //@todo Could change to only modify permissions of freshly extracted files not from others that happen to preexist. It's in KeYmaera's internal folders, though.
    Runtime.getRuntime.exec(permissionCmd)
    z3Source.close()
    z3Dest.close()
    assert(new File(z3AbsPath).exists())
    z3AbsPath
  }

  /** Return Z3 QE result and the proof evidence */
  def qeEvidence(f: Formula) : (Formula, Evidence) = {
    val smtCode = converter(f)
    val z3Output = callZ3(smtCode, "z3sat", getOperationTimeout) //@note (check-sat) gives unsat, sat or unknown
    if (DEBUG) println(s"[Z3 result] From calling Z3 on ${f.prettyString}: " + z3Output + "\n")
    //@todo So far does not handle get-model or unsat-core
    z3Output.stripLineEnd match {
      case "unsat" => (True, ToolEvidence(immutable.List("input" -> smtCode, "output" -> z3Output)))
      case "sat" => throw new SMTQeException("QE with Z3 gives SAT. Cannot reduce the following formula to True:\n" + f.prettyString + "\n")
      case "unknown" => throw new SMTQeException("QE with Z3 gives UNKNOWN. Cannot reduce the following formula to True:\n" + f.prettyString + "\n")
      case _ => throw new SMTConversionException("Back-conversion of Z3 result \n" + z3Output + "\n is not defined")
    }
  }

  /**
   * Simplify a KeYmaera X term into a possibly simple term
   * @param t  KeYmaera X term to be simplified
   * @return   the simplified term, or the original term if the simplify result is not a parsable KeYmaera X term
   */
  def simplify(t: Term) : Term = {
    val smtCode = converter.generateSimplify(t)
    if (DEBUG) println("[Simplifying with Z3 ...] \n" + smtCode)
    val z3Output = callZ3(smtCode, "z3simplify", getOperationTimeout)
    if (DEBUG) println("[Z3 simplify result] \n" + z3Output + "\n")
    if (z3Output.contains("!")) t
    else {
      try {
        KeYmaeraXParser.termParser(z3Output)
      } catch {
        case _: ParseException =>
          if (DEBUG) println("[Info] Cannot parse Z3 simplified result: " + z3Output)
          t
      }
    }
  }



  /** Calls Z3 with the command `z3Command` for at most `timeout` time, and returns the resulting output. */
  private def callZ3(z3Command: String, tmpFilePrefix: String, timeout: Int): String = {
    if (DEBUG) println("[Calling Z3...] \n" + z3Command)
    val smtFile = File.createTempFile(tmpFilePrefix, ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(z3Command)
    writer.close()
    val cmd = pathToZ3 + " " + smtFile.getAbsolutePath

    var result: String = ""
    val logger = ProcessLogger(s => result = s)
    val p = cmd.run(logger) // start asynchronously, log output to logger
    val f = Future(blocking(p.exitValue())) // wrap in Future
    val exitVal = try {
      if (timeout >= 0) Await.result(f, duration.Duration(timeout, "sec"))
      else Await.result(f, duration.Duration.Inf)
    } catch {
      case ex: TimeoutException =>
        p.destroy()
        throw ToolException(s"Z3 timeout of ${timeout}s exceeded", ex)
    }

    if (exitVal == 0) {
      result
    } else {
      throw ToolException(s"Error executing Z3, exit value $exitVal")
    }
  }
}
