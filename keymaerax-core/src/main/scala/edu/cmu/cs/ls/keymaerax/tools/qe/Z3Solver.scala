/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import java.io._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools._
import org.apache.logging.log4j.scala.Logging

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.sys.process._

/**
  * Starts a Z3 process with the binary at `z3Path`, converting KeYmaera X datastructures to SMT-Lib format
  * with `converter`.
  * @param z3Path The path to the Z3 binary.
  * @param converter Converts from KeYmaera X datastructures to SMT-Lib format.
  * Created by ran on 3/27/15.
  * @author Ran Ji
  * @author Stefan Mitsch
  */
class Z3Solver(val z3Path: String, val converter: SMTConverter) extends ToolOperationManagementBase with Logging {
  /** The currently running Z3 process. */
  private var z3Process: Option[Process] = None

  /** The expected version and hash code */
  private val version :: hash :: Nil =
    scala.io.Source.fromInputStream(getClass.getResourceAsStream("/z3/VERSION")).getLines().toList

  /** Lightweight check that we are communicating with Z3 in the expected version and build hash. */
  insist({
    val versionOutput = runZ3(z3Path + " -version", -1)
    versionOutput.startsWith("Z3 version " + version) && versionOutput.endsWith(hash)
  }, "Z3 not of the expected version and build hash")

  /** Return Z3 QE result and the proof evidence */
  def qe(f: Formula): Formula = {
    val smtCode = converter(f)
    val z3Output = runZ3Smt(smtCode, "z3sat", getOperationTimeout) //@note (check-sat) gives unsat, sat or unknown
    logger.debug(s"[Z3 result] From calling Z3 on ${f.prettyString}: " + z3Output + "\n")
    //@todo So far does not handle get-model or unsat-core
    //@note only accepts output that consists of one of the following words, except for trailing whitespace
    z3Output.stripLineEnd match {
      case "unsat" => True
      case "sat" => throw new SMTQeException("QE with Z3 gives SAT. Cannot reduce the following formula to True:\n" + f.prettyString + "\n")
      case "unknown" => throw new SMTQeException("QE with Z3 gives UNKNOWN. Cannot reduce the following formula to True:\n" + f.prettyString + "\n")
      case _ => throw new SMTConversionException("Back-conversion of Z3 result \n" + z3Output + "\n is not defined")
    }
  }

  /** Calls Z3 with the command `z3Command` in a temporary SMT file for at most `timeout` time, and returns the resulting output. */
  private[tools] def runZ3Smt(z3Command: String, tmpFilePrefix: String, timeout: Int): String = {
    logger.debug("[Calling Z3...] \n" + z3Command)

    if (z3Process.isDefined) throw ToolException("Z3 is busy")

    val smtFile = File.createTempFile(tmpFilePrefix, ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(z3Command)
    writer.close()

    runZ3(z3Path + " " + smtFile.getAbsolutePath, timeout)
  }

  /** Runs the process `cmd` for at most `timeout` time, and returns the resulting output. */
  private def runZ3(cmd: String, timeout: Int): String = {
    if (z3Process.isDefined) throw ToolException("Z3 is busy")
    //@todo ensure unique output (make sure no concurrently running Z3)
    var result: String = ""
    val pl = ProcessLogger(s => result = s)
    val p = cmd.run(pl) // start asynchronously, log output to logger
    z3Process = Some(p)
    val f = Future(blocking(p.exitValue()))
    val exitVal = try {
      if (timeout >= 0) Await.result(f, duration.Duration(timeout, "sec"))
      else Await.result(f, duration.Duration.Inf)
    } catch {
      case ex: TimeoutException =>
        p.destroy()
        throw ToolException(s"Z3 timeout of ${timeout}s exceeded", ex)
      case ex: InterruptedException =>
        p.destroy
        throw ToolException(s"Z3 interrupted", ex)
    } finally {
      z3Process = None
    }

    if (exitVal == 0) {
      result
    } else {
      throw ToolException(s"Error executing Z3, exit value $exitVal")
    }
  }

  /** Cancels the current Z3 process. */
  def cancel(): Boolean = z3Process match {
    case Some(p) =>
      z3Process = None
      p.destroy()
      true
    case None => true
  }

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
