/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review: 2016-08-02 */
package org.keymaerax.tools.qe

import java.io._
import org.keymaerax.Logging
import org.keymaerax.core._
import org.keymaerax.tools._

import java.util.concurrent.TimeUnit
import java.util.concurrent.ConcurrentHashMap
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.sys.process._

/**
 * Starts a Z3 process with the binary at `z3Path`, converting KeYmaera X datastructures to SMT-Lib format with
 * `converter`.
 *
 * Created by ran on 3/27/15.
 * @param z3Path
 *   The path to the Z3 binary.
 * @param converter
 *   Converts from KeYmaera X datastructures to SMT-Lib format.
 * @author
 *   Ran Ji
 * @author
 *   Stefan Mitsch
 */
class Z3Solver(val z3Path: String, val converter: SMTConverter) extends ToolOperationManagementBase with Logging {

  /** The currently running Z3 processes with their query indexes. */
  private val z3Processes = new ConcurrentHashMap[Long, Process]

  /** Provides a unique index for identifying the next query, incremented on every Z3 query. */
  private var queryIndex = 0

  /** Z3 version information. */
  val versionInfo: String = runZ3(z3Path + " -version", -1)

  /** Return Z3 QE result and the proof evidence */
  def qe(f: Formula): Formula = {
    val smtCode = converter(f)
    val z3Output = runZ3Smt(smtCode, "z3sat", getOperationTimeout) // @note (check-sat) gives unsat, sat or unknown
    logger.debug(s"[Z3 result] From calling Z3 on ${f.prettyString}: " + z3Output + "\n")
    // @todo So far does not handle get-model or unsat-core
    // @note only accepts output that consists of one of the following words, except for trailing whitespace
    z3Output.stripLineEnd match {
      case "unsat" => True
      case "sat" => throw SMTQeException(
          "QE with Z3 gives SAT. Cannot reduce the following formula to True:\n" + f.prettyString + "\n"
        )
      case "unknown" => throw SMTQeException(
          "QE with Z3 gives UNKNOWN. Cannot reduce the following formula to True:\n" + f.prettyString + "\n"
        )
      case _ => throw ConversionException("Back-conversion of Z3 result \n" + z3Output + "\n is not defined")
    }
  }

  /**
   * Calls Z3 with the command `z3Command` in a temporary SMT file for at most `timeout` time, and returns the resulting
   * output.
   */
  private[tools] def runZ3Smt(z3Command: String, tmpFilePrefix: String, timeout: Int): String = {
    logger.debug("[Calling Z3...] \n" + z3Command)

    val smtFile = File.createTempFile(tmpFilePrefix, ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(z3Command)
    writer.close()

    runZ3(z3Path + " " + smtFile.getAbsolutePath, timeout)
  }

  /** Runs the process `cmd` for at most `timeout` time, and returns the resulting output. */
  private def runZ3(cmd: String, timeout: Int): String = {
    // @note running on a single process, but additionally safeguard with a query index to test whether the returned
    // result fits the input query index
    val qidx: Long = synchronized { queryIndex += 1; queryIndex }
    var result: (Long, String) = (-1, "")
    val pl = ProcessLogger(s =>
      result match {
        case (-1, "") => result = (qidx, s)
        case (i, rs) =>
          assert(i == qidx)
          result = (i, rs + "\n" + s)
      }
    )
    val f = z3Processes.synchronized {
      val p = cmd.run(pl) // start asynchronously, log output to logger
      z3Processes.put(qidx, p)
      Future(blocking((qidx, p.exitValue())))
    }
    try {
      val (exitQIdx, exitVal) =
        if (timeout >= 0) Await.result(f, duration.Duration(timeout, TimeUnit.SECONDS))
        else Await.result(f, duration.Duration.Inf)
      if (exitQIdx != qidx) throw ToolCommunicationException(
        "Expected query index on tool exit to match input query index, but exit " + exitQIdx + " != " + qidx
      )
      if (exitVal == 0) {
        if (result._1 == qidx) result._2
        else throw ToolCommunicationException(
          "Expected result query index to match input query index, but result " + result._1 + " != " + qidx
        )
      } else { throw SMTQeException("Error executing Z3, exit value " + exitVal) }
    } catch {
      case ex: TimeoutException => throw SMTTimeoutException(s"Z3 timeout of ${timeout}s exceeded", ex)
      case ex: InterruptedException => throw ToolCommunicationException(s"Z3 interrupted", ex)
    } finally {
      z3Processes.remove(qidx) match {
        case null => // nothing to do
        case p => p.destroy()
      }
    }
  }

  /** Cancels the current Z3 process. */
  def cancel(): Boolean = z3Processes.synchronized {
    z3Processes.forEach((_, v) => v.destroy())
    z3Processes.clear()
    true
  }

  /** @inheritdoc */
  override def getAvailableWorkers: Int = Int.MaxValue
}
