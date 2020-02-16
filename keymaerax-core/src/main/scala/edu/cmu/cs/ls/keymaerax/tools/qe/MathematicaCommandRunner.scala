/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink.KernelLink
import edu.cmu.cs.ls.keymaerax.tools.MathematicaComputationAbortedException
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.MExpr
import org.apache.logging.log4j.scala.Logging

/** Interface for running and cancelling a Mathematica command. */
trait MathematicaCommandRunner {
  /**
    * Runs Mathematica command `cmd`, converts the result into KeYmaera X with the converter `m2k`.
    * @param cmd The Mathematica command.
    * @param m2k The converter from Mathematica back to KeYmaera X.
    * @return The result string and the converted result.
    * @tparam T The KeYmaera X expression type.
    * @ensures cmd is freed and should not ever be used again.
    */
  def run[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T)

  /**
    * Cancels the current request.
    * @return True if command is successfully cancelled, or False if the new status is unknown.
    */
  def cancel(): Boolean
}

/**
  * Base class for running Mathematica commands synchronously.
  */
abstract class BaseMathematicaCommandRunner extends MathematicaCommandRunner {
  /** Default timeout for Mathematica requests: no timeout. */
  val TIMEOUT_OFF: Int = -1
  /** Timeout for Mathematica requests in seconds, set to TIMEOUT_OFF to disable. */
  var timeout: Int = TIMEOUT_OFF
  /** Default memory limit: no limit. */
  val MEMORY_LIMIT_OFF: Long = -1
  /** Memory limit for Mathematica requests in MB, set to MEMORY_LIMIT_OFF to disable. */
  var memoryLimit: Long = MEMORY_LIMIT_OFF

  /** @inheritdoc */
  final override def run[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T) = doRun(memoryConstrained(timeConstrained(cmd)), m2k)

  /** @see [[run]] */
  protected def doRun[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T)

  protected def timeConstrained(cmd: MExpr): MExpr =
    if (timeout < 0) cmd
    else MathematicaOpSpec.timeConstrained(cmd, MathematicaOpSpec.long(timeout))

  protected def memoryConstrained(cmd: MExpr): MExpr =
    if (memoryLimit < 0) cmd
    else MathematicaOpSpec.memoryConstrained(cmd, MathematicaOpSpec.long(memoryLimit*1000000))
}

/** JLink command runner companion: keeps track of issued queries. */
object JLinkMathematicaCommandRunner {
  private var queryIndex: Long = 0
}

/** Runs a command using the supplied JLink `ml`. */
case class JLinkMathematicaCommandRunner(ml: KernelLink) extends BaseMathematicaCommandRunner with Logging {

  private val fetchMessagesCmd = "$MessageList"

  /** @inheritdoc */
  override def doRun[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T) = try {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    val qidx: Long = ml.synchronized { JLinkMathematicaCommandRunner.queryIndex += 1; JLinkMathematicaCommandRunner.queryIndex }
    val indexedCmd = MathematicaOpSpec.list(new MExpr(qidx), cmd)
    // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
    val checkErrorMsgCmd = MathematicaOpSpec.check(indexedCmd, MathematicaOpSpec.exception.op /*, checkedMessagesExpr*/)
    try {
      logger.debug("Sending : " + checkErrorMsgCmd)
      ml.synchronized {
        dispatch(checkErrorMsgCmd.toString)
        getAnswer(qidx, m2k, indexedCmd.toString) //@note disposes indexedCmd, do not use (except dispose) afterwards
      }
    } finally {
      //@note dispose in finally instead of after getAnswer, because interrupting thread externally aborts the scheduled task without dispose
      //@note nested cmd is disposed automatically
      checkErrorMsgCmd.dispose()
    }
    //@note during normal execution, this disposes cmd twice (once via checkErrorMsgCmd) but J/Link ensures us this would be acceptable.
  } finally { cmd.dispose() }

  /** @inheritdoc */
  override def cancel(): Boolean = {
    ml.abortEvaluation()
    true
  }

  /** Send command `cmd` for evaluation to Mathematica kernel straight away. */
  private def dispatch(cmd: String): Unit = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.evaluate(cmd)
  }

  /**
    * Blocks and returns the answer (as string and as KeYmaera X expression).
    *
    * @param cmdIdx The expected command index to avoid returning stale answers.
    * @param converter Converts Mathematica expressions back to KeYmaera X expressions.
    * @param ctx The context for error messages in exceptions.
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result as string and converted to the expected result type.
    */
  private def getAnswer[T](cmdIdx: Long, converter: MExpr=>T, ctx: String): (String, T) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.waitForAnswer()
    importResult(ml.getExpr,
      res => {
        if (isAborted(res)) {
          throw new MathematicaComputationAbortedException(ctx)
        } else if (res == MathematicaOpSpec.exception.op) {
          // an exception occurred, rerun to get the messages
          ml.evaluate(ctx + ";" + fetchMessagesCmd)
          ml.waitForAnswer()
          val txtMsg = importResult(ml.getExpr, _.toString)
          //@todo improve exception hierarchy (document exceptions)
          throw new IllegalArgumentException("Input " + ctx + " cannot be evaluated: " + txtMsg)
        } else {
          val head = res.head
          if (head == MathematicaOpSpec.check.op) {
            throw new IllegalStateException("JLink returned input as answer: " + res.toString)
          } else if (MathematicaOpSpec.list.applies(res) && res.args.length == 2 && res.args.head.asInt() == cmdIdx) {
            val theResult = res.args.last
            if (isAborted(theResult)) throw new MathematicaComputationAbortedException(ctx)
            else (theResult.toString, converter(theResult))
          } else {
            //@todo may not only be caused by stale answer
            throw new IllegalStateException("JLink returned a stale answer for " + res.toString)
          }
        }
      })
  }

}
