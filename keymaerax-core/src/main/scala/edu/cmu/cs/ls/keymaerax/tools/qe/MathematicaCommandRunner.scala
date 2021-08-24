/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink.{Expr, KernelLink, MathLinkException}
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.tools.{ConversionException, MathematicaComputationAbortedException, MathematicaInapplicableMethodException, MathematicaMathlinkException, MathematicaUnknownCauseCriticalException, ToolCommunicationException, ToolExecutionException}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.MExpr
import org.slf4j.{LoggerFactory, MarkerFactory}

/** Interface for running and cancelling a Mathematica command. */
trait MathematicaCommandRunner {
  /**
    * Runs Mathematica command `cmd`, converts the result into KeYmaera X with the converter `m2k`.
    * @param cmd The Mathematica command.
    * @param m2k The converter from Mathematica back to KeYmaera X.
    * @return The result string and the converted result.
    * @tparam T The KeYmaera X expression type.
    * @throws MathematicaComputationAbortedException if the computation was aborted inside Mathematica (e.g., due to timeout)
    * @throws ConversionException if the conversion back from Mathematica (using `converter`) fails
    * @throws ToolExecutionException if the command execution fails or no-ops or returns an unexpected answer format
    * @throws ToolCommunicationException if the communication with the tool fails or the tool is not in a proper state
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

  private val useExprInterface = Configuration.getBoolean(Configuration.Keys.JLINK_USE_EXPR_INTERFACE).getOrElse(false)
  /** @inheritdoc */
  override def doRun[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T) = try {
    if (ml == null) throw ToolCommunicationException("No MathKernel set")
    val qidx: Long = ml.synchronized { JLinkMathematicaCommandRunner.queryIndex += 1; JLinkMathematicaCommandRunner.queryIndex }
    val indexedCmd = MathematicaOpSpec.list(MathematicaOpSpec.long(qidx), cmd)
    // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
    val checkErrorMsgCmd = MathematicaOpSpec.check(indexedCmd, MathematicaOpSpec.exception.op /*, checkedMessagesExpr*/)
    try {
      LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-cmd"), checkErrorMsgCmd.toString)
      ml.synchronized {
        dispatch(checkErrorMsgCmd)
        getAnswer(qidx, m2k, indexedCmd) //@note disposes indexedCmd, do not use (except dispose) afterwards
      }
    } finally {
      //@note dispose in finally instead of after getAnswer, because interrupting thread externally aborts the scheduled task without dispose
      //@note nested cmd is disposed automatically
      checkErrorMsgCmd.dispose()
    }
    //@note during normal execution, this disposes cmd twice (once via checkErrorMsgCmd) but J/Link ensures us this would be acceptable.
  } finally {
    cmd.dispose()
    ml.newPacket() //@note done reading, clear the link for the next computation
  }

  /** @inheritdoc */
  override def cancel(): Boolean = {
    ml.abortEvaluation()
    true
  }

  /** Send command `cmd` for evaluation to Mathematica kernel straight away. */
  private def dispatch(cmd: Expr): Unit = {
    if (ml == null) throw ToolCommunicationException("No MathKernel set")
    try {
      if (useExprInterface) ml.evaluate(cmd)
      else ml.evaluate(cmd.toString)
    } catch {
      case ex: MathLinkException => throw MathematicaMathlinkException("Error executing command " + cmd, ex)
    }
  }

  /**
    * Blocks and returns the answer (as string and as KeYmaera X expression).
    *
    * @param cmdIdx The expected command index to avoid returning stale answers.
    * @param converter Converts Mathematica expressions back to KeYmaera X expressions.
    * @param ctx The context for error messages in exceptions.
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @throws MathematicaComputationAbortedException if the computation was aborted inside Mathematica
    * @throws ToolExecutionException if the command execution fails or no-ops or returns an unexpected answer format
    * @throws ConversionException if the conversion back from Mathematica (using `converter`) fails
    * @return The result as string and converted to the expected result type.
    */
  private def getAnswer[T](cmdIdx: Long, converter: MExpr=>T, ctx: Expr): (String, T) = {
    if (ml == null) throw ToolCommunicationException("No MathKernel set")
    try {
      ml.waitForAnswer()
    } catch {
      case ex: MathLinkException => throw MathematicaMathlinkException("Error executing Mathematica command " + ctx, ex)
    }
    importResult(ml.getExpr,
      res => {
        if (isAborted(res)) {
          throw MathematicaComputationAbortedException(ctx.toString)
        } else if (res == MathematicaOpSpec.exception.op) {
          // an exception occurred, rerun to get the messages
          ml.evaluate(ctx + ";" + fetchMessagesCmd)
          try {
            ml.waitForAnswer()
          } catch {
            case ex: MathLinkException => throw MathematicaMathlinkException("Error obtaining exception details for failed command " + ctx, ex)
          }
          val txtMsg = importResult(ml.getExpr, _.toString)
          if (txtMsg.contains("nsmet")) throw MathematicaInapplicableMethodException("Input " + ctx + " is not solvable with the available methods, cause: " + txtMsg)
          else throw ToolExecutionException("Input " + ctx + " cannot be evaluated, cause: " + txtMsg)
        } else if (res == MathematicaOpSpec.failed.op) {
          throw ToolExecutionException("Command failed: " + ctx)
        } else {
          val head = res.head
          if (head == MathematicaOpSpec.check.op) {
            throw MathematicaUnknownCauseCriticalException("JLink returned input as answer: " + res.toString)
          } else if (MathematicaOpSpec.list.applies(res) && res.args.length == 2 && res.args.head.asInt() == cmdIdx) {
            val theResult = res.args.last
            if (isAborted(theResult)) throw MathematicaComputationAbortedException(ctx.toString)
            else (theResult.toString,
              try {
                converter(theResult)
              } catch {
                case ex: ConversionException => throw ex
                case ex: Throwable => throw ConversionException("Error converting from Mathematica\ncommand: " + ctx + "\nreturned result: " + theResult.toString, ex)
              })
          } else {
            throw MathematicaUnknownCauseCriticalException("Unexpected result: either result length != 2 or JLink returned a stale answer\ncommand: " + ctx + "\nreturned result: " + res.toString)
          }
        }
      })
  }

}
