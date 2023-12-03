/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink.{Expr, KernelLink, MathLinkException}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import org.slf4j.{LoggerFactory, MarkerFactory}

/** Interface for running and cancelling a Mathematica command. */
trait MathematicaCommandRunner {
  /**
    * Runs Mathematica command `cmd`, converts the result into KeYmaera X with the converter `m2k`.
    * @param cmd The Mathematica command.
    * @param m2k The converter from Mathematica back to KeYmaera X.
    * @return The result string and the converted result.
    * @tparam T The KeYmaera X expression type.
    * @throws MathematicaComputationTimedOutException if the computation timed out in Mathematica
    * @throws MathematicaComputationAbortedException if the computation was aborted inside Mathematica
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
  final override def run[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T) =
    doRun(memoryConstrained(timeConstrained(cmd)), m2k)

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

  private val logMarkerName = "mathematica-qe-cmd"
  private val useExprInterface = Configuration
    .getBoolean(Configuration.Keys.JLINK_USE_EXPR_INTERFACE)
    .getOrElse(false)

  /** @inheritdoc */
  override def doRun[T](cmd: MExpr, m2k: M2KConverter[T]): (String, T) = try {
    ensureKernel()

    val queryIndex: Long = ml.synchronized {
      JLinkMathematicaCommandRunner.queryIndex += 1
      JLinkMathematicaCommandRunner.queryIndex
    }

    // {index, command}
    val indexedCmd = MathematicaOpSpec.list(MathematicaOpSpec.long(queryIndex), cmd)

    // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
    val checkErrorMsgCmd = MathematicaOpSpec.check(indexedCmd, MathematicaOpSpec.exception.op /*, checkedMessagesExpr*/)

    disposeAfter(checkErrorMsgCmd, expr => {
      LoggerFactory.getLogger(getClass)
        .debug(MarkerFactory.getMarker(logMarkerName), expr.toString)

      ml.synchronized {
        dispatch(expr)
        getAnswer(queryIndex, m2k, indexedCmd) //@note disposes indexedCmd, do not use (except dispose) afterwards
      }
    })

    // @note during normal execution, this disposes cmd twice (once via checkErrorMsgCmd)
    // but J/Link ensures us this would be acceptable.
  } finally {
    cmd.dispose()
    ml.newPacket() //@note done reading, clear the link for the next computation
  }

  /** @inheritdoc */
  override def cancel(): Boolean = {
    ml.abortEvaluation()
    true
  }

  /** Throws an exception if kernel is `null` */
  @inline private def ensureKernel(): Unit = {
    if (ml == null) {
      throw ToolCommunicationException("No MathKernel set!")
    }
  }

  /** Applies an expression converter, throws [[ConversionException]] if something goes wrong */
  private def apply[T](converter: MExpr => T, expr: MExpr, ctx: Expr = null): T = try {
    converter(expr)
  } catch {
    case ex: ConversionException =>
      throw ex
    case th: Throwable =>
      throw ConversionException(s"Error converting from Mathematica\ncommand: $ctx\nreturned result: $expr", th)
  }

  /** Send command `cmd` for evaluation to Mathematica kernel straight away. */
  private def dispatch(cmd: Expr): Unit = {
    ensureKernel()

    try {
      if (useExprInterface) {
        ml.evaluate(cmd)
      } else {
        ml.evaluate(cmd.toString)
      }
    } catch {
      case ex: MathLinkException =>
        throw MathematicaMathlinkException(s"Error executing command $cmd", ex)
    }
  }

  /** Wait for an answer and return its expression. */
  private def await(ctx: Expr = null): Expr = {
    ensureKernel()

    try {
      ml.waitForAnswer()
    } catch {
      case ex: MathLinkException =>
        throw MathematicaMathlinkException(s"Error executing Mathematica command: $ctx", ex)
    }

    ml.getExpr
  }

  /**
    * Blocks and returns the answer (as string and as KeYmaera X expression).
    *
    * @param cmdIdx The expected command index to avoid returning stale answers.
    * @param converter Converts Mathematica expressions back to KeYmaera X expressions.
    * @param ctx The context for error messages in exceptions.
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @throws MathematicaComputationTimedOutException if the computation timed out in Mathematica
    * @throws MathematicaComputationAbortedException if the computation was aborted inside Mathematica
    * @throws ToolExecutionException if the command execution fails or no-ops or returns an unexpected answer format
    * @throws ConversionException if the conversion back from Mathematica (using `converter`) fails
    * @return The result as string and converted to the expected result type.
    */
  private def getAnswer[T](cmdIdx: Long, converter: MExpr => T, ctx: Expr): (String, T) =
    disposeAfter(await(ctx), res => {
      if (isTimedOut(res)) {
        throw MathematicaComputationTimedOutException(ctx.toString)
      }

      if (isAborted(res)) {
        throw MathematicaComputationAbortedException(ctx.toString)
      }

      if (isException(res)) {
        // an exception occurred, rerun to get the messages
        ml.evaluate(s"$ctx;$$MessageList")

        // throw a more detailed error
        val txtMsg = disposeAfter(await(ctx), _.toString)
        if (txtMsg.contains("nsmet")) {
          throw MathematicaInapplicableMethodException(s"Input $ctx is not solvable with the available methods, cause: $txtMsg")
        }

        // default to tool exception
        throw ToolExecutionException(s"Input $ctx cannot be evaluated, cause: $txtMsg")
      }

      if (isFailed(res)) {
        throw ToolExecutionException(s"Command failed: $ctx")
      }

      if (MathematicaOpSpec.check.applies(res)) {
        throw MathematicaUnknownCauseCriticalException(s"JLink returned input as answer: $res")
      }

      // check for an indexed response {index, expr}
      if (MathematicaOpSpec.list.applies(res) &&
        res.args.length == 2 &&
        res.args.head.asInt() == cmdIdx) {

        val theResult = res.args.last
        if (isTimedOut(theResult)) {
          throw MathematicaComputationTimedOutException(ctx.toString)
        }

        if (isAborted(theResult)) {
          throw MathematicaComputationAbortedException(ctx.toString)
        }

        // Return string representation and converted
        (theResult.toString, apply(converter, theResult, ctx))
      } else {
        throw MathematicaUnknownCauseCriticalException(s"Unexpected result: either result length != 2 or JLink returned a stale answer\ncommand: $ctx\nreturned result: $res")
      }
    })
}
