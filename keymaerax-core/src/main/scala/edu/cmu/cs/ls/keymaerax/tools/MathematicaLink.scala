/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.util.{Date, GregorianCalendar}

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion._

import scala.collection.immutable

/**
 * An abstract interface to Mathematica link implementations.
 * The link may be used synchronously or asychronously.
 * Multiple MathematicaLinks may be created by instantiating multiple copies
 * of implementing classes (depends on license).
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
trait MathematicaLink {
  /** Runs Mathematica command `cmd` without safeguarding by exception checking for Mathematica results. */
  def runUnchecked[T](cmd: String, m2k: M2KConverter[T]): (String, T)
  /** Runs Mathematica command `cmd` converting back with `m2k` using tool `executor`, with Mathematica exception checking.
    * @ensures cmd is freed and should not ever be used again.
    */
  def run[T](cmd: MExpr, m2k: M2KConverter[T], executor: ToolExecutor[(String, T)]): (String, T)

  /** Cancels the current request.
    *
    * @return True if job is successfully cancelled, or False if the new
   * status is unknown.
   */
  def cancel(): Boolean
}

/**
  * Bridge for MathematicaLink, bundles tool executor (thread pools) with converters.
  */
trait KeYmaeraMathematicaBridge[T] {
  /** Runs Mathematica command `cmd` without safeguarding by exception checking for Mathematica results. */
  def runUnchecked(cmd: String): (String, T)
  /** Runs Mathematica command `cmd`, with Mathematica exception checking.
    * @ensures cmd is freed and should not ever be used again.
    */
  def run(cmd: MExpr): (String, T)
}

/**
  * Base class for Mathematica bridges. Running commands is synchronized.
  * @param link The Mathematica link for executing commands.
  * @param k2m Converts KeYmaeraX->Mathematica.
  * @param m2k Converts Mathematica->KeYmaera X.
  */
abstract class BaseKeYmaeraMathematicaBridge[T](val link: MathematicaLink, val k2m: K2MConverter[T],
                                             val m2k: M2KConverter[T]) extends KeYmaeraMathematicaBridge[T] {
  protected val DEBUG = System.getProperty("DEBUG", "false")=="true"
  protected val mathematicaExecutor: ToolExecutor[(String, T)] = ToolExecutor.defaultExecutor()

  override def runUnchecked(cmd: String): (String, T) = link.synchronized { link.runUnchecked(cmd, m2k) }
  override def run(cmd: MExpr): (String, T) = link.synchronized { link.run(cmd, m2k, mathematicaExecutor) }

  def shutdown(): Unit = mathematicaExecutor.shutdown()
}

/**
 * A link to Mathematica using the JLink interface.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class JLinkMathematicaLink extends MathematicaLink {
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  //@todo really should be private -> fix SpiralGenerator
  //@todo concurrent access to ml needs ml access to be synchronized everywhere or pooled or
  private[keymaerax] var ml: KernelLink = null
  private var linkName: String = null
  private var jlinkLibDir: Option[String] = None

  //@note all access to queryIndex must be synchronized
  private var queryIndex: Long = 0

  private val fetchMessagesCmd = "$MessageList"

  /**
   * Initializes the connection to Mathematica.
    *
    * @param linkName The name of the link to use (platform-dependent, see Mathematica documentation)
   * @return true if initialization was successful
   * @note Must be called before first use of ml
   */
  def init(linkName : String, jlinkLibDir : Option[String]): Boolean = {
    this.linkName = linkName
    this.jlinkLibDir = jlinkLibDir
    if (jlinkLibDir.isDefined) {
      System.setProperty("com.wolfram.jlink.libdir", jlinkLibDir.get) //e.g., "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink"
    }
    try {
      ml = MathLinkFactory.createKernelLink(Array[String](
        "-linkmode", "launch",
        "-linkname", linkName + " -mathlink"))
      try {
        ml.discardAnswer()
        //@todo How to gracefully shutdown an unsuccessfully initialized math link again without causing follow-up problems?
        //@note print warnings for license issues instead of shutting down immediately
        isActivated match {
          case Some(true) => isComputing match {
            case Some(true) => true // everything ok
            case Some(false) => println("ERROR: Test computation in Mathematica failed, shutting down.\n Please start a standalone Mathematica notebook and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
              throw new IllegalStateException("Test computation in Mathematica failed.\n Please start a standalone Mathematica notebook and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
            case None => println("WARNING: Unable to determine state of Mathematica, Mathematica may not be working.\n Restart KeYmaera X if you experience problems using arithmetic tactics."); true
          }
          case Some(false) => println("WARNING: Mathematica seems not activated or Mathematica license might be expired, Mathematica may not be working.\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\n If you experience problems during proofs, please renew your Mathematica license and restart KeYmaera X."); true
            //throw new IllegalStateException("Mathematica is not activated or Mathematica license is expired.\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\n Please renew your Mathematica license and restart KeYmaera X.")
          case None => println("WARNING: Mathematica may not be activated or Mathematica license might be expired.\\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\\n Please check your Mathematica license manually."); true
        }
      } catch {
        case e: UnsatisfiedLinkError =>
          val message = "Mathematica J/Link native library was not found in:\n" + System.getProperty("com.wolfram.jlink.libdir", "(undefined)") +
            "\nOr this path did not contain the native library compatible with " + System.getProperties.getProperty("sun.arch.data.model") + "-bit " + System.getProperties.getProperty("os.name") + " " + System.getProperties.getProperty("os.version") +
            diagnostic
          println(message)
          throw e.initCause(new Error(message))
        case e: MathLinkException => println("Mathematica J/Link errored " + e); throw e
      }
    } catch {
      case ex: Throwable => shutdown(); throw ex
    }
  }

  /**
   * Closes the connection to Mathematica.
   */
  def shutdown() = {
    if (ml == null) println("No need to shut down MathKernel if no link has been initialized")
    //if (ml == null) throw new IllegalStateException("Cannot shut down if no MathKernel has been initialized")
    else {
      println("Shutting down Mathematica...")
      val l: KernelLink = ml
      ml = null
      l.terminateKernel()
      l.close()
      println("...Done")
    }
  }

  /** Restarts the Mathematica connection */
  def restart() = {
    val l: KernelLink = ml
    ml = null
    l.terminateKernel()
    init(linkName, jlinkLibDir)
    l.close()
  }

  /**
    * Runs the command and then halts program execution until answer is returned.
    *
    * @param cmd The Mathematica command.
    * @param m2k The converter Mathematica->KeYmaera X
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    */
  def runUnchecked[T](cmd: String, m2k: M2KConverter[T]): (String, T) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.synchronized {
      ml.evaluate(cmd)
      ml.waitForAnswer()
      importResult(ml.getExpr, res => (res.toString, m2k(res)))
    }
  }

  /**
    * Runs a Mathematica command.
    *
    * @param cmd The Mathematica command to run. Disposed as a result of this method.
    * @param m2k The converter Mathematica->KeYmaera X
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    * @note Disposes cmd, do not use afterwards.
    * @see [[run()]]
    */
  def run[T](cmd: MExpr, m2k: M2KConverter[T], executor: ToolExecutor[(String, T)]): (String, T) = run(cmd, executor, m2k)

  /**
    * Runs a Mathematica command on the specified executor, converts the result back with converter.
    *
    * @param cmd The command to run. Disposed as a result of this method.
    * @param executor Executes commands (scheduled).
    * @param converter Converts Mathematica expressions to KeYmaera X expressions.
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    * @ensures cmd is freed and should not ever be used again.
    */
  protected def run[T](cmd: MExpr, executor: ToolExecutor[(String, T)], converter: MExpr=>T): (String, T) = {
    try {
      if (ml == null) throw new IllegalStateException("No MathKernel set")
      val qidx: Long = synchronized {
        queryIndex += 1; queryIndex
      }
      val indexedCmd = new MExpr(Expr.SYM_LIST, Array(new MExpr(qidx), cmd))
      // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
      val checkErrorMsgCmd = new MExpr(MathematicaSymbols.CHECK, Array(indexedCmd, MathematicaSymbols.EXCEPTION /*, checkedMessagesExpr*/))
      try {
        if (DEBUG) println("Sending to Mathematica " + checkErrorMsgCmd)

        val taskId = executor.schedule(_ => {
          dispatch(checkErrorMsgCmd.toString)
          getAnswer(qidx, converter, indexedCmd.toString) //@note disposes indexedCmd, do not use (except dispose) afterwards
        })

        executor.wait(taskId) match {
          case Some(Left(result)) => result
          case Some(Right(throwable)) => throwable match {
            case ex: MathematicaComputationAbortedException =>
              executor.remove(taskId)
              throw ex
            case ex: Throwable =>
              executor.remove(taskId, force = true)
              throw new ToolException("Error executing Mathematica " + checkErrorMsgCmd, throwable)
          }
          case None =>
            //@note Thread is interrupted by another thread (e.g., UI button 'stop')
            cancel()
            executor.remove(taskId, force = true)
            if (DEBUG) println("Initiated aborting Mathematica " + checkErrorMsgCmd)
            throw new MathematicaComputationAbortedException(checkErrorMsgCmd.toString)
        }
      } finally {
        //@note dispose in finally instead of after getAnswer, because interrupting thread externally aborts the scheduled task without dispose
        //@note nested cmd is disposed automatically
        checkErrorMsgCmd.dispose()
      }
      //@note during normal execution, this disposes cmd twice (once via checkErrorMsgCmd) but J/Link ensures us this would be acceptable.
    } finally { cmd.dispose() }
  }

  /** Send command `cmd` for evaluation to Mathematica kernel straight away */
  private def dispatch(cmd: String) = {
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
        //@todo check with MathematicaToKeYmaera.isAborted
        if (res == MathematicaSymbols.ABORTED) {
          throw new MathematicaComputationAbortedException(ctx)
        } else if (res == MathematicaSymbols.EXCEPTION) {
          // an exception occurred
          ml.evaluate(fetchMessagesCmd)
          ml.waitForAnswer()
          val txtMsg = importResult(ml.getExpr, _.toString)
          throw new IllegalArgumentException("Input " + ctx + " cannot be evaluated: " + txtMsg)
        } else {
          val head = res.head
          if (head.equals(MathematicaSymbols.CHECK)) {
            throw new IllegalStateException("Mathematica returned input as answer: " + res.toString)
          } else if (res.head == Expr.SYM_LIST && res.args().length == 2 && res.args.head.asInt() == cmdIdx) {
            val theResult = res.args.last
            //@todo check with MathematicaToKeYmaera.isAborted
            if (theResult == MathematicaSymbols.ABORTED) throw new MathematicaComputationAbortedException(ctx)
            else (theResult.toString, converter(theResult))
          } else {
            throw new IllegalStateException("Mathematica returned a stale answer for " + res.toString)
          }
        }
      })
  }

  def cancel(): Boolean = {
    ml.abortEvaluation()
    true
  }

  /** Returns the version as (Major, Minor, Release) */
  private def getVersion: (String, String, String) = {
    ml.evaluate("$VersionNumber")
    ml.waitForAnswer()
    val (major, minor) = importResult(
      ml.getExpr,
      version => { val versionParts = version.toString.split("\\."); (versionParts(0), versionParts(1)) })
    ml.evaluate("$ReleaseNumber")
    ml.waitForAnswer()
    val release = importResult(ml.getExpr, _.toString)
    //@note using strings to be robust in case Wolfram decides to switch from current major:Double/minor:Int
    (major, minor, release)
  }

  /** Checks if Mathematica is activated by querying the license expiration date */
  private def isActivated: Option[Boolean] = {
    val infinity = new MExpr(new MExpr(Expr.SYMBOL, "DirectedInfinity"), Array(new MExpr(1L)))
    try {
      val version = getVersion

      def licenseExpiredConverter(licenseExpirationDate: MExpr): Option[Boolean] = {
        val date: Array[MExpr] = version match {
          case ("9", _, _) => licenseExpirationDate.args
          case ("10", _, _) => licenseExpirationDate.args.head.args
          case (major, minor, _) => if (DEBUG) println("WARNING: Cannot check license expiration date since unknown Mathematica version " + major + "." + minor + ", only version 9.x and 10.x supported. Mathematica requests may fail if license is expired."); null
        }
        if (date == null) None
        else try {
          if (date.length >= 3 && date(0).integerQ() && date(1).integerQ() && date(2).integerQ()) {
            //@note month in calendar is 0-based, in Mathematica it's 1-based
            val expiration = new GregorianCalendar(date(0).asInt(), date(1).asInt() - 1, date(2).asInt())
            val today = new Date()
            Some(expiration.getTime.after(today))
          } else if (date.length >= 1 && date(0).equals(infinity)) {
            Some(true)
          } else {
            None
          }
        } catch {
          case e: ExprFormatException => println("WARNING: Unable to determine Mathematica expiration date\n cause: " + e); None
        }
        //@note date disposed as part of licenseExpirationDate
      }

      ml.evaluate("$LicenseExpirationDate")
      ml.waitForAnswer()
      importResult(ml.getExpr, licenseExpiredConverter)
    } finally {
      infinity.dispose()
    }
  }

  /** Sends a simple computation to Mathematica to ensure its actually working */
  private def isComputing: Option[Boolean] = {
    try {
      ml.evaluate("6*9")
      ml.waitForAnswer()
      Some(importResult(ml.getExpr, e => e.integerQ() && e.asInt() == 54))
    } catch {
      //@todo need better error reporting, this way it will never show up on UI
      case e: Throwable => println("WARNING: Mathematica may not be functional \n cause: " + e); None
    }
  }
}