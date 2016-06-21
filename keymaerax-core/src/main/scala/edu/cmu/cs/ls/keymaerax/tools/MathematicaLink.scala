/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools

import java.util.{Date, GregorianCalendar}

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaToKeYmaera.{KExpr, MExpr}

import scala.collection.immutable

/**
 * An abstract interface to Mathematica link implementations.
 * The link may be used syncrhonously or asychronously.
 * Each MathematicaLink 
 * Multiple MathematicaLinks may be created by instantiating multiple copies
 * of implementing classes.
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
trait MathematicaLink {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  type MExpr = com.wolfram.jlink.Expr

  def runUnchecked(cmd : String) : (String, KExpr)
  def run(cmd : MExpr) : (String, KExpr)

  //@todo Code Review: should probably be removed from the interface
  //@solution: removed ready from interface, removed empty implementations from derived classes

  /** Cancels the current request.
    *
    * @return True if job is successfully cancelled, or False if the new
   * status is unknown.
   */
  def cancel(): Boolean
}

/**
 * A link to Mathematica using the JLink interface.
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
abstract class JLinkMathematicaLink(val k2m: KExpr => MExpr, val m2k: MExpr => KExpr) extends MathematicaLink {
  protected val DEBUG = System.getProperty("DEBUG", "true")=="true"
  protected val TIMEOUT = 10

  //@todo really should be private -> fix SpiralGenerator
  private[keymaerax] var ml: KernelLink = null
  private var linkName: String = null
  private var jlinkLibDir: Option[String] = None

  protected val mathematicaExecutor: ToolExecutor[(String, KExpr)] = ToolExecutor.defaultExecutor()

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
      ml.discardAnswer()
      isActivated match {
        case Some(true) => isComputing match {
          case Some(true) => true // everything ok
          case Some(false) => throw new IllegalStateException("Test computation in Mathematica failed.\n Please start a standalone Mathematica notebook and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
          case None => if (DEBUG) println("Unable to determine state of Mathematica, Mathematica may not be working.\n Restart KeYmaera X if you experience problems using arithmetic tactics."); true
        }
        case Some(false) => throw new IllegalStateException("Mathematica is not activated or Mathematica license is expired.\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\n Please renew your Mathematica license and restart KeYmaera X.")
        case None => if (DEBUG) println("Mathematica may not be activated or Mathematica license might be expired.\\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\\n Please check your Mathematica license manually."); true
      }
    } catch {
      case e:UnsatisfiedLinkError =>
        val message = "Mathematica J/Link native library was not found in:\n" + System.getProperty("com.wolfram.jlink.libdir", "(undefined)") +
          "\nOr this path did not contain the native library compatible with " + System.getProperties.getProperty("sun.arch.data.model") + "-bit " + System.getProperties.getProperty("os.name") + " " + System.getProperties.getProperty("os.version") +
          diagnostic
        println(message)
        throw e.initCause(new Error(message))
      case e:MathLinkException => println("Mathematica J/Link errored " + e); throw e
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
      mathematicaExecutor.shutdown()
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
    * @return The result, as string and as KeYmaera X expression.
    */
  def runUnchecked(cmd: String): (String, KExpr) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.synchronized {
      ml.evaluate(cmd)
      ml.waitForAnswer()
      safeResult(ml.getExpr, res => (res.toString, m2k(res)))
    }
  }

  /**
    * Runs a Mathematica command.
    *
    * @param cmd The Mathematica command to run. Disposed as a result of this method.
    * @return The result, as string and as KeYmaera X expression.
    * @note Disposes cmd, do not use afterwards.
    * @see [[run()]]
    */
  def run(cmd: MExpr): (String, KExpr) = run(cmd, mathematicaExecutor, m2k)

  /**
    * Runs a Mathematica command on the specified executor, converts the result back with converter.
    *
    * @param cmd The command to run. Disposed as a result of this method.
    * @param executor Executes commands (scheduled).
    * @param converter Converts Mathematica expressions to KeYmaera X expressions.
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    * @note Disposes cmd, do not use afterwards.
    */
  protected def run[T](cmd: MExpr, executor: ToolExecutor[(String, T)], converter: MExpr=>T): (String, T) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    //@todo Code Review: querIndex increment should be synchronized
    //@solution: synchronized increment on global idx, then use local idx throughout instead; added a note to global queryIndex that all access must be synchronized
    val qidx: Long = synchronized { queryIndex += 1; queryIndex }
    val indexedCmd = new MExpr(Expr.SYM_LIST, Array(new MExpr(qidx), cmd))
    // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
    val checkErrorMsgCmd = new MExpr(MathematicaSymbols.CHECK, Array(indexedCmd, MathematicaSymbols.EXCEPTION /*, checkedMessagesExpr*/))
    if (DEBUG) println("Sending to Mathematica " + checkErrorMsgCmd)

    val taskId = executor.schedule(_ => {
      dispatch(checkErrorMsgCmd.toString)
      getAnswer(qidx, converter, indexedCmd.toString) //@note disposes indexedCmd, do not use (except dispose) afterwards
    })

    try {
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
      indexedCmd.dispose()
      checkErrorMsgCmd.dispose()
    }
  }

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
    */
  private def getAnswer[T](cmdIdx: Long, converter: MExpr=>T, ctx: String): (String, T) = {
    //@todo Properly dispose input in caller
    //@solution sole caller run() disposes input (+ other Expr) now in a finally block after the answer is retrieved
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.waitForAnswer()
    safeResult(ml.getExpr,
      res => {
        if (res == MathematicaSymbols.ABORTED) {
          //@todo Code Review do not hand MExpr to exceptions
          //@solution: exceptions accept message instead of Expr, cleaned up getAnswer interface (Expr not necessary)
          throw new MathematicaComputationAbortedException(ctx)
        } else if (res == MathematicaSymbols.EXCEPTION) {
          // an exception occurred
          ml.evaluate(fetchMessagesCmd)
          ml.waitForAnswer()
          val txtMsg = safeResult(ml.getExpr, _.toString)
          throw new IllegalArgumentException("Input " + ctx + " cannot be evaluated: " + txtMsg)
        } else {
          val head = res.head
          if (head.equals(MathematicaSymbols.CHECK)) {
            throw new IllegalStateException("Mathematica returned input as answer: " + res.toString)
          } else if (res.head == Expr.SYM_LIST && res.args().length == 2 && res.args.head.asInt() == cmdIdx) {
            val theResult = res.args.last
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
    val (major, minor) = safeResult(
      ml.getExpr,
      version => { val versionParts = version.toString.split("\\."); (versionParts(0), versionParts(1)) })
    ml.evaluate("$ReleaseNumber")
    ml.waitForAnswer()
    val release = safeResult(ml.getExpr, _.toString)
    //@note using strings to be robust in case Wolfram decides to switch from current major:Double/minor:Int
    (major, minor, release)
  }

  /** Checks if Mathematica is activated by querying the license expiration date */
  private def isActivated: Option[Boolean] = {
    val infinity = new MExpr(new MExpr(Expr.SYMBOL, "DirectedInfinity"), Array(new MExpr(1L)))
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
        case e: ExprFormatException => if (DEBUG) println("WARNING: Unable to determine Mathematica expiration date\n cause: " + e); None
      }
      //@note date disposed as part of licenseExpirationDate
    }

    ml.evaluate("$LicenseExpirationDate")
    ml.waitForAnswer()
    try {
      safeResult(ml.getExpr, licenseExpiredConverter)
    } finally {
      infinity.dispose()
    }
  }

  /** Sends a simple computation to Mathematica to ensure its actually working */
  private def isComputing: Option[Boolean] = {
    try {
      ml.evaluate("6*9")
      ml.waitForAnswer()
      Some(safeResult(ml.getExpr, e => e.integerQ() && e.asInt() == 54))
    } catch {
      //@todo need better error reporting, this way it will never show up on UI
      case e: Throwable => if (DEBUG) println("WARNING: Mathematica may not be functional \n cause: " + e); None
    }
  }

  /** Reads a result from e using the specified conversion, disposes e. */
  private def safeResult[T](e: MExpr, conversion: MExpr=>T): T = try { conversion(e) } finally { e.dispose() }
}