/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.qe._
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import spray.json.{JsArray, JsFalse, JsNull, JsNumber, JsString, JsTrue, JsValue, JsonParser}

import java.io.{File, FileWriter, IOException}
import java.time.LocalDate
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.sys.process._

/**
 * An abstract interface to Mathematica link implementations.
 * The link may be used synchronously or asynchronously.
 * Multiple MathematicaLinks may be created by instantiating multiple copies
 * of implementing classes (depends on license).
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
trait MathematicaLink {
  /** Runs Mathematica command `cmd` without safeguarding by exception checking for Mathematica results. */
  def runUnchecked[T](cmd: String, m2k: M2KConverter[T]): (String, T)

  /** Runs command `cmd` converting back with `m2k` using tool `executor`, with Mathematica exception checking.
    * @ensures cmd is freed and should not ever be used again.
    */
  def run[T](cmd: () => T, executor: ToolExecutor): T

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
  /** Default timeout for Mathematica requests: no timeout. */
  val TIMEOUT_OFF: Int = -1
  /** Timeout for Mathematica requests in seconds, set to TIMEOUT_OFF to disable. */
  var timeout: Int = TIMEOUT_OFF
  /** Default memory limit: no limit. */
  val MEMORY_LIMIT_OFF: Long = -1
  /** Memory limit for Mathematica requests in MB, set to MEMORY_LIMIT_OFF to disable. */
  var memoryLimit: Long = MEMORY_LIMIT_OFF

  protected val DEBUG: Boolean = Configuration(Configuration.Keys.DEBUG) == "true"
  protected var mathematicaExecutor: ToolExecutor = _

  /** @inheritdoc */
  override def runUnchecked(cmd: String): (String, T) = runUnchecked(cmd, m2k)

  /** @inheritdoc */
  override def run(cmd: MExpr): (String, T) = run(cmd, m2k)

  /** Run `cmd` with a local converter back from Mathematica. */
  private[tools] def runUnchecked[S](cmd: String, localm2k: M2KConverter[S]): (String, S) =
    link.runUnchecked(memoryConstrained(timeConstrained(cmd)), localm2k)

  /** Run `cmd` with a local converter back from Mathematica. */
  private[tools] def run[S](cmd: MExpr, localm2k: M2KConverter[S]): (String, S) = {
    val commandRunner = link match {
      case j: JLinkMathematicaLink => JLinkMathematicaCommandRunner(j.ml)
    }
    (cmd.toString, link.run(() => {
      try {
        commandRunner.run(memoryConstrained(timeConstrained(cmd)), localm2k)._2
      } catch {
        case ex: IllegalArgumentException =>
          throw ConversionException("Error executing " + cmd.toString + " command", ex)
      }
    }, mathematicaExecutor))
  }

  def availableWorkers: Int = mathematicaExecutor.availableWorkers()
  def init(): Boolean = { mathematicaExecutor = new ToolExecutor(1); true }
  def shutdown(): Unit = if (mathematicaExecutor != null) mathematicaExecutor.shutdown()

  protected def timeConstrained(cmd: MExpr): MExpr =
    if (timeout < 0) cmd
    else MathematicaOpSpec.timeConstrained(cmd, MathematicaOpSpec.int(timeout))

  protected def timeConstrained(cmd: String): String =
    if (timeout < 0) cmd
    else s"TimeConstrained[$cmd, $timeout, ${MathematicaOpSpec.timedOut.op}]"

  protected def memoryConstrained(cmd: MExpr): MExpr =
    if (memoryLimit < 0) cmd
    else MathematicaOpSpec.memoryConstrained(cmd, MathematicaOpSpec.long(memoryLimit*1000000))

  protected def memoryConstrained(cmd: String): String =
    if (memoryLimit < 0) cmd
    else s"MemoryConstrained[$cmd, ${memoryLimit*1000000}]"
}

/**
 * A link to Mathematica using the JLink interface.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class JLinkMathematicaLink(val engineName: String) extends MathematicaLink with Logging {
  //@note using strings to be robust in case Wolfram decides to switch from current major:Double/minor:Int
  private case class Version(major: String, minor: String, revision: String) {
    override def toString: String = s"$major.$minor"
  }

  private val DEFAULT_PORT = "1234"

  //@todo really should be private -> fix SpiralGenerator
  //@todo concurrent access to ml needs ml access to be synchronized everywhere or pooled or
  private[keymaerax] var ml: KernelLink = _
  private var linkName: String = _
  private var jlinkLibDir: Option[String] = None
  private var tcpip: String = ""

  //@note all access to queryIndex must be synchronized
  private var queryIndex: Long = 0

  private val fetchMessagesCmd = "$MessageList"

  private var mathProcess: Option[Process] = None

  /** Starts a kernel process if connecting over TCPIP. */
  private def startKernel(linkName: String, port: String): Option[Process] = {
    val cmd = linkName::"-mathlink"::"-linkmode"::"listen"::"-linkname"::port::"-linkprotocol"::"tcpip"::Nil
    val result: StringBuilder = new StringBuilder()
    val pl = ProcessLogger(s => result.append(s))
    val p = cmd.run(pl) // start asynchronously, log output to logger
    Some(p)
  }

  /**
    * Initializes the connection to Mathematica.
    * @param linkName The name of the link to use (platform-dependent, see Mathematica documentation, or a port number if on TCPIP)
    * @return true if initialization was successful
    * @note Must be called before first use of ml
    */
  def init(linkName: String, jlinkLibDir: Option[String], tcpip: String, remainingTrials: Int=5): Boolean = {
    this.linkName = linkName
    this.jlinkLibDir = jlinkLibDir
    this.tcpip = tcpip
    // set native library VM property for JLink
    if (jlinkLibDir.isDefined) {
      System.setProperty("com.wolfram.jlink.libdir", jlinkLibDir.get) //e.g., "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink"
    }
    try {
      ml = if (tcpip.nonEmpty && tcpip != "false") {
        logger.info("Connecting to Math Kernel over TCPIP to " + tcpip)
        val port::machine = tcpip match {
          case "true" => DEFAULT_PORT::Nil
          case _ => tcpip.split("@").toList
        }
        val args =
          if (machine.isEmpty) {
            startKernel(linkName, port) match {
              case Some(process: Process) =>
                for (_ <- 1 to 10; if !process.isAlive()) {
                  Thread.sleep(200) // wait for MathKernel to stay alive
                }
                if (process.isAlive()) mathProcess = Some(process)
                else {
                  mathProcess = None
                  throw new IllegalStateException(engineName + " terminated with exit code " + process.exitValue() + "; check that your license is valid and your computer is online for license checking")
                }
              case _ => mathProcess = None
            }
            ("-linkmode"::"connect"::"-linkprotocol"::"tcpip"::"-linkname"::port::Nil).toArray
          } else {
            ("-linkmode"::"connect"::"-linkprotocol"::"tcpip"::"-linkname"::tcpip::Nil).toArray
          }
        MathLinkFactory.createKernelLink(args)
      } else {
        logger.info("Launching " + engineName)
        val args = ("-linkmode" :: "launch" :: "-linkprotocol" :: "tcpip" :: "-linkname" :: "\""+linkName+"\" -mathlink" :: Nil).toArray
        MathLinkFactory.createKernelLink(args)
      }

      ml.synchronized {
        ml.connect()
        ml.discardAnswer()
        //@todo How to gracefully shutdown an unsuccessfully initialized math link again without causing follow-up problems?
        //@note print warnings for license issues instead of shutting down immediately
        val version = getVersion
        isActivated(version) match {
          case Some((true, date)) =>
            isComputing match {
              case Some(true) =>
                logger.info("Connected to " + engineName + " v" + version + " (TCPIP=" + tcpip + ", license expires " + date + ")")
                true // everything ok
              case Some(false) => logger.error("ERROR: Test computation in " + engineName + " failed, shutting down.\n Please start a standalone "  + engineName + " notebook and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
                throw new IllegalStateException("Test computation in "  + engineName + " failed.\n Please start a standalone " + engineName + " notebook and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
              case None => logger.warn("WARNING: Unable to determine state of " + engineName + ", " + engineName + " may not be working.\n Restart KeYmaera X if you experience problems using arithmetic tactics."); true
            }
          case Some((false, date)) => logger.warn("WARNING: " + engineName + " seems not activated or license might be expired (expires " + date + "), " + engineName + " may not be working.\n A valid license is necessary to use " + engineName + " as backend of KeYmaera X.\n If you experience problems during proofs, please renew your license and restart KeYmaera X."); true
          //throw new IllegalStateException("Mathematica is not activated or Mathematica license is expired.\n A valid license is necessary to use Mathematica as backend of KeYmaera X.\n Please renew your Mathematica license and restart KeYmaera X.")
          case None => logger.warn("WARNING: " + engineName + " may not be activated or license might be expired.\n A valid license is necessary to use " + engineName + " as backend of KeYmaera X.\n Please check your license manually."); true
        }
      }
    } catch {
      case e: UnsatisfiedLinkError =>
        logger.error("Shutting down since " + engineName + " J/Link native library was not found in:\n" + jlinkLibDir +
          "\nOr this path did not contain the native library compatible with " + System.getProperties.getProperty("sun.arch.data.model") + "-bit " + System.getProperties.getProperty("os.name") + " " + System.getProperties.getProperty("os.version") +
          diagnostic +
          "\nPlease provide paths to the J/Link native library in " + Configuration.KEYMAERAX_HOME_PATH + File.separator + "keymaerax.conf and restart KeYmaera X.", e)
        shutdown()
        false
      case e: MathLinkException if e.getErrCode == 1004 && e.getMessage.contains("Link failed to open") && remainingTrials > 0 =>
        // link did not open, wait a little and retry
        logger.info("Repeating connection attempt\n" + engineName + " J/Link failed to open " + e +
          "\nRepeating connection attempt (remaining trials: " + (remainingTrials-1) + ")\n" + diagnostic)
        Thread.sleep(10000)
        init(linkName, jlinkLibDir, tcpip, remainingTrials-1)
      case e: MathLinkException =>
        logger.error("Shutting down since " + engineName + " J/Link errored " + e + "\nPlease double check configuration and license.\n" + diagnostic, e)
        shutdown()
        false
      case ex: IOException =>
        logger.error("Shutting down since " + engineName + " was not reachable under the configured path. \nPlease double check configuration paths.\n" + diagnostic, ex)
        shutdown()
        false
      case ex: Throwable =>
        logger.warn("Unknown error " + ex + "\n" + engineName + " may or may not be working. If you experience problems, please double check configuration paths and license.\n" + diagnostic, ex)
        true
    }
  }

  /**
   * Closes the connection to Mathematica.
   */
  def shutdown(): Unit = {
    if (ml == null) logger.trace("No need to shut down MathKernel if no link has been initialized")
    else {
      logger.debug("Shutting down " + engineName + "...")
      val l: KernelLink = ml
      ml = null
      l.abandonEvaluation()
      l.terminateKernel()
      l.close()
      logger.info("Disconnected from " + engineName)
    }
    mathProcess match {
      case Some(p) =>
        mathProcess = None
        p.destroy()
      case None =>
    }
  }

  /** Restarts the Mathematica connection */
  def restart(): Unit = {
    // only stable with MATH_LINK_TCPIP, may fail due to Mathematica JLink segmentation fault otherwise
    shutdown()
    Thread.sleep(2000) // try to avoid Mathematica segmentation fault by waiting
    init(linkName, jlinkLibDir, tcpip)
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
      disposeAfter(ml.getExpr, res => (res.toString, m2k(res)))
    }
  }

  /**
    * Runs a Mathematica command on the specified executor, converts the result back with converter.
    *
    * @param cmd The command to run. Disposed as a result of this method.
    * @param executor Executes commands (scheduled).
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    * @ensures cmd is freed and should not ever be used again.
    */
  override def run[T](cmd: () => T, executor: ToolExecutor): T = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    val taskId = executor.schedule(_ => { ml.synchronized { cmd() } })

    executor.wait(taskId) match {
      case Some(Left(result)) =>
        executor.remove(taskId)
        result
      case Some(Right(throwable)) => throwable match {
        case ex: ToolInternalException =>
          // internal: Mathematica still functional
          executor.remove(taskId)
          throw ex
        case ex: ToolExternalException =>
          // external but Mathematica still functional
          executor.remove(taskId)
          throw ex
        case ex: ToolCriticalException =>
          logger.warn(ex.getMessage, ex)
          executor.remove(taskId, force = true)
          try {
            restart()
          } catch {
            case ex: Throwable =>
              throw ToolExecutionException("Restarting " + engineName + " failed. Please restart KeYmaera X. If the problem persists, try Z3 instead of " + engineName + " (KeYmaera X->Preferences). " + engineName + " error that triggered the restart:\n" + ex.getMessage, ex)
          }
          throw ToolCommunicationException("Restarted " + engineName + ", please rerun the failed command (error details below)", ex)
      }
      case None =>
        //@note Thread is interrupted by another thread (e.g., UI button 'stop')
        cancel()
        executor.remove(taskId, force = true)
        logger.debug("Initiated aborting "  + engineName)
        throw MathematicaComputationUserAbortException("Mathematica task aborted")
    }
  }

  def cancel(): Boolean = {
    if (ml != null) ml.abortEvaluation()
    true
  }

  /** Returns the version. */
  private def getVersion: Version = {
    ml.evaluate(MathematicaOpSpec.versionNumber.op.toString)
    ml.waitForAnswer()
    val (major, minor) = disposeAfter(
      ml.getExpr,
      version => {
        logger.debug("Running " + engineName + " version " + version.toString)
        val versionParts = version.toString.split("\\.")
        if (versionParts.length >= 2) (versionParts(0), versionParts(1))
        else ("Unknown", "Unknown")
      })
    ml.evaluate(MathematicaOpSpec.releaseNumber.op.toString)
    ml.waitForAnswer()
    val release = disposeAfter(ml.getExpr, _.toString)
    Version(major, minor, release)
  }

  /** Checks if Mathematica is activated by querying the license expiration date */
  private def isActivated(version: Version): Option[(Boolean, LocalDate)] = {
    val infinity = ExprFactory.makeExpr(new MExpr(Expr.SYMBOL, "DirectedInfinity"), Array(new MExpr(1L)))
    try {
      def toDate(date: Array[MExpr]): Option[LocalDate] = {
        logger.debug(engineName + " license expires: " + date.mkString)
        if (date.length >= 3 && date(0).integerQ() && date(1).integerQ() && date(2).integerQ()) {
          Some(LocalDate.of(date(0).asInt(), date(1).asInt(), date(2).asInt()))
        } else {
          None
        }
      }

      def checkExpired(date: Option[LocalDate]): Option[(Boolean, LocalDate)] = {
        date.map(d => d.isAfter(LocalDate.now()) -> d)
      }

      def checkInfinity(date: MExpr): Boolean = {
        date == infinity || date.head == infinity || date.args().exists(checkInfinity)
      }

      def licenseExpiredConverter(licenseExpirationDate: MExpr): Option[(Boolean, LocalDate)] = try {
        version match {
          case _ if checkInfinity(licenseExpirationDate) => Some(true, LocalDate.MAX)
          case Version("9", _, _)  => checkExpired(toDate(licenseExpirationDate.args))
          case Version("10", _, _) => checkExpired(toDate(licenseExpirationDate.args.head.args))
          case Version("11", _, _) => checkExpired(toDate(licenseExpirationDate.args.head.args))
          case Version("12", _, _) => checkExpired(toDate(licenseExpirationDate.args.head.args))
          case Version(major, minor, _) =>
            logger.debug("WARNING: Cannot check license expiration date since unknown " + engineName + " version " + major + "." + minor + ", only version 9.x, 10.x, and 11.x supported. " + engineName + " requests may fail if license is expired.")
            None
        }
        //@note date disposed as part of licenseExpirationDate
      } catch {
        case e: ExprFormatException => logger.warn("WARNING: Unable to determine " + engineName + " expiration date\n cause: " + e, e); None
      }

      ml.evaluate(MathematicaOpSpec.licenseExpirationDate.op.toString)
      ml.waitForAnswer()
      disposeAfter(ml.getExpr, licenseExpiredConverter)
    } finally {
      infinity.dispose()
    }
  }

  /** Sends a simple computation to Mathematica to ensure its actually working */
  private def isComputing: Option[Boolean] = {
    try {
      ml.evaluate("6*9")
      ml.waitForAnswer()
      Some(disposeAfter(ml.getExpr, e => e.integerQ() && e.asInt() == 54))
    } catch {
      //@todo need better error reporting, this way it will never show up on UI
      case e: Throwable => logger.warn("WARNING: " + engineName + " may not be functional \n cause: " + e, e); None
    }
  }
}

/**
  * A link to Wolfram Engine via WolframScript.
  * @author Stefan Mitsch
  */
class WolframScript extends MathematicaLink with Logging {
  //@note using strings to be robust in case Wolfram decides to switch from current major:Double/minor:Int
  case class Version(major: String, minor: String, revision: String) {
    override def toString: String = s"$major.$minor"
  }

  //@note all access to queryIndex must be synchronized
  private var queryIndex: Long = 0

  private val fetchMessagesCmd = "$MessageList"

  /** The currently running Wolfram Engine process. */
  private var wolframProcess: Option[Process] = None

  /**
    * Initializes the connection to Wolfram Engine.
    * @return true if initialization was successful
    * @note Must be called before first use of [[run]]
    */
  def init(remainingTrials: Int=5): Boolean = {
    try {
      val version = getVersion
      isActivated(version) match {
        case Some((true, date)) =>
          isComputing match {
            case Some(true) =>
              logger.info("Connected to Wolfram Engine v" + version + " (license expires " + date + ")")
              true // everything ok
            case Some(false) => logger.error("ERROR: Test computation in Wolfram Engine failed, shutting down.\n Please start a standalone Wolfram Engine and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
              throw new IllegalStateException("Test computation in Wolfram Engine failed.\n Please start a standalone Wolfram Engine and check that it can compute simple facts, such as 6*9. Then restart KeYmaera X.")
            case None => logger.warn("WARNING: Unable to determine state of Wolfram Engine, Wolfram Engine may not be working.\n Restart KeYmaera X if you experience problems using arithmetic tactics."); true
          }
        case Some((false, date)) => logger.warn("WARNING: Wolfram Engine seems not activated or license might be expired (expires " + date + "), Wolfram Engine may not be working.\n A valid license is necessary to use Wolfram Engine as backend of KeYmaera X.\n If you experience problems during proofs, please renew your license and restart KeYmaera X."); true
        case None => logger.warn("WARNING: Wolfram Engine may not be activated or license might be expired.\n A valid license is necessary to use Wolfram Engine as backend of KeYmaera X.\n Please check your license manually."); true
      }
    } catch {
      case e: MathLinkException if e.getErrCode == 1004 && e.getMessage.contains("Link failed to open") && remainingTrials > 0 =>
        // link did not open, wait a little and retry
        logger.info("Repeating connection attempt\nWolfram Engine failed to open " + e +
          "\nRepeating connection attempt (remaining trials: " + (remainingTrials-1) + ")\n" + diagnostic)
        Thread.sleep(10000)
        init(remainingTrials-1)
      case ex: Throwable =>
        logger.warn("Unknown error " + ex + "\nWolfram Engine may or may not be working. If you experience problems, please double check configuration paths and license.\n" + diagnostic, ex)
        true
    }
  }

  /** Closes the connection to Wolfram Engine. */
  def shutdown(): Unit = {}

  /** Restarts the Wolfram Engine connection */
  def restart(): Unit = {}

  /**
    * Runs the command and then halts program execution until answer is returned.
    *
    * @param cmd The WolframScript command.
    * @param m2k The converter Mathematica->KeYmaera X
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    */
  def runUnchecked[T](cmd: String, m2k: M2KConverter[T]): (String, T) = {
    wolframProcess.synchronized {
      val result = evaluate(cmd)
      disposeAfter(result, res => (res.toString, m2k(res)))
    }
  }

  /**
    * Runs a Mathematica command on the specified executor.
    *
    * @param cmd The command to run. Disposed as a result of this method.
    * @param executor Executes commands (scheduled).
    * @tparam T The exact KeYmaera X expression type expected as result.
    * @return The result, as string and as KeYmaera X expression.
    * @ensures cmd is freed and should not ever be used again.
    */
  override def run[T](cmd: () => T, executor: ToolExecutor): T = {
    val taskId = executor.schedule(_ => { wolframProcess.synchronized { cmd() } })

    executor.wait(taskId) match {
      case Some(Left(result)) =>
        executor.remove(taskId)
        result
      case Some(Right(throwable)) => throwable match {
        case ex: ToolInternalException =>
          executor.remove(taskId)
          throw ex
        case ex: ToolExternalException =>
          logger.warn(ex.getMessage, ex)
          executor.remove(taskId, force = true)
          try {
            restart()
          } catch {
            case restartEx: Throwable =>
              throw ToolExecutionException("Restarting Wolfram Engine failed. Please restart KeYmaera X. If the problem persists, try Z3 instead of Wolfram Engine (Help->Tools). Wolfram Engine error that triggered the restart:\n" + ex.getMessage, restartEx)
          }
          throw ToolCommunicationException("Restarted Wolfram Engine, please rerun the failed command (error details below)", throwable)
      }
      case None =>
        //@note Thread is interrupted by another thread (e.g., UI button 'stop')
        cancel()
        executor.remove(taskId, force = true)
        logger.debug("Initiated aborting Wolfram Engine")
        throw MathematicaComputationUserAbortException("Computation aborted")
    }
  }

  def cancel(): Boolean = wolframProcess match {
    case Some(p) =>
      wolframProcess = None
      p.destroy()
      true
    case None => true
  }

  /** Returns the version. */
  def getVersion: Version = {
    val mmResult = evaluate(MathematicaOpSpec.versionNumber.op.toString)
    val (major, minor) = disposeAfter(
      mmResult,
      version => {
        logger.debug("Running Wolfram Engine version " + version.toString)
        val versionParts = version.toString.split("\\.")
        if (versionParts.length >= 2) (versionParts(0), versionParts(1))
        else if (versionParts.nonEmpty) (versionParts(0), "0")
        else ("Unknown", "Unknown")
      })
    val rResult = evaluate(MathematicaOpSpec.releaseNumber.op.toString)
    val release = disposeAfter(rResult, _.toString)
    Version(major, minor, release)
  }

  /** Checks if Wolfram Engine is activated by querying the license expiration date */
  private def isActivated(version: Version): Option[(Boolean, LocalDate)] = {
    val infinity = ExprFactory.makeExpr(new MExpr(Expr.SYMBOL, "DirectedInfinity"), Array(new MExpr(1L)))
    try {
      def toDate(date: Array[MExpr]): Option[LocalDate] = {
        logger.debug("Wolfram Engine license expires: " + date.mkString)
        if (date.length >= 3 && date(0).integerQ() && date(1).integerQ() && date(2).integerQ()) {
          Some(LocalDate.of(date(0).asInt(), date(1).asInt(), date(2).asInt()))
        } else {
          None
        }
      }

      def checkExpired(date: Option[LocalDate]): Option[(Boolean, LocalDate)] = {
        date.map(d => d.isAfter(LocalDate.now()) -> d)
      }

      def checkInfinity(date: MExpr): Boolean = {
        date == infinity || date.head == infinity || date.args().exists(checkInfinity)
      }

      def licenseExpiredConverter(licenseExpirationDate: MExpr): Option[(Boolean, LocalDate)] = try {
        version match {
          case _ if checkInfinity(licenseExpirationDate) => Some(true, LocalDate.MAX)
          case Version("12", _, _) => checkExpired(toDate(licenseExpirationDate.args.head.args))
          case Version(major, minor, _) =>
            logger.debug("WARNING: Cannot check license expiration date since unknown Wolfram Engine version " + major + "." + minor + ", only version 12.x supported. Wolfram Engine requests may fail if license is expired.")
            None
        }
        //@note date disposed as part of licenseExpirationDate
      } catch {
        case e: ExprFormatException => logger.warn("WARNING: Unable to determine Wolfram Engine expiration date\n cause: " + e, e); None
      }

      val result = evaluate(MathematicaOpSpec.licenseExpirationDate.op.toString)
      disposeAfter(result, licenseExpiredConverter)
    } finally {
      infinity.dispose()
    }
  }

  /** Sends a simple computation to Wolfram Engine to ensure its actually working */
  private def isComputing: Option[Boolean] = {
    try {
      val result = evaluate("6*9")
      Some(disposeAfter(result, e => e.integerQ() && e.asInt() == 54))
    } catch {
      case e: Throwable => throw ToolExecutionException("Error running test computation", e)
    }
  }

  def evaluate(cmd: String): MExpr = {
    val wolframFile = File.createTempFile("wolfram", ".wl")
    val writer = new FileWriter(wolframFile)
    writer.write(s"Print[$cmd]")
    writer.close()

    val scriptCmd = "wolframscript -file " + wolframFile.getAbsolutePath + " -format ExpressionJSON"
    val result: StringBuilder = new StringBuilder()
    val pl = ProcessLogger(s => result.append(s))
    val p = scriptCmd.run(pl) // start asynchronously, log output to logger
    wolframProcess = Some(p)
    val f = Future(blocking(p.exitValue()))
    val exitVal = try {
      Await.result(f, duration.Duration.Inf)
    } catch {
      case _: InterruptedException => p.destroy()
    } finally {
      wolframProcess = None
    }

    val rs = result.toString
    if (exitVal == 0) {
      // rerun if Wolfram Engine fails with allocation errors
      if (rs.contains("malloc")) evaluate(cmd)
      else parseExpressionJSON(rs)
    } else {
      throw ToolExecutionException(s"Error executing Wolfram Engine, exit value $exitVal")
    }
  }

  private def parseExpressionJSON(expr: String): MExpr = {
    def convertJSON(v: JsValue): MExpr = v match {
      // strings are "'string'"
      case JsString(s) if s.startsWith("'") => new MExpr(s.substring(1, s.length-1))
      // symbols are "symbol"
      case JsString(s) => new MExpr(Expr.SYMBOL, s)
      case JsNumber(n) if  n.isWhole => new MExpr(n.toBigIntExact.getOrElse(
        throw ConversionException("Unexpected: whole BigDecimal cannot be converted to BigInteger")).bigInteger)
      case JsNumber(n) if !n.isWhole => new MExpr(n.bigDecimal)
      case JsTrue => MathematicaOpSpec.ltrue.op
      case JsFalse => MathematicaOpSpec.lfalse.op
      case JsNull => new MExpr(Expr.SYMBOL, "null")
      case JsArray(elems) =>
        val converted = elems.map(convertJSON)
        ExprFactory.makeExpr(converted.head, converted.tail.toArray)
    }
    val json = try {
      JsonParser(expr)
    } catch {
      case ex: JsonParser.ParsingException => throw ConversionException("Error parsing Wolfram Engine response; checking license may have failed, please double-check Wolfram Engine is activated and retry", ex)
    }
    convertJSON(json)
  }
}
