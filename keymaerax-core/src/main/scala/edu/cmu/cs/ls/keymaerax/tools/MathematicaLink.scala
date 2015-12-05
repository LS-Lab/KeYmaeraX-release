/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import java.util.{GregorianCalendar, Date}

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal
import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr

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
trait MathematicaLink extends QETool with DiffSolutionTool {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  type MExpr = com.wolfram.jlink.Expr

  def runUnchecked(cmd : String) : (String, KExpr)
  def run(cmd : MExpr) : (String, KExpr)

  /**
   * @return true if the job is finished, false if it is still running.
   */
  def ready : Boolean

  /** Cancels the current request.
   * @return True if job is successfully cancelled, or False if the new
   * status is unknown.
   */
  def cancel : Boolean

  def toMathematica(expr : KExpr): MExpr =
    KeYmaeraToMathematica.fromKeYmaera(expr)

  def toKeYmaera(expr : MExpr): KExpr =
    MathematicaToKeYmaera.fromMathematica(expr)
}

/**
 * A link to Mathematica using the JLink interface.
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class JLinkMathematicaLink extends MathematicaLink {
  private val DEBUG = System.getProperty("DEBUG", "true")=="true"
  private val TIMEOUT = 10

  var ml: KernelLink = null

  var queryIndex: Long = 0

  val checkExpr = new MExpr(Expr.SYMBOL, "Check")
  val exceptionExpr = new MExpr("$Exception")
  val fetchMessagesCmd = "$MessageList"
  val listExpr = new MExpr(Expr.SYMBOL, "List")
  val checkedMessages = (("Reduce", "nsmet") :: ("Reduce", "ratnz") :: Nil).map({ case (s, t) =>
    new MExpr(new MExpr(Expr.SYMBOL, "MessageName"), Array(new MExpr(Expr.SYMBOL, s), new MExpr(t))) })
  val checkedMessagesExpr = new MExpr(Expr.SYM_LIST, checkedMessages.toArray)

  // HACK assumed to be called before first use of ml
  // TODO replace with constructor and use dependency injection to provide JLinkMathematicaLink whereever needed
  /**
   * Initializes the connection to Mathematica.
   * @param linkName The name of the link to use (platform-dependent, see Mathematica documentation)
   * @return true if initialization was successful
   */
  def init(linkName : String, jlinkLibDir : Option[String]): Boolean = {
    if(jlinkLibDir.isDefined) {
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
      ml.terminateKernel()
      ml.close()
      ml = null
    }
  }

  /**
   * Runs the command and then halts program execution until answer is returned.
   */
  def runUnchecked(cmd: String): (String, KExpr) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.synchronized {
      ml.evaluate(cmd)
      ml.waitForAnswer()
      val res = ml.getExpr
      val keymaeraResult = MathematicaToKeYmaera.fromMathematica(res)
      // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
      (res.toString, keymaeraResult)
    }
  }

  def run(cmd: MExpr): (String, KExpr) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.synchronized {
      queryIndex += 1
      val indexedCmd = new MExpr(Expr.SYM_LIST, Array(new MExpr(queryIndex), cmd))
      // Check[expr, err, messages] evaluates expr, if one of the specified messages is generated, returns err
      val checkErrorMsgCmd = new MExpr(checkExpr, Array(indexedCmd, exceptionExpr/*, checkedMessagesExpr*/))
      if (DEBUG) println("Sending to Mathematica " + checkErrorMsgCmd)
      dispatch(checkErrorMsgCmd.toString)
      getAnswer(indexedCmd.toString, queryIndex)
    }
  }

  private def dispatch(cmd: String) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.evaluate(cmd)
  }

  /**
   * blocks and returns the answer.
   */
  private def getAnswer(input: String, cmdIdx: Long): (String, KExpr) = {
    if (ml == null) throw new IllegalStateException("No MathKernel set")
    ml.waitForAnswer()
    val res = ml.getExpr
    if (res == exceptionExpr) {
      res.dispose()
      // an exception occurred
      ml.evaluate(fetchMessagesCmd)
      ml.waitForAnswer()
      val msg = ml.getExpr
      val txtMsg = msg.toString
      // msg.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
      throw new IllegalArgumentException("Input " + input + " cannot be evaluated: " + txtMsg)
    } else {
      val head = res.head
      if (head.equals(checkExpr)) {
        val txtMsg = res.toString
        // res.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
        throw new IllegalStateException("Mathematica returned input as answer: " + txtMsg)
      }
      if(res.head == Expr.SYM_LIST && res.args().length == 2 && res.args.head.asInt() == cmdIdx) {
        val theResult = res.args.last
        val keymaeraResult = MathematicaToKeYmaera.fromMathematica(theResult)
        val txtResult = theResult.toString
        // res.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
        (txtResult, keymaeraResult)
      } else {
        val txtResult = res.toString
        // res.dispose() // toString calls dispose (see Mathematica documentation, so only call it when done with the Expr
        throw new IllegalStateException("Mathematica returned a stale answer for " + txtResult)
      }
    }
  }

  def ready = ???

  def cancel = ???

  def qe(f : Formula) : Formula = {
    qeEvidence(f)._1
  }

  def qeEvidence(f : Formula) : (Formula, Evidence) = {
    val input = new MExpr(new MExpr(Expr.SYMBOL,  "Reduce"),
      Array(toMathematica(f), new MExpr(listExpr, new Array[MExpr](0)), new MExpr(Expr.SYMBOL, "Reals")))
    val (output, result) = run(input)
    result match {
      case f : Formula => (f, new ToolEvidence(immutable.Map("input" -> input.toString, "output" -> output)))
      case _ => throw new Exception("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }

  def getCounterExample(f : Formula) : String = {
    val input = new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
      Array(toMathematica(Not(f)), new MExpr(listExpr, StaticSemantics.symbols(f).toList.sorted.map(s => toMathematica(s)).toArray), new MExpr(Expr.SYMBOL, "Reals")))
    val inputWithTO = new MExpr(new MExpr(Expr.SYMBOL,  "TimeConstrained"), Array(input, toMathematica(Number(TIMEOUT))))
    try {
      val (output, result) = run(inputWithTO)
      result match {
        case ff : Formula => KeYmaeraXPrettyPrinter(ff)
        case _ => throw new NoCountExException("Mathematica cannot find counter examples for: " + KeYmaeraXPrettyPrinter(f))
      }
    } catch {
      case e: MathematicaComputationAbortedException => throw new NoCountExException("Within " + TIMEOUT + " seconds, Mathematica cannot find counter examples for: " + KeYmaeraXPrettyPrinter(f))
    }

  }

  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Function]): Option[Formula] =
    diffSol(diffArg, iv, toDiffSys(diffSys, diffArg):_*)

  /**
   * Converts an expression into a differential equation system (list of x'=theta).
   * Expected to be in NFContEvolve form.
   * @param diffSys The expression form of the differential equation system.
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @return The differential equation system.
   */
  // TODO convert more general forms
  private def toDiffSys(diffSys: KExpr, diffArg: Variable): List[(Variable, Term)] = {
    diffSys match {
      // do not solve time for now (assumed to be there but should not be solved for)
      // TODO remove restriction on t once ghost time is introduced
      case Equal(Differential(x: Variable), theta) if x != diffArg =>  (x, theta) :: Nil
      case Equal(DifferentialSymbol(x), theta) if x != diffArg =>  (x, theta) :: Nil
      case Equal(Differential(x: Variable), theta) if x == diffArg =>  Nil
      case Equal(DifferentialSymbol(x), theta) if x == diffArg =>  Nil
      case And(lhs, rhs) => toDiffSys(lhs, diffArg) ::: toDiffSys(rhs, diffArg)
      case _ => ???
    }
  }

  /**
   * Converts a system of differential equations given as DifferentialProgram into list of x'=theta
   * @param diffSys The system of differential equations
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @return The differential equation system in list form.
   */
  private def toDiffSys(diffSys: DifferentialProgram, diffArg: Variable): List[(Variable, Term)] = {
    var result = List[(Variable, Term)]()
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case AtomicODE(DifferentialSymbol(x), theta) if x != diffArg => result = result :+ (x, theta); Left(None)
        case AtomicODE(DifferentialSymbol(x), theta) if x == diffArg => Left(None)
        case ODESystem(_, _) => Left(None)
        case DifferentialProduct(_, _) => Left(None)
      }
    }, diffSys)
    result
  }

  /**
   * Computes the symbolic solution of a system of differential equations.
   * @param diffArg The differential argument, i.e., d f(diffArg) / d diffArg.
   * @param diffSys The system of differential equations of the form x' = theta.
   * @return The solution if found; None otherwise
   */
  private def diffSol(diffArg: Variable, iv: Map[Variable, Function], diffSys: (Variable, Term)*): Option[Formula] = {
    val primedVars = diffSys.map(_._1)
    val functionalizedTerms = diffSys.map{ case (x, theta) => ( x, functionalizeVars(theta, diffArg, primedVars:_*)) }
    val mathTerms = functionalizedTerms.map{case (x, theta) =>
      (new MExpr(toMathematica(DifferentialSymbol(x)), Array[MExpr](toMathematica(diffArg))), toMathematica(theta))}
    val convertedDiffSys = mathTerms.map{case (x, theta) =>
      new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](x, theta))}

    val functions = diffSys.map(t => toMathematica(functionalizeVars(t._1, diffArg)))

    val initialValues = diffSys.map(t => toMathematica(
      Equal(functionalizeVars(t._1, Number(BigDecimal(0)), primedVars:_*), FuncOf(iv(t._1), Nothing))))

    val input = new MExpr(new MExpr(Expr.SYMBOL, "DSolve"),
      Array[MExpr](
        new MExpr(Expr.SYM_LIST, (convertedDiffSys ++ initialValues).toArray),
        new MExpr(Expr.SYM_LIST, functions.toArray),
        toMathematica(diffArg)))
    val (_, result) = run(input)
    result match {
      case f: Formula => Some(defunctionalize(f, diffArg, primedVars.map(_.name):_*))
      case _ => None
    }
  }

  /**
   * Replaces all occurrences of variables vars in the specified term t with functions of argument arg.
   * @param t The term.
   * @param arg The function argument.
   * @param vars The variables to functionalize.
   * @return The term with variables replaced by functions.
   */
  private def functionalizeVars(t: Term, arg: Term, vars: Variable*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v@Variable(name, idx, sort) if vars.isEmpty || vars.contains(v) =>
          Right(FuncOf(Function(name, idx, arg.sort, sort), arg))
        case _ => Left(None)
      }
    }, t) match {
    case Some(resultTerm) => resultTerm
    case None => throw new IllegalArgumentException("Unable to functionalize " + t)
  }

  /**
   * Replaces all functions with argument arg in formula f with a variable of the same name.
   * @param f The formula.
   * @param arg The function argument.
   * @return The term with functions replaced by variables.
   */
  private def defunctionalize(f: Formula, arg: Term, fnNames: String*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(Function(name, idx, _, range), fnArg) if arg == fnArg
          && (fnNames.isEmpty || fnNames.contains(name)) => Right(Variable(name, idx, range))
        case _ => Left(None)
      }
    }, f) match {
    case Some(resultF) => resultF
    case None => throw new IllegalArgumentException("Unable to defunctionalize " + f)
  }

  /** Returns the version as (Major, Minor, Release) */
  private def getVersion: (String, String, String) = {
    ml.evaluate("$VersionNumber")
    ml.waitForAnswer()
    val version = ml.getExpr
    ml.evaluate("$ReleaseNumber")
    ml.waitForAnswer()
    val release = ml.getExpr
    //@note using strings to be robust in case Wolfram decides to switch from current major:Double/minor:Int
    val (major, minor) = { val versionParts = version.toString.split("\\."); (versionParts(0), versionParts(1)) }
    (major, minor, release.toString)
  }

  /** Checks if Mathematica is activated by querying the license expiration date */
  private def isActivated: Option[Boolean] = {
    type MExpr = com.wolfram.jlink.Expr
    //@todo this is how Mathematica 10 represents infinity, test if 9 is the same
    val infinity = new MExpr(new MExpr(Expr.SYMBOL, "DirectedInfinity"), Array(new MExpr(1L)))

    ml.evaluate("$LicenseExpirationDate")
    ml.waitForAnswer()
    val licenseExpirationDate = ml.getExpr

    val date: Array[MExpr] = getVersion match {
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
  }

  /** Sends a simple computation to Mathematica to ensure its actually working */
  private def isComputing: Option[Boolean] = {
    try {
      ml.evaluate("6*9")
      ml.waitForAnswer()
      val answer = ml.getExpr
      Some(answer.integerQ() && answer.asInt() == 54)
    } catch {
      //@todo need better error reporting, this way it will never show up on UI
      case e: Throwable => if (DEBUG) println("WARNING: Mathematica may not be functional \n cause: " + e); None
    }
  }
}