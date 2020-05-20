package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaComputationAbortedException
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.install.SOSsolveInstaller
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.MExpr
import edu.cmu.cs.ls.keymaerax.tools.qe.{KeYmaeraToMathematica, MathematicaOpSpec}
import org.apache.logging.log4j.scala.Logging

object SOSsolveTool {
  trait Result
  final case object Aborted extends Result
  final case object NoSOS extends Result
  final case class Witness(sos: Term, cofactors: List[Term]) extends Result
  final case class Exception(exception: Throwable) extends Result
}

trait SOSsolveTool {
  /**
    * Returns a continuous invariant for a safety problem sent to the tool.
    * @param polys polynomials (assumed to be equal to 0)
    * @param vars variables of polys
    * @return (1 + sos, cofactors) such that  (cofactors, polynomials).zipped.map(Times) = 1 + sos.
    */
  def sosSolve(polys: List[Term], vars: List[Term], degree: Int, timeout: Option[Int]) : SOSsolveTool.Result
}

/**
  * Link to Yong Kiams SOSsolve implementation in Mathematica over the JLink interface.
  * @author Fabian Immler, based on MathematicaInvGenTool by Andrew Sogokon and QETool by Nathan Fulton and Stefan Mitsch
  */
class MathematicaSOSsolveTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[Expression](link, new KeYmaeraToMathematica(), PegasusM2KConverter)
    with SOSsolveTool
    with Logging {

  import SOSsolveTool._

  private val SOSSOLVE_NAMESPACE = "SOSsolve`"

  private val sossolvePath = SOSsolveInstaller.sossolveRelativeResourcePath
  private val pathSegments = scala.reflect.io.File(sossolvePath).segments.map(string)
  private val joinedPath = fileNameJoin(list(homeDirectory.op :: pathSegments:_*))
  private val setPathsCmd = compoundExpression(setDirectory(joinedPath), appendTo(path.op, joinedPath))

  val sossolveMain = Configuration.SOSsolve.mainFile("SOSsolve.wl")
  val setOptions = applyFunc(symbol("SetOptions"))
  private def ssymbol(s: String) = symbol(SOSSOLVE_NAMESPACE + s)

  private def decodeWitness(result: Expression): (Term, List[Term]) = result match {
    case Pair(g,Pair(coeff,Pair(st, Pair(cofactors, Nothing)))) => {
      val sos =
        (PegasusM2KConverter.decodeTermList(coeff) zip PegasusM2KConverter.decodeTermList(st)).map(
          {cs => Times(cs._1,Power(cs._2,Number(2)))}
        ).foldLeft(g)(Plus.apply)
      (sos, PegasusM2KConverter.decodeTermList(cofactors))
    }
    case e =>
      throw new IllegalArgumentException("Expected pair of sos and cofactors but got " + e)
  }

  /** FIXME: why is this.timeout a var? Provide a this.timeConstrained with a functional timeout argument!
      "Thanks" to exceptions it is probably very hard to reliably reset the timeout to the previous value...
    */
  protected def timeConstrained(timeout: Option[Int], cmd: MExpr): MExpr = timeout match {
    case Some(timeout) if timeout > 0 =>
      MathematicaOpSpec.timeConstrained(cmd, MathematicaOpSpec.int(timeout))
    case None => cmd
    case _ => throw new IllegalArgumentException("Timeout must be positive")
  }

  def sosSolve(polys: List[Term], vars: List[Term], degree: Int, timeout: Option[Int]) : Result = {
    val mPolys = list(polys.map(k2m):_*)
    val mVars = list(vars.map(k2m):_*)
    val mDegree = int(degree)
    val command =
      quiet(compoundExpression(
        setPathsCmd,
        needs(string(SOSSOLVE_NAMESPACE), string(sossolveMain)),
        timeConstrained(timeout, applyFunc(ssymbol("FindWitness"))(mPolys, mVars, mDegree))
      )
    )

    try {
      val (output, result) = run(command)
      logger.debug("Found witness: " + result.prettyString + " from raw output " + output)
      val (sos, cofactors) = decodeWitness(result)
      sos match {
        case Number(n) if n.compareTo(0) <= 0 =>
          NoSOS
        case _ => Witness(sos, cofactors)
      }
    } catch {
      case _: MathematicaComputationAbortedException =>
        Aborted
      case ex: Throwable =>
        Exception(ex)
    }
  }
}


