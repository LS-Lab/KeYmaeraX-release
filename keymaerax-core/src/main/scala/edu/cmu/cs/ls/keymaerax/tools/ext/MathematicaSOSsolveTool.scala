/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.install.SOSsolveInstaller
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.MExpr
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.qe.{KeYmaeraToMathematica, MathematicaOpSpec}
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, MathematicaComputationTimedOutException}
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}

object SOSsolveTool {
  trait Result
  final case object Aborted extends Result
  final case object NoSOS extends Result
  final case class Witness(sos: Term, cofactors: List[Term], lininst: List[(Int, Term, Term, Term)]) extends Result
  final case class Exception(exception: Throwable) extends Result
}

trait SOSsolveTool {

  /**
   * Returns a continuous invariant for a safety problem sent to the tool.
   * @param polys
   *   polynomials (assumed to be equal to 0)
   * @param vars
   *   variables of polys
   * @return
   *   (1 + sos, cofactors) such that (cofactors, polynomials).zipped.map(Times) = 1 + sos.
   */
  def sosSolve(polys: List[Term], vars: List[Term], degree: Int, timeout: Option[Int]): SOSsolveTool.Result
}

/**
 * Link to Yong Kiams SOSsolve implementation in Mathematica over the JLink interface.
 * @author
 *   Fabian Immler, based on MathematicaInvGenTool by Andrew Sogokon and QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaSOSsolveTool(override val link: MathematicaLink)
    extends BaseKeYmaeraMathematicaBridge[Expression](link, new KeYmaeraToMathematica(), PegasusM2KConverter)
    with SOSsolveTool
    with Logging {

  import SOSsolveTool._

  private val SOSSOLVE_NAMESPACE = "sossolve`"

  private val sossolvePath = SOSsolveInstaller.sossolveRelativeResourcePath
  private val joinedPath = fileNameJoin(
    list(Configuration.sanitizedPathSegments(Configuration.KEYMAERAX_HOME_PATH, sossolvePath).map(string).toSeq: _*)
  )
  private val setPathsCmd = compoundExpression(setDirectory(joinedPath), appendTo(path.op, joinedPath))

  private val k2mU = new UncheckedBaseK2MConverter

  private val sossolveMain = Configuration.SOSsolve.mainFile("sossolve.wl")
  private def ssymbol(s: String) = symbol(SOSSOLVE_NAMESPACE + s)

  private def decodeLin(tt: Term): (Int, Term, Term, Term) = tt match {
    case Pair(n: Number, Pair(a, Pair(b, Pair(c, Nothing)))) if n.value.isValidInt => (n.value.intValue, a, b, c)
    case e => throw new IllegalArgumentException("Unable to decode linear instruction: " + e)
  }
  private def decodeWitness(result: Expression): (Term, List[Term], List[(Int, Term, Term, Term)]) = result match {
    case Pair(g, Pair(coeff, Pair(st, Pair(cofactors, Pair(lin, Nothing))))) =>
      val sos = (PegasusM2KConverter.decodeTermList(coeff) zip PegasusM2KConverter.decodeTermList(st))
        .map({ cs => Times(cs._1, Power(cs._2, Number(2))) })
        .foldLeft(g)(Plus.apply)
      val linls = PegasusM2KConverter.decodeTermList(lin)
      (sos, PegasusM2KConverter.decodeTermList(cofactors), linls.map(decodeLin))
    case e => throw new IllegalArgumentException("Expected pair of sos and cofactors but got " + e)
  }

  /**
   * FIXME: why is this.timeout a var? Provide a this.timeConstrained with a functional timeout argument! "Thanks" to
   * exceptions it is probably very hard to reliably reset the timeout to the previous value...
   */
  protected def timeConstrained(timeout: Option[Int], cmd: MExpr): MExpr = timeout match {
    case Some(timeout) if timeout > 0 => MathematicaOpSpec.timeConstrained(cmd, MathematicaOpSpec.int(timeout))
    case None => cmd
    case _ => throw new IllegalArgumentException("Timeout must be positive")
  }

  def sosSolve(polys: List[Term], vars: List[Term], degree: Int, timeout: Option[Int]): Result = {
    val mPolys = list(polys.map(k2mU): _*)
    val mVars = list(vars.map(k2mU): _*)
    val mDegree = int(degree)
    val command = quiet(compoundExpression(
      setPathsCmd,
      needs(string(SOSSOLVE_NAMESPACE), string(sossolveMain)),
      timeConstrained(timeout, applyFunc(ssymbol("FindWitness"))(mPolys, mVars, mDegree)),
    ))

    try {
      val (output, result) = run(command)
      logger.debug("Found witness: " + result.prettyString + " from raw output " + output)
      val (sos, cofactors, lininst) = decodeWitness(result)
      sos match {
        case Number(n) if n.compareTo(0) <= 0 => NoSOS
        case _ => Witness(sos, cofactors, lininst)
      }
    } catch {
      case _: MathematicaComputationAbortedException => Aborted
      case _: MathematicaComputationTimedOutException => Aborted
      case ex: Throwable => Exception(ex)
    }
  }
}
