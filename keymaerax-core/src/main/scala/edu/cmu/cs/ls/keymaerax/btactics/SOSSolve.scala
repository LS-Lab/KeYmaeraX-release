package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticIndex.TacticRecursors
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.BigDecimalTool
import edu.cmu.cs.ls.keymaerax.tools.ext.SOSsolveTool._
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool

import scala.collection.immutable._

/** @TODO: move somewhere reasonable! */
trait Timer {
  def time[R](f: => R) : R
  def getTimeMs : Double
}
object Timer {
  def apply() = new NanoTimer
}
object NoTimer extends Timer {
  override def time[R](f: => R): R = f
  def getTimeMs = 0.0
}
class NanoTimer extends Timer {
  var count = 0L
  def time[R](f: => R): R = {
    val t0 = System.nanoTime()
    val result = f
    val t1 = System.nanoTime()
    count = count + (t1 - t0)
    result
  }
  def getTimeMs : Double = count / 1000000.0
}


/** tactics to prove SOSsolve witnesses */
object SOSSolve {

  private lazy val zeroGtOne = AnonymousLemmas.remember("1 > 0".asFormula, QE & done)
  private lazy val sosPosIntro = AnonymousLemmas.remember("x_() > 0 -> x_() + y_()^2 > 0".asFormula, QE & done)
  private lazy val sosPosCoeffIntro = AnonymousLemmas.remember("((c_() > 0<->true) & x_() > 0) -> x_() + c_()*y_()^2 > 0".asFormula, QE & done)
  private lazy val sosPosRatCoeffIntro = AnonymousLemmas.remember("(((c_() > 0 & d_() > 0)<->true) & x_() > 0) -> x_() + c_()/d_()*y_()^2 > 0".asFormula, QE & done)
  private def sosPosTac : DependentTactic = "sosPosTac" by { (seq: Sequent) =>
    require(seq.succ.length==1, "sosPosTac requires exactly one succedent")
    require(seq.ante.isEmpty, "sosPosTac requires empty antecedent")
    seq.succ(0) match {
      case Greater(Number(m), Number(n)) if m.compareTo(1) == 0 && n.compareTo(0) == 0 =>
        by(zeroGtOne)
      case Greater(Plus(x, Power(y, Number(p))), Number(n)) if p.compareTo(2) == 0 && n.compareTo(0) == 0 =>
        useAt(sosPosIntro, PosInExpr(1::Nil))(1) & sosPosTac
      case Greater(Plus(x, Times(Divide(c, d), Power(y, Number(p)))), Number(n)) if p.compareTo(2) == 0 && n.compareTo(0) == 0  =>
        val cPrv = ProvableSig.proveArithmetic(BigDecimalQETool, And(Greater(c, Number(0)), Greater(d, Number(0))))
        useAt(sosPosRatCoeffIntro, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(by(cPrv), sosPosTac)
      case Greater(Plus(x, Times(c, Power(y, Number(p)))), Number(n)) if p.compareTo(2) == 0 && n.compareTo(0) == 0  =>
        val cPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Greater(c, Number(0)))
        useAt(sosPosCoeffIntro, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(by(cPrv), sosPosTac)
      case fml => throw new IllegalArgumentException("sosPosTac must be applied to 1 > 0, x + y^2 > 0, x + c*y^2 > 0 but got " + fml)
    }
  }

  private lazy val plusEqZeroIntro = AnonymousLemmas.remember("(p_() = 0 & q_() = 0) -> p_() + q_() = 0".asFormula, QE & done)
  private lazy val timesEqZeroIntro = AnonymousLemmas.remember("p_() = 0 -> c_()*p_() = 0".asFormula, QE & done)
  private def eqZeroTac : DependentTactic = "eqZeroTac" by { (seq: Sequent) =>
    require(seq.succ.length==1, "eqZeroTac requires exactly one succedent")
    seq.succ(0) match {
      case Equal(Plus(p, q), Number(n)) if n.compareTo(0) == 0 =>
        useAt(plusEqZeroIntro, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(eqZeroTac, eqZeroTac)
      case Equal(Times(c, p), Number(n)) if n.compareTo(0) == 0 =>
        useAt(timesEqZeroIntro, PosInExpr(1::Nil))(1) & closeId
      case fml => throw new IllegalArgumentException("sosPos must be applied to 1 > 0 or x + y^2 > 0 but got " + fml)
    }
  }

  lazy val witnessSOSLemma = AnonymousLemmas.remember("(sos_() > 0 & sos_() = comb_() & comb_() = 0) -> false".asFormula, QE & done)

  case class SOSSolveAborted() extends BelleProofSearchControl("sossolve aborted")
  case class SOSSolveNoSOS() extends BelleProofSearchControl("sossolve did not find sos")

  def witnessSOS(degree: Int, timeout: Option[Int] = None, sosTimer: Timer = NoTimer, witnessTimer: Timer = NoTimer) : DependentTactic = {
    val name = "witnessSOS"
    name by { (seq: Sequent) =>
      require(seq.succ.isEmpty, name + " requires succedent to be empty")
      val polys = seq.ante.map{
        case Equal(p, Number(n)) if n.compareTo(0) == 0 => p
        case fml => throw new IllegalArgumentException(name + " requires only formulas of the form 'poly = 0' in the antecedent but got " + fml)
      }.toList
      val vars = polys.flatMap(StaticSemantics.freeVars(_).toSet).distinct
      val sosSolveTool = ToolProvider.sosSolveTool().getOrElse(throw new RuntimeException("no SOSSolveTool configured"))
      val (sos, cofactors) = sosTimer.time {
        sosSolveTool.sosSolve(polys, vars, degree, timeout) match {
          case Witness(sos, cofactors) => (sos, cofactors)
          case NoSOS => throw new SOSSolveNoSOS
          case Aborted => throw new SOSSolveAborted
        }
      }
      witnessTimer.time {
        val sosPos = proveBy(Greater(sos, Number(0)), sosPosTac & done)
        TaylorModelTactics.Timing.toc("sosPos")
        val combination = (cofactors, polys).zipped.map(Times).reduceLeft(Plus)
        TaylorModelTactics.Timing.tic()
        val witnessPrv = proveBy(Equal(sos, combination), PolynomialArithV2.equate(1))
        TaylorModelTactics.Timing.toc("PolynomialArithV2.equate")
        val zeroPrv = proveBy(Sequent(seq.ante, IndexedSeq(Equal(combination, Number(0)))), eqZeroTac & done)
        TaylorModelTactics.Timing.toc("eqZeroTac")
        cut(False) & Idioms.<(
          closeF,
          useAt(witnessSOSLemma.fact(USubst(Seq(SubstitutionPair("sos_()".asTerm, sos), SubstitutionPair("comb_()".asTerm, combination)))), PosInExpr(1 :: Nil))(1) &
            andR(1) & Idioms.<(cohideR(1) & by(sosPos), andR(1) & Idioms.<(cohideR(1) & by(witnessPrv), by(zeroPrv))))
      }
    }
  }

  val normalizeNNF = "ANON" by { (seq: Sequent) =>
    (seq.zipAnteWithPositions.flatMap { case(fml, pos) =>
      SimplifierV3.baseNormalize(fml) match {
        case (_, Some(prv)) => Some(useAt(prv, PosInExpr(0::Nil))(pos))
        case _ => None
      }
    } ++ seq.zipSuccWithPositions.map { case(fml, pos) =>
      SimplifierV3.baseNormalize(Not(fml)) match {
        case (_, Some(prv)) => useAt(DerivedAxioms.doubleNegationAxiom, PosInExpr(1 :: Nil))(pos) & useAt(prv, PosInExpr(0::Nil))(pos ++ PosInExpr(0::Nil))
        case _ => throw new RuntimeException("this should not happen because we expect baseNormalize to get rid of negations.")
      }
    }).foldLeft(skip)(_ & _) & SaturateTactic(notR('R))
  }

}
