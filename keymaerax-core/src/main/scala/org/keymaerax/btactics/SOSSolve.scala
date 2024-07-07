/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.btactics.TacticFactory._
import org.keymaerax.btactics.Idioms._
import org.keymaerax.btactics.PolynomialArithV2.{NonSupportedDivisorException, NonSupportedOperationInapplicability}
import org.keymaerax.core._
import org.keymaerax.infrastruct._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.ext.SOSsolveTool._
import org.keymaerax.tools.qe.BigDecimalQETool

import scala.collection.immutable._

/** @TODO: move somewhere reasonable! */
trait Timer {
  def time[R](f: => R): R
  def getTimeMs: Double
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
  def getTimeMs: Double = count / 1000000.0
}

/** tactics to prove SOSsolve witnesses */
object SOSSolve {

  private lazy val zeroGtOne = AnonymousLemmas.remember("1 > 0".asFormula, QE & done)
  private lazy val sosPosIntro = AnonymousLemmas.remember("x_() > 0 -> x_() + y_()^2 > 0".asFormula, QE & done)
  private lazy val sosPosCoeffIntro = AnonymousLemmas
    .remember("((c_() > 0<->true) & x_() > 0) -> x_() + c_()*y_()^2 > 0".asFormula, QE & done)
  private lazy val sosPosRatCoeffIntro = AnonymousLemmas
    .remember("(((c_() > 0 & d_() > 0)<->true) & x_() > 0) -> x_() + c_()/d_()*y_()^2 > 0".asFormula, QE & done)
  private def sosPosTac: DependentTactic = anon { (seq: Sequent) =>
    require(seq.succ.length == 1, "sosPosTac requires exactly one succedent")
    require(seq.ante.isEmpty, "sosPosTac requires empty antecedent")
    seq.succ(0) match {
      case Greater(Number(m), Number(n)) if m.compareTo(1) == 0 && n.compareTo(0) == 0 => by(zeroGtOne)
      case Greater(Plus(x, Power(y, Number(p))), Number(n)) if p.compareTo(2) == 0 && n.compareTo(0) == 0 =>
        useAt(sosPosIntro, PosInExpr(1 :: Nil))(1) & sosPosTac
      case Greater(Plus(x, Times(Divide(c, d), Power(y, Number(p)))), Number(n))
          if p.compareTo(2) == 0 && n.compareTo(0) == 0 =>
        val cPrv = ProvableSig.proveArithmetic(BigDecimalQETool, And(Greater(c, Number(0)), Greater(d, Number(0))))
        useAt(sosPosRatCoeffIntro, PosInExpr(1 :: Nil))(1) & andR(1) & Idioms.<(by(cPrv), sosPosTac)
      case Greater(Plus(x, Times(c, Power(y, Number(p)))), Number(n)) if p.compareTo(2) == 0 && n.compareTo(0) == 0 =>
        val cPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Greater(c, Number(0)))
        useAt(sosPosCoeffIntro, PosInExpr(1 :: Nil))(1) & andR(1) & Idioms.<(by(cPrv), sosPosTac)
      case fml => throw new IllegalArgumentException(
          "sosPosTac must be applied to 1 > 0, x + y^2 > 0, x + c*y^2 > 0 but got " + fml
        )
    }
  }

  private lazy val plusEqZeroIntro = AnonymousLemmas
    .remember("(p_() = 0 & q_() = 0) -> p_() + q_() = 0".asFormula, QE & done)
  private lazy val timesEqZeroIntro = AnonymousLemmas.remember("p_() = 0 -> c_()*p_() = 0".asFormula, QE & done)
  private def eqZeroTac: DependentTactic = anon { (seq: Sequent) =>
    require(seq.succ.length == 1, "eqZeroTac requires exactly one succedent")
    seq.succ(0) match {
      case Equal(Plus(p, q), Number(n)) if n.compareTo(0) == 0 =>
        useAt(plusEqZeroIntro, PosInExpr(1 :: Nil))(1) & andR(1) & Idioms.<(eqZeroTac, eqZeroTac)
      case Equal(Times(c, p), Number(n)) if n.compareTo(0) == 0 => useAt(timesEqZeroIntro, PosInExpr(1 :: Nil))(1) & id
      case fml => throw new IllegalArgumentException("sosPos must be applied to 1 > 0 or x + y^2 > 0 but got " + fml)
    }
  }

  lazy val witnessSOSLemma = AnonymousLemmas
    .remember("(sos_() > 0 & sos_() = comb_() & comb_() = 0) -> false".asFormula, QE & done)

  case class SOSSolveAborted() extends BelleProofSearchControl("sossolve aborted")
  case class SOSSolveNoSOS() extends BelleProofSearchControl("sossolve did not find sos")
  case class RatFormError(msg: String) extends TacticInapplicableFailure(msg)
  trait OutOfScope extends TacticInapplicableFailure
  final case class ExponentOutOfScopeFailure(msg: String) extends TacticInapplicableFailure(msg) with OutOfScope
  final case class NonUniversalOutOfScopeFailure(msg: String) extends TacticInapplicableFailure(msg) with OutOfScope
  case class SOSWelldefinedDivisionFailure(msg: String) extends TacticInapplicableFailure(msg)

  private def witnessSOSaux(sos: Term, cofactors: List[Term], witnessTimer: Timer): DependentTactic = {
    val name = "witnessSOSaux"
    anon { (seq: Sequent) =>
      val polys = seq
        .ante
        .map {
          case Equal(p, Number(n)) if n.compareTo(0) == 0 => p
          case fml => throw new IllegalArgumentException(
              name + " requires only formulas of the form 'poly = 0' in the antecedent but got " + fml
            )
        }
        .toList

      witnessTimer.time {
        val sosPos = proveBy(Greater(sos, Number(0)), sosPosTac & done)
        TaylorModelTactics.Timing.toc("sosPos")
        val combination = cofactors.lazyZip(polys).map(Times).reduceLeft(Plus)
        TaylorModelTactics.Timing.tic()
        val witnessPrv = proveBy(Equal(sos, combination), PolynomialArithV2.equate(1))
        TaylorModelTactics.Timing.toc("PolynomialArithV2.equate")
        val zeroPrv = proveBy(Sequent(seq.ante, IndexedSeq(Equal(combination, Number(0)))), eqZeroTac & done)
        TaylorModelTactics.Timing.toc("eqZeroTac")

        cut(False) & Idioms.<(
          closeF,
          useAt(
            witnessSOSLemma.fact(USubst(
              Seq(SubstitutionPair("sos_()".asTerm, sos), SubstitutionPair("comb_()".asTerm, combination))
            )),
            PosInExpr(1 :: Nil),
          )(1) & andR(1) &
            Idioms.<(cohideR(1) & by(sosPos), andR(1) & Idioms.<(cohideR(1) & by(witnessPrv), by(zeroPrv))),
        )
      }
    }
  }

  val lexicographicVariableOrdering: Ordering[Variable] = new Ordering[Variable] {
    def compare(x: Variable, y: Variable): Int = x.name.compareTo(y.name)
  }

  def augmentedVariableOrdering[A](augment: Variable => A, variableOrdering: Ordering[Variable])(implicit
      ordA: Ordering[A]
  ) = new Ordering[Variable] {
    def compare(x: Variable, y: Variable): Int = {
      implicit val vo = variableOrdering
      (augment(x), x).compareTo((augment(y), y))
    }
  }

  val preferAuxiliaryVariableOrdering: Ordering[Variable] =
    augmentedVariableOrdering(v => if (v.name.startsWith("wit_")) 0 else 1: Int, lexicographicVariableOrdering)

  val deferAuxiliaryVariableOrdering: Ordering[Variable] =
    augmentedVariableOrdering(v => if (v.name.startsWith("wit_")) 1 else 0: Int, lexicographicVariableOrdering)

  // search for a witness with SOSsolveTool and prove the goal
  def witnessSOS(
      degree: Int,
      variableOrdering: Ordering[Variable],
      timeout: Option[Int] = None,
      sosTimer: Timer = NoTimer,
      witnessTimer: Timer = NoTimer,
  ): DependentTactic = {
    val name = "witnessSOS"
    name by { (seq: Sequent) =>
      require(seq.succ.isEmpty, name + " requires succedent to be empty")
      val polys = seq
        .ante
        .map {
          case Equal(p, Number(n)) if n.compareTo(0) == 0 => p
          case fml => throw new IllegalArgumentException(
              name + " requires only formulas of the form 'poly = 0' in the antecedent but got " + fml
            )
        }
        .toList
      val consts = polys
        .flatMap(StaticSemantics.signature(_).toSet)
        .distinct
        .flatMap((e: Expression) =>
          e match {
            case bv: Function => Some(bv)
            case _ => None
          }
        )
        .map(FuncOf(_, Nothing))
      val vars = polys.flatMap(StaticSemantics.freeVars(_).toSet).distinct.sorted(variableOrdering)
      val sosSolveTool = ToolProvider.sosSolveTool().getOrElse(throw new RuntimeException("no SOSSolveTool configured"))
      val (sos, cofactors, lininst) = sosTimer.time {
        sosSolveTool.sosSolve(polys, consts ++ vars, degree, timeout) match {
          case Witness(sos, cofactors, lininst) => (sos, cofactors, lininst)
          case NoSOS => throw new SOSSolveNoSOS
          case Aborted => throw new SOSSolveAborted
        }
      }

      // Apply the linear instructions first then do the auxiliary
      linearElim(lininst) & witnessSOSaux(sos, cofactors, witnessTimer)
    }
  }

  // clear succedent and normalize antecedent to negation normal form
  val normalizeNNF = anon { (seq: Sequent) =>
    (seq
      .zipAnteWithPositions
      .flatMap { case (fml, pos) =>
        SimplifierV3.baseNormalize(fml) match {
          case (_, Some(prv)) => Some(useAt(prv, PosInExpr(0 :: Nil))(pos))
          case _ => None
        }
      } ++
      seq
        .zipSuccWithPositions
        .map { case (fml, pos) =>
          SimplifierV3.baseNormalize(Not(fml)) match {
            case (_, Some(prv)) => useAt(Ax.doubleNegation, PosInExpr(1 :: Nil))(pos) &
                useAt(prv, PosInExpr(0 :: Nil))(pos ++ PosInExpr(0 :: Nil))
            case _ => throw new RuntimeException(
                "this should not happen because we expect baseNormalize to get rid of negations."
              )
          }
        }).foldLeft[BelleExpr](skip)(_ & _) & SaturateTactic(notR(Symbol("R")))
  }

  // turns a ~ b into a - b ~ 0 in the antecedent
  def normalizeZeroRhs: DependentTactic = anon { (seq: Sequent) =>
    seq
      .zipAnteWithPositions
      .map { case (fml, pos) =>
        fml match {
          case cmp: ComparisonFormula if cmp.right == Number(0) => skip
          case LessEqual(_, _) => useAt(Ax.metricLe)(pos)
          case Less(_, _) => useAt(Ax.metricLt)(pos)
          case GreaterEqual(_, _) => useAt(Ax.geNormalize)(pos)
          case Greater(_, _) => useAt(Ax.gtNormalize)(pos)
          case Equal(_, _) => useAt(Ax.eqNormalize)(pos)
          case NotEqual(_, _) => useAt(Ax.neNormalize)(pos)
          case _ =>
            throw new TacticInapplicableFailure("normalizeZeroRhs expects only comparisonFormulas in the antecedent")
        }
      }
      .reduceLeftOption[BelleExpr](_ & _)
      .getOrElse(skip)
  }

  private def definedOrElse[T](x: Option[T], f: => Option[T]): Option[T] = x match {
    case None => f
    case Some(x) => Some(x)
  }

  // (ab)use PolynomialArithV2 to check for natural exponents
  private lazy val ringX = PolynomialArithV2.ofTerm("x".asVariable)
  def naturalExponentCheck(t: Term): Option[Term] =
    try {
      t match {
        case Power(a, b) => ringX ^ PolynomialArithV2.ofTerm(b); naturalExponentCheck(a)
        case t: BinaryCompositeTerm => definedOrElse(naturalExponentCheck(t.left), naturalExponentCheck(t.right))
        case t: UnaryCompositeTerm => naturalExponentCheck(t.child)
        case t: AtomicTerm => None
        case t: FuncOf => naturalExponentCheck(t.child)
        case _ => ???
      }
    } catch { case PolynomialArithV2.NonSupportedExponentException(_) => Some(t) }

  def naturalExponentCheck(fml: Formula): Option[Term] = fml match {
    case fml: BinaryCompositeFormula => definedOrElse(naturalExponentCheck(fml.left), naturalExponentCheck(fml.right))
    case fml: ComparisonFormula => definedOrElse(naturalExponentCheck(fml.left), naturalExponentCheck(fml.right))
    case fml: UnaryCompositeFormula => naturalExponentCheck(fml.child)
    case fml: Quantified => naturalExponentCheck(fml.child)
    case fml: Modal => naturalExponentCheck(fml.child)
    case fml: AtomicFormula => None
    case fml: PredOf => naturalExponentCheck(fml.child)
    case fml: PredicationalOf => naturalExponentCheck(fml.child)
    case _ => ???
  }

  def naturalExponentCheck(seq: Sequent): Option[Term] = (seq.ante ++ seq.succ)
    .collectFirst(scala.Function.unlift(naturalExponentCheck))

  def naturalExponentCheck: DependentTactic = anon { (seq: Sequent) =>
    naturalExponentCheck(seq) match {
      case None => skip
      case Some(t) => throw ExponentOutOfScopeFailure("(non natural number) exponent out of scope: " + t)
    }
  }

  // is the formula fml allowed to occur in the antecedent of a universal problem in negation normal form?
  def nonUniversal(fml: Formula): Boolean = fml match {
    case cmp: ComparisonFormula => false
    case cmp: BinaryCompositeFormula => throw new IllegalArgumentException(
        "universalCheck: preprocessing should have eliminated binary composite formulas - " + fml
      )
    case cmp: UnaryCompositeFormula => throw new IllegalArgumentException(
        "universalCheck: preprocessing should have eliminated unary composite formulas - " + fml
      )
    case a: AtomicFormula => throw new IllegalArgumentException(
        "universalCheck: preprocessing should have eliminated atomic formulas - " + fml
      )
    case a: ApplicationOf => true
    case m: Modal => true
    case Exists(_, _) => throw new IllegalArgumentException(
        "universalCheck: preprocessing should have eliminated existential quantifiers - " + fml
      )
    case Forall(_, _) => true
  }
  // check if antecedent is a universal problem
  def universalCheck: DependentTactic = anon { (seq: Sequent) =>
    require(seq.succ.length == 0, "universalCheck: preprocessing should have emptied succedent - " + seq.succ)
    (seq.ante).find(nonUniversal) match {
      case Some(fml) =>
        throw NonUniversalOutOfScopeFailure("(non universal) formula in the antecedent out of scope: " + fml)
      case None => skip
    }
  }

  // normalize to rational form on the lhs
  def ratFormLhs = anon { (seq: Sequent) =>
    seq
      .zipAnteWithPositions
      .map { case (cmp: ComparisonFormula, pos) =>
        cmp.right match {
          case (Number(n)) if n.compareTo(0) == 0 =>
            useAt(PolynomialArithV2.ratForm(cmp.left)._3, PosInExpr(0 :: Nil))(pos ++ PosInExpr(0 :: Nil))
          case _ => throw new TacticInapplicableFailure("ratFormLhs expects formulas with 0 on the rhs")
        }
      }
      .reduceLeftOption[BelleExpr](_ & _)
      .getOrElse(skip)
  }

  // turns "a/Number(d) ~ 0" to "a ~ 0" if "d > 0" occurs in the antecedent
  def solveNumericDenominators: DependentTactic = TacticFactory.anon { (seq: Sequent) =>
    require(seq.succ.length == 0, "proveNonzeros requires empty succedent")
    seq
      .zipAnteWithPositions
      .map {
        case (cmp: ComparisonFormula, pos) if cmp.right == Number(0) =>
          cmp.left match {
            case Divide(n, Number(d)) if d.compareTo(0) > 0 =>
              val prv = cmp match {
                case Equal(_, _) => Ax.divGtEq
                case NotEqual(_, _) => Ax.divGtNe
                case Greater(_, _) => Ax.divGtGt
                case GreaterEqual(_, _) => Ax.divGtGe
                case Less(_, _) => Ax.divGtLt
                case LessEqual(_, _) => Ax.divGtLe
              }
              cutL(cmp.reapply(n, Number(0)))(pos) & Idioms.<(
                skip,
                useAt(prv, PosInExpr(1 :: Nil))(1) & cohideR(1) & useAt(
                  ProvableSig.proveArithmetic(BigDecimalQETool, Greater(Number(d), Number(0))),
                  PosInExpr(0 :: Nil),
                )(1) & closeT,
              )
            case _ => skip
          }
        case _ => throw new TacticInapplicableFailure("elimNumericDenominators expects formulas with 0 on the rhs")
      }
      .reduceLeftOption(_ & _)
      .getOrElse(skip)
  }

  // turns "a/b ~ 0" to "a ~ 0" if "b > 0" occurs in the antecedent
  def solvePositiveDenominators: DependentTactic = TacticFactory.anon { (seq: Sequent) =>
    require(seq.succ.length == 0, "elimPositiveDenominators requires empty succedent")
    seq
      .zipAnteWithPositions
      .map {
        case (cmp: ComparisonFormula, pos) if cmp.right == Number(0) =>
          cmp.left match {
            case Divide(n, d) =>
              if (seq.ante.exists(_ == Greater(d, Number(0)))) {
                val prv = cmp match {
                  case Equal(_, _) => Ax.divGtEq
                  case NotEqual(_, _) => Ax.divGtNe
                  case Greater(_, _) => Ax.divGtGt
                  case GreaterEqual(_, _) => Ax.divGtGe
                  case Less(_, _) => Ax.divGtLt
                  case LessEqual(_, _) => Ax.divGtLe
                }
                cutL(cmp.reapply(n, Number(0)))(pos) & Idioms.<(skip, useAt(prv, PosInExpr(1 :: Nil))(1) & id)
              } else skip
            case _ => skip
          }
        case _ => throw new TacticInapplicableFailure("elimPositiveDenominators expects formulas with 0 on the rhs")
      }
      .reduceLeftOption(_ & _)
      .getOrElse(skip)
  }

  private def flip(cmp: ComparisonFormula): ComparisonFormula = cmp match {
    case Equal(a, b) => Equal(a, b)
    case NotEqual(a, b) => NotEqual(a, b)
    case Greater(a, b) => Less(a, b)
    case GreaterEqual(a, b) => LessEqual(a, b)
    case Less(a, b) => Greater(a, b)
    case LessEqual(a, b) => GreaterEqual(a, b)
  }
  // turns "a/b ~ 0" to "a ~ 0" if "b < 0" occurs in the antecedent
  def solveNegativeDenominators: DependentTactic = TacticFactory.anon { (seq: Sequent) =>
    require(seq.succ.length == 0, "elimNegativeDenominators requires empty succedent")
    seq
      .zipAnteWithPositions
      .map {
        case (cmp: ComparisonFormula, pos) if cmp.right == Number(0) =>
          cmp.left match {
            case Divide(n, d) =>
              if (seq.ante.exists(_ == Less(d, Number(0)))) {
                val prv = cmp match {
                  case Equal(_, _) => Ax.divLtEq
                  case NotEqual(_, _) => Ax.divLtNe
                  case Greater(_, _) => Ax.divLtGt
                  case GreaterEqual(_, _) => Ax.divLtGe
                  case Less(_, _) => Ax.divLtLt
                  case LessEqual(_, _) => Ax.divLtLe
                }
                cutL(flip(cmp).reapply(n, Number(0)))(pos) & Idioms.<(skip, useAt(prv, PosInExpr(1 :: Nil))(1) & id)
              } else skip
            case _ => skip
          }
        case _ => throw new TacticInapplicableFailure("elimNegativeDenominators expects formulas with 0 on the rhs")
      }
      .reduceLeftOption(_ & _)
      .getOrElse(skip)
  }
  // turns "a/b ~= 0" to "a ~= 0" if "b != 0" occurs in the antecedent
  def solveNonzeroDenominators: DependentTactic = TacticFactory.anon { (seq: Sequent) =>
    require(seq.succ.length == 0, "elimNegativeDenominators requires empty succedent")
    seq
      .zipAnteWithPositions
      .map {
        case (cmp: ComparisonFormula, pos) if cmp.right == Number(0) =>
          cmp match {
            case Equal(_, _) | NotEqual(_, _) => cmp.left match {
                case Divide(n, d) =>
                  if (seq.ante.exists(_ == NotEqual(d, Number(0)))) {
                    val prv = cmp match {
                      case Equal(_, _) => Ax.divNeEq
                      case NotEqual(_, _) => Ax.divNeNe
                    }
                    cutL(cmp.reapply(n, Number(0)))(pos) & Idioms.<(skip, useAt(prv, PosInExpr(1 :: Nil))(1) & id)
                  } else skip
                case _ => skip
              }
            case _ => skip
          }
        case _ => throw new TacticInapplicableFailure("elimNonzeroDenominators expects formulas with 0 on the rhs")
      }
      .reduceLeftOption(_ & _)
      .getOrElse(skip)
  }

  def subgoalNonzeroDenominators = anon { (seq: Sequent) =>
    val denominators = seq
      .zipAnteWithPositions
      .flatMap {
        case (Equal(Divide(num, denom), Number(n)), pos) if n.compareTo(0) == 0 => Some(true, num, denom, pos)
        case (NotEqual(Divide(num, denom), Number(n)), pos) if n.compareTo(0) == 0 => Some(false, num, denom, pos)
        case _ => None
      }
    def elimDenoms(denoms: List[(Boolean, Term, Term, Position)]): BelleExpr = denoms match {
      case (eq, num, denom, pos) :: denoms =>
        val (cmp, divNePrv) = if (eq) (Equal, Ax.divNeEq) else (NotEqual, Ax.divNeNe)
        cutL(cmp(num, Number(0)))(pos) & Idioms.<(
          elimDenoms(denoms),
          useAt(divNePrv, PosInExpr(1 :: Nil))(1) &
            denoms.map { case (_, _, _, pos) => hideL(pos) }.reduceLeftOption[BelleExpr](_ & _).getOrElse(skip),
        )
      case Nil => skip
    }
    elimDenoms(denominators.reverse)
  }

  // split formulas in negation normal form in the antecedent
  def splitAnte: BelleExpr = TacticFactory.anon { (seq: Sequent) =>
    seq
      .zipAnteWithPositions
      .collectFirst {
        case (Exists(_, _), pos) => existsL(pos) & splitAnte
        case (And(_, _), pos) => andL(pos) & splitAnte
        case (Or(_, _), pos) => orL(pos) & Idioms.<(splitAnte, splitAnte)
        case (True, pos) => hideL(pos) & splitAnte
        case (False, pos) => cohideL(pos) & closeF
      }
      .getOrElse(skip)
  }

  // check that all rational functions have been eliminated
  def checkNoRatForm = anon { (seq: Sequent) =>
    seq
      .ante
      .foreach {
        case cmp: ComparisonFormula => cmp.left match {
            case Divide(_, denom) =>
              throw RatFormError(s"division was not eliminated (try to cut in \'${denom} > 0\' or \'${denom} < 0\')")
            case _ => ()
          }
        case _ => throw new TacticInapplicableFailure("expects only comparisons in the antecedent")
      }
    skip
  }

  // turn the antecedent to 'rational form', where p_i and q_i are without division:
  // p_0(||)/q_0(||) ~ 0, ..., p_n(||) / q_n(||) ~ 0  |-
  // -------------------------------------------------------
  // r_0(||) ~ 0, ..., r_n(||) ~ 0  |-
  def ratFormAnte = OnAll(normalizeZeroRhs & ratFormLhs)

  // try to eliminate all rational forms and raise RatFormError otherwise.
  // may produce additional subgoals if branchNonzeroDenominators=true
  def elimRatForms(branchNonzeroDenominators: Boolean = false) = OnAll(
    solveNumericDenominators & solvePositiveDenominators & solveNegativeDenominators & solveNonzeroDenominators &
      (if (branchNonzeroDenominators) subgoalNonzeroDenominators else skip) & OnAll(checkNoRatForm)
  )

  // what to do about rational functions while preprocessing?
  trait RatFormStrategy
  // not expecting to deal with rational functions (division by constant numbers happen to work)
  final case object NoRatForm extends RatFormStrategy
  // normalize to rational form and eliminate divisions (with or without creating additional subgoals)
  final case class RatForm(branchNonzeroDenominators: Boolean) extends RatFormStrategy

  // preprocess real arithmetic sequent
  def preprocess(strategy: RatFormStrategy): BelleExpr = normalizeNNF & splitAnte &
    OnAll(universalCheck & naturalExponentCheck) &
    (strategy match {
      case NoRatForm => OnAll(normAnte)
      case RatForm(true) => OnAll(normAnte & ratFormAnte & elimRatForms(true))
      case RatForm(false) => OnAll(ratFormAnte & elimRatForms(false) & normAnte)
    })

  /** "main" method to preprocessing, sos witness generation, and proving. */
  def sos(
      ratFormStrategy: RatFormStrategy = NoRatForm,
      degree: Option[Int] = None,
      variableOrdering: Option[Ordering[Variable]] = None,
      timeout: Option[Option[Int]] = None,
      sosTimer: Timer = NoTimer,
      witnessTimer: Timer = NoTimer,
      skipPreprocessing: Boolean = false,
  ): BelleExpr = anon {
    val defaultTimeout = Some(120)
    val defaultDegree = 100
    (if (skipPreprocessing) skip else preprocess(ratFormStrategy)) & TryCatch(
      OnAll(anon { (seq: Sequent) =>
        val sostac = SOSSolve.witnessSOS(
          degree.getOrElse(defaultDegree),
          variableOrdering.getOrElse(deferAuxiliaryVariableOrdering),
          timeout.getOrElse(defaultTimeout),
          sosTimer,
          witnessTimer,
        )
        if (!seq.succ.isEmpty) {
          require(
            seq.succ.length == 1 && seq.succ(0).isInstanceOf[NotEqual],
            "sos: preprocess left something unexpected in the succedent " + seq.succ,
          )
          useAt(Ax.notEqual, PosInExpr(1 :: Nil))(1) & notR(1) & ?(sostac) |! anon { (seq: Sequent) =>
            throw SOSWelldefinedDivisionFailure(seq.toString)
          }
        } else { sostac }
      }),
      classOf[NonSupportedOperationInapplicability],
      (ex: NonSupportedOperationInapplicability) =>
        ex.cause match {
          case NonSupportedDivisorException(message) => throw RatFormError(
              "Rational function occured: " + message + "\nTry a RatForm strategy to eliminate rational functions."
            )
          case ex => throw ex
        },
    )
  }

  // Helper function for normalizing input sequents
  private val namespace = "sossolve"

  // Succedent to antecedent for inequations (rewrite left to right followed by notR)
  // todo: These can all go into the simplifier
  private lazy val ltSucc: ProvableSig = AnonymousLemmas
    .remember(
      " f_() < g_() <-> !(f_()>=g_())".asFormula,
      SimplifierV3.simpTac()(1) & prop & OnAll(SimplifierV3.simpTac()(1) & ?(close)),
      namespace,
    )
    .fact
  private lazy val leSucc: ProvableSig = AnonymousLemmas
    .remember(
      " f_() <= g_() <-> !(f_()>g_())".asFormula,
      SimplifierV3.simpTac()(1) & prop & OnAll(SimplifierV3.simpTac()(1) & ?(close)),
      namespace,
    )
    .fact
  private lazy val gtSucc: ProvableSig = AnonymousLemmas
    .remember(
      " f_() > g_() <-> !g_()>=f_()".asFormula,
      SimplifierV3.simpTac()(1) & prop & OnAll(SimplifierV3.simpTac()(1) & ?(close)),
      namespace,
    )
    .fact
  private lazy val geSucc: ProvableSig = AnonymousLemmas
    .remember(
      " f_() >= g_() <-> !g_()>f_()".asFormula,
      SimplifierV3.simpTac()(1) & prop & OnAll(SimplifierV3.simpTac()(1) & ?(close)),
      namespace,
    )
    .fact
  private lazy val eqSucc: ProvableSig = AnonymousLemmas
    .remember(
      " f_() = g_() <-> !g_()!=f_()".asFormula,
      SimplifierV3.simpTac()(1) & prop & OnAll(SimplifierV3.simpTac()(1) & ?(close)),
      namespace,
    )
    .fact // Convenient rule for A3
  private lazy val neSucc: ProvableSig = AnonymousLemmas
    .remember(
      " f_() != g_() <-> !g_()=f_()".asFormula,
      SimplifierV3.simpTac()(1) & prop & OnAll(SimplifierV3.simpTac()(1) & ?(close)),
      namespace,
    )
    .fact // Convenient rule for A3

  private lazy val ltAnte: ProvableSig = AnonymousLemmas
    .remember("f_() < g_() <-> \\exists wit_ (f_()-g_())*wit_^2 + 1 = 0".asFormula, QE, namespace)
    .fact
  private lazy val leAnte: ProvableSig = AnonymousLemmas
    .remember("f_() <= g_() <-> \\exists wit_ (f_()-g_()) + wit_^2 = 0".asFormula, QE, namespace)
    .fact
  private lazy val gtAnte: ProvableSig = AnonymousLemmas
    .remember("f_() > g_() <-> \\exists wit_ (f_()-g_())*wit_^2 - 1 = 0".asFormula, QE, namespace)
    .fact
  private lazy val geAnte: ProvableSig = AnonymousLemmas
    .remember("f_() >= g_() <-> \\exists wit_ (f_()-g_()) - wit_^2 = 0".asFormula, QE, namespace)
    .fact

  private lazy val eqAnte: ProvableSig = AnonymousLemmas
    .remember("f_() = g_() <-> f_() - g_() = 0".asFormula, QE & done, namespace)
    .fact
  private lazy val neAnte: ProvableSig = AnonymousLemmas
    .remember("f_() != g_() <-> \\exists wit_ (f_()-g_())*wit_ - 1 = 0".asFormula, QE & done, namespace)
    .fact

  private lazy val mulZero: ProvableSig = AnonymousLemmas
    .remember("g_() != 0 -> (f_() = 0 <-> g_() * f_() = 0)".asFormula, QE & done, namespace)
    .fact
  // A = 0 <-> B = 0 <- A = B
  private lazy val eqZeroEquiv = AnonymousLemmas
    .remember("(F_() = 0 <-> G_() = 0) <- F_() = G_()".asFormula, QE, namespace)
    .fact

  // clearSucc and normAnte are the real nullstellensatz versions (i.e. they normalise everything to equalities on the left)
  def clearSucc: DependentTactic = anon((seq: Sequent) => {
    seq
      .succ
      .zipWithIndex
      .foldLeft[BelleExpr](ident) { (tac: BelleExpr, fi) =>
        val ind = fi._2 + 1;
        (fi._1 match {
          case Greater(f, g) => useAt(gtSucc)(ind) & notR(ind)
          case GreaterEqual(f, g) => useAt(geSucc)(ind) & notR(ind)
          case Equal(_, _) => useAt(eqSucc)(ind) & notR(ind)
          case NotEqual(_, _) => useAt(neSucc)(ind) & notR(ind)
          case Less(f, g) => useAt(ltSucc)(ind) & notR(ind)
          case LessEqual(f, g) => useAt(leSucc)(ind) & notR(ind)
          case _ => ident
        }) & tac
      }
  })

  def normAnte: DependentTactic = anon((seq: Sequent) => {
    seq
      .ante
      .zipWithIndex
      .foldLeft[BelleExpr](ident) { (tac: BelleExpr, fi) =>
        val ind = -(fi._2 + 1);
        (fi._1 match {
          case Greater(f, g) => useAt(gtAnte)(ind) & existsL(ind)
          case GreaterEqual(f, g) => useAt(geAnte)(ind) & existsL(ind)
          case Equal(_, _) => useAt(eqAnte)(ind)
          case NotEqual(_, _) => useAt(neAnte)(ind) & existsL(ind)
          case Less(f, g) => useAt(ltAnte)(ind) & existsL(ind)
          case LessEqual(f, g) => useAt(leAnte)(ind) & existsL(ind)
          case _ => ident
        }) & tac
      }
  })

  lazy val prepareArith: BelleExpr = clearSucc & normAnte

  // Guided linear variable elimination at a top-level position (of shape A=B)
  // Rewrites that position to lhs = rhs using polynomial arithmetic to prove its correctness

  // The list of instructions contains:
  // 1) position to rewrite, 2) term to leave on LHS, 3) term on RHS
  // 4) determines the cofactor on the variable (expected to be provable to be non-zero by RCF)
  // The proof works by the following sequence of steps :
  // (clhs = crhs <-> lhs = rhs)
  // <= (clhs - crhs = 0) <-> (lhs - rhs =0)
  // <= (clhs-chrs=0) <-> (K*(lhs-rhs)=0)
  // <= clhs-chrs = K*(lhs-rhs) (by polynomial arithmetic)

  def rewriteEquality(pos: Position, lhs: Term, rhs: Term, cofactor: Term): DependentTactic = anon((seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Equal(clhs, crhs)) =>
        val cofact = proveBy(NotEqual(cofactor, Number(0)), RCF)
        val instMulZero = useFor(mulZero, PosInExpr(0 :: Nil))(Position(1))(cofact)
        // println(pos,lhs,rhs,cofactor)
        val pr = proveBy(
          Equiv(Equal(clhs, crhs), Equal(lhs, rhs)),
          useAt(eqAnte)(1, PosInExpr(0 :: Nil)) & useAt(eqAnte)(1, PosInExpr(1 :: Nil)) &
            useAt(instMulZero)(1, PosInExpr(1 :: Nil)) & useAt(eqZeroEquiv, PosInExpr(1 :: Nil))(1) &
            PolynomialArithV2.equate(1),
        )
        useAt(pr)(pos)
      case _ => ident
    }
  })

  // The actual linear elimination tactic takes a list
  def linearElim(ls: List[(Int, Term, Term, Term)]): BelleExpr = {
    val itopos = ls.map(p => (AntePosition(p._1), p._2, p._3, p._4))

    itopos.foldLeft[BelleExpr](ident)((tac, p) => tac & (rewriteEquality _).tupled(p) & exhaustiveEqL2R(true)(p._1))
  }
}
