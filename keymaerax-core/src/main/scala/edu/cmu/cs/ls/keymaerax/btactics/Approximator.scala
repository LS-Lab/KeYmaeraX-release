/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.infrastruct.{Context, FormulaTools, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.reflect.runtime.universe

/**
 * Approximations
 * @todo
 *   More Ideas:
 *   - Allow approximations at non-top-level.
 *   - Pre-processing -- add time var w/ t_0=0, etc.
 *   - Post-processing -- after reducing the arithmetic, hide all approximate terms except the last one. It might even
 *     be possible to do this during the tactic by remving all but the most recent <= and >=, but I'm not sure if that's
 *     true for any/all expansions.
 *   - Generalized tactics. Not sure this makes much sense though.
 *   - Add an (efficient) tactic that tries to close the proof using successively longer approximations. Maybe also a
 *     tactic that looks at an entire formula and tries to deduce how far to go based on pre/post-conditions and
 *     statements in discrete fragments for programs or in ev dom constraints.
 * @author
 *   Nathan Fulton
 */
object Approximator extends TacticProvider with Logging {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (Approximator.getClass, universe.typeOf[Approximator.type])

  // region The [[approximate]] tactic with helpers for figuring out which approximation to use.

  private val DEBUG = true // Configuration(Configuration.Keys.DEBUG) == "true"

  /**
   * Approximates the variable `t` in the ODE up to the `n^th` term.
   * @param n
   *   The number of terms to expand the series/
   * @return
   *   The relevant tactic.
   */
  @Tactic("Approximate", conclusion = "Γ |- [{X'=F}], Δ", premises = "Γ |- [{X'=F & Α(n)}], Δ")
  def autoApproximate(n: Number): DependentPositionWithAppliedInputTactic =
    inputanon { (pos: Position, sequent: Sequent) =>
      sequent.sub(pos) match {
        case Some(m: Modal) if (m.program.isInstanceOf[ODESystem]) => {
          val system = m.program.asInstanceOf[ODESystem]
          val t = timeVar(system.ode)

          DifferentialHelper.hasExp(system.ode) match {
            case Some(v) => expApproximate(v, n)(pos)
            case None => DifferentialHelper.hasSinCos(system.ode) match {
                case Some((cos, sin)) => circularApproximate(sin, cos, n)(pos)
                case None => throw new TacticInapplicableFailure("Could not find a system to approximate.")
              }
          }
        }
        case Some(e) => throw new TacticInapplicableFailure(
            "autoApproximate only applicable on positions of form [{ODE}]P, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
          )
      }
    }

  // endregion

  // region Approximation for {{{e'=e}}}
  @Tactic(
    "e'=e Approximation",
    conclusion = "Γ |- [{c1,exp'=exp,c2}], Δ",
    premises = "Γ |- [{c1,exp'=exp,c2 & approximate(n)}], Δ",
    inputs = "exp:variable;;n:number",
  )
  def expApproximate(e: Variable, n: Number): DependentPositionWithAppliedInputTactic =
    inputanon { (pos: Position, sequent: Sequent) =>
      val t = timeVarInModality(sequent.sub(pos))

      val N = n.value.toInt
      assert(
        N >= 0,
        s"expApproximate expects a non-negative number as its 3rd argument (# of terms to expand the Taylor series.)",
      )

      val cuts = Range(0, N).map(i => GreaterEqual(e, expExpansion(t, i)))

      logger.debug(s"exp approximator performing these cuts:\n\t${cuts.mkString("\n\t")}")

      // dI handles the normal case, ODE handles the base case.
      val proofOfCut = DebuggingTactics.debug("Trying to prove by proofOfCut", DEBUG) &
        (TactixLibrary.dI()(pos) | TactixLibrary.ODE(pos)) & DebuggingTactics.done("Expected dI to succeed.")

      val qAtoms = sequent.sub(pos ++ PosInExpr(0 :: Nil)) match {
        case Some(ODESystem(_, q)) => FormulaTools.conjuncts(q).toSet
        case _ => Set[Formula]()
      }

      val cutTactics: Seq[BelleExpr] = {
        cuts
          .filter(!FormulaTools.conjuncts(_).toSet.subsetOf(qAtoms))
          .map(cut => {
            TactixLibrary.dC(cut)(pos) <
              (nil, DebuggingTactics.debug("Trying to prove this by dI or by ODE", DEBUG) & proofOfCut)
          })
      }

      DebuggingTactics.debug(s"Beginning expApproximation on ${e.prettyString}, ${n.prettyString}", DEBUG) &
        cutTactics.reduce(_ & _)
    }

  /**
   * Cuts in Taylor approximations for circular dynamics {{{x'=y,y'=-x}}}.
   * @todo
   *   Good error messages for when the first cut or two fail ==> "missing assumptions."
   */
  @Tactic(
    "Circular Dynamics Approximation",
    conclusion = "Γ |- [{c1,sin'=cos,cos'=-sin,c2}], Δ",
    premises = "Γ |- [{c1,sin'=cos,cos'=-sin,c2 & approximate(num)}], Δ",
    inputs = "sin[sin]:variable;;cos[cos]:variable;;num:number",
  )
  def circularApproximate(s: Variable, c: Variable, n: Number): DependentPositionWithAppliedInputTactic =
    inputanon { (pos: Position, sequent: Sequent) =>
      val t = timeVarInModality(sequent.sub(pos))

      // Get the number of terms we should expand.
      val N = n.value.toInt
      assert(
        N >= 0,
        s"circularApproximate expects a non-negative number as its 3rd argument (# of terms to expand the Taylor series.)",
      )

      // Compute the series of cuts.
      val sinCuts = Range(0, N)
        .map(i => if (i % 2 == 0) LessEqual(s, taylorSin(t, i)) else GreaterEqual(s, taylorSin(t, i)))
      val cosCuts = Range(0, N)
        .map(i => if (i % 2 == 0) LessEqual(c, taylorCos(t, i)) else GreaterEqual(c, taylorCos(t, i)))

      val radius = Plus(Power(s, Number(2)), Power(c, Number(2)))
      val radiusIsConst = Equal(radius, FuncOf(Function("old", None, Real, Real), radius))

      // Prove that (c,s) is a circle.
      val isOnCircle = TactixLibrary.dC(radiusIsConst)(pos) <
        (nil, TactixLibrary.dI()(pos) & DebuggingTactics.done("Expected dI to succeed")) &
        DebuggingTactics.assertProvableSize(1) & DebuggingTactics.debug(s"Successfully cut isOnCircle", DEBUG)

      val cuts = interleave(cosCuts, sinCuts)
      logger.debug(s"Taylor Approximator performing these cuts: ${cuts.mkString("\n")}")

      val qAtoms = sequent.sub(pos ++ PosInExpr(0 :: Nil)) match {
        case Some(ODESystem(_, q)) => FormulaTools.conjuncts(q).toSet
        case _ => Set[Formula]()
      }

      // Construct a tactic that interleaves these cuts.
      val cutTactics: Seq[BelleExpr] = cuts
        .filter(!FormulaTools.conjuncts(_).toSet.subsetOf(qAtoms))
        .map(cut =>
          DebuggingTactics.print("Cutting " + cut.prettyString) &
            TactixLibrary.dC(cut)(pos) <
            (
              nil,
              // dW&QE handles the base case, dI handles all others.
              DebuggingTactics.debug("Trying to prove next bound: ", DEBUG) &
                (TactixLibrary.dI()(pos) | (TactixLibrary.dW(pos) & QE)) &
                DebuggingTactics.done("Expected dI to succeed"),
            ) & DebuggingTactics.assertProvableSize(1) & DebuggingTactics.debug(s"Successfully cut $cut", DEBUG)
        )

      DebuggingTactics
        .debug(s"Beginning expApproximation on ${s.prettyString}, ${c.prettyString}, ${n.prettyString}", DEBUG) &
        isOnCircle & cutTactics.reduce(_ & _)
    }

  // region Definitions of series.

  /** The nth term of a Taylor series approximation of sin(t) */
  private def taylorCos(t: Term, N: Int) = sumTerms(t, taylorCosTerm, N)
  private def taylorCosTerm(t: Term, n: Int): Term = {
    assert(n >= 0, "Series are 0-indexed.")
    if (n == 0) "1".asTerm
    else if (n % 2 == 0) s"${t.prettyString}^${2 * n}/${fac(2 * n)}".asTerm
    else s"-${t.prettyString}^${2 * n}/${fac(2 * n)}".asTerm
  }

  /** The nth term of a Taylor series approximation of cos(t) */
  private def taylorSin(t: Term, N: Int) = sumTerms(t, taylorSinTerm, N)
  private def taylorSinTerm(t: Term, n: Int): Term =
    if (n == 0) t
    else if (n % 2 == 0) s"${t.prettyString}^${2 * n + 1}/${fac(2 * n + 1)}".asTerm
    else s"-${t.prettyString}^${2 * n + 1}/${fac(2 * n + 1)}".asTerm

  private def expExpansion(t: Term, N: Int): Term = sumTerms(t, ithExpTerm, N)
  private def ithExpTerm(t: Term, n: Int): Term =
    if (n == 0) Number(1)
    else if (n == 1) t // We don't need these two special cases but it keeps things readable.
    else Divide(Power(t, Number(n)), Number(fac(n)))

  private def sumTerms(t: Term, ithTerm: (Term, Int) => Term, N: Int) = Range(0, N + 1)
    .map(ithTerm(t, _))
    .reduce(Plus.apply)

  // endregion

  // region in-context helpers

  /** If f == [{c & q}]p, this function returns [{c & q&cut}]p */
  def extendEvDom(f: Modal, cut: Formula): Formula = {
    require(f.program.isInstanceOf[ODESystem], s"Expected an ODE system but found ${f.prettyString}")

    val evDomCtx = Context.at(f, PosInExpr(0 :: 1 :: Nil))

    evDomCtx._2 match {
      case currentEvDom: Formula => evDomCtx._1.apply(And(currentEvDom, cut))
      case _ => assert(false, "Should have failed prior assertion."); ???
    }
  }

  /**
   * Produces a witness that [c&q]p -> [c&q&cut]p when cutProof proves that cut is an invariant.
   * @param f
   *   The current goal [c&q]p
   * @param cut
   *   The diff cut
   * @param cutProof
   *   The proof that [c&q]cut
   * @return
   *   A proved implication of the form [c&q]p -> [c&q&cut]p
   */
  def dcInCtx(f: Formula, cut: Formula, cutProof: BelleExpr): ProvableSig = f match {
    case m: Modal if m.program.isInstanceOf[ODESystem] => {
      val fact = Imply(extendEvDom(m, cut), f)

      TactixLibrary.proveBy(
        fact,
        DebuggingTactics.debug(s"Trying to prove lemma $fact", DEBUG) & TactixLibrary.implyR(1) &
          TactixLibrary.dC(cut)(1) <
          (
            DebuggingTactics.debug("lemma branch 1: closeId", DEBUG) & TactixLibrary.id & DebuggingTactics.done,
            DebuggingTactics.debug("lemma branch 2: use provided tactic to prove cut", DEBUG) &
              TactixLibrary
                .hideL(-1) & cutProof & DebuggingTactics.debug("should've been done", true) & DebuggingTactics.done,
          ) & DebuggingTactics.debug(s"Successfully proved lemma $fact", DEBUG),
      )

    }
    case _ =>
      throw new TacticInapplicableFailure(s"Expected to find a modality containing an ODE, but found ${f.prettyString}")
  }

  /** Does a CEat with extendEvDomAndProve. */
  def extendEvDomAndProve(f: Formula, cut: Formula, cutProof: BelleExpr): BuiltInPositionTactic = {
    TactixLibrary
      .CEat(dcInCtx(f, cut, cutProof)) // @todo this doesn't work because initial conditions are missing. Need a useAt
  }

  // endregion

  // region Generic helper functions that should be replaced by library implementations.

  // @todo replace with built-in

  private def fac(n: Int): Int = {
    assert(n > 0)
    if (n == 1) 1 else n * fac(n - 1)
  }

  /** Interleaves A with B: A_0 B_0 A_1 B_1 ... A_n B_n */
  private def interleave[T](A: Seq[T], B: Seq[T]) = {
    assert(A.length == B.length, "Cannot interleave sequences of uneven length.")
    Range(0, 2 * A.length).map(i => if (i % 2 == 0) A(i / 2) else B((i - 1) / 2))
  }

  private def timeVar(ode: DifferentialProgram): Option[Variable] = ode match {
    case AtomicODE(xp, e) => if (e.equals(Number(1))) Some(xp.x) else None
    case DifferentialProduct(l, r) => timeVar(l) match {
        case Some(t) => Some(t)
        case None => timeVar(r)
      }
  }

  private def timeVarInModality(e: Option[Expression]) = e match {
    case None => throw new IllFormedTacticApplicationException("Approximator was given a non-existent position.")
    case Some(m) if m.isInstanceOf[Modal] =>
      m.asInstanceOf[Modal].program match {
        case ODESystem(ode, child) => timeVar(ode) match {
            case Some(t) => t
            case None => throw new TacticInapplicableFailure(
                "Approximation tactics require existence of an explicit time variable; i.e., expected to find t'=1 in the ODE but no such t was found."
              )
          }
        case _ => throw new TacticInapplicableFailure(
            "Approximation tactics should only be applied to modalities containing ODEs in the top level"
          )
      }
    case _ => throw new TacticInapplicableFailure("Approximation tactics should only be applied to modalities")
  }

  // endregion
}
