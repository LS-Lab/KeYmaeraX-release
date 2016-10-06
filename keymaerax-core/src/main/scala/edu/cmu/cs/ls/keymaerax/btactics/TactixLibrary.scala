/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.{?, must}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.tools.{CounterExampleTool, ODESolverTool}

import scala.collection.immutable._
import scala.language.postfixOps
import scala.math.BigDecimal

/**
  * Tactix: Main tactic library with simple interface.
  * This library features all main tactics for the most common cases.
  *
  * For tactics implementing built-in rules such as sequent proof rules,
  * elaborate documentation can be found in the [[edu.cmu.cs.ls.keymaerax.core.Rule prover kernel]].
  *
  * Main search tactics that combine numerous other tactics for automation purposes include:
  *   - [[TactixLibrary.master]] automatic proof search
  *   - [[TactixLibrary.auto]] automatic proof search if that successfully proves the given property
  *   - [[TactixLibrary.normalize]] normalize to sequent normal form
  *   - [[TactixLibrary.unfoldProgramNormalize]] normalize to sequent normal form, avoiding unnecessary branching
  *   - [[TactixLibrary.prop]] propositional logic proving
  *   - [[TactixLibrary.QE]] prove real arithmetic
  *   - [[TactixLibrary.ODE]] proving properties of differential equations
  *   - [[TactixLibrary.step]] performs one canonical simplifying proof step
  *   - [[TactixLibrary.chase]] chase the given formula away by automatic reduction proofs
  *
  * The tactic library also includes individual proof calculi:
  *   - [[HilbertCalculus]]: Hilbert Calculus for differential dynamic logic.
  *   - [[SequentCalculus]]: Sequent Calculus for propositional and first-order logic.
  *   - [[UnifyUSCalculus]]: Automatic unification-based Uniform Substitution Calculus with indexing.
  *
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
  * @see [[HilbertCalculus]]
  * @see [[SequentCalculus]]
  * @see [[UnifyUSCalculus]]
  * @see [[DerivedAxioms]]
  * @see [[AxiomInfo]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
  * @see [[ToolProvider]]
  */
object TactixLibrary extends UnifyUSCalculus with SequentCalculus {
  import Generator.Generator
  /** Default generator for loop invariants and differential invariants to use.
    * @see [[InvariantGenerator]] */
  var invGenerator: Generator[Formula] = FixedGenerator(Nil)

  /** step: one canonical simplifying proof step at the indicated formula/term position (unless @invariant etc needed) */
  val step          : DependentPositionTactic = "step" by ((pos: Position) =>
    //@note AxiomIndex (basis for HilbertCalculus.stepAt) hands out assignment axioms, but those fail in front of an ODE -> try assignb if that happens
    if (pos.isTopLevel) stepAt(sequentStepIndex(pos.isAnte)(_))(pos) partial
    else throw new IllegalArgumentException("Not a top level position."))

  /** Normalize to sequent form, keeping branching factor down by precedence */
  lazy val normalize: BelleExpr = normalize(betaRule, step('L), step('R))
  /** Normalize to sequent form, customize branching with `beta`, customize simplification steps in antecedent/succedent with `stepL` and `stepR` */
  def normalize(beta: BelleExpr, stepL: BelleExpr, stepR: BelleExpr): BelleExpr = NamedTactic("normalize", {
    (OnAll(?(
              (alphaRule partial)
                | (closeId
                | ((allR('R) partial)
                | ((existsL('L) partial)
                | (close
                | ((beta partial)
                | ((stepL partial)
                | ((stepR partial) partial) partial) partial) partial) partial) partial) partial) partial) partial))*
    })

  /** Follow program structure when normalizing but avoid branching in typical safety problems (splits andR but nothing else). */
  val unfoldProgramNormalize = "unfoldProgramNormalize" by chase('R) & normalize(andR('R), Idioms.ident, Idioms.ident)

  /** prop: exhaustively apply propositional logic reasoning and close if propositionally possible. */
  def propStep : BelleExpr = NamedTactic("propStep", {
    OnAll(
      close
        | alphaRule
        | betaRule
        | implyL('L)
    )*
  })
  def prop : BelleExpr = NamedTactic("prop", {
    OnAll(
      (SaturateTactic(propStep) & done)
        | ( SaturateTactic(orR1('R) | propStep) & done )
        | ( SaturateTactic(orR2('R) | propStep) & done )
    )*
  })

  /** master: master tactic that tries hard to prove whatever it could
    * @see [[auto]] */
  def master(gen: Generator[Formula] = invGenerator): BelleExpr = "master" by {
    ((OnAll(?(
          (close
            | (must(normalize)
            | exhaustiveEqL2R('L) ) ) ) ))*)
  }

  /** auto: automatically try to prove the current goal if that succeeds.
    * @see [[master]] */
  def auto: BelleExpr = "auto" by {
    ((OnAll(?(
      (close
        | (must(normalize)
        | exhaustiveEqL2R('L) ) ) ) ))*) &
      done
  }

  /*******************************************************************
    * unification and matching based auto-tactics
 *
    * @see [[UnifyUSCalculus]]
    *******************************************************************/

//  /** US: uniform substitution ([[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule USubst]])
//    * @see [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]]
//    * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
//    */
//  def US(subst: USubst, origin: Sequent): BuiltInTactic = ProofRuleTactics.US(subst, origin)

  // conditional tactics

  /**
   * onBranch((lbl1,t1), (lbl2,t2)) uses tactic t1 on branch labelled lbl1 and t2 on lbl2
   *
   * @note Probably this String should be a BelleLabel, and we should move BranchLabels into BelleLabel.
   * @see [[label()]]
   */
  def onBranch(s1: (String, BelleExpr), spec: (String, BelleExpr)*): BelleExpr = ??? //SearchTacticsImpl.onBranch(s1, spec:_*)

  /** Call/label the current proof branch s
   *
   * @see [[onBranch()]]
   * @see [[sublabel()]]
   */
  def label(s: String): BelleExpr = ??? //new LabelBranch(s)

  /** Mark the current proof branch and all subbranches s
    *
    * @see [[label()]]
    */
  def sublabel(s: String): BelleExpr = ??? //new SubLabelBranch(s)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Bigger Tactics.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Utility Tactics
  /** nil=skip is a no-op tactic that has no effect */
  val nil : BelleExpr = Idioms.ident
  /** nil=skip is a no-op tactic that has no effect
    * @see [[done]] */
  val skip : BelleExpr = nil
  /** fail is a tactic that always fails
    * @see [[skip]] */
  val fail : BelleExpr = assertT(seq=>false, "fail")
  /** done: check that the current goal is proved and fail if it isn't.
    * @see [[skip]] */
  val done : BelleExpr = DebuggingTactics.done


  /** abbrv(name) Abbreviate the term at the given position by a new name and use that name at all occurrences of that term.
    * @example{{{
    *   maxcd = max(c,d) |- a+b <= maxcd+e
    *   ----------------------------------------abbrv(Variable("maxcd"))(1, 1::0::Nil)
    *                    |- a+b <= max(c, d) + e
    * }}}
    * @param name The new variable to use as an abbreviation.
    * */
  def abbrv(name: Variable): DependentPositionTactic = EqualityTactics.abbrv(name)
  /** Rewrites free occurrences of the left-hand side of an equality into the right-hand side at a specific position.
    * @example{{{
    *    x=0 |- 0*y=0, x+1>0
    *    ---------------------eqL2R(-1)(1)
    *    x=0 |- x*y=0, x+1>0
    * }}}
    * @param eqPos The position of the equality. If it points to a formula, it rewrites all occurrences of left in that formula.
    *              If it points to a specific term, then only this term is rewritten.
    */
  //@todo missing AxiomInfo for tactic extraction
  def eqL2R(eqPos: Int): DependentPositionTactic = EqualityTactics.eqL2R(eqPos)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = EqualityTactics.eqL2R(eqPos)
  /** Rewrites free occurrences of the right-hand side of an equality into the left-hand side at a specific position ([[EqualityTactics.eqR2L]]). */
  def eqR2L(eqPos: Int): DependentPositionTactic = EqualityTactics.eqR2L(eqPos)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = EqualityTactics.eqR2L(eqPos)
  /** Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively ([[EqualityTactics.exhaustiveEqL2R]]). */
  lazy val exhaustiveEqL2R: DependentPositionTactic = exhaustiveEqL2R(false)
  def exhaustiveEqL2R(hide: Boolean = false): DependentPositionTactic =
    if (hide) "allL2R" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(fml@Equal(_, _)) => EqualityTactics.exhaustiveEqL2R(pos) & hideL(pos, fml)
    })
    else EqualityTactics.exhaustiveEqL2R
  /** Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively ([[EqualityTactics.exhaustiveEqR2L]]). */
  lazy val exhaustiveEqR2L: DependentPositionTactic = exhaustiveEqR2L(false)
  def exhaustiveEqR2L(hide: Boolean = false): DependentPositionTactic =
    if (hide) "allR2L" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(fml@Equal(_, _)) => EqualityTactics.exhaustiveEqR2L(pos) & hideL(pos, fml)
    })
    else EqualityTactics.exhaustiveEqR2L

  //
  /** OnAll(e) == <(e, ..., e) runs tactic `e` on all current branches. */
  def onAll(e: BelleExpr): BelleExpr = OnAll(e)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Contract Tactics and Debugging Tactics
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Tactic contracts
  /** Assert that the given condition holds for the goal's sequent. */
  def assertT(cond : Sequent=>Boolean, msg: => String): BelleExpr = DebuggingTactics.assert(cond, msg)
  /** Assert that the sequent has the specified number of antecedent and succedent formulas, respectively. */
  def assertT(antecedents: Int, succedents: Int, msg: => String = ""): BelleExpr = DebuggingTactics.assert(antecedents, succedents, msg)

  // PositionTactic contracts
  /** Assert that the given condition holds for the sequent at the position where the tactic is applied */
  def assertT(cond : (Sequent,Position)=>Boolean, msg: => String): BuiltInPositionTactic = DebuggingTactics.assert(cond, msg)
  /** Assert that the given expression is present at the position in the sequent where this tactic is applied to. */
  def assertE(expected: => Expression, msg: => String): BuiltInPositionTactic = DebuggingTactics.assertE(expected, msg)

  /** errorT raises an error upon executing this tactic, stopping processing */
  def errorT(msg: => String): BuiltInTactic = DebuggingTactics.error(msg)

  /** debug(s) sprinkles debug message s into the output and the ProofNode information */
  def debug(s: => Any): BuiltInTactic = DebuggingTactics.debug(s.toString)
  /** debugAt(s) sprinkles debug message s into the output and the ProofNode information */
  def debugAt(s: => Any): BuiltInPositionTactic = DebuggingTactics.debugAt(s.toString)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Special functions
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /** Expands absolute value using `abs(x)=y <-> (x>=0&y=x | x<=0&y=-x)`, see [[EqualityTactics.abs]] */
  lazy val abs: DependentPositionTactic = EqualityTactics.abs
  /** Expands minimum function using `min(x,y)=z <-> (x<=y&z=x | x>=y&z=y)`, see [[EqualityTactics.minmax]] */
  lazy val min: DependentPositionTactic = EqualityTactics.minmax
  /** Expands maximum function using `max(x,y)=z <-> (x>=y&z=x | x<=y&z=y)`, see [[EqualityTactics.minmax]] */
  lazy val max: DependentPositionTactic = EqualityTactics.minmax

  /** Alpha rules are propositional rules that do not split */
  lazy val alphaRule: BelleExpr = (andL('_) ) |
        ((implyR('_) ) |
          (
            (notR('_) )
            )
          )
  /** Beta rules are propositional rules that split */
  lazy val betaRule: BelleExpr = (andR('_) ) |
    ((orL('_) ) |
      (  //(implyL('_) ) |
        ((notL('_) ) |
        ((equivL('_) ) |
          (equivR('_) )
          )
        )
      ))

//  /** Lazy Quantifier Elimination after decomposing the logic in smart ways */
//  //@todo ideally this should be ?RCF so only do anything of RCF if it all succeeds with true
//  def lazyQE = (
//    ((alphaRule | allR('_) | existsL('_)
//          | close
//          //@todo eqLeft|eqRight for equality rewriting directionally toward easy
//          //| (la(TacticLibrary.eqThenHideIfChanged)*)
//          | betaRule)*)
//      | QE)



  // Global Utility Functions

  /**
    * The position of `here()` in the formula `fml`.
    * @return The term or formula position where `here()` occurs in `fml`.
    * @throws IllegalArgumentException if `here()` does not occur in `fml`.
    * @example {{{
    *    positionOf("p() & x>2 -> here() | x=y^2".asFormula) == PosInExpr(1::0::Nil)
    *    positionOf("p() & here() -> x=1 | x=y^2".asFormula) == PosInExpr(0::1::Nil)
    *    positionOf("p() & x>2 -> x=1 | here()=y^2".asFormula) == PosInExpr(1::1::0::Nil)
    *    positionOf("p() & x>2 -> x=1 | x=here()^2".asFormula) == PosInExpr(1::1::1::0::Nil)
    *    positionOf("_ & here() -> _ | _".asFormula) == PosInExpr(0::1::Nil)
    *    positionOf("_ & _ -> _ | .=here()^2".asFormula) == PosInExpr(1::1::1::0::Nil)
    *    positionOf("_ & here() -> _".asFormula) == PosInExpr(0::1::Nil)
    * }}}
    */
  def positionOf(fml: Formula): PosInExpr = fml.find(e =>
    e==FuncOf(Function("here",None,Unit,Real),Nothing) || e==PredOf(Function("here",None,Unit,Bool),Nothing)
  ) match {
    case Some((pos,_)) => pos
    case None => throw new IllegalArgumentException("here() locator does not occur in positionOf(" + fml + ")")
  }

  /**
    * Prove the new goal by the given tactic, returning the resulting Provable
    *
    * @see [[SequentialInterpreter]]
    * @see [[TactixLibrary.by(Provable)]]
    * @see [[proveBy()]]
    */
  def proveBy(goal: Provable, tactic: BelleExpr): Provable = {
    val v = BelleProvable(goal)
    //@todo fetch from some factory
    SequentialInterpreter()(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => throw new BelleUserGeneratedError("Error in proveBy, goal\n" + goal + " was not provable but instead resulted in\n" + r)
    }
  }

  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
    *
   * @see [[SequentialInterpreter]]
   * @see [[TactixLibrary.by(Provable)]]
   * @see [[proveBy()]]
   * @example {{{
   *   import StringConverter._
   *   import TactixLibrary._
   *   val proof = TactixLibrary.proveBy(Sequent(IndexedSeq(), IndexedSeq("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula)), prop)
   * }}}
   */
  def proveBy(goal: Sequent, tactic: BelleExpr): Provable = proveBy(Provable.startProof(goal), tactic)
  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
    *
   * @see [[TactixLibrary.by(Provable)]]
   * @example {{{
   *   import StringConverter._
   *   import TactixLibrary._
   *   val proof = TactixLibrary.proveBy("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula, prop)
   * }}}
   */
  def proveBy(goal: Formula, tactic: BelleExpr): Provable = proveBy(Sequent(IndexedSeq(), IndexedSeq(goal)), tactic)

  ///

  /* Axiom and tactic index for stepAt */
  private def sequentStepIndex(isAnte: Boolean)(expr: Expression): Option[String] = (expr, isAnte) match {
    case (True, false) => Some("closeTrue")
    case (False, true) => Some("closeFalse")
    case (_: Not, true) => Some("notL")
    case (_: Not, false) => Some("notR")
    case (_: And, true) => Some("andL")
    case (_: And, false) => Some("andR")
    case (_: Or, true) => Some("orL")
    case (_: Or, false) => Some("orR")
    case (_: Imply, true) => Some("implyL")
    case (_: Imply, false) => Some("implyR")
    case (_: Equiv, true) => Some("equivL")
    case (_: Equiv, false) => Some("equivR")
    case (_: Forall, true) => Some("allL")
    case (_: Forall, false) => Some("allR")
    case (_: Exists, true) => Some("existsL")
    case (_: Exists, false) => Some("existsR")
    case _ => AxiomIndex.axiomFor(expr) /* @note same as HilbertCalculus.stepAt(pos) */
  }


}
