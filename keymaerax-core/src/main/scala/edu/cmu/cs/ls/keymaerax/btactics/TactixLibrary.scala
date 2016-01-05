/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.{?, must}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, Generator, NoneGenerate, Position, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tools.DiffSolutionTool

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Tactix: Main tactic library with simple interface.
 *
 * This library features all main tactic elements for most common cases, except sophisticated tactics.
 * Brief documentation for the tactics is provided inline in this interface file.
 *
 * '''Following tactics forward to their implementation reveals more detailed documentation'''
 *
 * For tactics implementing built-in rules such as sequent proof rules,
 * elaborate documentation is in the [[edu.cmu.cs.ls.keymaerax.core.Rule prover kernel]].
 *
 * @author Andre Platzer
 * @author Stefan Mitsch
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[HilbertCalculi]]
 * @see [[SequentCalculi]]
 * @see [[UnifyUSCalculus]]
 * @see [[DerivedAxioms]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
 */
object TactixLibrary extends HilbertCalculi with SequentCalculi {
  /** Generates loop and differential invariants */
  var invGenerator: Generator[Formula] = new NoneGenerate()

  /** step: one canonical simplifying proof step at the indicated formula/term position (unless @invariant etc needed) */
  lazy val step               : DependentPositionTactic = HilbertCalculus.stepAt

    /** Normalize to sequent form, keeping branching factor down by precedence */
  lazy val normalize               : BelleExpr = DoAll(?(
    (alphaRule partial)
      | (closeId
      | ((allR('R) partial)
      | ((existsL('L) partial)
      | (close
      | ((betaRule partial)
      | ((step('L) partial)
      | ((step('R) partial) partial) partial) partial) partial) partial) partial) partial) partial) partial)*@TheType()

  /** exhaust propositional logic */
  lazy val prop                    : BelleExpr = DoAll(?(
    (close
      | ((alphaRule partial)
      | ((betaRule partial) partial) partial) partial) partial) partial)*@TheType()

  /** master: master tactic that tries hard to prove whatever it could */
  def master(gen: Generator[Formula] = invGenerator): BelleExpr =
    DoAll(?(
      (close
        | ((must(normalize) partial)
        | ((loop(gen)('L) partial)
        | ((loop(gen)('R) partial)
        | ((diffSolve(None)('R) partial)
        | ((diffInd partial)
        | (exhaustiveEqL2R('L) partial) partial) partial) partial) partial) partial) partial) partial) partial)*@TheType() & ?(DoAll(QE))

  /*******************************************************************
    * unification and matching based auto-tactics
    * @see [[UnifyUSCalculus]]
    *******************************************************************/

  /** US: uniform substitution ([[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule USubst]])
    * @see [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]]
    * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
    */
  def US(subst: USubst, origin: Sequent): BuiltInTactic = ProofRuleTactics.US(subst, origin)

  // conditional tactics

  /**
   * onBranch((lbl1,t1), (lbl2,t2)) uses tactic t1 on branch labelled lbl1 and t2 on lbl2
   * @see [[edu.cmu.cs.ls.keymaerax.tactics.BranchLabels]]
   * @note Probably this String should be a BelleLabel, and we should move BranchLabels into BelleLabel.
   * @see [[label()]]
   */
  def onBranch(s1: (String, BelleExpr), spec: (String, BelleExpr)*): BelleExpr = ??? //SearchTacticsImpl.onBranch(s1, spec:_*)

  /** Call/label the current proof branch s
    * @see [[onBranch()]]
    * @see [sublabel()]]
    */
  def label(s: String): BelleExpr = ??? //new LabelBranch(s)

  /** Mark the current proof branch and all subbranches s
    * @see [[label()]]
    */
  def sublabel(s: String): BelleExpr = ??? //new SubLabelBranch(s)

  // modalities

  /** discreteGhost: introduces a ghost defined as term t; if ghost is None the tactic chooses a name by inspecting t */
  def discreteGhost(t: Term, ghost: Option[Variable] = None): DependentPositionTactic = DLBySubst.discreteGhost(t, ghost)

  /** abstraction: turns '[a]p' into \\forall BV(a) p */
  lazy val abstractionb       : DependentPositionTactic = DLBySubst.abstractionb

  /** 'position' tactic t with universal abstraction at the same position afterwards
    * @see [[abstractionb]] */
  def withAbstraction(t: AtPosition[_ <: BelleExpr]): DependentPositionTactic = new DependentPositionTactic("with abstraction") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isTopLevel, "with abstraction only at top-level")
        sequent(pos) match {
          case Box(a, p) =>
            t(pos) & abstractionb(pos) & (if (pos.isSucc) allR(pos)*@TheType() partial else skip)
          case Diamond(a, p) if pos.isAnte => ???
        }
      }
    }
  }

  /**
   * loop: prove a property of a loop by induction with the given loop invariant (hybrid systems)
   * @see [[DLBySubst.I]]
   */
  def loop(invariant : Formula)  : DependentPositionTactic = DLBySubst.I(invariant)
  def I(invariant: Formula)      : DependentPositionTactic = loop(invariant)
  /** loop=I: prove a property of a loop by induction, if the given generator finds a loop invariant
    * @see [[loop(Formula)]] */
  def loop(gen: Generator[Formula]): DependentPositionTactic = new DependentPositionTactic("I gen") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = loop(gen(sequent, pos).getOrElse(
        throw new BelleError("Unable to generate an invariant for " + sequent(pos) + " at position " + pos)))(pos)
    }
  }

  // differential equations

  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)` */
  def diffSolve(solution: Option[Formula] = None): DependentPositionTactic = DifferentialTactics.diffSolve(solution)(tool)

  /** DW: Differential Weakening to use evolution domain constraint `[{x'=f(x)&q(x)}]p(x)` reduces to `\forall x (q(x)->p(x))` */
  lazy val diffWeaken         : DependentPositionTactic = withAbstraction(DW)
  /** DC: Differential Cut a new invariant, use old(.) to refer to initial values of variables.
    * @see[[DC]]
    * @see[[DifferentialTactics.diffCut]]
    */
  def diffCut(formulas: Formula*)     : DependentPositionTactic = DifferentialTactics.diffCut(formulas:_*)
  /** DI: Differential Invariant proves a formula to be an invariant of a differential equation (plus usual steps) */
  def diffInd(implicit qeTool: QETool): DependentPositionTactic = DifferentialTactics.diffInd(qeTool)
  /** DC+DI: Prove the given list of differential invariants in that order by DC+DI via [[diffCut]] followed by [[diffInd]] */
  def diffInvariant(invariants: Formula*): DependentPositionTactic =
    DifferentialTactics.diffInvariant(tool, invariants:_*)

  /** DG: Differential Ghost add auxiliary differential equations with extra variables `y'=a*y+b`.
    * `[x'=f(x)&q(x)]p(x)` reduces to `\exists y [x'=f(x),y'=a*y+b&q(x)]p(x)`.
    */
  override def DG(y:Variable, a:Term, b:Term): DependentPositionTactic = DifferentialTactics.DG(y, a, b)
  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and postcondition replaced by r.
    * {{{
    * G |- p(x), D   |- r(x,y) -> [x'=f(x),y'=g(x,y)&q(x)]r(x,y)
    * ----------------------------------------------------------- DA
    * G |- [x'=f(x)&q(x)]p(x), D
    * }}}
    * @see[[DA(Variable, Term, Term, Provable)]]
    * @note Uses QE to prove p(x) <-> \exists y. r(x,y)
    * @note G |- p(x) will be proved already from G if p(x) in G (verbatim)
    */
  def DA(y:Variable, a:Term, b:Term, r:Formula) : BuiltInPositionTactic = ??? //ODETactics.diffAuxiliariesRule(y,a,b,r)
  /**
   * DA: Differential Ghost expert mode. Use if QE cannot prove p(x) <-> \exists y. r(x,y).
   * To obtain a Provable with conclusion p(x) <-> \exists y. r(x,y), use TactixLibrary.by, for example:
   * @example{{{
   *   val provable = by("x>0 <-> \exists y (y>0&x*y>0)".asFormula, QE)
   * }}}
   * @see[[DA(Variable, Term, Term, Formula)]]
   * @see[[by]]
   **/
  def DA(y:Variable, a:Term, b:Term, r:Provable) : BuiltInPositionTactic = ??? //ODETactics.diffAuxiliariesRule(y,a,b,r)

  /** Dconstify: substitute all non-bound occurences of variables x with constant function symbols x() */
  lazy val Dconstify          : DependentPositionTactic = DifferentialTactics.Dconstify


  // more

  /**
   * Generalize postcondition to C and, separately, prove that C implies postcondition.
   * {{{
   *   genUseLbl:        genShowLbl:
   *   G |- [a]C, D      C |- B
   *   ------------------------
   *          G |- [a]B, D
   * }}}
   * @see [[DLBySubst.generalize]]
   */
  def generalize(C: Formula)  : DependentPositionTactic = DLBySubst.generalize(C)

  /** Prove the given cut formula to hold for the modality at position and turn postcondition into cut->post
    * {{{
    *   cutUseLbl:           cutShowLbl:
    *   G |- [a](C->B), D    G |- [a]C, D
    *   ---------------------------------
    *          G |- [a]B, D
    * }}}
    * @see [[DLBySubst.postCut]]
    */
  def postCut(cut: Formula)   : DependentPositionTactic = DLBySubst.postCut(cut)



  // closing

  /** QE: Quantifier Elimination to decide arithmetic (after simplifying logical transformations) */
  def QE(order: List[NamedSymbol] = Nil): BelleExpr = ToolTactics.fullQE(order)
  def QE: BelleExpr = QE()

  // counter example

  /** Generate counter example */
//  lazy val counterEx         : Tactic         = TacticLibrary.counterExampleT

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Bigger Tactics.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Utility Tactics
  /** nil: skip is a no-op tactic that has no effect */
  lazy val nil : BelleExpr = Idioms.ident
  /** nil: skip is a no-op tactic that has no effect */
  lazy val skip : BelleExpr = nil

  /** abbrv(name) Abbreviate the term at the given position by a new name and use that name at all occurrences of that term ([[EqualityTactics.abbrv]]) */
  def abbrv(name: Variable): DependentPositionTactic = EqualityTactics.abbrv(name)
  /** Rewrites free occurrences of the left-hand side of an equality into the right-hand side at a specific position ([[EqualityTactics.eqL2R]]). */
  def eqL2R(eqPos: Int): DependentPositionTactic = EqualityTactics.eqL2R(eqPos)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = EqualityTactics.eqL2R(eqPos)
  /** Rewrites free occurrences of the right-hand side of an equality into the left-hand side at a specific position ([[EqualityTactics.eqR2L]]). */
  def eqR2L(eqPos: Int): DependentPositionTactic = EqualityTactics.eqR2L(eqPos)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = EqualityTactics.eqR2L(eqPos)
  /** Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively ([[EqualityTactics.exhaustiveEqL2R]]). */
  lazy val exhaustiveEqL2R: DependentPositionTactic = exhaustiveEqL2R(false)
  def exhaustiveEqL2R(hide: Boolean = false): DependentPositionTactic =
    if (hide) "Find Left and Replace Left with Right" by ((pos, sequent) => sequent.sub(pos) match {
      case Some(fml: Formula) => EqualityTactics.exhaustiveEqL2R(pos) & hideL(Find(0, Some(fml), AntePosition(0), exact=true))
    })
    else EqualityTactics.exhaustiveEqL2R
  /** Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively ([[EqualityTactics.exhaustiveEqR2L]]). */
  lazy val exhaustiveEqR2L: DependentPositionTactic = exhaustiveEqR2L(false)
  def exhaustiveEqR2L(hide: Boolean = false): DependentPositionTactic =
    if (hide) "Find Right and Replace Right with Left" by ((pos, sequent) => sequent.sub(pos) match {
      case Some(fml: Formula) => EqualityTactics.exhaustiveEqR2L(pos) & hideL(Find(0, Some(fml), AntePosition(0), exact=true))
    })
    else EqualityTactics.exhaustiveEqR2L


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
  /** Expands abs using abs(x)=y <-> (x>=0&y=x | x<=0&y=-x), see [[EqualityTactics.abs]] */
  lazy val abs: DependentPositionTactic = EqualityTactics.abs
  /** Expands min using min(x,y)=z <-> (x<=y&z=x | x>=y&z=y), see [[EqualityTactics.minmax]] */
  lazy val min: DependentPositionTactic = EqualityTactics.minmax
  /** Expands max using max(x,y)=z <-> (x>=y&z=x | x<=y&z=y), see [[EqualityTactics.minmax]] */
  lazy val max: DependentPositionTactic = EqualityTactics.minmax

  /** Alpha rules are propositional rules that do not split */
  lazy val alphaRule: BelleExpr = (andL('_) partial) |
    ((orR('_) partial) |
      ((implyR('_) partial) |
        ((notL('_) partial) |
          (notR('_) partial)
          partial)
        partial)
      partial)
  /** Beta rules are propositional rules that split */
  lazy val betaRule: BelleExpr = (andR('_) partial) |
    ((orL('_) partial) |
      ((implyL('_) partial) |
        ((equivL('_) partial) |
          (equivR('_) partial)
          partial)
        partial)
      partial)
  /** Real-closed field arithmetic after consolidating sequent into a single universally-quantified formula */
  def RCF: BelleExpr = QE

  /** Lazy Quantifier Elimination after decomposing the logic in smart ways */
  //@todo ideally this should be ?RCF so only do anything of RCF if it all succeeds with true
  def lazyQE = (
    ((alphaRule | allR('_) | existsL('_)
      | close
      //@todo eqLeft|eqRight for equality rewriting directionally toward easy
      //| (la(TacticLibrary.eqThenHideIfChanged)*)
      | betaRule)*@TheType())
      | RCF)


  // Global Utility Functions

  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
   * @see [[TactixLibrary.by(Provable)]]
   * @see [[proveBy()]]
   * @example {{{
   *   import StringConverter._
   *   import TactixLibrary._
   *   val proof = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula)), prop)
   * }}}
   */
  def proveBy(goal: Sequent, tactic: BelleExpr): Provable = {
    val v = BelleProvable(Provable.startProof(goal))
    //@todo fetch from some factory
    SequentialInterpreter()(tactic, v) match {
      case BelleProvable(provable, _) => provable
      case r => throw new BelleUserGeneratedError("Error in proveBy, goal\n " + goal + " was not provable but instead resulted in\n " + r)
    }
  }
  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
   * @see [[TactixLibrary.by(Provable)]]
   * @example {{{
   *   import StringConverter._
   *   import TactixLibrary._
   *   val proof = TactixLibrary.proveBy("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula, prop)
   * }}}
   */
  def proveBy(goal: Formula, tactic: BelleExpr): Provable = proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq(goal)), tactic)

}
