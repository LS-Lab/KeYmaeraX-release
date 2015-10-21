/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._

import scala.collection.immutable
import scala.collection.immutable._

/**
 * Tactix: Main tactic library with simple interface.
 *
 * This library features all main tactic elements for most common cases, except sophisticated tactics.
 * Brief documentation for the tactics is provided inline in this interface file.
 *
 * *Following tactics forward to their implementation reveals more detailed documentation*.
 *
 * For tactics implementing built-in rules such as sequent proof rules,
 * elaborate documentation is in the [[edu.cmu.cs.ls.keymaerax.core.Rule prover kernel]].
 *
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[HilbertCalculus]]
 * @see [[UnifyUSCalculus]]
 * @see [[TacticLibrary]]
 * @see [[DerivedAxioms]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
 */
object TactixLibrary extends UnifyUSCalculus {
  private val parser = KeYmaeraXParser

//  /** step: makes one sequent proof step to simplify the formula at the indicated position (unless @invariant needed) */
  val step                    : PositionTactic = TacticLibrary.step

  /** stepAt: one canonical simplifying proof step at the indicated formula/term position (unless @invariant etc needed) */
  lazy val stepAt             : PositionTactic = HilbertCalculus.stepAt

    /** Normalize to sequent form, keeping branching factor down by precedence */
  def normalize               : Tactic = (alphaRule | closeId | ls(allR) | la(existsL)
    | close
    | betaRule
    | l(step))*
  /** exhaust propositional logic */
  def prop                    : Tactic = TacticLibrary.propositional
  /** master: master tactic that tries hard to prove whatever it could */
  def master                  : Tactic = master(new NoneGenerate(), "Mathematica")
  def master(qeTool: String)  : Tactic = master(new NoneGenerate(), qeTool)
  def master(gen: Generator[Formula] = new NoneGenerate(), qeTool: String = "Mathematica"): Tactic = TacticLibrary.master(gen, true, qeTool)

  /*******************************************************************
    * unification and matching based auto-tactics
    * @see [[UnifyUSCalculus]]
    *******************************************************************/

  /** US: uniform substitution ([[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule USubst]])
    * @see [[UnifyUSCalculus]]
    * @see [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]]
    * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
    */
  def US(subst: List[SubstitutionPair], delta: (Map[Formula, Formula]) = Map()): Tactic = PropositionalTacticsImpl.uniformSubstT(subst, delta)

  // conditional tactics

  /**
   * onBranch((lbl1,t1), (lbl2,t2)) uses tactic t1 on branch labelled lbl1 and t2 on lbl2
   * @see [[BranchLabels]]
   * @see [[label()]]
   */
  def onBranch(s1: (String, Tactic), spec: (String, Tactic)*): Tactic = SearchTacticsImpl.onBranch(s1, spec:_*)

  /** Call/label the current proof branch s
    * @see [[onBranch()]]
    * @see [sublabel()]]
    */
  def label(s: String): Tactic = new LabelBranch(s)

  /** Mark the current proof branch and all subbranches s
    * @see [[label()]]
    */
  def sublabel(s: String): Tactic = new SubLabelBranch(s)

  // Locating applicable positions for PositionTactics


  /** Locate applicable position in antecedent on the left in which something matching the given shape occurs */
  def llu(tactic: PositionTactic, shape: Formula): Tactic =
    SearchTacticsImpl.locateAnte(tactic, f => UnificationMatch.unifiable(f, shape)!=None)
  /** Locate applicable position in antecedent on the left in which something matching the given shape occurs */
  def llu(tactic: PositionTactic, shape: String): Tactic = llu(tactic, parser.formulaParser(shape))
  /** Locate applicable position in succedent on the right in which something matching the given shape occurs */
  def lru(tactic: PositionTactic, shape: Formula): Tactic =
    SearchTacticsImpl.locateSucc(tactic, f => UnificationMatch.unifiable(f, shape)!=None)
  /** Locate applicable position in succedent on the right in which something matching the given shape occurs */
  def lru(tactic: PositionTactic, shape: String): Tactic = lru(tactic, parser.formulaParser(shape))

  /** Locate applicable position in succedent on the right in which fml occurs verbatim */
  def ls(tactic: PositionTactic, fml: String = "", key: Option[Expression] = None): Tactic =
    SearchTacticsImpl.locateSucc(tactic,
      if (fml == "") (_ => true) else _ == fml.asFormula,
      if (key.isDefined) Some(_ == key.get) else None)
  /** Locate applicable position in succedent on the right */
  def lR(tactic: PositionTactic): Tactic = ls(tactic)
  /** Locate applicable position in antecedent on the left in which fml occurs verbatim  */
  def la(tactic: PositionTactic, fml: String = "", key: Option[Expression] = None): Tactic =
    SearchTacticsImpl.locateAnte(tactic,
      if (fml == "") _ => true else _ == fml.asFormula,
      if (key.isDefined) Some(_ == key.get) else None)
  /** Locate applicable position in antecedent on the left */
  def lL(tactic: PositionTactic): Tactic = la(tactic)
  /** Locate applicable position in left or right in antecedent or succedent */
  def l(tactic: PositionTactic): Tactic  = TacticLibrary.locateAnteSucc(tactic)
  /** Locate applicable position within a given position */
  def lin(tactic: PositionTactic): PositionTactic = ???


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics

  /** Hide/weaken whether left or right */
  lazy val hide               : PositionTactic = TacticLibrary.hideT
  /** Hide/weaken given formula at given position */
  def hide(fml: Formula)      : PositionTactic = assertT(fml, "hiding expects given formula") ~ TacticLibrary.hideT
  /** Hide/weaken left: weaken a formula to drop it from the antecedent ([[edu.cmu.cs.ls.keymaerax.core.HideLeft HideLeft]]) */
  lazy val hideL              : PositionTactic = TacticLibrary.hideT
  /** Hide/weaken right: weaken a formula to drop it from the succcedent ([[edu.cmu.cs.ls.keymaerax.core.HideRight HideRight]]) */
  lazy val hideR              : PositionTactic = TacticLibrary.hideT
  /** CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  lazy val cohide             : PositionTactic = PropositionalTacticsImpl.cohideT
  /** !L Not left: move an negation in the antecedent to the succedent ([[edu.cmu.cs.ls.keymaerax.core.NotLeft NotLeft]]) */
  lazy val notL               : PositionTactic = TacticLibrary.NotLeftT
  /** !R Not right: move an negation in the succedent to the antecedent ([[edu.cmu.cs.ls.keymaerax.core.NotRight NotRight]]) */
  lazy val notR               : PositionTactic = TacticLibrary.NotRightT
  /** &L And left: split a conjunction in the antecedent into separate assumptions ([[edu.cmu.cs.ls.keymaerax.core.AndLeft AndLeft]]) */
  lazy val andL               : PositionTactic = TacticLibrary.AndLeftT
  /** &R And right: prove a conjunction in the succedent on two separate branches ([[edu.cmu.cs.ls.keymaerax.core.AndRight AndRight]]) */
  lazy val andR               : PositionTactic = TacticLibrary.AndRightT
  /** |L Or left: use a disjunction in the antecedent by assuming each option on separate branches ([[edu.cmu.cs.ls.keymaerax.core.OrLeft OrLeft]]) */
  lazy val orL                : PositionTactic = TacticLibrary.OrLeftT
  /** |R Or right: split a disjunction in the succedent into separate formulas to show alternatively ([[edu.cmu.cs.ls.keymaerax.core.OrRight OrRight]]) */
  lazy val orR                : PositionTactic = TacticLibrary.OrRightT
  /** ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its right-hand side on the other branch ([[edu.cmu.cs.ls.keymaerax.core.ImplyLeft ImplyLeft]]) */
  lazy val implyL             : PositionTactic = TacticLibrary.ImplyLeftT
  /** ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand side ([[edu.cmu.cs.ls.keymaerax.core.ImplyRight ImplyRight]]) */
  lazy val implyR             : PositionTactic = TacticLibrary.ImplyRightT
  /** <->L Equiv left: use an equivalence by considering both true or both false cases ([[edu.cmu.cs.ls.keymaerax.core.EquivLeft EquivLeft]]) */
  lazy val equivL             : PositionTactic = TacticLibrary.EquivLeftT
  /** <->R Equiv right: prove an equivalence by proving both implications ([[edu.cmu.cs.ls.keymaerax.core.EquivRight EquivRight]]) */
  lazy val equivR             : PositionTactic = TacticLibrary.EquivRightT

  /** cut a formula in to prove it on one branch and then assume it on the other. Or to perform a case distinction on whether it holds ([[edu.cmu.cs.ls.keymaerax.core.Cut Cut]]) */
  def cut(cut : Formula)      : Tactic         = TacticLibrary.cutT(Some(cut))
  /** cut a formula in in place of pos on the right to prove it on one branch and then assume it on the other. ([[edu.cmu.cs.ls.keymaerax.core.CutRight CutRight]]) */
  def cutR(cut : Formula)     : PositionTactic  = PropositionalTacticsImpl.cutRightT(cut)
  /** cut a formula in in place of pos on the left to prove it on one branch and then assume it on the other. ([[edu.cmu.cs.ls.keymaerax.core.CutLeft CutLeft]]) */
  def cutL(cut : Formula)     : PositionTactic  = PropositionalTacticsImpl.cutLeftT(cut)
  /** cut a formula in in place of pos to prove it on one branch and then assume it on the other (whether pos is left or right). ([[edu.cmu.cs.ls.keymaerax.core.CutLeft CutLeft]] or [[edu.cmu.cs.ls.keymaerax.core.CutRight CutRight]]) */
  def cutLR(cut : Formula)    : PositionTactic  = PropositionalTacticsImpl.cutLeftRight(cut)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // First-order tactics

  // quantifiers
  /** all right: Skolemize a universal quantifier in the succedent ([[edu.cmu.cs.ls.keymaerax.core.Skolemize Skolemize]]) */
  lazy val allR               : PositionTactic = TacticLibrary.skolemizeT
  /** all left: instantiate a universal quantifier in the antecedent by a concrete instance */
  def allL(x: Variable, inst: Term) : PositionTactic = TacticLibrary.instantiateQuanT(x, inst)
  def allL(inst: Term)        : PositionTactic = TacticLibrary.instantiateQuanT(???, inst)
  /** exists left: Skolemize an existential quantifier in the antecedent */
  lazy val existsL            : PositionTactic = TacticLibrary.skolemizeT
  /** exists right: instantiate an existential quantifier in the succedwent by a concrete instance as a witness */
  def existsR(x: Variable, inst: Term) : PositionTactic = TacticLibrary.instantiateQuanT(x, inst)
  def existsR(inst: Term)     : PositionTactic = TacticLibrary.instantiateQuanT(???, inst)

  // modalities

  /** assignb: [:=] simplify assignment `[x:=f;]p(x)` by substitution `p(f)` or equation */
  lazy val assignb            : PositionTactic = TacticLibrary.boxAssignT
  /** randomb: [:*] simplify nondeterministic assignment `[x:=*;]p(x)` to a universal quantifier `\forall x p(x)` */
  lazy val randomb            : PositionTactic = TacticLibrary.boxNDetAssign
  /** testb: [?] simplifies test `[?q;]p` to an implication `q->p` */
  lazy val testb              : PositionTactic = TacticLibrary.boxTestT
  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)` */
  lazy val diffSolve          : PositionTactic = TacticLibrary.diffSolutionT
  /** choiceb: [++] handles both cases of a nondeterministic choice `[a++b]p(x)` separately `[a]p(x) & [b]p(x)` */
  lazy val choiceb            : PositionTactic = TacticLibrary.boxChoiceT
  /** composeb: [;] handle both parts of a sequential composition `[a;b]p(x)` one at a time `[a][b]p(x)` */
  lazy val composeb           : PositionTactic = TacticLibrary.boxSeqT
  /** iterateb: [*] prove a property of a loop `[{a}*]p(x)` by unrolling it once `p(x) & [a][{a}*]p(x)` */
  lazy val iterateb           : PositionTactic = HilbertCalculus.iterateb

  /** splitb: splits `[a](p&q)` into `[a]p & [a]q` */
  lazy val splitb             : PositionTactic = HybridProgramTacticsImpl.boxSplitConjunctionT

  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
  /** loop=I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
  def loop(invariant: Formula) = I(invariant)
  /** K: modal modus ponens (hybrid systems) */
  lazy val K                  : PositionTactic = PropositionalTacticsImpl.kModalModusPonensT
  /** V: vacuous box [a]p() will be discarded and replaced by p() provided a does not changes values of postcondition p */
  lazy val V                  : PositionTactic = HybridProgramTacticsImpl.boxVacuousT

  // differential equations
  /** DW: Differential Weakening to use evolution domain constraint (equivalence form) */
  lazy val DW                 : PositionTactic = TacticLibrary.diffWeakenT
  /** DC: Differential Cut a new invariant for a differential equation */
  def DC(invariant: Formula)  : PositionTactic = TacticLibrary.diffCutT(invariant)
  /** DE: Differential Effect exposes the effect of a differential equation on its differential symbols */
  lazy val DE                 : PositionTactic = ODETactics.diffEffectT
  /** DI: Differential Invariant proves a formula to be an invariant of a differential equation */
  lazy val DI                 : PositionTactic = TacticLibrary.diffInvariant
  /** DG: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b */
  def DG(y:Variable, a:Term, b:Term) : PositionTactic = ODETactics.diffAuxiliaryT(y,a,b)
  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
  /** DS: Differential Solution solves a differential equation */
  def DS                      : PositionTactic = ???

  /** Dassignb: Substitute a differential assignment `[x':=f]p(x')` to `p(f)` */
  lazy val Dassignb           : PositionTactic = HybridProgramTacticsImpl.boxDerivativeAssignT
  /** Dplus: +' derives a sum `(f(x)+g(x))' = (f(x))' + (g(x))'` */
  lazy val Dplus              : PositionTactic = SyntacticDerivationInContext.AddDerivativeT
  /** neg: -' derives unary negation `(-f(x))' = -(f(x)')` */
  lazy val Dneg               : PositionTactic = SyntacticDerivationInContext.NegativeDerivativeT
  /** Dminus: -' derives a difference `(f(x)-g(x))' = (f(x))' - (g(x))'` */
  lazy val Dminus             : PositionTactic = SyntacticDerivationInContext.SubtractDerivativeT
  /** Dtimes: *' derives a product `(f(x)*g(x))' = f(x)'*g(x) + f(x)*g(x)'` */
  lazy val Dtimes             : PositionTactic = SyntacticDerivationInContext.MultiplyDerivativeT
  /** Dquotient: /' derives a quotient `(f(x)/g(x))' = (f(x)'*g(x) - f(x)*g(x)') / (g(x)^2)` */
  lazy val Dquotient          : PositionTactic = SyntacticDerivationInContext.DivideDerivativeT
  /** Dcompose: o' derives a function composition by chain rule */
  lazy val Dcompose           : PositionTactic = ???
  /** Dconstify: substitute non-bound occurences of x with x() */
  lazy val Dconstify          : PositionTactic = ODETactics.diffIntroduceConstantT

  /** Prove the given list of differential invariants in that order by DC+DI */
  //@todo could change type to invariants: Formula* if considered more readable
  def diffInvariant(invariants: List[Formula]): PositionTactic = ODETactics.diffInvariant(invariants)

  // more

  /* Generalize postcondition to C and, separately, prove that C implies postcondition
   * {{{
   *   genUseLbl:        genShowLbl:
   *   G |- [a]C, D      C |- B
   *   ------------------------
   *          G |- [a]B, D
   * }}}
   */
  def generalize(C: Formula)  : PositionTactic = TacticLibrary.generalize(C)

  /** Prove the given cut formula to hold for the modality at position and turn postcondition into cut->post
    * {{{
    *   cutUseLbl:           cutShowLbl:
    *   G |- [a](C->B), D    G |- [a]C, D
    *   ---------------------------------
    *          G |- [a]B, D
    * }}}
    */
  def postCut(cut: Formula)   : PositionTactic = TacticLibrary.postCut(cut)



  // closing

  /** QE: Quantifier Elimination to decide arithmetic (after simplifying logical transformations) */
  lazy val QE                : Tactic         = TacticLibrary.arithmeticT

  /** close: closes the branch when the same formula is in the antecedent and succedent or true or false close */
  lazy val close             : Tactic         = TacticLibrary.closeT
  /** close: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  def close(a: AntePosition, s: SuccPosition) : Tactic = PropositionalTacticsImpl.CloseId(a,s)
  def close(a: Int, s: Int)  : Tactic = close(new AntePosition(SeqPos(a).asInstanceOf[AntePos].getIndex), new SuccPosition(SeqPos(s).asInstanceOf[SuccPos].getIndex))
  /** closeId: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  lazy val closeId           : Tactic         = TacticLibrary.AxiomCloseT
  /** closeT: closes the branch when true is in the succedent ([[edu.cmu.cs.ls.keymaerax.core.CloseTrue CloseTrue]]) */
  lazy val closeT            : PositionTactic = TacticLibrary.CloseTrueT
  /** closeF: closes the branch when false is in the antecedent ([[edu.cmu.cs.ls.keymaerax.core.CloseFalse CloseFalse]]) */
  lazy val closeF            : PositionTactic = TacticLibrary.CloseFalseT

  // counter example

  /** Generate counter example */
  lazy val counterEx         : Tactic         = TacticLibrary.counterExampleT

  // derived

  /** Turn implication on the right into an equivalence, which is useful to prove by CE etc. ([[edu.cmu.cs.ls.keymaerax.core.EquivifyRight EquivifyRight]]) */
  lazy val equivifyR          : PositionTactic = PropositionalTacticsImpl.equivifyRightT
  /** Commute an equivalence on the right. ([[edu.cmu.cs.ls.keymaerax.core.CommuteEquivRight CommuteEquivRight]]) */
  lazy val commuteEquivR      : PositionTactic = PropositionalTacticsImpl.commuteEquivRightT
  //@todo commuteEquivLeft

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Bigger Tactics.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Utility Tactics
  /** nil: skip is a no-op tactic that has no effect */
  lazy val nil : Tactic = Tactics.NilT
  /** nil: skip is a no-op tactic that has no effect */
  lazy val skip : Tactic = nil

  /** abbrv(name) Abbreviate the term at the given position by a new name and use that name at all occurrences of that term. */
  def abbrv(name: Variable): PositionTactic = EqualityRewritingImpl.abbrv(name)


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Contract Tactics and Debugging Tactics
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Tactic contracts
  /** Assert that the given condition holds for the goal's sequent. */
  def assertT(cond : Sequent=>Boolean, msg:String = ""): Tactic = Tactics.assertT(cond, msg)
  /** Assertion that the sequent has the specified number of antecedent and succedent formulas, respectively. */
  def assertT(antecedents: Int, succedents: Int): Tactic = Tactics.assertT(antecedents, succedents)
  /** Assert that the given formula is present at the given position in the sequent that this tactic is applied to. */
  def assertT(expected: Formula, pos: Position, msg:String): Tactic = Tactics.assertT(expected, pos, msg)

  // PositionTactic contracts
  /** Assert that the given condition holds for the sequent at the position where the tactic is applied */
  def assertT(cond : (Sequent,Position)=>Boolean, msg:String): PositionTactic = Tactics.assertPT(cond, msg)
  /** Assert that the given expression is present at the position in the sequent where this tactic is applied to. */
  def assertT(expected: Expression, msg:String): PositionTactic = expected match {
    case t: Term => Tactics.assertPT(t, msg)
    case f: Formula => Tactics.assertPT(f, msg)
  }

  /** errorT raises an error upon executing this tactic, stopping processing */
  def errorT(msg: String): Tactic = Tactics.errorT(msg)

  /** debug(s) sprinkles debug message s into the output and the ProofNode information */
  def debug(s: => Any): Tactic = TacticLibrary.debugT(s)
  /** debugAt(s) sprinkles debug message s into the output and the ProofNode information */
  def debugAt(s: => Any): PositionTactic = TacticLibrary.debugAtT(s)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Special functions
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /** Expands abs using abs(x)=y <-> (x>=0&y=x | x<=0&y=-x) */
  def abs: PositionTactic = ArithmeticTacticsImpl.AbsT
  /** Expands min using min(x,y)=z <-> (x<=y&z=x | x>=y&z=y) */
  def min: PositionTactic = ArithmeticTacticsImpl.MinMaxT
  /** Expands max using max(x,y)=z <-> (x>=y&z=x | x<=y&z=y) */
  def max: PositionTactic = ArithmeticTacticsImpl.MinMaxT


  /** Alpha rules are propositional rules that do not split */
  def alphaRule: Tactic = lL(andL) | lR(orR) | lR(implyR) | lL(notL) | lR(notR)
  /** Beta rules are propositional rules that split */
  def betaRule: Tactic = lR(andR) | lL(orL) | lL(implyL) | lL(equivL) | lR(equivR)
  /** Real-closed field arithmetic after consolidating sequent into a single universally-quantified formula */
  def RCF: Tactic = PropositionalTacticsImpl.ConsolidateSequentT & assertT(0, 1) & FOQuantifierTacticsImpl.universalClosureT(1) & debug("Handing to Mathematica") &
    ArithmeticTacticsImpl.quantifierEliminationT("Mathematica")

  /** Lazy Quantifier Elimination after decomposing the logic in smart ways */
  //@todo ideally this should be ?RCF so only do anything of RCF if it all succeeds with true
  def lazyQE = (
    ((alphaRule | ls(allR) | la(existsL)
      | close
      //@todo eqLeft|eqRight for equality rewriting directionally toward easy
      | (la(TacticLibrary.eqThenHideIfChanged)*)
      | betaRule)*)
      | RCF)


  // Global Utility Functions

  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
   * @see [[TactixLibrary.by(Provable)]]
   * @see [[proveBy()]]
   * @example {{{
   *   import StringConverter._
   *   val proof = TactixLibrary.proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula)), prop)
   * }}}
   */
  def proveBy(goal: Sequent, tactic: Tactic): Provable = {
    val rootNode = new RootNode(goal)
    //@todo what/howto ensure it's been initialized already
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))
    if (!rootNode.isClosed() || Tactic.DEBUG) println("proveBy " + (if (rootNode.isClosed()) "closed" else "open\n\n" + rootNode.openGoals().map(x => "Open: " + x.tacticInfo.infos.getOrElse("subLabel", "") + "/" + x.tacticInfo.infos.getOrElse("branchLabel", "<unknown>") + ":\n" + x.sequent.prettyString).mkString(("\n"))) + "\n")
    val proof = rootNode.provableWitness
    if (Tactic.DEBUG) println("proveBy " + proof + "\n")
    proof
  }
  /**
   * Prove the new goal by the given tactic, returning the resulting Provable
   * @see [[TactixLibrary.by(Provable)]]
   * @example {{{
   *   import StringConverter._
   *   val proof = TactixLibrary.proveBy("(p()|q()->r()) <-> (p()->r())&(q()->r())".asFormula, prop)
   * }}}
   */
  def proveBy(goal: Formula, tactic: Tactic): Provable = proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq(goal)), tactic)

}
