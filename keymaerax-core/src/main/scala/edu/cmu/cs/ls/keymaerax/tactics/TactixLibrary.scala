/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._

import scala.collection.immutable
import scala.collection.immutable._

/**
 * Tactix: Main tactic library with simple interface.
 *
 * This library features all main tactic elements for most common cases, except sophisticated tactics.
 *
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[TacticLibrary]]
 * @see [[HilbertCalculus]]
 * @see [[edu.cmu.cs.ls.keymaerax.tactics]]
 */
object TactixLibrary {
//  /** step: makes one sequent proof step to simplify the formula at the indicated position (unless @invariant needed) */
  val step                    : PositionTactic = TacticLibrary.step

  /** step: one canonical simplifying proof step at the indicated formula/term position (unless @invariant etc needed) */
  lazy val stepAt: PositionTactic = HilbertCalculus.stepAt

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

  /** US(form) reduce the proof to a proof of form by a suitable uniform substitution obtained by unification */
  def US(form: Sequent): Tactic = TacticLibrary.US(form)
  /** US: uniform substitution */
  def US(subst: List[SubstitutionPair], delta: (Map[Formula, Formula]) = Map()): Tactic = PropositionalTacticsImpl.uniformSubstT(subst, delta)

  type Subst = UnificationMatch.Subst
  //def Subst(subsDefs: immutable.Seq[(Expression,Expression)]): Subst = RenUSubst(subsDefs)

  /** useAt(fact, tactic)(pos) uses the given fact (that'll be proved by tactic after unification) at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Formula, key: PosInExpr, tactic: Tactic, inst: Subst=>Subst): PositionTactic = TacticLibrary.useAt(fact, key, tactic, inst)
  def useAt(fact: Formula, key: PosInExpr, tactic: Tactic): PositionTactic = TacticLibrary.useAt(fact, key, tactic)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Formula, key: PosInExpr, inst: Subst=>Subst): PositionTactic = useAt(fact, key, skip, inst)
  def useAt(fact: Formula, key: PosInExpr): PositionTactic = useAt(fact, key, skip)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Provable, key: PosInExpr, inst: Subst=>Subst): PositionTactic = {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
    useAt(fact.conclusion.succ.head, key, byUS(fact), inst)
  }
  def useAt(fact: Provable, key: PosInExpr): PositionTactic = {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
    useAt(fact.conclusion.succ.head, key, byUS(fact))
  }
  /** useAt(lem)(pos) uses the given lemma at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(lem: Lemma, key:PosInExpr, inst: Subst=>Subst): PositionTactic = useAt(lem.fact, key, inst)
  def useAt(lem: Lemma, key:PosInExpr): PositionTactic = useAt(lem.fact, key)
  def useAt(lem: Lemma, inst: Subst=>Subst) : PositionTactic = useAt(lem.fact, PosInExpr(0::Nil), inst)
  def useAt(lem: Lemma)       : PositionTactic = useAt(lem.fact, PosInExpr(0::Nil))
  /** useAt(axiom)(pos) uses the given axiom at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(axiom: String, key: PosInExpr, inst: Subst=>Subst): PositionTactic =
    if (Axiom.axioms.contains(axiom)) useAt(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms(axiom))))(Axiom(axiom), 0), key, inst)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useAt(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(DerivedAxioms.derivedAxiomFormula(axiom).get)))(DerivedAxioms.derivedAxiomR((axiom)), 0), key, inst)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  def useAt(axiom: String, key: PosInExpr): PositionTactic =
    if (Axiom.axioms.contains(axiom)) useAt(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms(axiom))))(Axiom(axiom), 0), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useAt(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(DerivedAxioms.derivedAxiomFormula(axiom).get)))(DerivedAxioms.derivedAxiomR(axiom), 0), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  def useAt(axiom: String, inst: Subst=>Subst): PositionTactic = useAt(axiom, PosInExpr(0::Nil), inst)
  def useAt(axiom: String): PositionTactic = useAt(axiom, PosInExpr(0::Nil))

  /** by(provable) is a pseudo-tactic that uses the given Provable to continue or close the proof (if it fits to what has been proved) */
  def by(provable: Provable)  : Tactic = new ByProvable(provable)
  /** by(lemma) is a pseudo-tactic that uses the given Lemma to continue or close the proof (if it fits to what has been proved) */
  def by(lemma: Lemma)        : Tactic = by(lemma.fact)
  /** byUS(provable) proves by a uniform substitution instance of provable */
  def byUS(provable: Provable): Tactic = US(provable.conclusion) & by(provable)
  /** byUS(lemma) proves by a uniform substitution instance of lemma */
  def byUS(lemma: Lemma)      : Tactic  = byUS(lemma.fact)
  /** byUS(axiom) proves by a uniform substitution instance of axiom */
  def byUS(axiom: String)     : Tactic =
    if (Axiom.axioms.contains(axiom)) byUS(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms(axiom))))(Axiom(axiom), 0))
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) byUS(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(DerivedAxioms.derivedAxiomFormula(axiom).get)))(DerivedAxioms.derivedAxiomR(axiom), 0))
    else throw new IllegalArgumentException("Unknown axiom " + axiom)


  // conditional tactics

  /**
   * onBranch((lbl1,t1), (lbl2,t2)) uses tactic t1 on branch labelled lbl1 and t2 on lbl2
   * @see [[BranchLabels]]
   * @see [[label()]]
   */
  def onBranch(s1: (String, Tactic), spec: (String, Tactic)*): Tactic = SearchTacticsImpl.onBranch(s1, spec:_*)

  /** Call the current branch s */
  def label(s: String): Tactic = new LabelBranch(s)

  // Locating applicable positions for PositionTactics

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
  /** Locate applicable position in antecedent on the left in which something matching the given shape occurs */
  //@todo implement using = SearchTacticsImpl.locateSucc(tactic, UnificationMatcher.unifiable(s(pos), parser(shape))!=None)
  def la(tactic: PositionTactic, shape: String): Tactic = ???
  /** Locate applicable position in antecedent on the left */
  def lL(tactic: PositionTactic): Tactic = la(tactic)
  /** Locate applicable position in left or right in antecedent or succedent */
  def l(tactic: PositionTactic): Tactic  = TacticLibrary.locateAnteSucc(tactic)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics
  /** Hide whether left or right */
  def hide                    : PositionTactic = TacticLibrary.hideT
  /** Hide left: weaken a formula to drop it from the antecedent */
  def hideL                   : PositionTactic = TacticLibrary.hideT
  /** Hide right: weaken a formula to drop it from the succcedent */
  def hideR                   : PositionTactic = TacticLibrary.hideT
  /** CoHide whether left or right: drop all other formulas from the sequent */
  def cohide                  : PositionTactic = PropositionalTacticsImpl.cohideT
  /** !L Not left: move an negation in the antecedent to the succedent */
  def notL                    : PositionTactic = TacticLibrary.NotLeftT
  /** !R Not right: move an negation in the succedent to the antecedent */
  def notR                    : PositionTactic = TacticLibrary.NotRightT
  /** &L And left: split a conjunction in the antecedent into separate assumptions */
  def andL                    : PositionTactic = TacticLibrary.AndLeftT
  /** &R And right: prove a conjunction in the succedent on two separate branches */
  def andR                    : PositionTactic = TacticLibrary.AndRightT
  /** |L Or left: use a disjunction in the antecedent by assuming each option on separate branches */
  def orL                     : PositionTactic = TacticLibrary.OrLeftT
  /** |R Or right: split a disjunction in the succedent into separate formulas to show alternatively */
  def orR                     : PositionTactic = TacticLibrary.OrRightT
  /** ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its right-hand side on the other branch */
  def implyL                  : PositionTactic = TacticLibrary.ImplyLeftT
  /** ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand side */
  def implyR                  : PositionTactic = TacticLibrary.ImplyRightT
  /** <->L Equiv left: use an equivalence by considering both true or both false cases */
  def equivL                  : PositionTactic = TacticLibrary.EquivLeftT
  /** <->R Equiv right: prove an equivalence by proving both implications */
  def equivR                  : PositionTactic = TacticLibrary.EquivRightT

  /** cut a formula in to prove it on one branch and then assume it on the other. Or to perform a case distinction on whether it holds */
  def cut(cut : Formula)      : Tactic         = TacticLibrary.cutT(Some(cut))

  // quantifiers
  /** all right: Skolemize a universal quantifier in the succedent */
  def allR                    : PositionTactic = TacticLibrary.skolemizeT
  /** all left: instantiate a universal quantifier in the antecedent by a concrete instance */
  def allL(x: Variable, inst: Term) : PositionTactic = TacticLibrary.instantiateQuanT(x, inst)
  def allL(inst: Term)        : PositionTactic = TacticLibrary.instantiateQuanT(???, inst)
  /** exists left: Skolemize an existential quantifier in the antecedent */
  def existsL                 : PositionTactic = TacticLibrary.skolemizeT
  /** exists right: instantiate an existential quantifier in the succedwent by a concrete instance as a witness */
  def existsR(x: Variable, inst: Term) : PositionTactic = TacticLibrary.instantiateQuanT(x, inst)
  def existsR(inst: Term)     : PositionTactic = TacticLibrary.instantiateQuanT(???, inst)

  // modalities
  //  def SpecificMaster(toolId : String) : Tactic = TacticLibrary.master(new NoneGenerate(), true, toolId)
  /** assignb: [:=] simplify assignment by substitution or equation */
  def assignb                 : PositionTactic = TacticLibrary.boxAssignT
  /** randomb: [:*] simplify nondeterministic assignment to universal quantifier */
  def randomb                 : PositionTactic = TacticLibrary.boxNDetAssign
  /** testb: [?] simplifies test to an implication */
  def testb                   : PositionTactic = TacticLibrary.boxTestT
  /** diffSolve: solve a differential equationb */
  def diffSolve               : PositionTactic = TacticLibrary.diffSolutionT
  /** choiceb: [++] handles both cases of a nondeterministic choice separately */
  def choiceb                 : PositionTactic = TacticLibrary.boxChoiceT
  /** composeb: [;] handle both parts of a sequential composition one at a time */
  def composeb                : PositionTactic = TacticLibrary.boxSeqT
  /** iterateb: [*] prove a property of a loop by unrolling it once */
  def iterateb                : PositionTactic = ???
  /** splitb: splits [a](p&q) into [a]p & [a]q */
  def splitb                  : PositionTactic = HybridProgramTacticsImpl.boxSplitConjunctionT
  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
  def loop(invariant: Formula) = I(invariant)
  /** K: modal modus ponens (hybrid systems) */
  def K                       : PositionTactic = PropositionalTacticsImpl.kModalModusPonensT
  /** V: vacuous box will be discarded (unless it changes values of the postcondition) (hybrid systems) */
  def V                       : PositionTactic = HybridProgramTacticsImpl.boxVacuousT

  // differential equations
  /** DW: Differential Weakening to use evolution domain constraint (equivalence form) */
  def DW                      : PositionTactic = TacticLibrary.diffWeakenT
  /** DC: Differential Cut a new invariant for a differential equation */
  def DC(invariant: Formula)  : PositionTactic = TacticLibrary.diffCutT(invariant)
  /** DE: Differential Effect exposes the effect of a differential equation on its differential symbols */
  def DE                      : PositionTactic = ODETactics.diffEffectT
  /** DI: Differential Invariant proves a formula to be an invariant of a differential equation */
  def DI                      : PositionTactic = TacticLibrary.diffInvariant
  /** DG: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b */
  def DG(y:Variable, a:Term, b:Term) : PositionTactic = ODETactics.diffAuxiliaryT(y,a,b)
  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
  /** DS: Differential Solution solves a differential equation */
  def DS                      : PositionTactic = ???
  /** Dassignb: Substitute a differential assignment */
  def Dassignb                : PositionTactic = HybridProgramTacticsImpl.boxDerivativeAssignT
  /** Dplus: +' derives a sum */
  def Dplus                   : PositionTactic = SyntacticDerivationInContext.AddDerivativeT
  /** neg: -' derives neg */
  def Dneg                    : PositionTactic = SyntacticDerivationInContext.NegativeDerivativeT
  /** Dminus: -' derives a difference */
  def Dminus                  : PositionTactic = SyntacticDerivationInContext.SubtractDerivativeT
  /** Dtimes: *' derives a product */
  def Dtimes                  : PositionTactic = SyntacticDerivationInContext.MultiplyDerivativeT
  /** Dquotient: /' derives a quotient */
  def Dquotient               : PositionTactic = SyntacticDerivationInContext.DivideDerivativeT
  /** Dcompose: o' derives a function composition by chain rule */
  def Dcompose                : PositionTactic = ???
  /** Dconstify: substitute non-bound occurences of x with x() */
  def Dconstify               : PositionTactic = ODETactics.diffIntroduceConstantT

  /** Prove the given list of differential invariants in that order by DC+DI */
  //@todo could change type to invariants: Formula* if considered more readable
  def diffInvariant(invariants: List[Formula]): PositionTactic = ODETactics.diffInvariant(invariants)

  // real closed fields
  def equalReflexive: PositionTactic = ArithmeticTacticsImpl.EqualReflexiveT

  // rules

  /** G: Goedel rule proves the postcondition of a box in isolation (hybrid systems) */
  def G                       : Tactic         = AxiomaticRuleTactics.goedelT
  /** allG: all generalization rule proves the formula after a universal quantifier in isolation */
  def allG                    : Tactic         = AxiomaticRuleTactics.forallGeneralizationT
  /** CT: Term Congruence: Contextual Equivalence of terms proves an equality */
  def CT(inEqPos: PosInExpr)  : Tactic         = ???
  /** CQ: Equation Congruence: Contextual Equivalence of terms proves an equivalence */
  def CQ(inEqPos: PosInExpr)  : Tactic         = AxiomaticRuleTactics.equationCongruenceT(inEqPos)
  /** CE: Congruence: Contextual Equivalence proves an equivalence */
  def CE(inEqPos: PosInExpr)  : Tactic         = AxiomaticRuleTactics.equivalenceCongruenceT(inEqPos)


  /** QE: Quantifier Elimination to decide arithmetic (after simplifying logical transformations) */
  def QE                      : Tactic         = TacticLibrary.arithmeticT

  /** close: closes the branch when the same formula is in the antecedent and succedent or true or false close */
  def close                   : Tactic         = TacticLibrary.closeT
  /** closeId: closes the branch when the same formula is in the antecedent and succedent */
  def closeId                 : Tactic         = TacticLibrary.AxiomCloseT
  /** closeT: closes the branch when true is in the succedent */
  def closeT                  : PositionTactic = TacticLibrary.CloseTrueT
  /** closeF: closes the branch when false is in the antecedent */
  def closeF                  : PositionTactic = TacticLibrary.CloseFalseT

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Bigger Tactics.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Utility Tactics
  /** nil: skip is a no-op that has no effect */
  def nil : Tactic = Tactics.NilT
  def skip : Tactic = nil

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

  def debug(s: => Any): Tactic = TacticLibrary.debugT(s)
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
   */
  def proveBy(goal: Sequent, tactic: Tactic): Provable = {
    val rootNode = new RootNode(goal)
    //@todo what/howto ensure it's been initialized already
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))
    println("proveBy " + (if (rootNode.isClosed()) "closed" else "open\n" + rootNode.openGoals().map(x => "Open Goal: " + x.sequent).mkString(("\n"))))
    rootNode.provableWitness
  }

}
