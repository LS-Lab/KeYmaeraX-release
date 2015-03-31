package edu.cmu.cs.ls.keymaera.tactics

//@todo minimize imports

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics.{equivalenceCongruenceT,equationCongruenceT}
import edu.cmu.cs.ls.keymaera.tactics.ContextTactics.{cutEquivInContext,cutEqualsInContext}
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.{hideT,AxiomCloseT}
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.{onBranch,lastAnte,lastSucc,locateTerm}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.{getFormula,getTerm}

import scala.collection.immutable.List

/**
 * @todo The tactics do not actually do this -- the AxiomNameT only got the "correct" direction in the new implementation.
 *       The atomize and aggregate tactics are out-of-date.
 * Contains the axiom tactics and wrapper tactics for syntactic derivation of formulas and terms.
 * The axiom tactics go both directions; for this reason, there are three tactics per axiom:
 *    - The AxiomNameT tactic is the actual axiom.
 *    - The AxiomNameAtomizeT tactic derives in the typical left-to-right direction; that is, it takes a derivative
 *      term and constructs a non-derivative term.
 *    - The AxiomNameAggregateT tactic goes in the typical right-to-left direction.
 *
 * There is some code duplication in this file, but I figured it is probably not the end of the for such fundamental
 * tactics to be implement on a stand-alone basis.
 *
 * Created by nfulton on 2/4/15.
 */
object SyntacticDerivationInContext {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 1: "Derivatives" of Formulas
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  private def createSubstitution(frm: Formula, f: Formula, g: Formula,
                                 lhsFactory: (Formula, Formula) => Formula,
                                 rhsFactory: (Formula, Formula) => Formula) = {
    val aF = ApplyPredicate(Function("p", None, Real, Bool), Anything)
    val aG = ApplyPredicate(Function("q", None, Real, Bool), Anything)

    uniformSubstT(List(SubstitutionPair(aF, f), SubstitutionPair(aG, g)),
      Map(Equiv(frm, rhsFactory(FormulaDerivative(f), FormulaDerivative(g))) ->
        Equiv(FormulaDerivative(lhsFactory(aF, aG)),
          rhsFactory(FormulaDerivative(aF), FormulaDerivative(aG)))))
  }

  /*
 * Axiom "->' derive imply".
 *   (p -> q)' <-> (!p | q)'
 * End.
 */
  def ImplyDerivativeT = new DerivativeAxiomInContextTactic("->' derive imply", "->' derive imply") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Imply(_,_))              => true
      //      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(Imply(p, q)) => {
        val g = FormulaDerivative(Or(Not(p), q))

        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        val aQ = ApplyPredicate(Function("q", None, Real, Bool), Anything)

        val usubst = uniformSubstT(List(SubstitutionPair(aP, p), SubstitutionPair(aQ, q)),
          Map(Equiv(f, FormulaDerivative(Or(Not(p), q))) ->
            Equiv(FormulaDerivative(Imply(aP, aQ)),
              FormulaDerivative(Or(Not(aP), aQ)))))

        Some(g, Some(usubst))
      }
      case _ => None
    }
  }

  /*
   * Axiom "&' derive and".
   *   (p & q)' <-> ((p') & (q'))
   * End.
   */
  def AndDerivativeT = new DerivativeAxiomInContextTactic("&' derive and", "&' derive and") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(And(_,_))              => true
//      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(And(p,q)) =>
        val usubst = createSubstitution(f, p, q, And.apply, And.apply)
        Some(And(FormulaDerivative(p), FormulaDerivative(q)), Some(usubst))
      case _ => None
    }
  }

  def AndDerivativeAtomizeT = new PositionTactic("&' derive and Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && (s(p) match {
        case FormulaDerivative(And(_,_)) => true
        case _ => false
      })
    }

    override def apply(p: Position): Tactic = AndDerivativeT(p)
  }

  def AndDerivativeAggregateT = new PositionTactic("&' derive and Aggregate") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _                                               => false
    })

    override def apply(p: Position): Tactic = AndDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "|' derive or".
   *   (p | q)' <-> ((p') & (q'))
   * End.
   */
  def OrDerivativeT = new DerivativeAxiomInContextTactic("|' derive or","|' derive or") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Or(_,_)) => true
//      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(Or(p,q)) =>
        val usubst = createSubstitution(f, p, q, Or.apply, And.apply)
        Some(And(FormulaDerivative(p), FormulaDerivative(q)), Some(usubst))
      case _ => None
    }
  }

  def OrDerivativeAtomizeT = new PositionTactic("|' derive or\",\"|' derive or Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case FormulaDerivative(Or(_,_)) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = OrDerivativeT(p)
  }

  def OrDerivativeAggregateT = new PositionTactic("|' derive or\",\"|' derive or Aggregate") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = OrDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // @TODO A lot of things are missing from the axiom file...

  private def createSubstitution(frm: Formula, f: Term, g: Term, sort: Sort,
                                 lhsFactory: (Sort, Term, Term) => BinaryRelation,
                                 rhsFactory: (Sort, Term, Term) => BinaryRelation) = {
    val aF = Apply(Function("f", None, sort, sort), Anything)
    val aG = Apply(Function("g", None, sort, sort), Anything)

    uniformSubstT(List(SubstitutionPair(aF, f), SubstitutionPair(aG, g)),
      Map(Equiv(frm, rhsFactory(sort, Derivative(sort, f), Derivative(sort, g))) ->
        Equiv(FormulaDerivative(lhsFactory(sort, aF, aG)),
          rhsFactory(sort, Derivative(sort, aF), Derivative(sort, aG)))))
  }

  /*
   * Axiom "=' derive =".
   *   (s = t)' <-> ((s') = (t'))
   * End.
   */
  def EqualsDerivativeT = new DerivativeAxiomInContextTactic("=' derive =", "=' derive =") {
    override def applies(f: Formula): Boolean = {
      f match {
        case FormulaDerivative(Equals(eqSort, s, t)) => true
        //      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
        case _ => false
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(Equals(eqSort, s, t)) =>
        val usubst = createSubstitution(f, s, t, eqSort, Equals.apply, Equals.apply)
        Some(Equals(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), Some(usubst))
      case _ => None
    }
  }

  def EqualsDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(Equals(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = EqualsDerivativeT(p)
  }

  def EqualsDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = EqualsDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom ">=' derive >=".
   *   (s >= t)' <-> ((s') >= (t'))
   * End.
   */
  def GreaterEqualDerivativeT = new DerivativeAxiomInContextTactic(">=' derive >=", ">=' derive >=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => true
//      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }


    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) =>
        val usubst = createSubstitution(f, s, t, eqSort, GreaterEqual.apply, GreaterEqual.apply)
        Some(GreaterEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), Some(usubst))
      case _ => None
    }
  }

  def GreaterEqualDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterEqualDerivativeT(p)
  }

  def GreaterEqualDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterEqualDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom ">' derive >".
   *   (s > t)' <-> ((s') >= (t'))
   * End.
   */
  def GreaterThanDerivativeT = new DerivativeAxiomInContextTactic(">' derive >", ">' derive >") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) => true
//      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) =>
        val usubst = createSubstitution(f, s, t, eqSort, GreaterThan.apply, GreaterEqual.apply)
        Some(GreaterEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), Some(usubst))
      case _ => None
    }
  }

  def GreaterThanDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterThanDerivativeT(p)
  }

  def GreaterThanDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterThanDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "<=' derive <=".
   *   (s <= t)' <-> ((s') <= (t'))
   * End.
   */
  def LessEqualDerivativeT = new DerivativeAxiomInContextTactic("<=' derive <=", "<=' derive <=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) => true
//      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f : Formula) = f match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) =>
        val usubst = createSubstitution(f, s, t, eqSort, LessEqual.apply, LessEqual.apply)
        Some(LessEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), Some(usubst))
    }
  }

  def LessEqualDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = LessEqualDerivativeT(p)
  }

  def LessEqualDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = LessEqualDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "<' derive <".
   *   (s < t)' <-> ((s') <= (t'))
   * End.
   */
  def LessThanDerivativeT = new DerivativeAxiomInContextTactic("<' derive <", "<' derive <") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(LessThan(eqSort, s, t)) => true
//      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => {println(this.getClass() + " is not applicable to: " + f); false}
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(LessThan(eqSort, s, t)) =>
        val usubst = createSubstitution(f, s, t, eqSort, LessThan.apply, LessEqual.apply)
        Some( LessEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), Some(usubst))
      case _ => None
    }
  }

  def LessThanDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(LessThan(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = LessThanDerivativeT(p)
  }

  def LessThanDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = LessThanDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "!=' derive !=".
   *   (s != t)' <-> ((s') = (t'))
   * End.
   */
  def NotEqualsDerivativeT = new DerivativeAxiomInContextTactic("!=' derive !=", "!=' derive !=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) => true
//      case NotEquals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) =>
        val usubst = createSubstitution(f, s, t, eqSort, NotEquals.apply, Equals.apply)
        Some(Equals(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), Some(usubst))
    }
  }

  def NotEqualsDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = NotEqualsDerivativeT(p)
  }

  def NotEqualsDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = NotEqualsDerivativeT(p)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 2. Syntactic Total Derivation of Terms.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo throughout this section, the <- direction applicability is disabled in comments because the Atomize/Aggregate thing isn't possible to implement without position tactics for terms.
  //@todo when re-enabliong these applies lines, uncomment and re-run the relevant tests in SyntacticDerivationTests

  /*
   * Axiom "c()' derive constant fn".
   *   c()' = 0
   * End.
   */
  def ConstantFnDerivativeT = new TermAxiomTactic("c()' derive constant fn","c()' derive constant fn") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(dSort, Apply(Function(_, _, Unit, nSort), Nothing)) => dSort == nSort
      case _ => false
    }

    override def constructInstanceAndSubst(t: Term, ax: Formula, pos: Position): Option[(Formula, List[SubstitutionPair])] = {
      t match {
        case Derivative(dSort, s@Apply(Function(n, i, Unit, nSort), Nothing)) if dSort == nSort => {
          val sort = nSort

          val aS = Apply(Function("c", None, Unit, sort), Nothing)

          val subst = List(SubstitutionPair(aS, s))

          val right = Number(0)
          val axiomInstance = Equals(sort, t, right)

          Some(axiomInstance, subst)
        }
        case _ => None
      }
    }
  }

  def findParentFormulaPos(f: Formula, p: PosInExpr): PosInExpr = {
    if (TacticHelper.isFormula(f, p)) p
    else findParentFormulaPos(f, PosInExpr(p.pos.init))
  }

  /*
   * Axiom "-' derive neg".
   *   (-s)' = -(s')
   * End.
   */
  def NegativeDerivativeT = new PositionTactic("-' derive neg") with ApplicableAtTerm {
    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))
    override def applies(t: Term): Boolean = t match {
      case Derivative(_,Neg(_,_)) => true
      //      case Neg(_,Derivative(_,_)) => true //@todo add term position derivatives and re-enable this case, then uncomment test cases.
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTerm(node.sequent, p) match {
        case t@Derivative(dSort, Neg(nSort, s)) =>
          val r = Neg(nSort, Derivative(dSort, s))
          val formulaCtxPos = findParentFormulaPos(node.sequent(p), p.inExpr)
          val termCtxPos = PosInExpr(p.inExpr.pos.drop(formulaCtxPos.pos.length))

          Some(cutEqualsInContext(Equals(nSort, t, r), p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) &
              equivalenceCongruenceT(formulaCtxPos) &
              equationCongruenceT(termCtxPos) & lastSucc(NegativeDerivativeBaseT)),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
      }
    }
  }

  def NegativeDerivativeBaseT = new PositionTactic("-' derive neg") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equals(_, Derivative(_,Neg(_,_)), _) => true
      //      case Neg(_,Derivative(_,_)) => true //@todo add term position derivatives and re-enable this case, then uncomment test cases.
      case _ => false
    }


    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case fml@Equals(_, t@Derivative(dSort, Neg(nSort, s)), _) => {
          val sort = nSort; assert(nSort == dSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val subst = List(SubstitutionPair(aF, s))
          val axiom = Axiom.axioms.get("-' derive neg") match { case Some(f) => f }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("-' derive neg") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
        case fml@Equals(_, Neg(nSort, Derivative(dSort, s)), _) => {
          val sort = nSort; assert(nSort == dSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val subst = List(SubstitutionPair(aF, s))
          val axiom = Axiom.axioms.get("-' derive neg") match { case Some(f) => f }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("-' derive neg") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
      }
    }
  }

  /*
   * Axiom "+' derive sum".
   *  (s + t)' = (s') + (t')
   * End.
   */
  def AddDerivativeT = new PositionTactic("+' derive sum") with ApplicableAtTerm {
    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))
    override def applies(t: Term): Boolean = t match {
      case Derivative(sort, Add(sort2, _, _)) => true
      //      case Add(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTerm(node.sequent, p) match {
        case t@Derivative(sort, Add(sort2, f, g)) =>
          val r = Add(sort, Derivative(sort, f), Derivative(sort, g))
          val formulaCtxPos = findParentFormulaPos(node.sequent(p), p.inExpr)
          val termCtxPos = PosInExpr(p.inExpr.pos.drop(formulaCtxPos.pos.length))

          Some(cutEqualsInContext(Equals(sort, t, r), p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) &
              equivalenceCongruenceT(formulaCtxPos) &
              equationCongruenceT(termCtxPos) & lastSucc(AddDerivativeBaseT)),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
      }
    }
  }

  def AddDerivativeBaseT = new PositionTactic("+' derive sum") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equals(_, Derivative(sort, Add(sort2, _, _)), _) => sort == sort2
//      case Add(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }


    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case fml@Equals(_, Derivative(dSort, Add(aSort, f, g)), _) => {
          val sort = aSort; assert(dSort == aSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)
          val subst = SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil

          val axiom = Axiom.axioms.get("+' derive sum") match { case Some(f) => f }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("+' derive sum") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
        case fml@Equals(_, Add(aSort, Derivative(fSort, f), Derivative(gSort, g)), _) => {
          val sort = aSort; assert(aSort == fSort && aSort == gSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)
          val subst = SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil

          val axiom = Axiom.axioms.get("+' derive sum") match { case Some(f) => f }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("+' derive sum") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
      }
    }
  }

  trait ApplicableAtTerm {
    def applies(t : Term) : Boolean
  }

  /*
   * Axiom "-' derive minus".
   *   (s - t)' = (s') - (t')
   * End.
 */
  def SubtractDerivativeT = new TermAxiomTactic("-' derive minus","-' derive minus") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(sort, Subtract(sort2, _, _)) => sort == sort2
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, List[SubstitutionPair])] = {
      term match {
        case Derivative(dSort, Subtract(aSort, f, g)) => {
          val sort = aSort; assert(dSort == aSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val right = Subtract(sort, Derivative(sort, f), Derivative(sort, g))
          val axiomInstance = Equals(sort, term, right)

          val subst = List(
            SubstitutionPair(aF, f),
            SubstitutionPair(aG, g)
          )

          Some(axiomInstance, subst)
        }
        case Subtract(aSort, Derivative(fSort, f), Derivative(gSort, g)) => {
          val sort = aSort; assert(aSort == fSort && aSort == gSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val left = Derivative(sort, Subtract(sort, f, g))
          val axiomInstance = Equals(sort, left, term)

          val subst = List(
            SubstitutionPair(aF, f),
            SubstitutionPair(aG, g)
          )

          Some(axiomInstance, subst)
        }
      }
    }
  }

  /*
Axiom "*' derive product".
  (s * t)' = ((s')*t) + (s*(t'))
End.
   */
  def MultiplyDerivativeT = new TermAxiomTactic("*' derive product","*' derive product") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(sort, Multiply(sort2, _, _)) => sort == sort2
//      case Add(_, Multiply(_,Derivative(_,_), _),Multiply(_,_,Derivative(_))) => true
//      case Subtract(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, List[SubstitutionPair])] = {
      term match {
        case Derivative(dSort, Multiply(aSort, f, g)) => {
          val sort = aSort; assert(dSort == aSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val right = Add(sort, Multiply(sort, Derivative(sort, f), g), Multiply(sort, f, Derivative(sort, g)))
          val axiomInstance = Equals(sort, term, right)

          val subst = List(
            SubstitutionPair(aF, f),
            SubstitutionPair(aG, g)
          )

          Some(axiomInstance, subst)
        }
        case Add(aSort, Multiply(mSort, Derivative(_, f), g), Multiply(_, _, _)) => {
          //@TODO Need shape tests for _, _, _ arguments?
          val sort = aSort; assert(aSort == mSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val left = Derivative(sort, Multiply(sort, f, g))
          val axiomInstance = Equals(sort, left, term)

          val subst = List(
            SubstitutionPair(aF, f),
            SubstitutionPair(aG, g)
          )

          Some(axiomInstance, subst)
        }
      }
    }
  }

  /*
  Axiom "/' derive quotient".
  (s / t)' = (((s')*t) - (s*(t'))) / (t^2)
End.
   */
  def DivideDerivativeT = new TermAxiomTactic("/' derive quotient","/' derive quotient") {
    override def applies(term: Term): Boolean = term match {
      case Derivative(sort, Divide(sort2, _, _)) => sort == sort2
//      case Divide(dSort, Subtract(_, Multiply(_,Derivative(_,s), _),Multiply(_,_,Derivative(_))), Exp(_, t, Number(_))) => true
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, List[SubstitutionPair])] = {
      term match {
        case Derivative(dSort, Divide(aSort, f, g)) => {
          val sort = aSort; assert(dSort == aSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val right = Divide(dSort,
            Subtract(sort,
              Multiply(sort, Derivative(sort, f), g),
              Multiply(sort, f, Derivative(sort, g))
            ),
            Exp(sort, g, Number(2))
          )
          val axiomInstance = Equals(sort, term, right)

          val subst = List(
            SubstitutionPair(aF, f),
            SubstitutionPair(aG, g)
          )

          Some(axiomInstance, subst)
        }
        case Divide(dSort,
                Exp(_, g, Number(_)),
                Subtract(_, Multiply(_,Derivative(_, f), _), Multiply(_, _, Derivative(_)))) => {
          val sort = dSort

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val aG = Apply(Function("g", None, sort, sort), Anything)

          val left = Derivative(Real, Divide(Real, f, g))
          val axiomInstance = Equals(sort, left, term)

          val subst = List(
            SubstitutionPair(aF, f),
            SubstitutionPair(aG, g)
          )

          Some(axiomInstance, subst)
        }
      }
    }
  }

  def PowerDerivativeT = new TermAxiomTactic("^' derive power","^' derive power") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(Real, Exp(Real, _, _)) => true
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, List[SubstitutionPair])] = {
      term match {
        case Derivative(Real, Exp(Real, f, c)) => {
          assert(c != Number(0), "not power 0")

          val aF = Apply(Function("f", None, Real, Real), Anything)
          val aC = Apply(Function("c", None, Unit, Real), Nothing)

          val right = Multiply(Real,
            Multiply(Real, c, Exp(Real, f, Subtract(Real, c, Number(1)))),
            Derivative(Real, f))
          val axiomInstance = Equals(Real, term, right)

          val subst =
            SubstitutionPair(aF, f) ::
            SubstitutionPair(aC, c) :: Nil

          Some(axiomInstance, subst)
        }
        //@TODO case backwards
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof rule implementations
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  def SyntacticDerivationRulesT : Tactic =
    (SearchTacticsImpl.locateTerm(ConstantDerivativeT, inAnte = false) *) ~
    (SearchTacticsImpl.locateTerm(PowerDerivativeT, inAnte = false) *)

  def ConstantDerivativeT = new TermAxiomTactic("c()' derive constant fn", "c()' derive constant fn") {
    override def applies(term: Term): Boolean = term match {
      case Derivative(Real, Number(_, _)) => true
      case Derivative(Real, Apply(Function(_, _, Unit, Real), Nothing)) => true
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, List[SubstitutionPair])] = {
      term match {
        case f@Derivative(Real, s@Number(_, _)) =>
          // construct substitution
          val aC = Apply(Function("c", None, Unit, Real), Nothing)
          val l = List(new SubstitutionPair(aC, s))
          val g = Number(0)
          val axiomInstance = Equals(Real, f, g)
          Some(axiomInstance, l)
        case f@Derivative(Real, s@Apply(Function(_, _, Unit, Real), Nothing)) =>
          // construct substitution
          val aC = Apply(Function("c", None, Unit, Real), Nothing)
          val l = List(new SubstitutionPair(aC, s))
          val g = Number(0)
          val axiomInstance = Equals(Real, f, g)
          Some(axiomInstance, l)
        case _ => None
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Atomize for Term Tactics @todo
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //@todo So that when this gets refactored we're not stuck changing a bunch of stuff.
  def ConstantFnDerivativeAtomizeT = ConstantFnDerivativeT
  def NegativeDerivativeAtomizeT = NegativeDerivativeT
  def AddDerivativeAtomizeT      = AddDerivativeT
  def SubtractDerivativeAtomizeT = SubtractDerivativeT
  def MultiplyDerivativeAtomizeT = MultiplyDerivativeT
  def DivideDerivativeAtomizeT   = DivideDerivativeT
  def ConstantDerivativeAtomizeT = ConstantDerivativeT


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for term syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * This list of *all* the atomizing TermAxiomTactics is used in the implementation of wrapper tactics.
   */
  val termDerivativeTactics : List[PositionTactic with ApplicableAtTerm] =
    NegativeDerivativeAtomizeT ::
      ConstantFnDerivativeAtomizeT ::
      AddDerivativeAtomizeT ::
      SubtractDerivativeAtomizeT ::
      MultiplyDerivativeAtomizeT ::
      DivideDerivativeAtomizeT ::
      ConstantDerivativeAtomizeT ::
      Nil

  val formulaDerivativeTactics : List[DerivativeAxiomInContextTactic] =
    AndDerivativeT          ::
    OrDerivativeT           ::
    EqualsDerivativeT       ::
    GreaterEqualDerivativeT ::
    GreaterThanDerivativeT  ::
    LessEqualDerivativeT    ::
    LessThanDerivativeT     ::
    NotEqualsDerivativeT    ::
    ImplyDerivativeT      ::
    Nil

  /**
   * Finds a position in ``expression" where ``tactic" is applicable, or else returns None if ``tactic" is never applicable
   * in subexpressions of ``expression".
   *
   * This is used in the implementation of wrapper tactics.
   * @param expression
   * @param tactic
   */
  def findApplicablePositionForTermAxiom(expression : Expr, tactic : ApplicableAtTerm) : Option[(PosInExpr, Term)] = {
    val traversal = new ExpressionTraversalFunction {
      var mPosition : Option[PosInExpr] = None
      var mTerm : Option[Term] = None

      override def preT(p:PosInExpr, t:Term) = {
        if(tactic.applies(t)) {
          mPosition = Some(p);
          mTerm = Some(t);
          println("Found applicable tactic: " + tactic + " which applies to: " + expression) //@todo added because this tactic diverged when wrapped in a star for - examples.
          Left(Some(ExpressionTraversal.stop)) //stop once we find one applicable location.
        }
        else{
          Left(None)
        }
      }
    }

    expression match {
      case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
      case expression : Term => ExpressionTraversal.traverse(traversal, expression)
      case expression : Program => ExpressionTraversal.traverse(traversal, expression)
      case _ => ???
    }

    (traversal.mPosition, traversal.mTerm) match {
      case (Some(p:PosInExpr), Some(t:Term)) => Some((p,t))
      case (None,None) => None
      case _ => ???
    }
  }

  def formulaContainsModality(f : Formula) : Option[(PosInExpr, Formula)] = {
    val fn = new ExpressionTraversalFunction {
      var thePair : Option[(PosInExpr, Formula)] = None
      override def preF(p : PosInExpr, f : Formula) = {
        val matches : Boolean = f match {
          case Modality(_,_) => true
          case BoxModality(_,_) => true
          case DiamondModality(_,_) => true
          case _ => false
        }
        if(matches) {thePair = Some( (p,f) ); Left(Some(ExpressionTraversal.stop))}
        else Left(None)
      }
    }
    ExpressionTraversal.traverse(fn,f)
    fn.thePair
  }

  /**
   * The wrapper tactic for total synactic derivation of *terms*.
   * In a single step, this tactic finds *one* location where *one* of the atomizing term derivative rewrites applies,
   * and then applies that tactic.
   */
  def TermSyntacticDerivationT = new PositionTactic("Total Syntactic Derivation of Terms") {
    //@todo this is wrong b/c what if we're applying in ^A -> [pi;](^^x > 0)' where ^^ is the term pos and ^ the formula pos?
    //@todo better but not quite right; what if we have something like ^[pi;]a -> ^^b?

    def applies(s : Sequent, p : Position) : Boolean = {
      appliesRegardlessOfContext(s,p) && !formulaContainsModality(s(p)).isDefined
    }

    //@todo move this into SyntacticDerivationT I guess...
    def appliesRegardlessOfContext(s: Sequent, p: Position): Boolean = {
      def tacticApplies(tactic : ApplicableAtTerm) = findApplicablePositionForTermAxiom(s(p), tactic) match {
        case Some(_) => true
        case None => false
      }

      termDerivativeTactics.foldLeft(false)((b, tat : PositionTactic with ApplicableAtTerm) => {
        tacticApplies(tat) || b
      }) || findApplicablePositionForTermAxiom(s(p), PowerDerivativeT).isDefined
    }

    /**
     * @todo this code is kind of complicated and probably deserves some refactoring.
     *       The formula version is much cleaner .
     */
    override def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        /**
         * Returns a list of positions, together with the first applicable tactic at each position.
         */
        def firstApplicableTacticForEachPosition(seq : IndexedSeq[Formula]) : Seq[(PositionTactic with ApplicableAtTerm, Int, PosInExpr)] = {
          seq.zipWithIndex.map(p => {
            val formula = p._1
            val index: Int = p._2

            val tacticAndPos : Option[(PositionTactic with ApplicableAtTerm, PosInExpr)] = {
              //Check each of the tactics to determine if any apply.
              def findApplicablePosInFormula(tactic : ApplicableAtTerm) : Option[PosInExpr] = {
                findApplicablePositionForTermAxiom(formula, tactic) match {
                  case Some((posInExpr, term)) => Some(posInExpr)
                  case None => None
                }
              }

              val applicableTactics = termDerivativeTactics.map(t => findApplicablePosInFormula(t) match {
                case Some(posInExpr) => Some(t,posInExpr)
                case None => None
              }).filter(_.isDefined)

              if(applicableTactics.length == 0) {
                None
              }
              else {
                applicableTactics.last //just the first applicable tactic.
              }
            }

            tacticAndPos match {
              case Some((tactic:PositionTactic with ApplicableAtTerm, posInExpr:PosInExpr)) => Some(tactic, index, posInExpr)
              case None => None
            }
          }).filter(_.isDefined).map(_.get)
        }

        //First check the ante for any applicable tactics and positions; if there is one, return that one.
        //Else move on to the succ and so the same thing.
        val antePositions = firstApplicableTacticForEachPosition(node.sequent.ante)
        if(antePositions.length > 0) {
          val elmt      = antePositions.last
          val tactic    = elmt._1
          val anteIndex = elmt._2
          val posInExpr = elmt._3
          val position  = AntePosition(anteIndex, posInExpr)

          Some(tactic(position))
        }
        else {
          val succPositions = firstApplicableTacticForEachPosition(node.sequent.succ)
          if(succPositions.length > 0) {
            val elmt      = succPositions.last
            val tactic    = elmt._1
            val anteIndex = elmt._2
            val posInExpr = elmt._3
            Some(tactic(SuccPosition(anteIndex, posInExpr)))
          }
          else {
            None
          }
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }



  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for formula syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def FormulaSyntacticDerivationT = new PositionTactic("Formula Syntactic Derivation") {
    override def applies(s: Sequent, p: Position): Boolean = {
      formulaDerivativeTactics.map(t => findApplicablePositionForFormulaDerivativeAxiom(s(p), t) match {
        case Some(_) => true
        case None    => false
      }).reduce(_ | _)
    }

    override def apply(p:Position) : Tactic = new ConstructionTactic("Formula Syntactic Derivation") {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val applicableTactics : Seq[(PositionTactic, PosInExpr)] =
          formulaDerivativeTactics.map(t => (t, findApplicablePositionForFormulaDerivativeAxiom(node.sequent(p), t))).
            filter(_._2.isDefined).map(p => (p._1, p._2.get._1))
        if (applicableTactics.length > 0) {
          val tactic    = applicableTactics.last._1
          val posInExpr = applicableTactics.last._2
          return Some(tactic(if (p.isAnte) AntePosition(p.index, posInExpr) else SuccPosition(p.index, posInExpr)))
        }
        assert(!applicable(node), "tactic signalled applicability, but about to return None")
        None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    def findApplicablePositionForFormulaDerivativeAxiom(expression : Expr, tactic : DerivativeAxiomInContextTactic) : Option[(PosInExpr, Formula)] = {
      val traversal = new ExpressionTraversalFunction {
        var mPosition : Option[PosInExpr] = None
        var mFormula : Option[Formula]    = None

        override def preF(p:PosInExpr, f:Formula) = {
          if(tactic.applies(f)) {
            mPosition = Some(p);
            mFormula  = Some(f);

            Left(Some(ExpressionTraversal.stop)) //stop once we find one applicable location.
          }
          else{
            Left(None)
          }
        }
      }

      expression match {
        case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
        case expression : Term    => ExpressionTraversal.traverse(traversal, expression)
        case expression : Program => ExpressionTraversal.traverse(traversal, expression)
        case _ => ???
      }

      (traversal.mPosition, traversal.mFormula) match {
        case (Some(p:PosInExpr), Some(f:Formula)) => Some((p,f))
        case (None,None) => None
        case _ => ???
      }
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Syntactic derivation of constants and monomials.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /**
   * @todo I cannot believe that this does not exist somewhere already.
   */
  def getTermAtPosition(s : Sequent, p : Position) : Option[Term] = {
    val fn = new ExpressionTraversalFunction {
      var retVal : Option[Term] = None
      override def preT(pie : PosInExpr, t : Term) = {
        if(p.inExpr == pie) { //yummy
          retVal = Some(t)
          Left(Some(ExpressionTraversal.stop))
        }
        else Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, s(p))
    fn.retVal
  }

  def MonomialAndConstantDerivationT = new PositionTactic("Derive monomial and constant") {
    override def applies(s: Sequent, p: Position): Boolean = !formulaContainsModality(s(p)).isDefined && {getTermAtPosition(s,p) match {
      case Some(Derivative(_, Number(_))) => true
      case Some(Derivative(_, exp:Exp)) => true
      case _ => false
    }}

    override def apply(p: Position): Tactic = PowerDerivativeT(p) ~ ConstantDerivativeT(p)
  }

  def MonomialAndConstantInContextDerivationT = new PositionTactic("Derive monomial and context in context") {
    override def applies(s: Sequent, p: Position): Boolean = {
      formulaContainsModality(s(p)).isDefined && {getTermAtPosition(s,p) match {
        case Some(Derivative(_, Number(_))) => true
        case Some(Derivative(_, exp:Exp)) => true
        case _ => false
      }}
    }

    override def apply(p: Position): Tactic =  SyntacticDerivativeProofRulesInContext.PowerDerivativeInContext(p) ~ SyntacticDerivativeProofRulesInContext.ConstantDerivativeInContext(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  def SyntacticDerivationT = new PositionTactic("Formula Syntactic Derivation") {
//    //Formula derivatives are treated using the in context base class, but the term derivative rules require the K construction.
//    //Hence, SyntacticDerivativeTermAxiomsInContext.
//    //@todo FormulaSyntacticDerivationT does something mean -- it looks around for a place to apply itself internally. This should be done in locate tactics, not in the main tactic.
//    override def applies(s: Sequent, p: Position): Boolean = SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT.applies(s,p) | FormulaSyntacticDerivationT.applies(s,p)
//
//    override def apply(p: Position): Tactic = (FormulaSyntacticDerivationT(p) *) ~ (SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT(p) *)
//  }


  import SyntacticDerivativeProofRulesInContext._

  /**
   * @todo this is just brokwn. Needs to apply at position, not everywhere... But that's an interface change, so for the moment I'll leave as-is.
   */
  def SyntacticDerivationT = new PositionTactic("Single Step of Total Syntactic Derivation") {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = FormulaSyntacticDerivationT.applies(s, p) || TermSyntacticDerivationT.appliesRegardlessOfContext(s,p) || MonomialAndConstantDerivationT.applies(s,p) || MonomialAndConstantInContextDerivationT.applies(s,p) //@todo oh dear... should move this applies logic into SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT

    override def apply(p: Position): Tactic = (locate(FormulaSyntacticDerivationT)*) &
      assertT(!containsFormulaDerivative(_), "Formula derivative left unhandled by FormulaSyntacticDerivationT") &
      (locateTerm(SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT, inAnte = false)*) &
      (locateTerm(TermSyntacticDerivationT, inAnte = false) *) &
      assertT(!containsTermDerivative(_), "Term derivative left unhandled by TermSyntacticDerivationT") &
      (locateTerm(MonomialAndConstantDerivationT, inAnte = false) *) &
      assertT(containsOnlyVariableDerivatives(_), "Syntactic derivation left monomial or constant unhandled")

    private def containsFormulaDerivative(s: Sequent): Boolean =
      s.ante.exists(containsFormulaDerivative) || s.succ.exists(containsFormulaDerivative)

    private def containsFormulaDerivative(f: Formula): Boolean = {
      var containsFd = false
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, frm: Formula): Either[Option[StopTraversal], Formula] = frm match {
          case FormulaDerivative(_) => containsFd = true; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, f)
      containsFd
    }

    private def containsTermDerivative(s: Sequent): Boolean =
      s.ante.exists(containsTermDerivative) || s.succ.exists(containsTermDerivative)

    private def containsTermDerivative(f: Formula): Boolean = {
      var containsTd = false
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case Derivative(_, _: Variable) => Left(None)
          case Derivative(_, _: Exp) => Left(None)
          case Derivative(_, _) => containsTd = true; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, f)
      containsTd
    }

    private def containsOnlyVariableDerivatives(s: Sequent): Boolean =
      s.ante.forall(containsOnlyVariableDerivatives) && s.succ.forall(containsOnlyVariableDerivatives)

    private def containsOnlyVariableDerivatives(f: Formula): Boolean = {
      var onlyPrimitiveDerivatives = true
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case Derivative(_, _: Variable) => Left(None)
          case Derivative(_, _) => onlyPrimitiveDerivatives = false; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, f)
      onlyPrimitiveDerivatives
    }

  }
}
