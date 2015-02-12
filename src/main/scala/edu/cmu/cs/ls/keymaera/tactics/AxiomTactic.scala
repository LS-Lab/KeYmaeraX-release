package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getTerm
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

object AxiomTactic {
  /**
   * Axiom lookup imports an axiom into the antecedent.
   */
  def axiomT(id: String): Tactic = Axiom.axioms.get(id) match {
    case Some(_) => new Tactics.ApplyRule(Axiom(id)) {
      override def applicable(node: ProofNode): Boolean = true
    }
    case _ => throw new IllegalArgumentException("Unknown axiom " + id)
  }
}

// axiom wrapper shell
// TODO: Use findPosInExpr to find a position that matches the left side of the axiom and cut in the resulting instance
// we start with just using findPos to get a top level position

/**
 * Base class for axiom tactics.
 * @param name The name of the tactic.
 * @param axiomName The name of the axiom.
 */
abstract class AxiomTactic(name: String, axiomName: String) extends PositionTactic(name) {
  //@todo a java.lang.ExceptionInInitializerError is thrown
  require(Axiom.axioms != null, "the list of axioms should be defined.")
  require(Axiom.axioms.keySet.contains(axiomName), "The requested axiom should be in the set of axioms.") //@todo remove before production.
  val axiom = Axiom.axioms.get(axiomName)
  def applies(f: Formula): Boolean
  override def applies(s: Sequent, p: Position): Boolean = axiom.isDefined && applies(getFormula(s, p))

  /**
   * This methods constructs the axiom before the renaming, axiom instance, substitution to be performed and a tactic
   * that performs the renaming.
   *
   * An axiom tactic performs the following steps (Hilbert style):
   * 1. Guess axiom
   * 2. Rename bound variables to match the instance we want
   * 3. Perform Uniform substitution to instantiate the axiom
   *
   * Axioms usually have the form ax = OP(a, b). The constructed instance either has the form OP(f, g) or OP(g, f).
   * Here, f is an input to this function and g is derived from the axiom to be used. The output of this function
   * should be 4 things:
   * 1. The form of the axiom before apply the tactic provided in 4
   * 2. The instance of the axiom eventually to be used in the proof
   * 3. The substitution to turn 2 into 1
   * 4. A tactic to turn the result of 3 into the actual axiom (and/or the other way around)
   *
   * In the long run all this should be computed by unification.
   *
   * @param f the formula that should be rewritten using the axiom
   * @param ax the axiom to be used
   * @param pos the position to which this rule is applied to
   * @return (Axiom before executing the given position tactic;
   *         the instance of the axiom,
   *         the uniform substitution that transforms the first into the second axiom (Hilbert style);
   *         an optional position tactic that transforms the actual axiom into the first argument;
   *         an optional position tactic that transforms the first
   *         argument into the actual axiom (usually alpha renaming)).
   * @see #constructInstanceAndSubst(Formula)
   */
  def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution,
      Option[PositionTactic], Option[PositionTactic])] =
    constructInstanceAndSubst(f, ax)

  def constructInstanceAndSubst(f: Formula, ax: Formula): Option[(Formula, Formula, Substitution,
      Option[PositionTactic], Option[PositionTactic])] = {
    constructInstanceAndSubst(f) match {
      case Some((instance, subst)) => Some((ax, instance, subst, None, None))
      case None => None
    }
  }

  /**
   * This is a simpler form of the constructInstanceAndSubst method. It just gets the formula to be rewritten
   * and has to construct the axiom instance and the substitution to transform the axiom into its instance.
   *
   * This method will be called by the default implementation of constructInstanceAndSubst(f: Formula, a: Formula).
   *
   * @param f The formula to be rewritten using an axiom
   * @return (The axiom instance to be constructed and used for rewriting;
   *          Substitution to transform the axiom into its instance)
   * @see #constructInstanceAndSubst(Formula,Formula)
   */
  def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = ???

  //@TODO Add contract that applies()=>\result fine
  override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
    override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import EqualityRewritingImpl.equalityRewriting
      import AxiomTactic.axiomT
      axiom match {
        case Some(ax) =>
          constructInstanceAndSubst(getFormula(node.sequent, pos), ax, pos) match {
            case Some((modAx, axiomInstance, subst, anteTac, succTac)) =>
              val axiomInstPos = AntePosition(node.sequent.ante.length)
              val axiomApplyTactic = assertPT(axiomInstance)(axiomInstPos) & (axiomInstance match {
                //@TODO Prefer simpler sequent proof rule for <->left rather than congruence rewriting if the position to use it on is on top-level of sequent
                //@TODO If Pos.isAnte the following position management seems wrong since unstable.
                case Equiv(_, _) => equalityRewriting(axiomInstPos, pos) & ((assertPT(axiomInstance)&hideT)(axiomInstPos) & (assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos.topLevel))
                case Equals(Real, _, _) => equalityRewriting(axiomInstPos, pos, checkDisjoint = false) & ((assertPT(axiomInstance)&hideT)(axiomInstPos) & (assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos.topLevel))
                case Imply(_, _) if pos.isAnte  && pos.inExpr == HereP => modusPonensT(pos, axiomInstPos)
                case Imply(_, _) if !pos.isAnte && pos.inExpr == HereP => ImplyLeftT(axiomInstPos) & ((assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos), AxiomCloseT(axiomInstPos.topLevel, pos))
                case _ => ???
              })
              // // hide in reverse order since hiding changes positions
              // val hideAllAnte = for(i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
              // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
              // val hideAllSuccButLast = for(i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
              // val hideAllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
              //@TODO Insert contract tactic after hiding all which checks that exactly the intended axiom formula remains and nothing else.
              //@TODO Introduce a reusable tactic that hides all formulas except the ones given as argument and is followed up by a contract ensuring that exactly those formuals remain.
              val anteCont = anteTac match {
                // AntePosition(0) is the only antecedent position remaining in axiom proof
                case Some(tactic) => assertT(1, 1) & tactic(AntePosition(0))
                case None => NilT
              }
              val succCont = succTac match {
                // SuccPosition(0) is the only position remaining in axiom proof
                case Some(tactic) => assertT(0, 1) & tactic(SuccPosition(0))
                case None => NilT
              }
              val axiomPos = SuccPosition(node.sequent.succ.length)
              println("Axiom instance " + axiomInstance)
              val axiomInstanceTactic = (assertPT(axiomInstance) & cohideT)(axiomPos) & (assertT(0,1) & assertT(axiomInstance, SuccPosition(0)) & uniformSubstT(subst, Map(axiomInstance -> modAx)) & assertT(0, 1) & (succCont & axiomT(axiomName) & assertT(1,1) & anteCont & AxiomCloseT))
              Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
            case None => None
          }
        case None => None
      }
    }
  }

}

/**
 * Base class for tactics that want to use some knowledge in context. Derived classes have to close the
 * "knowledge subclass continue" branch (e.g., by axiom lookup or propositional tactics).
 * @param name The name of the tactic.
 */
abstract class ContextualizeKnowledgeTactic(name: String) extends PositionTactic(name) {
  def applies(f: Formula): Boolean
  override def applies(s: Sequent, p: Position): Boolean = applies(getFormula(s, p))

  /**
   * This methods constructs the desired result before the renaming, substitution to be performed and a tactic
   * that performs the renaming.
   *
   * An contextualize knowledge tactic performs the following steps:
   * 1. Guess desired result
   * 2. Rename bound variables to match the instance we want
   * 3. Perform Uniform substitution
   *
   * @param f the formula that should be rewritten
   * @param pos the position to which this rule is applied to
   * @return (Desired result before executing the given position tactic;
   *         the uniform substitution that transforms the desired result into the second axiom (Hilbert style);
   *         an optional position tactic that transforms the actual axiom or propositional truth
   *         into the desired result (usually substitution)).
   * @see #constructInstanceAndSubst(Formula)
   */
  def constructInstanceAndSubst(f: Formula, pos: Position): Option[(Formula,
    Substitution, Option[PositionTactic])]

  //@TODO Add contract that applies()=>\result fine
  override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
    override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import TacticLibrary.{abstractionT,skolemizeT,cutT}
      constructInstanceAndSubst(getFormula(node.sequent, pos), pos) match {
        case Some((desiredResult, subst, succTac)) =>
          val f = getFormula(node.sequent, pos)
          def fToPhi(phi: Formula) = new ExpressionTraversalFunction {
            override def preF(pos: PosInExpr, frm: Formula): Either[Option[StopTraversal], Formula] =
              if (frm == f) Right(phi) else Left(None)
          }
          def traverse(phi: Formula) = ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fToPhi(phi)),
            getFormula(node.sequent, pos.topLevel)) match {
            case Some(frm) => frm
            case None => throw new IllegalArgumentException("Unable to replace formula")
          }
          val desiredResultInContext = traverse(desiredResult)
          val fInContext = getFormula(node.sequent, pos.topLevel)
          val axiomInstance = Imply(desiredResultInContext, fInContext)

          val axiomInstPos = AntePosition(node.sequent.ante.length)

          val axiomApplyTactic = assertPT(axiomInstance)(axiomInstPos) &
            ImplyLeftT(axiomInstPos) && (
              hideT(SuccPosition(0)) /* desired result remains */,
              AxiomCloseT
            )

          //@TODO Insert contract tactic after hiding all which checks that exactly the intended axiom formula remains and nothing else.
          //@TODO Introduce a reusable tactic that hides all formulas except the ones given as argument and is followed up by a contract ensuring that exactly those formuals remain.
          val succCont = succTac match {
            // SuccPosition(0) is the only position remaining in axiom proof
            case Some(tactic) => assertT(0, 1) & tactic(SuccPosition(0))
            case None => NilT
          }

          println("Axiom instance " + axiomInstance)
          val axiomPos = SuccPosition(node.sequent.succ.length)
          val axiomInstanceTactic = (assertPT(axiomInstance) & cohideT)(axiomPos) & (assertT(0,1) &
            assertT(axiomInstance, SuccPosition(0)) & kModalModusPonensT(SuccPosition(0)) &
            abstractionT(SuccPosition(0)) & hideT(SuccPosition(0)) & skolemizeT(SuccPosition(0)) &
            assertT(0, 1) & succCont & LabelBranch("knowledge subclass continue"))
          Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
        case None => None
      }
    }
  }

}

/**
 * Base class for derivative axiom in context tactics.
 * @param name The name of the tactic.
 * @param axiomName The name of the axiom.
 */
abstract class DerivativeAxiomInContextTactic(name: String, axiomName: String)
    extends ContextualizeKnowledgeTactic(name) {
  require(Axiom.axioms != null, "the list of axioms should be defined.")
  require(Axiom.axioms.keySet.contains(axiomName), "The requested axiom should be in the set of axioms.")
  val axiom = Axiom.axioms.get(axiomName)
  def applies(f: Formula): Boolean
  override def applies(s: Sequent, p: Position): Boolean = axiom.isDefined && applies(getFormula(s, p))

  import TacticLibrary.AxiomCloseT
  import AxiomTactic.axiomT
  import scala.language.postfixOps
  override def apply(pos: Position): Tactic = super.apply(pos) &
    onBranch("knowledge subclass continue", axiomT(axiomName) & assertT(1,1) & ImplyRightT(SuccPosition(0)) &
      EquivLeftT(AntePosition(0)) & AndLeftT(AntePosition(0)) & onBranch(
        (equivRightLbl, locateAnte(NotLeftT)*)
      ) & AxiomCloseT)
}

/**
 * Base class for propositional equivalences in context tactics.
 * @param name The name of the tactic.
 */
abstract class PropositionalInContextTactic(name: String)
    extends ContextualizeKnowledgeTactic(name) {
  def applies(f: Formula): Boolean
  override def applies(s: Sequent, p: Position): Boolean = applies(getFormula(s, p))

  override def apply(pos: Position): Tactic = super.apply(pos) &
    onBranch("knowledge subclass continue", TacticLibrary.propositional)
}

/**
 * Base class for term axiom tactics.
 * @param name The name of the tactic.
 * @param axiomName The name of the axiom.
 */
abstract class TermAxiomTactic(name: String, axiomName: String) extends PositionTactic(name) {
  //@todo a java.lang.ExceptionInInitializerError is thrown
  require(Axiom.axioms != null, "the list of axioms should be defined.")
  require(Axiom.axioms.keySet.contains(axiomName), "The requested axiom should be in the set of axioms.")
  val axiom = Axiom.axioms.get(axiomName)
  def applies(t: Term): Boolean
  override def applies(s: Sequent, p: Position): Boolean = {
    axiom.isDefined && { applies(getTerm(s, p))
      //Allow for the use of invalid positions, and simply silently fail.
      //@todo might not be the best idea?
//      if(p.isAnte && s.ante.length > p.getIndex) {
//        applies(getTerm(s, p))
//      }
//      else if(!p.isAnte && s.succ.length > p.getIndex) {
//        applies(getTerm(s,p))
//      }
//      else {
//        false
//      }
    }
  }

  /**
   * This methods constructs the axiom instance and substitution to be performed.
   *
   * An axiom tactic performs the following steps (Hilbert style):
   * 1. Guess axiom
   * 2. Perform Uniform substitution to instantiate the axiom
   *
   * Axioms usually have the form ax = OP(a, b). The constructed instance either has the form OP(t, e) or OP(e, t).
   * Here, t is an input to this function and e is derived from the axiom to be used. The output of this function
   * should be 2 things:
   * 1. The instance of the axiom eventually to be used in the proof
   * 2. The substitution to turn 2 into 1
   *
   * In the long run all this should be computed by unification.
   *
   * @param t the term that should be rewritten using the axiom
   * @param ax the axiom to be used
   * @param pos the position to which this rule is applied to
   * @return (the instance of the axiom,
   *         the uniform substitution that transforms the axiom into the axiom instance (Hilbert style)).
   * @see #constructInstanceAndSubst(Term)
   */
  def constructInstanceAndSubst(t: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)]

  //@TODO Add contract that applies()=>\result fine
  override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
    override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      import EqualityRewritingImpl.equalityRewriting
      import AxiomTactic.axiomT
      axiom match {
        case Some(ax) =>
          constructInstanceAndSubst(getTerm(node.sequent, pos), ax, pos) match {
            case Some((axiomInstance, subst)) =>
              val axiomInstPos = AntePosition(node.sequent.ante.length)
              val axiomApplyTactic = assertPT(axiomInstance)(axiomInstPos) & (axiomInstance match {
                //@TODO If Pos.isAnte the following position management seems wrong since unstable.
                case Equals(Real, _, _) => equalityRewriting(axiomInstPos, pos, checkDisjoint = false) & ((assertPT(axiomInstance)&hideT)(axiomInstPos) & (assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos.topLevel))
                case _ => ???
              })
              val axiomPos = SuccPosition(node.sequent.succ.length)
              println("Axiom instance " + axiomInstance)
              val axiomInstanceTactic = (assertPT(axiomInstance) & cohideT)(axiomPos) & (assertT(0,1) & assertT(axiomInstance, SuccPosition(0)) & uniformSubstT(subst, Map(axiomInstance -> ax)) & assertT(0, 1) & (axiomT(axiomName) & assertT(1,1) & AxiomCloseT))
              Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
            case None => None
          }
        case None => None
      }
    }
  }

}
