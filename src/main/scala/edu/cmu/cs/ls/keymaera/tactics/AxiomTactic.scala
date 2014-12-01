package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
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
   * 4. A tactic to turn the result of 3 into the actual axiom
   *
   * In the long run all this should be computed by unification.
   *
   * @param f the formula that should be rewritten using the axiom
   * @param ax the axiom to be used
   * @param pos the position to which this rule is applied to
   * @return (Axiom before executing the given position tactic;
   *         the instance of the axiom,
   *         the uniform substitution that transforms the first into the second axiom (Hilbert style);
   *         an optional position tactic that transforms the first
   *         argument into the actual axiom (usually alpha renaming)).
   * @see #constructInstanceAndSubst(Formula)
   */
  def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
    constructInstanceAndSubst(f, ax)

  def constructInstanceAndSubst(f: Formula, ax: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = {
    constructInstanceAndSubst(f) match {
      case Some((instance, subst)) => Some((ax, instance, subst, None))
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
          constructInstanceAndSubst(getFormula(node.sequent, pos.topLevel), ax, pos) match {
            case Some((_, axiomInstance, subst, ptac)) =>
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
              val cont = ptac match {
                // SuccPosition(0) is the only position remaining in axiom proof
                case Some(tactic) => assertT(0, 1) & tactic(SuccPosition(0))
                case None => NilT
              }
              val axiomPos = SuccPosition(node.sequent.succ.length)
              println("Axiom instance " + axiomInstance)
              val axiomInstanceTactic = (assertPT(axiomInstance) & cohideT)(axiomPos) & (assertT(0,1) & assertT(axiomInstance, SuccPosition(0)) & uniformSubstT(subst, Map(axiomInstance -> ax)) & assertT(0, 1) & (cont & axiomT(axiomName) & assertT(1,1) & AxiomCloseT))
              Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
            case None => None
          }
        case None => None
      }
    }
  }

}
