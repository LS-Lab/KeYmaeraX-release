package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.SyntacticDerivationInContext.ApplicableAtFormula
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{LabelBranch, Tactic, PositionTactic}

/**
 * Tactics for rewriting formulas into various normal/canonical/whatever forms.
 * Created by nfulton on 7/19/15.
 */
object Formatters {
  def debugger(s : String) = TacticLibrary.debugT("[Formatters] " + s)

  /**
   * Converts a conjunctive formula into left associative form; i.e., turns any And(x, And(y,z)) into
   * And(And(x,y),z)
   * @author Nathan Fulton
   */
  def leftAssociateConj : (PositionTactic with ApplicableAtFormula) = new PositionTactic("Canonize Conjunction") with ApplicableAtFormula {
    override def applies(f : Formula) = f match {
      case x:And => !leftAssociated(x)
      case _ => false
    }
    override def applies(s: Sequent, p: Position): Boolean = applies(TacticHelper.getFormula(s, p))
    private def leftAssociated(f: Formula): Boolean = f match {
      case And(l, r) => leftAssociated(l) && notConj(r)
      case _ => true //base.
    }
    private def notConj(f: Formula) = f match {
      case And(l, r) => false
      case _ => true
    }

    override def apply(p: Position): Tactic = {
      val t : PositionTactic =
        TacticLibrary.debugAtT("[Formatters] About to try AndAssocT") &
        PropositionalAxioms.AndAssocT &
        TacticLibrary.debugAtT("[Formatters] Done with AndAssocT")

      debugger("About to try to reassociate Ands") &
      SearchTacticsImpl.locateLargestSubformula(((x:Formula) => x.isInstanceOf[And] && !leftAssociated(x)), t)(p)

    }
  }
}

object PropositionalAxioms {
  def AndAssocT : PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case And(l, And(rl, rr)) => Equiv(And(And(l, rl), rr), fml)
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s:Sequent, p:Position):Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(BranchLabels.cutShowLbl)
    }

    AxiomTactic.uncoverAxiomT("& associative", axiomInstance, _ => andAssocBaseT)
  }
  private def andAssocBaseT: PositionTactic = {
    def subst(fml: Formula) : List[SubstitutionPair] = fml match {
      case Equiv(And(And(ll, lr), r), _) => {
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredOf(Function("q", None, Real, Bool), Anything)
        val aR = PredOf(Function("r", None, Real, Bool), Anything)
        SubstitutionPair(aP, ll) :: SubstitutionPair(aQ, lr) :: SubstitutionPair(aR, r) :: Nil
      }
    }
    AxiomTactic.axiomLookupBaseT("& associative", subst, _ => Tactics.NilPT, (f, ax) => ax)
  }
}



/*
  def AndReoderingT : PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ODESystem(c, And(h, q)), p) =>
        Equiv(fml, Box(ODESystem(c, And(q, h)), p))
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(cutShowLbl)
    }

    uncoverAxiomT("Domain Constraint Conjunction Reordering", axiomInstance, _ => andReorderingAxiomBaseT)
  }

  def andReorderingAxiomBaseT: PositionTactic = { // diffcut = thing to remove
  def subst(fml: Formula) : List[SubstitutionPair] = fml match {
      case Equiv(Box(ODESystem(c, And(h, q)), p), _) =>
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredOf(Function("q", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: SubstitutionPair(aP, p):: SubstitutionPair(aQ, q) :: Nil
    }
    axiomLookupBaseT("Domain Constraint Conjunction Reordering", subst, _ => NilPT, (f, ax) => ax) //@todo not sure the ax is necessary here.
  }
 */