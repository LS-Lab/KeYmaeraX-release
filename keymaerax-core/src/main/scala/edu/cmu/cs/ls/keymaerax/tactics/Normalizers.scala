package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.{And, Sequent}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, PositionTactic}

/**
 * Tactics for rewriting formulas into various normal forms.
 * Created by nfulton on 7/19/15.
 */
object Normalizers {
  def canonizeConjunction : PositionTactic = CanonizeConjunction()
}

/**
 * Converts a conjunctive formula into the canonical form; i.e., turns any And(x, And(y,z)) into
 * And(And(x,y),z)
 * @author Nathan Fulton
 */
object CanonizeConjunction {
  def apply() = new PositionTactic("Canonize Conjunction") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case And(l,r) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = {

    }
  }
}


object PropositionalAxioms {
  def AndAssocT : PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case And(l, And(rl, rr)) => Equiv(And(And(rl, rr), l), fml)
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s:Sequent, p:Position):Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(BranchLabels.cutShowLbl)
    }

    uncoverAxiomT("& associative", axiomInstance, _ => andAssocBaseT)
  }

  def andAssocBaseT: PositionTactic = {
    def subst(fml: Formula) : List[SubstitutionPair] = fml match {
      case Equiv(And(l, And(rl, rr)), _) => {
        val aP = PredicationalOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredicationalOf(Function("q", None, Real, Bool), Anything)
        val aR = PredicationalOf(Function("r", None, Real, Bool), Anything)
        substitutionPair(aP, p) :: SubstitutionPair(aQ, q) :: SubstitutionPair(aR, r) :: Nil
      }
    }
    axiomLookupBaseT("& associative", subst, _ => NilPT, (f, ax) => ax)
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