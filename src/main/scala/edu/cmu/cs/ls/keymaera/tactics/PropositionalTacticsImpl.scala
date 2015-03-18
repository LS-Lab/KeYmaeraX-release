package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import scala.collection.immutable.{Map, List}

/**
 * Implementation of tactics for handling propositions.
 */
object PropositionalTacticsImpl {
  protected[tactics] def NonBranchingPropositionalT: PositionTactic = ListPropositionalT("Nonbranching Propositional",
    NotLeftT :: AndLeftT :: NotRightT :: ImplyRightT :: OrRightT :: Nil)

  protected[tactics] def Propositional: PositionTactic = new PositionTactic("Propositional") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) PropositionalLeftT.applies(s, p) else PropositionalRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) PropositionalLeftT.apply(pos) else PropositionalRightT.apply(pos)
  }

  protected[tactics] def PropositionalLeftT: PositionTactic = ListPropositionalT("Propositional Left",
    NotLeftT :: AndLeftT :: OrLeftT :: ImplyLeftT :: EquivLeftT :: Nil)

  protected[tactics] def PropositionalRightT: PositionTactic = ListPropositionalT("Propositional Right",
    NotRightT :: AndRightT :: OrRightT :: ImplyRightT :: EquivRightT :: Nil)

  private def ListPropositionalT(name: String, tactics: List[PositionTactic]): PositionTactic = new PositionTactic(name) {
    def applies(s: Sequent, p: Position) = tactics.exists(_.applies(s, p))
    def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) : Boolean = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(tactics.find(_.applies(node.sequent, pos)).get(pos))
      }
    }
  }

  protected[tactics] def AndT: PositionTactic = new PositionTactic("And") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) AndLeftT.applies(s, p) else AndRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) AndLeftT.apply(pos) else AndRightT.apply(pos)
  }

  protected[tactics] def AndLeftT: PositionTactic = new PositionTactic("AndLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def AndRightT: PositionTactic = new PositionTactic("AndRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def OrT: PositionTactic = new PositionTactic("Or") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) OrLeftT.applies(s, p) else OrRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) OrLeftT.apply(pos) else OrRightT.apply(pos)
  }

  protected[tactics] def OrLeftT: PositionTactic = new PositionTactic("OrLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def OrRightT: PositionTactic = new PositionTactic("OrRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def ImplyT: PositionTactic = new PositionTactic("Imply") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) ImplyLeftT.applies(s, p) else ImplyRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) ImplyLeftT.apply(pos) else ImplyRightT.apply(pos)
  }

  protected[tactics] def ImplyLeftT: PositionTactic = new PositionTactic("ImplyLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Imply(_, _) => p.inExpr == HereP
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def ImplyRightT: PositionTactic = new PositionTactic("ImplyRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && p.inExpr == HereP && (s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def EquivT: PositionTactic = new PositionTactic("Equiv") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) EquivLeftT.applies(s, p) else EquivRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) EquivLeftT.apply(pos) else EquivRightT.apply(pos)
  }

  protected[tactics] def EquivLeftT: PositionTactic = new PositionTactic("EquivLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(equivLeftLbl), LabelBranch(equivRightLbl))
  }

  protected[tactics] def EquivRightT: PositionTactic = new PositionTactic("EquivRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && (s.succ(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(equivLeftLbl), LabelBranch(equivRightLbl))
  }

  protected[tactics] def NotT: PositionTactic = new PositionTactic("Not") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) NotLeftT.applies(s, p) else NotRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) NotLeftT.apply(pos) else NotRightT.apply(pos)
  }

  protected[tactics] def NotLeftT: PositionTactic = new PositionTactic("NotLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def NotRightT: PositionTactic = new PositionTactic("NotRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  protected[tactics] def AxiomCloseT(a: Position, b: Position): Tactic = new Tactics.ApplyRule(AxiomClose(a, b)) {
    override def applicable(node: ProofNode): Boolean = a.isAnte && !b.isAnte &&
      getFormula(node.sequent, a) == getFormula(node.sequent, b)
  }

  protected[tactics] def AxiomCloseT: Tactic = new ConstructionTactic("AxiomClose") {
    def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = findPositions(p.sequent) match {
      case Some((a, b)) => Some(AxiomCloseT(a, b))
      case None => None
    }

    def findPositions(s: Sequent): Option[(Position, Position)] = {
      for (f <- s.ante; g <- s.succ)
        if (f == g) return Some((AntePosition(s.ante.indexOf(f)), SuccPosition(s.succ.indexOf(g))))
      None
    }

    override def applicable(node: ProofNode): Boolean = findPositions(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  protected[tactics] def CloseTrueT: PositionTactic = new PositionTactic("CloseTrue") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && (getFormula(s, p) match {
      case True() => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(CloseTrue(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  protected[tactics] def CloseFalseT: PositionTactic = new PositionTactic("CloseFalse") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case False() => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(CloseFalse(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  protected[tactics] def hideT: PositionTactic = new PositionTactic("Hide") {
    def applies(s: Sequent, p: Position) = p.isIndexDefined(s) && p.isTopLevel

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) HideLeft(pos) else HideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = pos.isIndexDefined(node.sequent) && pos.isTopLevel
      //@TODO Shouldn't this be = pos.isDefined(node.sequent) here and everywhere?
    }
  }

  protected[tactics] def cohideT: PositionTactic = new PositionTactic("CoHide") {
    def applies(s: Sequent, p: Position) = p.isIndexDefined(s) && p.isTopLevel

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) CoHideLeft(pos) else CoHideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = pos.isIndexDefined(node.sequent) && pos.isTopLevel
    }
  }

  protected[tactics] def cutT(f: Option[Formula]): Tactic = cutT((x: ProofNode) => f)
  protected[tactics] def cutT(g: (ProofNode => Option[Formula])): Tactic = new ConstructionTactic("Cut") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Some(_) => true
      case _ => false
    }

    override def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = g(p) match {
      case Some(t) =>
        Some(new Tactics.ApplyRule(Cut(t)) {
          override def applicable(node: ProofNode): Boolean = true
        } & (LabelBranch(BranchLabels.cutUseLbl), LabelBranch(BranchLabels.cutShowLbl)))
      case _ => None
    }
  }

  def modusPonensT(assumption: Position, implication: Position): Tactic = new ConstructionTactic("Modus Ponens") {
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val p = AntePosition(assumption.getIndex - (if(assumption.getIndex > implication.getIndex) 1 else 0))
      Some(ImplyLeftT(implication) & (AxiomCloseT(p, SuccPosition(node.sequent.succ.length)), hideT(p)))
    }

    override def applicable(node: ProofNode): Boolean = assumption.isAnte && implication.isAnte &&
      ((getFormula(node.sequent, assumption), getFormula(node.sequent, implication)) match {
        case (a, Imply(b, c)) if a == b => true
        case (a, b) => false
      })
  }

  def kModalModusPonensT = new AxiomTactic("K modal modus ponens", "K modal modus ponens") {
    override def applies(f: Formula): Boolean = f match {
      case Imply(BoxModality(a, _), BoxModality(b, _)) => a == b
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair])] = f match {
      case Imply(BoxModality(a, p), BoxModality(b, q)) if a == b =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        val aQ = ApplyPredicate(Function("q", None, Real, Bool), Anything)
        val l = List(SubstitutionPair(aA, a), SubstitutionPair(aP, p), SubstitutionPair(aQ, q))
        // construct axiom instance: [a](p->q) -> (([a]p) -> ([a]q))
        val g = BoxModality(a, Imply(p, q))
        val axiomInstance = Imply(g, f)
        Some(axiomInstance, l)
      case _ => None
    }
  }

  /**
   * Tactic to perform uniform substitution. In most cases this is called on a sequent that only contains a single
   * formula in order to show that a formula is an instance of an axiom (modulo an alpha renaming of that).
   *
   * @param subst the substitution to perform
   * @param delta a map with replacement for formulas in the sequent. That is, for all (f, g) in delta we will replace
   *              every top-level occurrence of formula f in the conclusion by the respective g
   *              in order to construct the origin of the uniform substitution.
   * @return an instance of a tactic that performs the given uniform substitution
   */
  def uniformSubstT(subst: List[SubstitutionPair], delta: (Map[Formula, Formula])): Tactic = new ConstructionTactic("Uniform Substitution") {
    def applicable(pn: ProofNode) = true

    def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = {
      val ante = for (f <- p.sequent.ante) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      val succ = for (f <- p.sequent.succ) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      Some(new Tactics.ApplyRule(UniformSubstitutionRule(USubst(subst), Sequent(p.sequent.pref, ante, succ))) {
        override def applicable(node: ProofNode): Boolean = true
      })
    }

  }
}
