/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.equivalenceCongruenceT
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{uncoverAxiomT, axiomLookupBaseT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.ContextTactics.cutInContext
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{lastAnte, lastSucc, locateAnte, locateSucc, onBranch}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Position._
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable.{Map, List}

/**
 * Implementation of tactics for handling propositions.
 */
object PropositionalTacticsImpl {
  /** Alpha-rules that is propositional rules that do not split branches*/
  def NonBranchingPropositionalT: PositionTactic = ListPropositionalT("Nonbranching Propositional",
    NotLeftT :: AndLeftT :: NotRightT :: ImplyRightT :: OrRightT :: Nil)

  def Propositional: PositionTactic = new PositionTactic("Propositional") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) PropositionalLeftT.applies(s, p) else PropositionalRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) PropositionalLeftT.apply(pos) else PropositionalRightT.apply(pos)
  }

  def PropositionalLeftT: PositionTactic = ListPropositionalT("Propositional Left",
    NotLeftT :: AndLeftT :: OrLeftT :: ImplyLeftT :: EquivLeftT :: Nil)

  def PropositionalRightT: PositionTactic = ListPropositionalT("Propositional Right",
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

  def AndT: PositionTactic = new PositionTactic("And") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) AndLeftT.applies(s, p) else AndRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) AndLeftT.apply(pos) else AndRightT.apply(pos)
  }

  def AndLeftT: PositionTactic = new PositionTactic("AndLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndRightT: PositionTactic = new PositionTactic("AndRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrT: PositionTactic = new PositionTactic("Or") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) OrLeftT.applies(s, p) else OrRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) OrLeftT.apply(pos) else OrRightT.apply(pos)
  }

  def OrLeftT: PositionTactic = new PositionTactic("OrLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrRightT: PositionTactic = new PositionTactic("OrRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyT: PositionTactic = new PositionTactic("Imply") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) ImplyLeftT.applies(s, p) else ImplyRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) ImplyLeftT.apply(pos) else ImplyRightT.apply(pos)
  }

  def ImplyLeftT: PositionTactic = new PositionTactic("ImplyLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Imply(_, _) => p.inExpr == HereP
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  /**
   * @see [[ImplyRight]]
   * @see [[InverseImplyRightT]]
   */
  def ImplyRightT: PositionTactic = new PositionTactic("ImplyRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && p.inExpr == HereP && (s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyToAndT: PositionTactic = new PositionTactic("ImplyToAnd") {
    def applies(s: Sequent, p: Position) = !p.isAnte & (getFormula(s, p) match {
      case Imply(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, pos) match {
        case fml@Imply(l, r) => Some(cutInContext(Equiv(fml, Not(And(l, Not(r)))), pos) & onBranch(
          (cutShowLbl, lastSucc(cohideT) & equivalenceCongruenceT(pos.inExpr) & lastSucc(EquivRightT) & onBranch(
            // use concrete positions instead of locate, so that original formulas remain untouched. makes assumptions about where formulas will appear after tactic execution
            (equivLeftLbl, lastSucc(NotRightT) & lastAnte(AndLeftT) & lastAnte(NotLeftT) & ImplyLeftT(AntePosition(0)) & AxiomCloseT),
            (equivRightLbl, lastAnte(NotLeftT) & ImplyRightT(SuccPosition(0)) & AndRightT(SuccPosition(0)) && (AxiomCloseT, NotRightT(SuccPosition(0)) & AxiomCloseT))
            )),
          (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), pos.topLevel))
        ))
        case _ => throw new IllegalStateException("Checked by applies to never happen")
      }
    }
  }

  def EquivT: PositionTactic = new PositionTactic("Equiv") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) EquivLeftT.applies(s, p) else EquivRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) EquivLeftT.apply(pos) else EquivRightT.apply(pos)
  }

  def EquivLeftT: PositionTactic = new PositionTactic("EquivLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(equivLeftLbl), LabelBranch(equivRightLbl))
  }

  def EquivRightT: PositionTactic = new PositionTactic("EquivRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && (s.succ(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(equivLeftLbl), LabelBranch(equivRightLbl))
  }

  def NotT: PositionTactic = new PositionTactic("Not") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) NotLeftT.applies(s, p) else NotRightT.applies(s, p)
    def apply(pos: Position): Tactic = if (pos.isAnte) NotLeftT.apply(pos) else NotRightT.apply(pos)
  }

  def NotLeftT: PositionTactic = new PositionTactic("NotLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotRightT: PositionTactic = new PositionTactic("NotRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AxiomCloseT(a: Position, b: Position): Tactic = new Tactics.ApplyRule(Close(a, b)) {
    override def applicable(node: ProofNode): Boolean = a.isAnte && !b.isAnte &&
      getFormula(node.sequent, a) == getFormula(node.sequent, b)
  }

  def AxiomCloseT: Tactic = new ConstructionTactic("AxiomClose") {
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

  def CloseTrueT: PositionTactic = new PositionTactic("CloseTrue") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && (getFormula(s, p) match {
      case True => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(CloseTrue(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def CloseFalseT: PositionTactic = new PositionTactic("CloseFalse") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case False => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(CloseFalse(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def ConsolidateSequentT: Tactic = new ConstructionTactic("Consolidate Sequent") {
    override def applicable(node: ProofNode): Boolean = true

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val s = node.sequent
      //TODO-nrf Not sure what to do with pref. Matters in non-taut case.
      if (s.ante.isEmpty && s.succ.isEmpty) Some(NilT)
      else {
        val assumption =
          if (s.ante.isEmpty) True
          else s.ante.reduce((l, r) => And(l, r))

        val implicant =
          if (s.succ.isEmpty) Not(assumption)
          else s.succ.reduce((l, r) => Or(l, r))

        val consolidatedFml =
          if (s.ante.isEmpty) implicant
          else Imply(assumption, implicant)

        Some(cutT(Some(consolidatedFml)) & onBranch(
          (cutUseLbl,
            if (s.ante.isEmpty) {
              if (s.succ.isEmpty) lastAnte(NotLeftT) & AxiomCloseT
              else AxiomCloseT | (lastAnte(OrLeftT) && (AxiomCloseT | NilT, AxiomCloseT))*(s.succ.length-1)
            } else {
              if (s.succ.isEmpty) lastAnte(ImplyLeftT) && (
                AxiomCloseT | (lastSucc(AndRightT) && (AxiomCloseT | NilT, AxiomCloseT))*(s.ante.length-1),
                lastAnte(NotLeftT) & (AxiomCloseT | (lastSucc(AndRightT) && (AxiomCloseT | NilT, AxiomCloseT))*(s.ante.length-1)))
              else lastAnte(ImplyLeftT) && (
                AxiomCloseT | (lastSucc(AndRightT) && (AxiomCloseT | NilT, AxiomCloseT))*(s.ante.length-1),
                AxiomCloseT | (lastAnte(OrLeftT) && (AxiomCloseT | NilT, AxiomCloseT))*(s.succ.length-1))
            }
            ),
          (cutShowLbl, SearchTacticsImpl.lastSucc(cohideT))
        ))
      }
    }
  }

  def hideT: PositionTactic = new PositionTactic("Hide") {
    def applies(s: Sequent, p: Position) = p.isIndexDefined(s) && p.isTopLevel

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) HideLeft(pos) else HideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = pos.isIndexDefined(node.sequent) && pos.isTopLevel
      //@TODO Shouldn't this be = pos.isDefined(node.sequent) here and everywhere?
    }
  }

  def cohideT: PositionTactic = new PositionTactic("CoHide") {
    def applies(s: Sequent, p: Position) = p.isIndexDefined(s) && p.isTopLevel

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) CoHideLeft(pos) else CoHideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = pos.isIndexDefined(node.sequent) && pos.isTopLevel
    }
  }

  def cohide2T(p1: Position, p2: Position): Tactic = new Tactic("CoHide2") { outer =>
    override def applicable(node: ProofNode): Boolean =
       p1.isAnte && p1.isTopLevel && p1.getIndex < node.sequent.ante.length &&
      !p2.isAnte && p2.isTopLevel && p2.getIndex < node.sequent.succ.length

    override def apply(tool: Tool, node: ProofNode): Unit = {
      val cohideRule = new Tactics.ApplyRule(CoHide2(p1, p2)) {
        override def applicable(node: ProofNode): Boolean = outer.applicable(node)
      }
      cohideRule.continuation = continuation
      cohideRule.apply(tool, node)
    }
  }

  def cutT(f: Option[Formula]): Tactic = cutT((x: ProofNode) => f)
  def cutT(g: (ProofNode => Option[Formula])): Tactic = new ConstructionTactic("Cut") {
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

  def kModalModusPonensT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Imply(Box(a, p), Box(b, q)) if a == b => Imply(Box(a, Imply(p, q)), fml)
      case _ => False
    }
    uncoverAxiomT("K modal modus ponens", axiomInstance, _ => kModalModusPonensBaseT)
  }
  /** Base tactic for k modal modus ponens */
  private def kModalModusPonensBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(_, Imply(Box(a, p), Box(b, q))) if a == b =>
        val aA = ProgramConst("a")
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredOf(Function("q", None, Real, Bool), Anything)
        SubstitutionPair(aA, a) :: SubstitutionPair(aP, p) :: SubstitutionPair(aQ, q) :: Nil
    }
    axiomLookupBaseT("K modal modus ponens", subst, _ => NilPT, (f, ax) => ax)
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
  def uniformSubstT(subst: List[SubstitutionPair], delta: (Map[Formula, Formula]) = Map()): Tactic = new ConstructionTactic("Uniform Substitution") {
    def applicable(pn: ProofNode) = true

    def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = {
      val ante = for (f <- p.sequent.ante) yield delta.get(f) match {
        case Some(frm) => frm
        case None => f
      }
      val succ = for (f <- p.sequent.succ) yield delta.get(f) match {
        case Some(frm) => frm
        case None => f
      }
      Some(new Tactics.ApplyRule(UniformSubstitutionRule(USubst(subst), Sequent(p.sequent.pref, ante, succ))) {
        override def applicable(node: ProofNode): Boolean = true
      })
    }

  }

  // derived

  def equivifyRightT: PositionTactic = new PositionTactic("EquivifyRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && p.inExpr == HereP && (s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivifyRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def cutRightT(cut: Formula): PositionTactic = new PositionTactic("CutRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && p.inExpr == HereP

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(CutRight(cut, pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(BranchLabels.cutUseLbl), LabelBranch(BranchLabels.cutShowLbl))
  }

  def cutLeftT(cut: Formula): PositionTactic = new PositionTactic("CutLeft") {
    def applies(s: Sequent, p: Position) = p.isAnte && p.inExpr == HereP

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(CutLeft(cut, pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(BranchLabels.cutUseLbl), LabelBranch(BranchLabels.cutShowLbl))
  }

  def commuteEquivRightT: PositionTactic = new PositionTactic("CommuteEquivRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && p.inExpr == HereP && (s.succ(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(CommuteEquivRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  /**
   * {{{
   *   |- a -> b
   * ----------
   *   a |- b
   * }}}
   * @author Nathan Fulton
   *         (only used in one place. Delete if this duplicates something that already exists.)
   * @see [[ImplyRightT]]
   * @todo could generalize to work in gamma delta context when specifying TwoPositionRule type positions.
   */
  def InverseImplyRightT : Tactic = new ConstructionTactic("inverse imply right") {
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val left = node.sequent.ante.head
      val right = node.sequent.succ.head
      Some(
        cutT(Some(Imply(left, right))) & onBranch(
          (BranchLabels.cutUseLbl,
            assertT(2, 1) ~
            PropositionalTacticsImpl.modusPonensT(AntePos(0), AntePos(1)) ~
            AxiomCloseT ~ errorT("Should have closed.")
          ),
          (BranchLabels.cutShowLbl, hideT(SuccPos(0)) & hideT(AntePos(0)) /* This is the result. */)
        )
      )
    }

    override def applicable(node: ProofNode): Boolean =
      node.sequent.succ.length == 1 && node.sequent.ante.length == 1
  }
}
