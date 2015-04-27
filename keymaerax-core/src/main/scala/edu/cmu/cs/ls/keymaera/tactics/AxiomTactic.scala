package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.{lastAnte, lastSucc, onBranch}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getTerm
import AxiomaticRuleTactics.{equivalenceCongruenceT,boxMonotoneT,diamondMonotoneT}
import ContextTactics.{cutInContext,cutImplyInContext}
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tools.Tool

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

  /**
   * Creates a new tactic that uses equivalence congruence or equation congruence or monotone to uncover an axiom inside
   * a context.
   * @param axiomName The name of the axiom.
   * @param axiomInstance The axiom instance that should be used in context (an equivalence or equality).
   * @param baseT The base tactic to show the axiom instance once uncovered.
   * @return The new tactic.
   * @todo use CutLeft+CutRight+EquivifyRight for efficiency instead of cut etc.
   */
  def uncoverAxiomT(axiomName: String,
                    axiomInstance: Formula => Formula,
                    baseT: Formula => PositionTactic): PositionTactic = new PositionTactic(axiomName) {
    override def applies(s: Sequent, p: Position): Boolean = axiomInstance(getFormula(s, p)) match {
      case Equiv(lhs, rhs) => getFormula(s, p) == lhs || getFormula(s, p) == rhs
      case Imply(lhs, rhs) => getFormula(s, p) == lhs || getFormula(s, p) == rhs
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiomInstance(getFormula(node.sequent, p)) match {
          case inst@Equiv(f, g) =>
            Some(cutInContext(inst, p) & onBranch(
              (cutShowLbl, lastSucc(cohideT) & equivalenceCongruenceT(p.inExpr) & lastSucc(baseT(getFormula(node.sequent, p)))),
              (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
            ))
          case inst@Imply(f, g) if p.isAnte =>
            Some(cutImplyInContext(inst, p) & onBranch(
              (cutShowLbl, lastSucc(cohideT) & lastSucc(ImplyRightT) & (boxMonotoneT | diamondMonotoneT | NilT) &
                assertT(1, 1) & lastAnte(assertPT(f, "Unexpected formula in ante")) & lastSucc(assertPT(g, "Unexpected formula in succ")) &
                cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getFormula(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              )),
              (cutUseLbl, lastAnte(ImplyLeftT) &&(
                AxiomCloseT,
                (assertPT(node.sequent(p), "hiding original instance") & hideT)(p.topLevel)))
            ))
          case inst@Imply(f, g) if !p.isAnte =>
            Some(cutImplyInContext(inst, p) & onBranch(
              (cutShowLbl, lastSucc(cohideT) & lastSucc(ImplyRightT) & (boxMonotoneT | diamondMonotoneT | NilT) &
                assertT(1, 1) & lastAnte(assertPT(f, "Unexpected formula in ante")) & lastSucc(assertPT(g, "Unexpected formula in succ")) &
                cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getFormula(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              )),
              (cutUseLbl, lastAnte(ImplyLeftT) &&(
                (assertPT(node.sequent(p), "hiding original instance") & hideT)(p.topLevel),
                AxiomCloseT)
                )
            ))
          case Equal(lhs, rhs) => ???
        }
    }
  }

  def uncoverConditionalAxiomT(axiomName: String,
                               axiomInstance: Formula => Formula,
                               condT: Formula => PositionTactic,
                               baseT: Formula => PositionTactic): PositionTactic = new PositionTactic(axiomName) {
    // TODO generalize to non-toplevel positions
    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (axiomInstance(getFormula(s, p)) match {
        case Imply(_, Equiv (lhs, rhs)) => getFormula(s, p) == lhs || getFormula(s, p) == rhs
        case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = axiomInstance(getFormula(node.sequent, p)) match {
        case inst@Imply(cond, equiv@Equiv(lhs, rhs)) =>
          Some(cutT(Some(equiv))/*cutEquivInContext(equiv, p)*/ & onBranch(
            (cutShowLbl, hideT(p.topLevel) & /* only works because top-level */ cutT(Some(cond)) & onBranch(
              (cutShowLbl, /* hide second-to-last */ hideT(SuccPosition(node.sequent.succ.length - 1)) &
                lastSucc(condT(getFormula(node.sequent, p)))),
              (cutUseLbl, cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getFormula(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              ))
              )),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel) & LabelBranch(cutUseLbl))
          ))
      }
    }
  }

  def uncoverConditionalTermAxiomT(axiomName: String,
                                   axiomInstance: Term => Formula,
                                   condT: Term => PositionTactic,
                                   baseT: Term => PositionTactic): PositionTactic = new PositionTactic(axiomName) {
    override def applies(s: Sequent, p: Position): Boolean = axiomInstance(getTerm(s, p)) match {
      case Imply(_, Equiv (lhs, rhs)) => s(p) == lhs || s(p) == rhs
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = axiomInstance(getTerm(node.sequent, p)) match {
        case inst@Imply(cond, equiv@Equiv(lhs, rhs)) =>
          Some(cutT(Some(equiv))/*cutEquivInContext(equiv, p)*/ & onBranch(
            (cutShowLbl, hideT(p.topLevel) & /* only works because top-level */ cutT(Some(cond)) & onBranch(
              (cutShowLbl, /* hide second-to-last */ hideT(SuccPosition(node.sequent.succ.length - 1)) &
                lastSucc(condT(getTerm(node.sequent, p)))),
              (cutUseLbl, cutT(Some(inst)) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & lastSucc(baseT(getTerm(node.sequent, p)))),
                (cutUseLbl, lastAnte(ImplyLeftT) & AxiomCloseT)
              ))
            )),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel) & LabelBranch(cutUseLbl))
          ))
      }
    }
  }

  /**
   * Creates a new tactic to show an axiom by lookup.
   * @param axiomName The name of the axiom.
   * @param subst A function fml => subst to create the substitution from the current axiom form fml (an equivalence or equality).
   * @param alpha A function fml => alpha to create tactic for alpha renaming after substitution from the current axiom form fml.
   * @param axiomInstance A function (fml, axiom) => axiomInstance to generate the axiom instance from the axiom
   *                      form as in the axiom file and the current form fml as in the sequent.
   * @return The new tactic.
   */
  def axiomLookupBaseT(axiomName: String,
                       subst: Formula => List[SubstitutionPair],
                       alpha: Formula => PositionTactic,
                       axiomInstance: (Formula, Formula) => Formula): PositionTactic = new PositionTactic(axiomName) {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equiv(_, _) => true
      case Imply(_, _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      val axiom = Axiom.axioms.get(axiomName) match {
        case Some(ax) => ax
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val fml = getFormula(node.sequent, p)
        Some(
          uniformSubstT(subst(fml), Map(fml -> axiomInstance(fml, axiom))) &
            assertT(0, 1) & lastSucc(assertPT(axiomInstance(fml, axiom), "Unexpected uniform substitution result")) &
            lastSucc(alpha(fml)) & AxiomTactic.axiomT(axiomName) &
            assertT(1, 1) & lastAnte(assertPT(axiom, "Unexpected axiom form in antecedent")) &
            lastSucc(assertPT(axiom, "Unexpected axiom form in succedent")) & AxiomCloseT
        )
      }
    }
  }
}