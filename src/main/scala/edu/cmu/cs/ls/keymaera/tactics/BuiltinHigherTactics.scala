package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import SearchTacticsImpl.locateSucc
import EqualityRewritingImpl.eqLeft
import HybridProgramTacticsImpl.{assignment,genInductionT}

/**
 * Implementation of builtin higher tactics composed of base tactics.
 */
object BuiltinHigherTactics {
  /**
   * Tactic that makes a proof step based on the top-level operator
   * except when a decision needs to be made (e.g. for loops, differential equations).
   * This tactics step is thus "indecisive", because it will not reach decisions only make progress.
   * @param beta true to use beta rules (such as AndRight) which split branches.
   * @param simplifyProg false to stop working on modalities. True to take simplifying steps on modalities (except when decisions would be needed).
   * @param equiv true to split equivalences.
   */
  protected[tactics] def stepAt(beta: Boolean, simplifyProg: Boolean, quantifiers: Boolean, equiv: Boolean = false):
      PositionTactic = new PositionTactic("StepAt") {
    override def applies(s: Sequent, p: Position): Boolean = getTactic(s, p).isDefined

    def getTactic(s: Sequent, p: Position): Option[Tactic] = {
      import FOQuantifierTacticsImpl.skolemizeT
      val f = getFormula(s, p)
      val res = f match {
        case Not(_) => if(p.isAnte) Some(NotLeftT(p)) else Some(NotRightT(p))
        case And(_, _) => if(p.isAnte) Some(AndLeftT(p)) else if(beta) Some(AndRightT(p)) else None
        case Or(_, _) => if(p.isAnte) if(beta) Some(OrLeftT(p)) else None else Some(OrRightT(p))
        case Imply(_, _) => if(p.isAnte) if(beta) Some(ImplyLeftT(p)) else None else Some(ImplyRightT(p))
        case Equiv(_, _) => if(equiv) if(p.isAnte) Some(EquivLeftT(p)) else Some(EquivRightT(p)) else None
        case BoxModality(prog, _) if simplifyProg => prog match {
          case Sequence(_, _) => Some(boxSeqT(p))
          case Choice(_, _) => Some(boxChoiceT(p))
          case Assign(_, _) => Some(assignment(p))
          // case Assign(_, _) => Some(assignT(p))
          case NDetAssign(_) => Some(boxNDetAssign(p))
          case Test(_) => Some(boxTestT(p))
          case _ => None
        }
        //@TODO case DiamondModality(prog, f)
        case Forall(_, _) if quantifiers && !p.isAnte => Some(skolemizeT(p))
        case Exists(_, _) if quantifiers && p.isAnte => Some(skolemizeT(p))
        case _ => None
      }
      res
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTactic(node.sequent, p)
    }
  }

  /**
   * Master tactic.
   * @param invGenerator Generates invariants.
   * @param exhaustive True, if tactic should be applied exhaustively, false otherwise.
   * @return The applicable tactic.
   */
  protected[tactics] def master(invGenerator: Generator[Formula], exhaustive: Boolean = false) = {
    def repeat(t: Tactic):Tactic = if(exhaustive) repeatT(t) else t
    repeat(closeT
      | locateSuccAnte(stepAt(beta = false, simplifyProg = true, quantifiers = true))
      | locateSuccAnte(stepAt(beta = true, simplifyProg = true, quantifiers = true))
      | locateSucc(genInductionT(invGenerator))
      | locateAnte(eqLeft(exhaustive = false))
      | locateSucc(differentialInduction)
      | locateSuccAnte(stepAt(beta = true, simplifyProg = true, quantifiers = true, equiv = true))
    ) ~ arithmeticT
  }

  /**
   * Master tactic without arithmetic.
   * @param invGenerator Generates invariants.
   * @param exhaustive True, if tactic should be applied exhaustively, false otherwise.
   * @return The applicable tactic.
   */
  protected[tactics] def noArith(invGenerator: Generator[Formula], exhaustive: Boolean = false) = {
    def repeat(t: Tactic):Tactic = if(exhaustive) repeatT(t) else t
    repeat(closeT
      | locateSuccAnte(stepAt(beta = false, simplifyProg = true, quantifiers = true))
      | locateSuccAnte(stepAt(beta = true, simplifyProg = true, quantifiers = true))
      | locateSucc(genInductionT(invGenerator))
      | locateAnte(eqLeft(exhaustive = false))
      | locateSucc(differentialInduction)
      | locateSuccAnte(stepAt(beta = true, simplifyProg = true, quantifiers = true, equiv = true))
    )
  }
}
