package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, ConstructionTactic, Tactic}

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
object AxiomaticRuleTactics {

  /**
   * Creates a new tactic for box congruence rewriting. Expects a sequent with a sole formula in the succedent, of
   * the form [a]p <-> [a]q.
   * @return The newly created tactic.
   */
  def boxCongruenceT: Tactic = new ConstructionTactic("[] congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Equiv(BoxModality(a, p), BoxModality(b, q)) => a == b
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Equiv(BoxModality(a, p), BoxModality(b, q)) if a == b =>
        val aX = ProgramConstant("a")
        val pX = Function("p", None, Real, Bool)
        val qX = Function("q", None, Real, Bool)
        val s = Substitution(SubstitutionPair(aX, a) ::
          SubstitutionPair(ApplyPredicate(pX, Anything), p) ::
          SubstitutionPair(ApplyPredicate(qX, Anything), q) :: Nil)
        Some(new ApplyRule(AxiomaticRule("[] congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
      case _ => None
    }
  }
}
