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
        val s = USubst(SubstitutionPair(aX, a) ::
          SubstitutionPair(ApplyPredicate(pX, Anything), p) ::
          SubstitutionPair(ApplyPredicate(qX, Anything), q) :: Nil)
        Some(new ApplyRule(AxiomaticRule("[] congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
      case _ => None
    }
  }

  /**
   * Creates a new tactic for box congruence rewriting. Expects a sequent with a sole formula in the succedent, of
   * the form < a >p <-> < a >q.
   * @return The newly created tactic.
   */
  def diamondCongruenceT: Tactic = new ConstructionTactic("<> congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Equiv(DiamondModality(a, p), DiamondModality(b, q)) => a == b
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Equiv(DiamondModality(a, p), DiamondModality(b, q)) if a == b =>
        val aX = ProgramConstant("a")
        val pX = Function("p", None, Real, Bool)
        val qX = Function("q", None, Real, Bool)
        val s = USubst(SubstitutionPair(aX, a) ::
          SubstitutionPair(ApplyPredicate(pX, Anything), p) ::
          SubstitutionPair(ApplyPredicate(qX, Anything), q) :: Nil)
        Some(new ApplyRule(AxiomaticRule("<> congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
      case _ => None
    }
  }

  /**
   * Creates a new tactic for box monotone. Expects a sequent with a sole formula in the antecedent of the form [a]p
   * and a sole formula in the succedent of the form [a]q.
   * @return The newly created tactic.
   */
  def boxMonotoneT: Tactic = new ConstructionTactic("[] monotone") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.length == 1 && node.sequent.succ.length == 1 &&
      (node.sequent.ante(0) match {
        case BoxModality(a, _) => node.sequent.succ(0) match {
          case BoxModality(b, _) => a == b
          case _ => false
        }
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.ante(0) match {
      case BoxModality(a, p) => node.sequent.succ(0) match {
        case BoxModality(b, q) =>
          val aX = ProgramConstant("a")
          val pX = Function("p", None, Real, Bool)
          val qX = Function("q", None, Real, Bool)
          val s = USubst(SubstitutionPair(aX, a) ::
            SubstitutionPair(ApplyPredicate(pX, Anything), p) ::
            SubstitutionPair(ApplyPredicate(qX, Anything), q) :: Nil)
          Some(new ApplyRule(AxiomaticRule("[] monotone", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          })
        case _ => None
      }
      case _ => None
    }
  }

  /**
   * Creates a new tactic for box monotone. Expects a sequent with a sole formula in the antecedent of the form < a >p
   * and a sole formula in the succedent of the form < a >q.
   * @return The newly created tactic.
   */
  def diamondMonotoneT: Tactic = new ConstructionTactic("<> monotone") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.length == 1 && node.sequent.succ.length == 1 &&
      (node.sequent.ante(0) match {
        case DiamondModality(a, _) => node.sequent.succ(0) match {
          case DiamondModality(b, _) => a == b
          case _ => false
        }
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.ante(0) match {
      case DiamondModality(a, p) => node.sequent.succ(0) match {
        case DiamondModality(b, q) =>
          val aX = ProgramConstant("a")
          val pX = Function("p", None, Real, Bool)
          val qX = Function("q", None, Real, Bool)
          val s = USubst(SubstitutionPair(aX, a) ::
            SubstitutionPair(ApplyPredicate(pX, Anything), p) ::
            SubstitutionPair(ApplyPredicate(qX, Anything), q) :: Nil)
          Some(new ApplyRule(AxiomaticRule("<> monotone", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          })
        case _ => None
      }
      case _ => None
    }
  }

  /**
   * Creates a new tactic for Goedel. Expects a sequent with a sole formula in the succedent of the form [a]p.
   * @return The newly created tactic.
   */
  def goedelT: Tactic = new ConstructionTactic("Goedel") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
          case BoxModality(_, _) => true
          case _ => false
        })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case BoxModality(a, p) =>
        val aX = ProgramConstant("a")
        val pX = Function("p", None, Real, Bool)
        val s = USubst(SubstitutionPair(aX, a) ::
          SubstitutionPair(ApplyPredicate(pX, Anything), p) :: Nil)
        Some(new ApplyRule(AxiomaticRule("Goedel", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }

  /**
   * Creates a new tactic for universal generalization. Expects a sequent with a sole formula in the succedent of the
   * form \forall x. p(x).
   * @return The newly created tactic.
   */
  def forallGeneralizationT: Tactic = new ConstructionTactic("all generalization") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Forall(_, _) => true
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Forall(vars, p) =>
        assert(vars.length == 1, "forall generalization only supported for one variable")
        val x = vars(0) match {
          case v: Variable => v
          case _ => throw new UnsupportedOperationException("forall generalization only supported for variables")
        }
        val pX = Function("p", None, Real, Bool)
        val s = USubst(SubstitutionPair(ApplyPredicate(pX, CDot), SubstitutionHelper.replaceFree(p)(x, CDot)) :: Nil)
        Some(new ApplyRule(AxiomaticRule("all generalization", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }
}
