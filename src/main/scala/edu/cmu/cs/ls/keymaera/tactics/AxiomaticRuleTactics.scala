package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper.replace
import edu.cmu.cs.ls.keymaera.tactics.SubstitutionHelper.replaceFree
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, ConstructionTactic, Tactic, NilT}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.globalAlphaRenamingT
import edu.cmu.cs.ls.keymaera.tactics.FormulaConverter._


/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
object AxiomaticRuleTactics {

  /**
   * Creates a new tactic for CE equivalence congruence rewriting.
   * @return The newly created tactic.
   */
  def equivalenceCongruenceT(inEqPos: PosInExpr): Tactic = new ConstructionTactic("CE congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ.head match {
        case Equiv(p, q) => p.extractContext(inEqPos)._1 == q.extractContext(inEqPos)._1
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Equiv(lhs, rhs) =>
        val (ctxP, p) = lhs.extractContext(inEqPos)
        val (ctxQ, q) = rhs.extractContext(inEqPos)
        assert(ctxP == ctxQ)

        if (ctxP.isFormulaContext) {
          val pX = ApplyPredicate(Function("p_", None, Real, Bool), Anything)
          val qX = ApplyPredicate(Function("q_", None, Real, Bool), Anything)
          val cX = ApplyPredicational(Function("ctx_", None, Bool, Bool), CDotFormula)
          val s = USubst(SubstitutionPair(pX, p) :: SubstitutionPair(qX, q) :: SubstitutionPair(cX, ctxP.ctx) :: Nil)
          Some(new ApplyRule(AxiomaticRule("CE congruence", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          })
        } else Some(NilT)
    }
  }

  /**
   * Creates a new tactic for CO one-sided congruence rewriting.
   * @return The newly created tactic.
   */
  def onesidedCongruenceT(inEqPos: PosInExpr): Tactic = new ConstructionTactic("CO one-sided congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.length == 1 && node.sequent.succ.length == 1 &&
      node.sequent.ante.head.extractContext(inEqPos)._1 == node.sequent.succ.head.extractContext(inEqPos)._1

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val lhs = node.sequent.ante.head
      val rhs = node.sequent.succ.head

      val (ctxP, p) = lhs.extractContext(inEqPos)
      val (ctxQ, q) = rhs.extractContext(inEqPos)
      assert(ctxP == ctxQ)

      if (ctxP.isFormulaContext) {
        val pX = ApplyPredicate(Function("p_", None, Real, Bool), Anything)
        val qX = ApplyPredicate(Function("q_", None, Real, Bool), Anything)
        val cX = ApplyPredicational(Function("ctx_", None, Bool, Bool), CDotFormula)
        val s = USubst(SubstitutionPair(pX, p) :: SubstitutionPair(qX, q) :: SubstitutionPair(cX, ctxP.ctx) :: Nil)
        Some(new ApplyRule(AxiomaticRule("CO one-sided congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
      } else Some(NilT)
    }
  }

  /**
   * Creates a new tactic for CQ equation congruence rewriting.
   * @return The newly created tactic.
   */
  def equationCongruenceT(inEqPos: PosInExpr): Tactic = new ConstructionTactic("CQ equation congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ.head match {
        case Equiv(p, q) => p.extractContext(inEqPos)._1 == q.extractContext(inEqPos)._1
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Equiv(lhs, rhs) =>
        val (ctxP, f) = lhs.extractContext(inEqPos)
        val (ctxQ, g) = rhs.extractContext(inEqPos)
        assert(ctxP == ctxQ)

        val fX = Apply(Function("f_", None, Real, Real), Anything)
        val gX = Apply(Function("g_", None, Real, Real), Anything)
        val cX = ApplyPredicate(Function("ctx_", None, Real, Bool), CDot)
        val s = USubst(SubstitutionPair(fX, f) :: SubstitutionPair(gX, g) :: SubstitutionPair(cX, ctxP.ctx) :: Nil)
        Some(new ApplyRule(AxiomaticRule("CQ equation congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }

  /**
   * Creates a new tactic for congruence rewriting.
   * @return The newly created tactic.
   */
  def congruenceT: Tactic =
    boxCongruenceT |
    diamondCongruenceT |
    forallCongruenceT |
    existsCongruenceT |
    equivCongruenceT |
    implyCongruenceT |
    andCongruenceT |
    orCongruenceT |
    notCongruenceT

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
        val aX = ProgramConstant("a_")
        val pX = Function("p_", None, Real, Bool)
        val qX = Function("q_", None, Real, Bool)
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
        val aX = ProgramConstant("a_")
        val pX = Function("p_", None, Real, Bool)
        val qX = Function("q_", None, Real, Bool)
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
          val aX = ProgramConstant("a_")
          val pX = Function("p_", None, Real, Bool)
          val qX = Function("q_", None, Real, Bool)
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
          val aX = ProgramConstant("a_")
          val pX = Function("p_", None, Real, Bool)
          val qX = Function("q_", None, Real, Bool)
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
        val aX = ProgramConstant("a_")
        val pX = Function("p_", None, Real, Bool)
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
        val pX = Function("p_", None, Real, Bool)
        val aX = Variable("x_", None, Real)
        val s = USubst(SubstitutionPair(ApplyPredicate(pX, CDot), replaceFree(replace(p)(x, aX))(aX, CDot)) :: Nil)

        Some(
          globalAlphaRenamingT(x.name, x.index, aX.name, aX.index) &
          new ApplyRule(AxiomaticRule("all generalization", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          } & globalAlphaRenamingT(aX.name, aX.index, x.name, x.index)
        )
    }
  }

  /**
   * Creates a new tactic for universal congruence. Expects a sequent with a sole formula in the succedent of the
   * form \forall x. p(x) <-> \forall x. q(x).
   * @return The newly created tactic.
   */
  def forallCongruenceT: Tactic = new ConstructionTactic("all congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Equiv(Forall(lvars, _), Forall(rvars, _)) => lvars == rvars
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Equiv(Forall(lvars, p), Forall(rvars, q)) if lvars == rvars =>
        assert(lvars.length == 1, "forall congruence only supported for one variable")
        val x = lvars(0) match {
          case v: Variable => v
          case _ => throw new UnsupportedOperationException("forall congruence only supported for variables")
        }
        val pX = ApplyPredicate(Function("p_", None, Real, Bool), CDot)
        val qX = ApplyPredicate(Function("q_", None, Real, Bool), CDot)

        val aX = Variable("x_", None, Real)
        val s = USubst(
          SubstitutionPair(pX, replaceFree(replace(p)(x, aX))(aX, CDot)) ::
          SubstitutionPair(qX, replaceFree(replace(q)(x, aX))(aX, CDot)) :: Nil)

        Some(
          globalAlphaRenamingT(x.name, x.index, aX.name, aX.index) &
          new ApplyRule(AxiomaticRule("all congruence", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          } & globalAlphaRenamingT(aX.name, aX.index, x.name, x.index)
        )
    }
  }

  /**
   * Creates a new tactic for existential congruence. Expects a sequent with a sole formula in the succedent of the
   * form \exists x. p(x) <-> \exists x. q(x).
   * @return The newly created tactic.
   */
  def existsCongruenceT: Tactic = new ConstructionTactic("exists congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Equiv(Exists(lvars, _), Exists(rvars, _)) => lvars == rvars
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Equiv(Exists(lvars, p), Exists(rvars, q)) if lvars == rvars =>
        assert(lvars.length == 1, "exists congruence only supported for one variable")
        val x = lvars(0) match {
          case v: Variable => v
          case _ => throw new UnsupportedOperationException("exists congruence only supported for variables")
        }
        val pX = ApplyPredicate(Function("p_", None, Real, Bool), CDot)
        val qX = ApplyPredicate(Function("q_", None, Real, Bool), CDot)
        val aX = Variable("x_", None, Real)
        val s = USubst(
          SubstitutionPair(pX, replaceFree(replace(p)(x, aX))(aX, CDot)) ::
          SubstitutionPair(qX, replaceFree(replace(q)(x, aX))(aX, CDot)) :: Nil)

        Some(
          globalAlphaRenamingT(x.name, x.index, aX.name, aX.index) &
          new ApplyRule(AxiomaticRule("exists congruence", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          } & globalAlphaRenamingT(aX.name, aX.index, x.name, x.index)
        )
    }
  }

  /**
   * Creates a new tactic for ! congruence. Expects a sequent with a sole formula in the succedent of the
   * form !p <-> !q.
   * @return The newly created tactic.
   */
  def notCongruenceT: Tactic = new ConstructionTactic("! congruence") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Equiv(Not(_), Not(_)) => true
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Equiv(Not(p), Not(q)) =>
        val pX = ApplyPredicate(Function("p_", None, Real, Bool), Anything)
        val qX = ApplyPredicate(Function("q_", None, Real, Bool), Anything)
        val s = USubst(SubstitutionPair(pX, p) :: SubstitutionPair(qX, q) :: Nil)
        Some(new ApplyRule(AxiomaticRule("! congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }

  /**
   * Creates a new tactic for -> congruence. Expects a sequent with a sole formula in the succedent of the
   * form (F -> p) <-> (F -> q).
   * @return The newly created tactic.
   */
  def implyCongruenceT: Tactic = binaryPropositionalCongruenceT("-> congruence", Imply.unapply)

  /**
   * Creates a new tactic for <-> congruence. Expects a sequent with a sole formula in the succedent of the
   * form (F <-> p) <-> (F <-> q).
   * @return The newly created tactic.
   */
  def equivCongruenceT: Tactic = binaryPropositionalCongruenceT("<-> congruence", Equiv.unapply)

  /**
   * Creates a new tactic for & congruence. Expects a sequent with a sole formula in the succedent of the
   * form (F & p) <-> (F & q).
   * @return The newly created tactic.
   */
  def andCongruenceT: Tactic = binaryPropositionalCongruenceT("& congruence", And.unapply)

  /**
   * Creates a new tactic for | congruence. Expects a sequent with a sole formula in the succedent of the
   * form (F | p) <-> (F | q).
   * @return The newly created tactic.
   */
  def orCongruenceT: Tactic = binaryPropositionalCongruenceT("| congruence", Or.unapply)

  private class BinaryRelationUnapplyer[T: Manifest](unapply: T => Option[(Formula, Formula)]) {
    def unapply(a: Any): Option[(Formula, Formula)] = {
      if (manifest[T].runtimeClass.isInstance(a)) unapply(a.asInstanceOf[T]) else None
    }
  }

  /**
   * Creates a new tactic for propositional congruence. Expects a sequent with a sole formula in the succedent of the
   * form (F ~ p) <-> (F ~ q). Basis for concrete binary propositional congruence tactics.
   * @param ruleName The name of the propositional axiomatic rule.
   * @param rel The unapply method of the relation.
   * @return The newly created tactic.
   */
  private def binaryPropositionalCongruenceT[T: Manifest](ruleName: String, rel: T => Option[(Formula, Formula)]): Tactic =
      new ConstructionTactic(ruleName) { outer =>
    val BinRel = new BinaryRelationUnapplyer(rel)
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ(0) match {
        case Equiv(BinRel(lf, _), BinRel(rf, _)) => lf == rf
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ(0) match {
      case Equiv(BinRel(lf, p), BinRel(rf, q)) if lf == rf =>
        val fX = ApplyPredicate(Function("F_", None, Real, Bool), Anything)
        val pX = ApplyPredicate(Function("p_", None, Real, Bool), Anything)
        val qX = ApplyPredicate(Function("q_", None, Real, Bool), Anything)
        val s = USubst(SubstitutionPair(fX, lf) :: SubstitutionPair(pX, p) :: SubstitutionPair(qX, q) :: Nil)
        Some(new ApplyRule(AxiomaticRule(ruleName, s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }
}
