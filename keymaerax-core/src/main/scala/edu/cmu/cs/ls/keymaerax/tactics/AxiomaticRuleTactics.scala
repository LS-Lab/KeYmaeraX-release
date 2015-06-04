package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.AlphaConversionHelper.replace
import edu.cmu.cs.ls.keymaerax.tactics.SubstitutionHelper.replaceFree
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ApplyRule, ConstructionTactic, Tactic, NilT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.globalAlphaRenamingT
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tools.Tool


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
          val pX = PredOf(Function("p_", None, Real, Bool), Anything)
          val qX = PredOf(Function("q_", None, Real, Bool), Anything)
          val cX = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)
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
        val pX = PredOf(Function("p_", None, Real, Bool), Anything)
        val qX = PredOf(Function("q_", None, Real, Bool), Anything)
        val cX = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)
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

        val fX = FuncOf(Function("f_", None, Real, Real), Anything)
        val gX = FuncOf(Function("g_", None, Real, Real), Anything)
        val cX = PredOf(Function("ctx_", None, Real, Bool), DotTerm)
        val s = USubst(SubstitutionPair(fX, f) :: SubstitutionPair(gX, g) :: SubstitutionPair(cX, ctxP.ctx) :: Nil)
        Some(new ApplyRule(AxiomaticRule("CQ equation congruence", s)) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }

  /**
   * Creates a new tactic for box monotone. Expects a sequent with a sole formula in the antecedent of the form [a]p
   * and a sole formula in the succedent of the form [a]q.
   * @return The newly created tactic.
   */
  def boxMonotoneT: Tactic = new ConstructionTactic("[] monotone") { outer =>
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.length == 1 && node.sequent.succ.length == 1 &&
      (node.sequent.ante.head match {
        case Box(a, _) => node.sequent.succ.head match {
          case Box(b, _) => a == b
          case _ => false
        }
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.ante.head match {
      case Box(a, p) => node.sequent.succ.head match {
        case Box(b, q) =>
          val aX = ProgramConst("a_")
          val pX = Function("p_", None, Real, Bool)
          val qX = Function("q_", None, Real, Bool)
          val s = USubst(SubstitutionPair(aX, a) ::
            SubstitutionPair(PredOf(pX, Anything), p) ::
            SubstitutionPair(PredOf(qX, Anything), q) :: Nil)
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
      (node.sequent.ante.head match {
        case Diamond(a, _) => node.sequent.succ.head match {
          case Diamond(b, _) => a == b
          case _ => false
        }
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.ante.head match {
      case Diamond(a, p) => node.sequent.succ.head match {
        case Diamond(b, q) =>
          val aX = ProgramConst("a_")
          val pX = Function("p_", None, Real, Bool)
          val qX = Function("q_", None, Real, Bool)
          val s = USubst(SubstitutionPair(aX, a) ::
            SubstitutionPair(PredOf(pX, Anything), p) ::
            SubstitutionPair(PredOf(qX, Anything), q) :: Nil)
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
      (node.sequent.succ.head match {
          case Box(_, _) => true
          case _ => false
        })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Box(a, p) =>
        val aX = ProgramConst("a_")
        val pX = Function("p_", None, Real, Bool)
        val s = USubst(SubstitutionPair(aX, a) ::
          SubstitutionPair(PredOf(pX, Anything), p) :: Nil)
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
      (node.sequent.succ.head match {
        case Forall(vars, _) => vars.length == 1
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Forall(vars, p) =>
        assert(vars.length == 1, "forall generalization only supported for one variable")
        val x = vars.head match {
          case v: Variable => v
          case _ => throw new UnsupportedOperationException("forall generalization only supported for variables")
        }
        val pX = Function("p_", None, Real, Bool)
        val aX = Variable("x_", None, Real)
        val s = USubst(SubstitutionPair(PredOf(pX, Anything), replace(p)(x, aX)) :: Nil)

        Some(
          globalAlphaRenamingT(x.name, x.index, aX.name, aX.index) &
          new ApplyRule(AxiomaticRule("all generalization", s)) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          } /* TODO this step will not work, since aX not bound anymore */& globalAlphaRenamingT(aX.name, aX.index, x.name, x.index)
        )
    }
  }
}
