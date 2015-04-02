package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import NNFRewrite.rewriteDoubleNegationEliminationT
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics.boxMonotoneT
import edu.cmu.cs.ls.keymaera.tactics.AxiomTactic.{uncoverAxiomT, axiomLookupBaseT}
import edu.cmu.cs.ls.keymaera.tactics.ContextTactics.cutEquivInContext
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.{AndRightT,AxiomCloseT,ImplyLeftT,ImplyRightT,cutT,
  hideT,kModalModusPonensT}
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import BindingAssessment.allNames

import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import TacticHelper.getFormula
import SearchTacticsImpl.onBranch

import scala.collection.immutable.{List, Seq}

import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper._

/**
 * Implementation of tactics for handling hybrid programs.
 */
object HybridProgramTacticsImpl {
  private class ModalityUnapplyer[T: Manifest](m: T => Option[(Program, Formula)]) {
    def unapply(a: Any): Option[(Program, Formula)] = {
      if (manifest[T].runtimeClass.isInstance(a)) m(a.asInstanceOf[T]) else None
    }
  }

  /*********************************************
   * Axiom Tactics
   *********************************************/

  class ByDualityAxiomTactic(base: PositionTactic) extends PositionTactic(base.name) {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case DiamondModality(prg, phi) => base.applies(s.updated(p, BoxModality(prg, Not(phi))), p)
      case BoxModality(prg, phi) => base.applies(s.updated(p, DiamondModality(prg, Not(phi))), p)
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      def applicable(node : ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case DiamondModality(prg, phi) =>
          Some(diamondDualityT(p) & base(p.first) & boxDualityT(p.first) & rewriteDoubleNegationEliminationT(p))
        case BoxModality(prg, phi) =>
          Some(boxDualityT(p) & base(p.first) & diamondDualityT(p.first) & rewriteDoubleNegationEliminationT(p))
        case _ => None
      }
    }
  }

  def boxDualityT: PositionTactic = {
    def g(f: Formula): Formula = f match {
      case BoxModality(prg, phi) => Equiv(f, Not(DiamondModality(prg, Not(phi))))
      case Not(DiamondModality(prg, Not(phi))) => Equiv(BoxModality(prg, phi), f)
      case _ => False
    }

    uncoverAxiomT("[] dual", g, _ => boxDualityBaseT)
  }
  /* Base tactic for boxDualityT */
  private def boxDualityBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BoxModality(prg, phi), _) =>
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, prg) :: SubstitutionPair(aP, phi) :: Nil
      case Equiv(Not(DiamondModality(prg, Not(phi))), _) =>
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, prg) :: SubstitutionPair(aP, phi) :: Nil
    }

    axiomLookupBaseT("[] dual", subst, _ => NilPT, (f, ax) => ax)
  }

  def boxSeqGenT(q: Formula): PositionTactic = new PositionTactic("[;] generalize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case BoxModality(Sequence(_, _), _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case BoxModality(Sequence(a, b), phi) =>
          Some(boxSeqT(p) & cutT(Some(BoxModality(a, q))) & onBranch(
            // boxSeqT will move its result into last succ, cut later moves one behind
            (cutShowLbl, hideT(SuccPosition(node.sequent.succ.length - 1))),
            (cutUseLbl,
              // cut shows up at last ante
              (0 until node.sequent.ante.length).foldRight(NilT)((i, t) => t & hideT(AntePosition(i))) &
              // boxSeqT will move programs into last succ
              (0 until node.sequent.succ.length - 1).foldRight(NilT)((i, t) => t & hideT(SuccPosition(i))) &
              boxMonotoneT
              )
          ))
      }
    }
  }

  def diamondDualityT: PositionTactic = {
    def g(f: Formula): Formula = f match {
      case DiamondModality(prg, phi) => Equiv(f, Not(BoxModality(prg, Not(phi))))
      case Not(BoxModality(prg, Not(phi))) => Equiv(DiamondModality(prg, phi), f)
      case _ => False
    }

    uncoverAxiomT("<> dual", g, _ => diamondDualityBaseT)
  }
  /* Base tactic for diamondDualityT */
  private def diamondDualityBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(DiamondModality(prg, phi), _) =>
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, prg) :: SubstitutionPair(aP, phi) :: Nil
      case Equiv(Not(BoxModality(prg, Not(phi))), _) =>
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, prg) :: SubstitutionPair(aP, phi) :: Nil
    }

    axiomLookupBaseT("<> dual", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for differential box assignment [x := t;].
   *  [v':=t;]p(v') <-> p(t)
   * @author Nathan Fulton
   * @author Stefan Mitsch
   * @return The axiom tactic.
   *
   */
  def boxDerivativeAssignT: PositionTactic = {
    def g(f: Formula): Formula = f match {
      case BoxModality(Assign(d@Derivative(_, _: Variable), t), p) =>
        Equiv(f, SubstitutionHelper.replaceFree(p)(d, t))
      case _ => False
    }

    uncoverAxiomT("[':=] differential assign", g, f => boxDerivativeAssignBaseT)
  }
  /** Base tactic for box derivative assignment */
  private def boxDerivativeAssignBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BoxModality(Assign(d@Derivative(vSort, v:Variable), t), p), _) =>
        val aT = Apply(Function("t", None, Unit, vSort), Nothing)
        val aP = ApplyPredicate(Function("p", None, vSort, Bool), CDot) //(p(t)
        SubstitutionPair(aT, t) :: SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(d, CDot)) :: Nil
    }

    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(BoxModality(Assign(d@Derivative(vSort, v:Variable), t), p), _) =>
        val aV = Variable("v", None, vSort)
        if (v.name != aV.name || v.index != aV.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Equiv(BoxModality(Assign(Derivative(_), _), _), _) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(v.name, v.index, aV.name, aV.index))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(BoxModality(Assign(d@Derivative(vSort, v:Variable), t), p), _) =>
        val aV = Variable("v", None, vSort)
        if (v.name == aV.name && v.index == aV.index) axiom
        else replace(axiom)(aV, v)
    }

    axiomLookupBaseT("[':=] differential assign", subst, alpha, axiomInstance)
  }

  /**
   * Creates a new axiom tactic for box assignment [x := t;]. Uses the box assignment tactic most appropriate
   * for the specific position.
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  def boxAssignT: PositionTactic = boxAssignT(FOQuantifierTacticsImpl.skolemizeT)
  def boxAssignT(skolemizeHow: Boolean => PositionTactic): PositionTactic =
      new PositionTactic("[:=] assign equational") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case BoxModality(Assign(Variable(_, _, _), _), _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def assignEqualMandatory(v: Variable, t: Term, rest: Formula) = allNames(t).contains(v) || (rest match {
        case BoxModality(_: DifferentialProgram, _) => true
        case BoxModality(_: Loop, _) => true
        case _ => /* false requires substitution of variables */ true
      })

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case BoxModality(Assign(v: Variable, t: Term), phi) if assignEqualMandatory(v, t, phi) =>
          if (p.isAnte) Some(boxAssignEqualT(p))
          else Some(boxAssignEqualT(p) & skolemizeHow(true)(p) & ImplyRightT(p) & (v2vAssignT(p) | NilT))
        case BoxModality(Assign(v: Variable, t: Term), phi) if !assignEqualMandatory(v, t, phi) =>
          Some(substitutionBoxAssignT(p))
        }
      }
  }


  /**
   * Creates a new axiom tactic for box assignment equational [x := t;].
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  def boxAssignEqualT: PositionTactic = new PositionTactic("[:=] assign equational") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case BoxModality(Assign(Variable(_, _,_), _), _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps

        val f = node.sequent(p)
        // construct a new name for the quantified variable
        val (newV1, newV2) = f match {
          case BoxModality(Assign(v: Variable, _), _) =>
            val tIdx = TacticHelper.freshIndexInFormula(v.name, f)
            (Variable(v.name, tIdx, v.sort), Variable(v.name, Some(tIdx.get + 1), v.sort))
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        node.sequent(p) match {
          case BoxModality(Assign(v: Variable, _), BoxModality(prg: Loop, _))
            if allNames(prg).contains(v) && !NameCategorizer.freeVariables(prg).contains(v) => Some(
            alphaRenamingT(v.name, v.index, newV1.name, newV1.index)(p.second) &
              boxAssignWithoutAlphaT(newV2, checkNewV = false)(p)
          )
          case BoxModality(Assign(v: Variable, _), BoxModality(prg: DifferentialProgram, _))
            if allNames(prg).contains(v) && !NameCategorizer.freeVariables(prg).contains(v) => Some(
            alphaRenamingT(v.name, v.index, newV1.name, newV1.index)(p.second) &
              boxAssignWithoutAlphaT(newV2, checkNewV = false)(p)
          )
          case _ => Some(boxAssignWithoutAlphaT(newV1)(p))
        }
      }
    }
  }

  /**
   * Creates a new axiom tactic for box assignment [x := t;]. Helper for boxAssignEqualT
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  private def boxAssignWithoutAlphaT(newV: Variable, checkNewV: Boolean = true): PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case BoxModality(Assign(v: Variable, t), p) if !checkNewV || !allNames(fml).contains(newV) =>
        val g = Forall(Seq(newV), Imply(Equals(Real, newV, t), SubstitutionHelper.replaceFree(p)(v, newV)))
        Equiv(fml, g)
      case _ => False
    }
    uncoverAxiomT("[:=] assign equational", axiomInstance, f => boxAssignWithoutAlphaBaseT(newV))
  }
  /** Base tactic for box assign without alpha */
  private def boxAssignWithoutAlphaBaseT(newV: Variable): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BoxModality(Assign(v: Variable, t), p), _) =>
        val aT = Apply(Function("t", None, Unit, Real), Nothing)
        val aP = Function("p", None, Real, Bool)
        SubstitutionPair(aT, t) :: SubstitutionPair(ApplyPredicate(aP, CDot), SubstitutionHelper.replaceFree(p)(v, CDot)) :: Nil
    }

    val aV = Variable("v", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(BoxModality(Assign(v: Variable, t), p), _) =>
        val left = v.name != aV.name || v.index != aV.index
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(Assign(_, _), _), Forall(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              if(left)
                Some(globalAlphaRenamingT(v.name, v.index, aV.name, aV.index)
                  & alphaRenamingT(newV.name, newV.index, aV.name, aV.index)(p.second))
              else
                Some(alphaRenamingT(newV.name, newV.index, aV.name, aV.index)(p.second))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(BoxModality(Assign(v: Variable, t), p), _) =>
        val Equiv(left, right) = axiom
        if (v.name == aV.name && v.index == aV.index) Equiv(left, replaceFree(right)(aV, newV))
        else Equiv(replaceFree(left)(aV, v, None), replaceFree(right)(aV, newV))
    }

    axiomLookupBaseT("[:=] assign equational", subst, alpha, axiomInstance)
  }

  /**
   * Creates a new axiom tactic for reversing box assignment [v := t;], i.e., introduces a ghost v for term t
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  def discreteGhostT(ghost: Option[Variable], t: Term): PositionTactic = {
    // check specified name, or construct a new name for the ghost variable if None
    def ghostV(f: Formula): Variable = ghost match {
      case Some(gv) => require(gv == t || (!allNames(f).contains(gv))); gv
      case None => t match {
        case v: Variable => TacticHelper.freshNamedSymbol(v, f)
        case _ => throw new IllegalArgumentException("Only variables allowed when ghost name should be auto-provided")
      }
    }

    def g(f: Formula) = Equiv(BoxModality(Assign(ghostV(f), t), SubstitutionHelper.replaceFree(f)(t, ghostV(f))), f)

    uncoverAxiomT("[:=] assign", g, f => discreteGhostBaseT(ghostV(f), t))
  }
  /** Base tactic for discrete ghost. */
  private def discreteGhostBaseT(v: Variable, t: Term): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(g, f) =>
        val aT = Apply(Function("t", None, Unit, Real), Nothing)
        val aP = Function("p", None, Real, Bool)
        SubstitutionPair(aT, t) :: SubstitutionPair(ApplyPredicate(aP, CDot), SubstitutionHelper.replaceFree(f)(t, CDot)) :: Nil
    }

    def alpha(fml: Formula): PositionTactic = {
      val aV = Variable("v", None, Real)
      if (v.name != aV.name || v.index != aV.index) {
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(Assign(_, _), _), _) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(v.name, v.index, aV.name, aV.index))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
      } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Equiv(left, right) = axiom
      val aV = Variable("v", None, Real)
      Equiv(replace(left)(aV, v), right)
    }

    axiomLookupBaseT("[:=] assign", subst, alpha, axiomInstance)
  }

  /**
   * Creates a new axiom tactic for reversing box assignment [v := t;], i.e., introduces a ghost v for term t
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  def nonAbbrvDiscreteGhostT(ghost: Option[Variable], t: Term): PositionTactic = {
    def ghostV(f: Formula): Variable = ghost match {
      case Some(gv) => require(gv == t || (!allNames(f).contains(gv))); gv
      case None => t match {
        case v: Variable => TacticHelper.freshNamedSymbol(v, f)
        case _ => throw new IllegalArgumentException("Only variables allowed when ghost name should be auto-provided")
      }
    }

    def g(f: Formula) = Equiv(BoxModality(Assign(ghostV(f), t), f), f)

    uncoverAxiomT("[:=] vacuous assign", g, f => nonAbbrvDiscreteGhostBaseT(ghostV(f), t))
  }
  /** Base tactic for nonAbbrvDiscreteGhost */
  private def nonAbbrvDiscreteGhostBaseT(v: Variable, t: Term): PositionTactic = {
    def subst(fml: Formula) = fml match {
      case Equiv(g, f) =>
        val aT = Apply(Function("t", None, Unit, Real), Nothing)
        val aP = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
        SubstitutionPair(aT, t) :: SubstitutionPair(aP, f) :: Nil
    }

    val aV = Variable("v", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      if (v.name != aV.name || v.index != aV.index) {
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(Assign(_, _), _), _) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(v.name, v.index, aV.name, aV.index))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
      } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Equiv(left, right) = axiom
      Equiv(replace(left)(aV, v), right)
    }

    axiomLookupBaseT("[:=] vacuous assign", subst, alpha, axiomInstance)
  }

  /**
   * Creates a new position tactic for box assignment [x := t;], for the case when followed by ODE or loop.
   * Alpha renaming in ODEs and loops introduces initial value assignments. This tactic is designed to handle those.
   * @return The tactic.
   * @author Stefan Mitsch
   */
  def v2vAssignT: PositionTactic = new PositionTactic("[:=]/<:=> assign") {
    import NameCategorizer.freeVariables
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case BoxModality(Assign(_: Variable, v: Variable), pred) => checkNested(pred, v)
      case DiamondModality(Assign(_: Variable, v: Variable), pred) => checkNested(pred, v)
      case _ => false
    }

    private def checkNested(f: Formula, v: Variable) = f match {
      case BoxModality(_: DifferentialProgram, _) => !freeVariables(f).contains(v)
      case BoxModality(_: Loop, _) => !freeVariables(f).contains(v)
      case DiamondModality(_: DifferentialProgram, _) => !freeVariables(f).contains(v)
      case DiamondModality(_: Loop, _) => !freeVariables(f).contains(v)
      // prevent application on anything else. otherwise, assignT has the surprising effect of handling multiple
      // assignments at once
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps
        import SearchTacticsImpl.onBranch
        import BranchLabels.cutShowLbl
        import PropositionalTacticsImpl.EquivRightT

        val succLength = node.sequent.succ.length
        val anteLength = node.sequent.ante.length

        def createTactic(m: Formula, pred: Formula, v: Variable, t: Variable) = Some(
          cutEquivInContext(Equiv(m, replace(pred)(v, t)), p) &
            onBranch(
              (cutShowLbl,
                // TODO does not work in mixed settings such as <x:=t>[x'=2] and [x:=t]<x'=2>
                PropositionalTacticsImpl.cohideT(SuccPosition(succLength)) & assertT(0, 1) &
                alphaRenamingT(t.name, t.index, v.name, v.index)(SuccPosition(0, PosInExpr(1 :: p.inExpr.pos))) &
                  EquivRightT(SuccPosition(0)) & (AxiomCloseT | debugT("v2vAssign: Axiom close failed unexpectedly") & stopT)),
              (cutUseLbl, equivRewriting(AntePosition(anteLength), p.topLevel))
            )
        )

        getFormula(node.sequent, p) match {
          case b@BoxModality(Assign(v: Variable, t: Variable), pred) => createTactic(b, pred, v, t)
          case d@DiamondModality(Assign(v: Variable, t: Variable), pred) => createTactic(d, pred, v, t)
        }
      }
    }
  }

  /**
   * Creates a new tactic for box assignment [x := t;] when x == t.
   * @return The tactic.
   * @author Stefan Mitsch
   */
  def selfAssignmentT: PositionTactic = new PositionTactic("[:=] self-assign") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case BoxModality(Assign(v: Variable, t: Variable), _) => v == t
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
          case b@BoxModality(Assign(v: Variable, t: Variable), _) if v == t => Some(
            abstractionT(p) & skolemizeT(p))
          case _ => throw new IllegalArgumentException("Checked by applicable to not happen")
      }
    }
  }

  /**
   * Creates a new axiom tactic for box assignment [x := t;]
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  def substitutionBoxAssignT = substitutionAssignT("[:=] assign", BoxModality.unapply)

  /**
   * Creates a new axiom tactic for box assignment [x := t;]
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  def substitutionDiamondAssignT = substitutionAssignT("<:=> assign", DiamondModality.unapply)

  /**
   * Creates a new axiom tactic for box/diamond assignment [x := t;], < x := t;>.
   * @return The axiom tactic.
   * @author Stefan Mitsch
   */
  private def substitutionAssignT[T: Manifest](name: String, mod: T => Option[(Program, Formula)]): PositionTactic = {
    val BDModality = new ModalityUnapplyer(mod)

    def axiomInstance(fml: Formula) = fml match {
      case BDModality(Assign(v: Variable, t: Term), pred) =>
        val g = SubstitutionHelper.replaceFree(pred)(v, t)
        val instance = Equiv(fml, g)
        pred match {
          // loop and ODE are probably a little too strict here, but we have v2vBoxAssignT to handle those
          case BoxModality(_: DifferentialProgram, _) => t match {
            case tv: Variable if v == tv => instance
            case _ => False
          }
          case BoxModality(_: Loop, _) => t match {
            case tv: Variable if v == tv => instance
            case _ => False
          }
          case DiamondModality(_: DifferentialProgram, _) => t match {
            case tv: Variable if v == tv => instance
            case _ => False
          }
          case DiamondModality(_: Loop, _) => t match {
            case tv: Variable if v == tv => instance
            case _ => False
          }
          case _ => instance
        }
      case _ => False
    }

    uncoverAxiomT(name, axiomInstance, f => substitutionAssignBaseT(name, mod))
  }
  /** Base tactic for substitution assignment */
  private def substitutionAssignBaseT[T: Manifest](name: String, mod: T => Option[(Program, Formula)]): PositionTactic = {
    val BDModality = new ModalityUnapplyer(mod)

    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BDModality(Assign(v: Variable, t: Term), p), _) =>
        val aT = Apply(Function("t", None, Unit, Real), Nothing)
        val aP = Function("p", None, Real, Bool)
        SubstitutionPair(aT, t) :: SubstitutionPair(ApplyPredicate(aP, CDot), SubstitutionHelper.replaceFree(p)(v, CDot)) :: Nil
    }

    val aV = Variable("v", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(BDModality(Assign(v: Variable, _: Term), _), _) =>
        if (v.name != aV.name || v.index != aV.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Equiv(BDModality(Assign(_, _), _), _) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(alphaRenamingT(v.name, v.index, aV.name, aV.index)(p) ~
                  globalAlphaRenamingT(v.name, v.index, aV.name, aV.index))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(BDModality(Assign(v: Variable, _: Term), _), _) =>
        val Equiv(lhs, rhs) = axiom
        Equiv(if (v.name != aV.name || v.index != None) replace(lhs)(aV, v) else lhs, rhs)
    }

    axiomLookupBaseT(name, subst, alpha, axiomInstance)
  }

  /**
   * Creates a new axiom tactic for V vacuous.
   * @return The new tactic.
   */
  def boxVacuousT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case BoxModality(prg, phi) => Imply(phi, fml)
      case _ => False
    }
    uncoverAxiomT("V vacuous", axiomInstance, _ => boxVacuousBaseT)
  }
  /** Base tactic for box vacuous */
  private def boxVacuousBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(_, BoxModality(prg, phi)) =>
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
        SubstitutionPair(aA, prg) :: SubstitutionPair(aP, phi) :: Nil
    }
    axiomLookupBaseT("V vacuous", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for test [?H].
   * @return The new tactic.
   */
  def boxTestT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case BoxModality(Test(h), p) => Equiv(fml, Imply(h, p))
    }
    uncoverAxiomT("[?] test", axiomInstance, _ => boxTestBaseT)
  }
  /** Base tactic for boxTestT */
  private def boxTestBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BoxModality(Test(h), p), _) =>
        // construct substitution
        val aH = ApplyPredicate(Function("H", None, Unit, Bool), Nothing)
        val aP = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
        SubstitutionPair(aH, h) :: SubstitutionPair(aP, p) :: Nil
    }
    axiomLookupBaseT("[?] test", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for diamond test.
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  def diamondTestT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case DiamondModality(Test(h), p) => Equiv(fml, And(h, p))
    }
    uncoverAxiomT("<?> test", axiomInstance, _ => diamondTestBaseT)
  }
  /** Base tactic for diamondTestT */
  private def diamondTestBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(DiamondModality(Test(h), p), _) =>
        // construct substitution
        val aH = ApplyPredicate(Function("H", None, Unit, Bool), Nothing)
        val aP = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
        SubstitutionPair(aH, h) :: SubstitutionPair(aP, p) :: Nil
    }
    axiomLookupBaseT("<?> test", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for non-deterministic assignment [x := *].
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  def boxNDetAssign: PositionTactic = new PositionTactic("[:=] assign equational") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case BoxModality(NDetAssign(v: Variable), _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val f = node.sequent(p)
        // construct a new name for renaming in ODE
        val newV = f match {
          case BoxModality(NDetAssign(v: Variable), _) => TacticHelper.freshNamedSymbol(v, f)
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        node.sequent(p) match {
          case BoxModality(NDetAssign(v: Variable), BoxModality(prg: Loop, _))
            if BindingAssessment.catVars(prg).bv.contains(v) => Some(
            alphaRenamingT(v.name, v.index, newV.name, newV.index)(p.second) &
              boxNDetAssignWithoutAlphaT(p) & skolemizeT(p) & v2vAssignT(p)
          )
          case BoxModality(NDetAssign(v: Variable), BoxModality(prg: DifferentialProgram, _))
            if BindingAssessment.catVars(prg).bv.contains(v) => Some(
            alphaRenamingT(v.name, v.index, newV.name, newV.index)(p.second) &
              boxNDetAssignWithoutAlphaT(p) & skolemizeT(p) & v2vAssignT(p)
          )
          case _ => Some(boxNDetAssignWithoutAlphaT(p) & skolemizeT(p))
        }
      }
    }
  }

  /**
   * Creates a new axiom tactic for non-deterministic assignment [x := *]. Helper for boxNDetAssign.
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  private def boxNDetAssignWithoutAlphaT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: [v:=*]p(v) <-> \forall v. p(v).
      case BoxModality(NDetAssign(v: Variable), p) => Equiv(fml, Forall(Seq(v), p))
      case _ => False
    }
    uncoverAxiomT("[:*] assign nondet", axiomInstance, _ => boxNDetAssignWithoutAlphaBaseT)
  }
  /** Base tactic for box nondeterministic assignment without alpha renaming */
  private def boxNDetAssignWithoutAlphaBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BoxModality(NDetAssign(v: Variable), p), _) =>
        val aP = Function("p", None, Real, Bool)
        SubstitutionPair(ApplyPredicate(aP, CDot), SubstitutionHelper.replaceFree(p)(v, CDot)) :: Nil
    }

    val aV = Variable("v", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(BoxModality(NDetAssign(v: Variable), p), _) =>
        if (v.name != aV.name || v.index != aV.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Equiv(BoxModality(NDetAssign(_), _), Forall(_, _)) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(v.name, v.index, aV.name, aV.index))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(BoxModality(NDetAssign(v: Variable), p), _) =>
        if (v.name != aV.name || v.index != None) replaceFree(axiom)(aV, v, None)
        else axiom
    }

    axiomLookupBaseT("[:*] assign nondet", subst, alpha, axiomInstance)
  }

  /**
   * Creates a new axiom tactic for non-deterministic assignment < x := *>.
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  def diamondNDetAssign: PositionTactic = new PositionTactic("<:=> assign nondet") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case DiamondModality(NDetAssign(v: Variable), _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps
        import FOQuantifierTacticsImpl.skolemizeT

        val f = getFormula(node.sequent, p)
        // construct a new name for renaming in ODE
        val newV = f match {
          case DiamondModality(NDetAssign(v: Variable), _) => TacticHelper.freshNamedSymbol(v, f)
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        f match {
          case DiamondModality(NDetAssign(v: Variable), DiamondModality(prg: Loop, _))
            if BindingAssessment.catVars(prg).bv.contains(v) => Some(
            alphaRenamingT(v.name, v.index, newV.name, newV.index)(p.second) &
              diamondNDetAssignWithoutAlphaT(p)
          )
          case DiamondModality(NDetAssign(v: Variable), DiamondModality(prg: DifferentialProgram, _))
            if BindingAssessment.catVars(prg).bv.contains(v) => Some(
            alphaRenamingT(v.name, v.index, newV.name, newV.index)(p.second) &
              diamondNDetAssignWithoutAlphaT(p)
          )
          case _ => Some(diamondNDetAssignWithoutAlphaT(p))
        }
      }
    }
  }

  /**
   * Creates a new axiom tactic for non-deterministic assignment < x := *>. Helper for diamondNDetAssign.
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  private def diamondNDetAssignWithoutAlphaT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: <v:=*>p(v) <-> \exists v. p(v).
      case DiamondModality(NDetAssign(v: Variable), p) => Equiv(fml, Exists(Seq(v), p))
      case _ => False
    }
    uncoverAxiomT("<:*> assign nondet", axiomInstance, _ => diamondNDetAssignWithoutAlphaBaseT)
  }
  /** Base tactic for diamond nondeterministic assignment without alpha renaming */
  private def diamondNDetAssignWithoutAlphaBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(DiamondModality(NDetAssign(v: Variable), p), _) =>
        val aP = Function("p", None, Real, Bool)
        SubstitutionPair(ApplyPredicate(aP, CDot), SubstitutionHelper.replaceFree(p)(v, CDot)) :: Nil
    }

    val aV = Variable("v", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(DiamondModality(NDetAssign(v: Variable), p), _) =>
        if (v.name != aV.name || v.index != aV.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Equiv(DiamondModality(NDetAssign(_), _), Exists(_, _)) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(v.name, v.index, aV.name, aV.index))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(DiamondModality(NDetAssign(v: Variable), p), _) =>
        if (v.name != aV.name || v.index != None) replaceFree(axiom)(aV, v, None)
        else axiom
    }

    axiomLookupBaseT("<:*> assign nondet", subst, alpha, axiomInstance)
  }

  /**
   * Creates a new axiom tactic for sequential composition [;]
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  def boxSeqT = seqT("[;] compose", BoxModality.unapply, BoxModality.apply)

  /**
   * Creates a new axiom tactic for diamond sequential composition <;>
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  def diamondSeqT = seqT("<;> compose", DiamondModality.unapply, DiamondModality.apply)

  /**
   * Creates a new axiom tactic for box/diamond sequential composition
   * @param name The name of the axiom.
   * @param mod The unapply method of the concrete modality.
   * @param factory The apply method of the concrete modality.
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  private def seqT[T: Manifest](name: String, mod: T => Option[(Program, Formula)],
                                factory: (Program, Formula) => Formula): PositionTactic = {
    val BDModality = new ModalityUnapplyer(mod)

    def axiomInstance(fml: Formula): Formula = fml match {
      case BDModality(Sequence(a, b), p) => Equiv(fml, factory(a, factory(b, p)))
      case _ => False
    }
    uncoverAxiomT(name, axiomInstance, _ => seqBaseT(name, mod))
  }
  /** Base tactic for seqT */
  private def seqBaseT[T: Manifest](name: String, mod: T => Option[(Program, Formula)]): PositionTactic = {
    val BDModality = new ModalityUnapplyer(mod)

    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BDModality(Sequence(a, b), p), _) =>
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, a) :: SubstitutionPair(aB, b) :: SubstitutionPair(aP, p) :: Nil
    }
    axiomLookupBaseT(name, subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for box induction [*] I induction
   * @return The new tactic.
   */
  def boxInductionT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: (p & [a*](p -> [a] p)) -> [a*]p
      case BoxModality(Loop(a), p) => Imply(And(p, BoxModality(Loop(a), Imply(p, BoxModality(a, p)))), fml)
      case _ => False
    }
    uncoverAxiomT("I induction", axiomInstance, _ => boxInductionBaseT)
  }
  /** Base tactic for box induction */
  private def boxInductionBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(And(p, BoxModality(Loop(a), Imply(_, BoxModality(_, _)))), _) =>
        val aA = ProgramConstant("a")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, a) :: SubstitutionPair(aP, p) :: Nil
    }

    axiomLookupBaseT("I induction", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for box choice [++].
   * @return The new tactic.
   */
  def boxChoiceT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: [ a ++ b ]p <-> [a]p & [b]p.
      case BoxModality(Choice(a, b), p) => Equiv(fml, And(BoxModality(a, p), BoxModality(b, p)))
      case _ => False
    }
    uncoverAxiomT("[++] choice", axiomInstance, _ => boxChoiceBaseT)
  }
  /** Base tactic for box choice */
  private def boxChoiceBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(BoxModality(Choice(a, b), p), _) =>
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, a) :: SubstitutionPair(aB, b) :: SubstitutionPair(aP, p) :: Nil
    }
    axiomLookupBaseT("[++] choice", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for diamond choice <++>.
   * @return The new tactic.
   * @author Stefan Mitsch
   */
  def diamondChoiceT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: < a ++ b >p <-> <a>p | <b>p.
      case DiamondModality(Choice(a, b), p) => Equiv(fml, Or(DiamondModality(a, p), DiamondModality(b, p)))
      case _ => False
    }
    uncoverAxiomT("<++> choice", axiomInstance, _ => diamondChoiceBaseT)
  }
  /** Base tactic for diamond choice */
  private def diamondChoiceBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(DiamondModality(Choice(a, b), p), _) =>
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aA, a) :: SubstitutionPair(aB, b) :: SubstitutionPair(aP, p) :: Nil
    }
    axiomLookupBaseT("<++> choice", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new position tactic to apply the induction rule.
   * @param inv The invariant.
   * @return The position tactic.
   */
  def inductionT(inv: Option[Formula]): PositionTactic = new PositionTactic("induction") {
    def getBody(g: Formula): Option[Program] = g match {
      case BoxModality(Loop(a), _) => Some(a)
      case _ => None
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && getBody(s(p)).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def ind(cutSPos: Position, cont: Tactic) = boxInductionT(cutSPos) & AndRightT(cutSPos) &
        (LabelBranch("Close Next"), abstractionT(cutSPos) & cont)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = inv match {
        case Some(f) =>
          val cutAPos = AntePosition(node.sequent.ante.length, HereP)
          val prepareKMP = new ConstructionTactic("Prepare K modus ponens") {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
              case x@BoxModality(a, _) =>
                val cPos = AntePosition(node.sequent.ante.length)
                val b1 = ImplyLeftT(cPos) & AxiomCloseT
                val b2 = hideT(p)
                Some(cutT(Some(Imply(BoxModality(a, f), x))) & onBranch((cutUseLbl, b1), (cutShowLbl, b2)))
              case _ => None
            }
            override def applicable(node: ProofNode): Boolean = true
          }
          val cutSPos = SuccPosition(node.sequent.succ.length - 1, HereP)
          val useCase = prepareKMP & hideT(cutAPos) & kModalModusPonensT(cutSPos) & abstractionT(cutSPos) &
            LabelBranch(indUseCaseLbl)
          val branch1Tactic = ImplyLeftT(cutAPos) & (hideT(p) & LabelBranch(indInitLbl), useCase)
          val branch2Tactic = hideT(p) &
            ImplyRightT(cutSPos) &
            ind(cutSPos, hideT(cutAPos) & LabelBranch(indStepLbl)) &
            onBranch(("Close Next", AxiomCloseT))
          getBody(node.sequent(p)) match {
            case Some(a) =>
              Some(cutT(Some(Imply(f, BoxModality(Loop(a), f)))) &
                onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
            case None => None
          }
        case None => Some(ind(p, NilT) & LabelBranch(indStepLbl))
      }
    }
  }

  /**
   * Creates a new position tactic to apply the induction rule. Wipes the context instead of abstraction.
   * @param inv The invariant.
   * @return The new position tactic.
   * @author Stefan Mitsch
   */
  def wipeContextInductionT(inv: Option[Formula]): PositionTactic = new PositionTactic("induction") {
    def getBody(g: Formula): Option[Program] = g match {
      case BoxModality(Loop(a), _) => Some(a)
      case _ => None
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && getBody(s(p)).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def wipeContext(bvFromPos: Position, except: Position*) = new ConstructionTactic("Wipe Context") {
        require(!bvFromPos.isAnte)
        override def applicable(node: ProofNode) = true
        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(bvFromPos) match {
          case Forall(vars, _) =>
            val anteExcepts = except.filter(_.isInstanceOf[AntePosition]).map(_.index).toSet
            val anteHidePos = node.sequent.ante.zipWithIndex.collect {
              case (f,i) if allNames(f).intersect(vars.toSet).nonEmpty => i }.toSet -- anteExcepts
            val anteHides = anteHidePos.toList.sorted.reverseMap(i => hideT(AntePosition(i)))
            val succExcepts = except.filter(_.isInstanceOf[SuccPosition]).map(_.index).toSet
            val succHidePos = node.sequent.succ.zipWithIndex.collect {
              case (f,i) if allNames(f).intersect(vars.toSet).nonEmpty => i }.toSet -- succExcepts
            val succHides = succHidePos.toList.sorted.reverseMap(i => hideT(SuccPosition(i)))
            val bvFromPosCorr = succHidePos.count(_ < bvFromPos.index)
            Some((anteHides ++ succHides).foldLeft(NilT)((t, i) => t & i) &
              skolemizeT(SuccPosition(bvFromPos.index - bvFromPosCorr)))
        }
      }

      def ind(cutSPos: Position, cont: Tactic) = boxInductionT(cutSPos) & AndRightT(cutSPos) &
        (LabelBranch("Close Next"), abstractionT(cutSPos) & wipeContext(cutSPos, cutSPos) & cont)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = inv match {
        case Some(f) =>
          val cutAPos = AntePosition(node.sequent.ante.length)
          val cutSPos = SuccPosition(node.sequent.succ.length - 1)

          val prepareKMP = new ConstructionTactic("Prepare K modus ponens") {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
              case x@BoxModality(a, _) =>
                val cPos = AntePosition(node.sequent.ante.length)
                val b1 = ImplyLeftT(cPos) & AxiomCloseT
                val b2 = hideT(p)
                Some(cutT(Some(Imply(BoxModality(a, f), x))) & onBranch((cutUseLbl, b1), (cutShowLbl, b2)))
              case _ => None
            }
            override def applicable(node: ProofNode): Boolean = true
          }

          val useCase = prepareKMP & hideT(cutAPos) & kModalModusPonensT(cutSPos) & abstractionT(cutSPos) &
            wipeContext(cutSPos, cutSPos) & LabelBranch(indUseCaseLbl)
          val branch1Tactic = ImplyLeftT(cutAPos) & (hideT(p) & LabelBranch(indInitLbl), useCase)
          val branch2Tactic = hideT(p) &
            ImplyRightT(cutSPos) &
            ind(cutSPos, LabelBranch(indStepLbl)) &
            onBranch(("Close Next", AxiomCloseT))
          getBody(node.sequent(p)) match {
            case Some(a) =>
              Some(cutT(Some(Imply(f, BoxModality(Loop(a), f)))) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
            case None => None
          }
        case None => Some(ind(p, NilT) & LabelBranch(indStepLbl))
      }
    }
  }

  /**
   * Induction tactic that generates an invariant using the specified generator.
   * @param gen The invariant generator.
   * @return The induction tactic.
   */
  protected[tactics] def genInductionT(gen: Generator[Formula]): PositionTactic = new PositionTactic("Generate Invariant") {
    override def applies(s: Sequent, p: Position): Boolean = gen.peek(s, p) match {
      case Some(inv) => wipeContextInductionT(Some(inv)).applies(s, p)
      case None => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = gen(node.sequent, p) match {
        case Some(inv) => Some(wipeContextInductionT(Some(inv))(p))
        case None => None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

}
