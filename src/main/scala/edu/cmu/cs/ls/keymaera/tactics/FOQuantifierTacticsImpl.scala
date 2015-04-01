package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.BindingAssessment.allNames
import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper._
import edu.cmu.cs.ls.keymaera.tactics.AxiomTactic.{uncoverAxiomT,axiomLookupBaseT}
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl.v2vAssignT
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.{getFormula, freshNamedSymbol}
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import TacticLibrary.alphaRenamingT
import PropositionalTacticsImpl.uniformSubstT
import AxiomTactic.axiomT

import scala.collection.immutable.List
import scala.collection.immutable.Seq

/**
 * Implementation of first order quantifier tactics.
 * @author Stefan Mitsch
 */
object FOQuantifierTacticsImpl {

  /**
   * Creates a new tactic for the universal/existential duality axiom.
   * @return The newly created tactic
   */
  def forallDualT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // \forall x . p(x) <-> !(\exists x . (!p(x)))
      case Forall(v, p) =>
        assert(v.size == 1, "Duality not supported for more than one variable")
        Equiv(fml, Not(Exists(v, Not(p))))
      case Not(Exists(v, Not(p))) => Equiv(Forall(v, p), fml)
      case _ => False
    }
    uncoverAxiomT("all dual", axiomInstance, _ => forallDualBaseT)
  }
  /** Base tactic for forall duality */
  private def forallDualBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (p, v) = fml match {
        case Equiv(Forall(vv, pp), _) => (pp, vv)
        case Equiv(Not(Exists(vv, Not(pp))), _) => (pp, vv)
      }
      val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
      SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(v.head.asInstanceOf[Variable], CDot)) :: Nil
    }
    axiomLookupBaseT("all dual", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new tactic for the universal/existential duality axiom.
   * @return The newly created tactic
   */
  def existsDualT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // \exists x . p(x) <-> !(\forall x . (!p(x)))
      case Exists(v, p) =>
        assert(v.size == 1, "Duality not supported for more than one variable")
        Equiv(fml, Not(Forall(v, Not(p))))
      case Not(Forall(v, Not(p))) => Equiv(Exists(v, p), fml)
      case _ => False
    }
    uncoverAxiomT("exists dual", axiomInstance, _ => existsDualBaseT)
  }
  /** Base tactic for exists duality */
  private def existsDualBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (p, v) = fml match {
        case Equiv(Exists(vv, pp), _) => (pp, vv)
        case Equiv(Not(Forall(vv, Not(pp))), _) => (pp, vv)
      }
      val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
      SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(v.head.asInstanceOf[Variable], CDot)) :: Nil
    }
    axiomLookupBaseT("exists dual", subst, _ => NilPT, (f, ax) => ax)
  }

  def instantiateT: PositionTactic = new PositionTactic("Quantifier Instantiation") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Forall(_, _) => p.isAnte
      case Exists(_, _) => !p.isAnte
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, pos) match {
        case Forall(vars, phi) =>
          Some(vars.filter(_.isInstanceOf[Variable]).
            map(v => instantiateT(v.asInstanceOf[Variable], v.asInstanceOf[Variable])(pos)).
            fold(NilT)((a, b) => a & b))
        case Exists(vars, phi) =>
          Some(vars.filter(_.isInstanceOf[Variable]).
            map(v => instantiateT(v.asInstanceOf[Variable], v.asInstanceOf[Variable])(pos)).
            fold(NilT)((a, b) => a & b))
        case _ => None
      }
    }
  }

  /**
   * Creates a tactic which does quantifier instantiation.
   * @param quantified The quantified variable.
   * @param instance The instance.
   * @return The tactic.
   */
  def instantiateT(quantified: Variable, instance: Term): PositionTactic = new PositionTactic("Quantifier Instantiation") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Forall(vars, _) => p.isAnte && vars.contains(quantified)
      case Exists(vars, _) => !p.isAnte && vars.contains(quantified)
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, pos) match {
        case Forall(_, _) =>
          Some(withStuttering(node.sequent, instantiateUniversalQuanT(quantified, instance)(pos)))
        case Exists(_, _) =>
          Some(withStuttering(node.sequent, instantiateExistentialQuanT(quantified, instance)(pos)))
        case _ => None
      }

      private def withStuttering(s: Sequent, around: Tactic): Tactic = {
        var stutteringAt: Option[PosInExpr] = None
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case BoxModality(prg@Loop(_), _) if StaticSemantics(prg).bv.contains(quantified) => stutteringAt = Some(p); Left(Some(ExpressionTraversal.stop))
            case BoxModality(prg@ODESystem(_, _, _), _) if StaticSemantics(prg).bv.contains(quantified) => stutteringAt = Some(p); Left(Some(ExpressionTraversal.stop))
            case DiamondModality(prg@Loop(_), _) if StaticSemantics(prg).bv.contains(quantified) => stutteringAt = Some(p); Left(Some(ExpressionTraversal.stop))
            case DiamondModality(prg@ODESystem(_, _, _), _) if StaticSemantics(prg).bv.contains(quantified) => stutteringAt = Some(p); Left(Some(ExpressionTraversal.stop))
            case _ => Left(None)
          }
        }, getFormula(s, pos))

        stutteringAt match {
          case Some(p) =>
            val freshQuantified = freshNamedSymbol(quantified, s)
            val pPos = if (pos.isAnte) new AntePosition(pos.index, p) else new SuccPosition(pos.index, p)
            val assignPos = if (pos.isAnte) new AntePosition(pos.index, PosInExpr(p.pos.tail)) else new SuccPosition(pos.index, PosInExpr(p.pos.tail))
            alphaRenamingT(quantified.name, quantified.index, freshQuantified.name, freshQuantified.index)(pPos) &
              around & v2vAssignT(assignPos)
          case None => around
        }

      }
    }
  }

  def instantiateUniversalQuanT(quantified: Variable, instance: Term): PositionTactic = new PositionTactic("Universal Quantifier Instantiation") {
    val axiomName = "all instantiate"
    val axiom = Axiom.axioms.get(axiomName)
    require(axiom.isDefined)

    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case Forall(vars, _) => vars.contains(quantified)
      case _ => false
    })

    override def apply(pos: Position): Tactic = new ConstructionTactic("Universal Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      def replace(f: Formula)(o: NamedSymbol, n: Term): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Forall(v, fa) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), fa))
          case Exists(v, fa) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), fa))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
      }, f) match {
        case Some(g) => g
        case None => throw new IllegalStateException("Replacing one variable by another should not fail")
      }

      def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair], (Variable, Variable), (Term, Term))] = f match {
        case Forall(x, qf) if x.contains(quantified) =>
          def forall(h: Formula) = if (x.length > 1) Forall(x.filter(_ != quantified), h) else h
          // construct substitution
          val aX = Variable("x", None, Real)
          val aT = Apply(Function("t", None, Unit, Real), Nothing)
          val aP = Function("p", None, Real, Bool)
          val l = List(SubstitutionPair(aT, instance), SubstitutionPair(ApplyPredicate(aP, CDot),
            forall(SubstitutionHelper.replaceFree(qf)(quantified, CDot))))
          // construct axiom instance: \forall x. p(x) -> p(t)
          val g = SubstitutionHelper.replaceFree(qf)(quantified, instance)
          val axiomInstance = Imply(f, forall(g))
          Some(axiomInstance, l, (quantified, aX), (instance, aT))
        case Forall(x, qf) if !x.contains(quantified) => None
        case _ => None
      }

      def decompose(d: Formula): Formula = d match {
        case Forall(v, f) if v.length > 1 => Forall(v.take(1), Forall(v.drop(1), f))
        case Exists(v, f) if v.length > 1 => Exists(v.take(1), Exists(v.drop(1), f))
        case _ => d
      }

      // since we have an implication, we use modus ponens to get it's consequence
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiom match {
          case Some(a) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos)) match {
              case Some((axiomInstance, subst, (quant, aX), (inst, aT))) =>
                val eqPos = AntePosition(node.sequent.ante.length)
                val branch1Tactic = modusPonensT(pos, eqPos)
                // val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                // val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                // val hideSllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
                def repl(f: Formula, v: Variable):Formula = f match {
                  case Imply(Forall(vars, aa), b) =>
                    Imply(
                      decompose(
                        Forall(vars.map(qv => if (qv == v) quantified else qv), SubstitutionHelper.replaceFree(aa)(v, quantified))),
                      b)
                  case _ => throw new IllegalArgumentException("...")
                }

                val (renAxiom, alpha) =
                  if (quantified.name != aX.name || quantified.index != aX.index)
                    (repl(a, aX), alphaRenamingT(aX.name, aX.index, quantified.name, quantified.index)(AntePosition(0, HereP.first)))
                  else (a, NilT)

                val axInstance = axiomInstance match {
                  case Imply(lhs, rhs) => Imply(decompose(lhs), rhs)
                }

                val replMap = Map(axInstance -> renAxiom)
                val branch2Tactic = cohideT(SuccPosition(node.sequent.succ.length)) ~
                  decomposeQuanT(SuccPosition(0, HereP.first)) ~
                  (uniformSubstT(subst, replMap) &
                    (axiomT(axiomName) & alpha & AxiomCloseT))
                Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
              case None => println("Giving up " + this.name); None
            }
          case None => println("Giving up because the axiom does not exist " + this.name); None
        }

    }
  }

  def instantiateExistentialQuanT(quantified: Variable, t: Term) = new PositionTactic("exists instantiate") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Exists(vars, _) => vars.contains(quantified) &&
        ((p.isAnte && polarityAt(s, p) == -1) || (!p.isAnte && polarityAt(s, p) == 1))
      case _ => false
    }

    private def parentPosOf(p: Position) =
      if (p.isAnte) AntePosition(p.index, PosInExpr(p.inExpr.pos.init))
      else SuccPosition(p.index, PosInExpr(p.inExpr.pos.init))

    private def polarityAt(s: Sequent, p: Position): Int =
      if (p.isTopLevel) 1 else getFormula(s, parentPosOf(p)) match {
        case Not(_) => -polarityAt(s, parentPosOf(p))
        case Imply(_, _) if p.inExpr.pos.last == 0 => -polarityAt(s, parentPosOf(p))
        case Imply(_, _) if p.inExpr.pos.last == 1 => polarityAt(s, parentPosOf(p))
        case Equiv(_, _) => 0
        case _ => polarityAt(s, parentPosOf(p))
      }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case Exists(vars, phi) =>
          val desired = createDesired(node.sequent)
          val cutFrm = Imply(desired, node.sequent(p))
          Some(cutT(Some(cutFrm)) & onBranch(
            (cutUseLbl, lastAnte(assertPT(cutFrm)) & lastAnte(ImplyLeftT) && (hideT(p.topLevel), AxiomCloseT)),
            (cutShowLbl, lastSucc(assertPT(cutFrm)) & lastSucc(cohideT) & assertT(0, 1) & assertPT(cutFrm)(SuccPosition(0)) &
              ImplyRightT(SuccPosition(0)) & assertT(1, 1) &
              generalize(replace(phi)(quantified, t)))
          ))
        case _ => None
      }

      private def createDesired(s: Sequent) = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
          case Exists(_, phi) => Right(replace(phi)(quantified, t))
          case _ => Left(Some(ExpressionTraversal.stop))
        }
      }), s(p)) match {
        case Some(frm) => frm
        case None => throw new IllegalArgumentException(s"Did not find existential quantifier in $s at $p")
      }

      private def generalize(fToGen: Formula) = {
        if (p.isTopLevel) {
          existentialGenT(quantified, t)(AntePosition(0)) & AxiomCloseT
        } else {
          repeatT(AxiomCloseT | locateAnte(PropositionalLeftT) | locateSucc(PropositionalRightT)) &
            locateAnte(existentialGenT(quantified, t), _ == fToGen) & AxiomCloseT
        }
      }
    }
  }

  /**
   * Tactic for existential quantifier generalization.
   * @param x The new existentially quantified variable.
   * @param t The term to generalize.
   * @return The tactic.
   */
  def existentialGenT(x: Variable, t: Term): PositionTactic = {
    // construct axiom instance: p(t) -> \exists x. p(x)
    def axiomInstance(fml: Formula): Formula = Imply(fml, Exists(x :: Nil, SubstitutionHelper.replaceFree(fml)(t, x)))
    uncoverAxiomT("exists generalize", axiomInstance, _ => existentialGenBaseT(x, t))
  }
  /** Base tactic for existential generalization */
  private def existentialGenBaseT(x: Variable, t: Term): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(p, Exists(_, _)) =>
        val aT = Apply(Function("t", None, Unit, Real), Nothing)
        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
        SubstitutionPair(aT, t) :: SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(t, CDot)) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Imply(_, Exists(_, _)) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(x.name, x.index, aX.name, aX.index)(p.second))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Imply(left, right) = axiom
      if (x.name != aX.name || x.index != aX.index) Imply(left, replaceFree(right)(aX, x))
      else Imply(left, right)
    }

    axiomLookupBaseT("exists generalize", subst, alpha, axiomInstance)
  }

  def vacuousUniversalQuanT(x: Option[Variable]) = vacuousQuantificationT(x, "vacuous all quantifier", Forall.apply)
  def vacuousExistentialQuanT(x: Option[Variable]) = vacuousQuantificationT(x, "vacuous exists quantifier", Exists.apply)

  /**
   * Base class for vacuous quantifier elimination/introduction tactics.
   * @param x The new quantified variable. If None, the tactic eliminates a vacuous quantifier.
   * @param axiomName The name of the axiom.
   * @param quantFactory Creates the quantifier.
   */
  def vacuousQuantificationT(x: Option[Variable], axiomName: String,
                             quantFactory: (Seq[NamedSymbol], Formula) => Quantifier): PositionTactic = {

    def axiomInstance(fml: Formula): Formula = x match {
      case Some(v) if !allNames(fml).contains(v) => Equiv(fml, quantFactory(v :: Nil, fml))
      case _ => fml match {
        case q: Quantifier if q.variables.size == 1 && allNames(q.child.asInstanceOf[Formula]).intersect(q.variables.toSet).isEmpty =>
          Equiv(q.child.asInstanceOf[Formula], fml)
        case _ => False
      }
    }
    uncoverAxiomT(axiomName, axiomInstance, _ => vacuousQuantificationBaseT(x, axiomName, quantFactory))
  }

  private def vacuousQuantificationBaseT(x: Option[Variable], axiomName: String,
                                         quantFactory: (Seq[NamedSymbol], Formula) => Quantifier): PositionTactic = {

    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(p, _) =>
        val aP = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
        SubstitutionPair(aP, p) :: Nil
    }

    def v(fml: Formula) = x match {
      case Some(vv) => vv
      case None => fml match {
        case Equiv(_, q: Quantifier) =>
          require(q.variables.size == 1 && q.variables.head.isInstanceOf[Variable])
          q.variables.head.asInstanceOf[Variable]
      }
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      new PositionTactic("Alpha") {
        override def applies(s: Sequent, p: Position): Boolean = s(p) match {
          case Equiv(_, _: Quantifier) => true
          case _ => false
        }

        override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
            Some(alphaRenamingT(v(fml).name, v(fml).index, aX.name, aX.index)(p.second))

          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }
      }
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Equiv(left, right) = axiom
      if (v(fml).name == aX.name && v(fml).index == aX.index) Equiv(left, right)
      else Equiv(left, replaceFree(right)(aX, v(fml)))
    }

    axiomLookupBaseT(axiomName, subst, alpha, axiomInstance)
  }

  /**
   * Creates a tactic to decompose quantifiers.
   * @return The tactic.
   */
  def decomposeQuanT = new PositionTactic("Decompose Quantifiers") {
    override def applies(s: Sequent, pos: Position): Boolean = {
      var res = false
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if(p == pos.inExpr) Left(None) else Right(e)
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Forall(vars, f) if vars.length > 1 => res = true
            case Exists(vars, f) if vars.length > 1 => res = true
            case _ => res = false
          }
          Left(Some(new StopTraversal {}))
        }
      }
      ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), s(pos))
      res
    }

    override def apply(p: Position): Tactic = new ApplyRule(DecomposeQuantifiers(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /**
   * Creates a new tactic for skolemization.
   * @return The skolemization tactic.
   */
  def skolemizeT: PositionTactic = skolemizeT(forceUniquify = false)
  def skolemizeT(forceUniquify: Boolean): PositionTactic = skolemize(new Skolemize(_), forceUniquify)
  def skolemizeToFnT: PositionTactic = skolemizeToFnT(forceUniquify = false)
  def skolemizeToFnT(forceUniquify: Boolean): PositionTactic = skolemize(new SkolemizeToFn(_), forceUniquify)

  private def skolemize(factory: Position => PositionRule, forceUniquify: Boolean): PositionTactic =
      new PositionTactic("Skolemize") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case Forall(_, _) => !p.isAnte
      case Exists(_, _) => p.isAnte
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      import BindingAssessment.allNamesExceptAt
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Forall(vars, _) =>
          val rename =
            if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty) uniquify(p)
            else NilT
          Some(rename ~ new ApplyRule(factory(p)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          })
        case Exists(vars, _) =>
          val rename =
            if (forceUniquify || allNamesExceptAt(node.sequent, p).intersect(vars.toSet).nonEmpty) uniquify(p)
            else NilT
          Some(rename ~ new ApplyRule(factory(p)) {
            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          })
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  val uniquify = new PositionTactic("Uniquify") {
    // for now only on top level
    def getBoundVariables(s: Sequent, p: Position): Option[Seq[(String, Option[Int])]] = s(p) match {
      case Forall(v, _) => Some(v.map {
        case Variable(n, i, _) => (n, i)
        case DifferentialSymbol(Variable(n, i, _)) => (n, i)
        case _ => ???
      })
      case Exists(v, _) => Some(v.map {
        case Variable(n, i, _) => (n, i)
        case DifferentialSymbol(Variable(n, i, _)) => (n, i)
        case _ => ???
      })
      case BoxModality(Assign(Variable(n, i, _), e), _) => Some(Seq((n, i)))
      case BoxModality(NDetAssign(Variable(n, i, _)), _) => Some(Seq((n, i)))
      case DiamondModality(Assign(Variable(n, i, _), e), _) => Some(Seq((n, i)))
      case DiamondModality(NDetAssign(Variable(n, i, _)), _) => Some(Seq((n, i)))
      case a => None
    }

    override def applies(s: Sequent, p: Position): Boolean = (p.inExpr == HereP) && getBoundVariables(s, p).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import BindingAssessment.{allNames,allNamesExceptAt}
        getBoundVariables(node.sequent, p) match {
          case Some(s) =>
            var otherVars = allNamesExceptAt(node.sequent, p).map((n: NamedSymbol) => (n.name, n.index)) ++ s.distinct
            val pVars = allNames(node.sequent(p)).map((n: NamedSymbol) => (n.name, n.index))
            val res: Seq[Option[Tactic]] = for((n, idx) <- s.distinct) yield {
              val vars = otherVars.filter(_._1 == n) ++ pVars.filter(_._1 == n)
              //require(vars.size > 0, "The variable we want to rename was not found in the sequent all together " + n + " " + node.sequent)
              // we do not have to rename if there are no name clashes
              if (vars.size > 0) {
                val maxIdx: Option[Int] = vars.map(_._2).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) => acc match {
                  case Some(a) => i match {
                    case Some(b) => if (a < b) Some(b) else Some(a)
                    case None => Some(a)
                  }
                  case None => i
                })
                val tIdx: Option[Int] = maxIdx match {
                  case None => Some(0)
                  case Some(a) => Some(a + 1)
                }
                otherVars = otherVars ++ Seq((n, tIdx))
                Some(alphaRenamingT(n, idx, n, tIdx)(p))
              } else {
                None
              }
            }
            val tactic = res.flatten.reduceRight(seqT)
            Some(tactic)
          case None => None
        }
      }
    }

  }
}
