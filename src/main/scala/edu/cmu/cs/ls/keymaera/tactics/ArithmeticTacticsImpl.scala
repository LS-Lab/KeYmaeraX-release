package edu.cmu.cs.ls.keymaera.tactics

import ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomTactic.{axiomLookupBaseT,uncoverAxiomT}
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.Propositional
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import TacticLibrary.{universalClosure,closeT,hideT,CloseTrueT, debugT, locate}
import BuiltinHigherTactics.stepAt
import PropositionalTacticsImpl.{AndLeftT,NotLeftT,EquivLeftT,cohideT,kModalModusPonensT,NotT,ImplyT,cutT, AxiomCloseT}
import SearchTacticsImpl.{locateAnte,locateSucc,onBranch}
import FOQuantifierTacticsImpl.instantiateT
import AxiomaticRuleTactics.goedelT
import TacticLibrary.TacticHelper.getFormula

import scala.collection.immutable.List
import scala.language.postfixOps

/**
 * Implementation of arithmetic tactics.
 */
object ArithmeticTacticsImpl {

  /**
   * The quantifier elimination tactic.
   * @param toolId The quantifier elimination tool to use.
   * @return The tactic.
   */
  protected[tactics] def quantifierEliminationT(toolId: String): Tactic = new Tactic("Quantifier Elimination") {
    def qeApplicable(s: Sequent): Boolean = (s.ante ++ s.succ).forall(qeApplicable)

    def qeApplicable(f: Formula): Boolean = {
      var qeAble = true
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Modality(_, _) => qeAble = false
            case ApplyPredicate(_, _) => qeAble = false
            case _ =>
          }
          if (qeAble) Left(None) else Left(Some(new StopTraversal {}))
        }

        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          e match {
            case Pair(_, _, _) => qeAble = false
            case Apply(Function(_, _, Unit, _), Nothing) => true
            case Apply(fun, _) => qeAble = false // check if fun is an external function
            case Derivative(_, _) => qeAble = false
            case IfThenElseTerm(_, _, _) => qeAble = false
            case _ =>
          }
          if (qeAble) Left(None) else Left(Some(new StopTraversal {}))
        }
      }
      ExpressionTraversal.traverse(fn, f)
      qeAble
    }

    override def applicable(node: ProofNode): Boolean = qeApplicable(node.sequent) && toolIsInitialized()

    override def apply(tool: Tool, node: ProofNode): Unit = {
      var tacticName : String = ""
      if (toolId.equals("Mathematica")) {
        tacticName = "Mathematica QE"
      } else if (toolId.equals("Z3")) {
        tacticName = "Z3 QE"
      }
      val t: Tactic = new ConstructionTactic(tacticName) {
        override def applicable(node: ProofNode): Boolean = true

        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
          LookupLemma.addRealArithLemma(tool, universalClosure(desequentialization(node.sequent))) match {
            case Some((file, id, f)) =>
              f match {
                case Equiv(res, True) => {
                  val lemma = new ApplyRule(LookupLemma(file, id)) {
                    override def applicable(node: ProofNode): Boolean = true
                  }
                  // reinstantiate quantifiers
                  val pos = AntePosition(node.sequent.ante.length)
                  def reInst(f: Formula): Option[Tactic] = f match {
                    case Forall(v, g) =>
                      val resG = reInst(g)
                      if (v.isEmpty) resG
                      else {
                        val vars = v.map({
                          case x: Variable => x
                          case _ => throw new IllegalArgumentException("Can only handle quantifiers over variables")
                        })
                        val tac = (for (n <- vars) yield instantiateT(n, n)(pos)).reduce(seqT)
                        resG match {
                          case Some(tt) => Some(tac & tt)
                          case None => Some(tac)
                        }
                      }
                    case _ => None
                  }
                  val contTactic = (closeT | locateSucc(Propositional) | locateAnte(Propositional))*
                  def branch1(inst: Tactic): Tactic = AndLeftT(pos) & hideT(pos + 1) & inst & contTactic
                  //Really simple because this is just checking that the thing we believe to be true is actually true.
                  val branch2 = AndLeftT(pos) & NotLeftT(AntePosition(node.sequent.ante.length + 1)) & CloseTrueT(SuccPosition(node.sequent.succ.length))
                  val tr = reInst(res) match {
                    case Some(inst) => lemma & EquivLeftT(pos) & onBranch((equivLeftLbl, branch1(inst)), (equivRightLbl, branch2))
                    case _ => lemma & contTactic
                  }
                  Some(tr) //& debugT("Test"))
                }
                case _ => println("Only apply QE if the result is true, have " + f.prettyString()); None
              }
            case _ => None
          }
        }
      }

      if (toolId.equals("Mathematica")) {
        t.scheduler = Tactics.MathematicaScheduler
      } else if (toolId.equals("Z3")) {
        t.scheduler = Tactics.Z3Scheduler
      } else throw new Exception("Cannot find the QE tool")

      t.continuation = continuation
      t.dispatch(this, node)
    }

    private def toolIsInitialized(): Boolean = {
      if (toolId == "Mathematica") MathematicaScheduler.isInitialized
      else if (toolId == "Z3") Z3Scheduler.isInitialized
      else false
    }
  }

  /**
   * Turns a sequent into a form suitable for quantifier elimination.
   * @param s The sequent.
   * @return The desequentialized form.
   */
  private def desequentialization(s: Sequent) = {
    //TODO-nrf Not sure what to do with pref. Matters in non-taut case.
    if (s.ante.isEmpty && s.succ.isEmpty) False
    else {
      val assumption =
        if (s.ante.isEmpty) True
        else s.ante.reduce((l, r) => And(l, r))

      val implicant =
        if (s.succ.isEmpty) Not(assumption)
        else s.succ.reduce((l, r) => Or(l, r))

      if (s.ante.isEmpty) implicant
      else Imply(assumption, implicant)
    }
  }

  /**
   * Creates a new axiom tactic for negating equality: s=t <-> !(s!=t)
   * @return The axiom tactic.
   */
  def NegateEqualsT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: s=t <-> !(s!=t)
      case Equals(sort, f, g) => Equiv(fml, Not(NotEquals(sort, f, g)))
      case Not(NotEquals(sort, f, g)) => Equiv(Equals(sort, f, g), fml)
      case _ => False
    }
    uncoverAxiomT("= negate", axiomInstance, _ => NegateEqualsBaseT)
  }
  /** Base tactic for negate equals */
  private def NegateEqualsBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (sort, f, g) = fml match {
        case Equiv(Equals(s, ff, gg), _) => (s, ff, gg)
        case Not(NotEquals(s, ff, gg)) => (s, ff, gg)
      }
      // TODO check that axiom is of the expected form s=t <-> !(s != t)
      val aF = Apply(Function("f", None, sort, sort), Anything)
      val aG = Apply(Function("g", None, sort, sort), Anything)
      SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil
    }
    axiomLookupBaseT("= negate", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for negating equality: s=t <-> !(s!=t)
   * @return The axiom tactic.
   */
  def NegateLessThanT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: s<t <-> !(s>=t)
      case LessThan(sort, f, g) => Equiv(fml, Not(GreaterEqual(sort, f, g)))
      case Not(GreaterEqual(sort, f, g)) => Equiv(LessThan(sort, f, g), fml)
      case _ => False
    }
    uncoverAxiomT("< negate", axiomInstance, _ => NegateLessThanBaseT)
  }
  /** Base tactic for negate less than */
  def NegateLessThanBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (sort, f, g) = fml match {
        case Equiv(LessThan(s, ff, gg), _) => (s, ff, gg)
        case Equiv(Not(GreaterEqual(s, ff, gg)), _) => (s, ff, gg)
      }
      val aF = Apply(Function("f", None, sort, sort), Anything)
      val aG = Apply(Function("g", None, sort, sort), Anything)
      SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil
    }
    axiomLookupBaseT("< negate", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for splitting <=: s<=t <-> s < t | s=t
   * @return The axiom tactic.
   */
  def LessEqualSplitT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      // construct axiom instance: s<=t <-> (s < t | s=t)
      case LessEqual(sort, f, g) => Equiv(fml, Or(LessThan(sort, f, g), Equals(sort, f, g)))
      case Or(LessThan(sort, f, g), Equals(sort2, f2, g2)) if sort == sort2 && f == f2 && g == g2 => Equiv(LessEqual(sort, f, g), fml)
      case _ => False
    }
    uncoverAxiomT("<=", axiomInstance, _ => LessEqualSplitBaseT)
  }
  /** Base tactic for less equal split  */
  private def LessEqualSplitBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (sort, f, g) = fml match {
        case Equiv(LessEqual(s, ff, gg), _) => (s, ff, gg)
        case Equiv(Or(LessThan(s, ff, gg), Equals(s2, f2, g2)), _) if s == s2 && ff == f2 && gg == g2 => (s, ff, gg)
      }
      val aF = Apply(Function("f", None, sort, sort), Anything)
      val aG = Apply(Function("g", None, sort, sort), Anything)
      SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil
    }
    axiomLookupBaseT("<=", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for flipping >=
   * @return The axiom tactic.
   */
  def GreaterEqualFlipT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case GreaterEqual(sort, f, g) => Equiv(fml, LessEqual(sort, g, f))
      case LessEqual(sort, f, g) => Equiv(GreaterEqual(sort, g, f), fml)
      case _ => False
    }
    uncoverAxiomT(">= flip", axiomInstance, _ => GreaterEqualFlipBaseT)
  }
  /** Base tactic for greater equal flip */
  def GreaterEqualFlipBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (sort, f, g) = fml match {
        case Equiv(GreaterEqual(s, ff, gg), _) => (s, ff, gg)
        case Equiv(LessEqual(s, ff, gg), _) => (s, ff, gg)
      }
      val aF = Apply(Function("f", None, sort, sort), Anything)
      val aG = Apply(Function("g", None, sort, sort), Anything)
      SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil
    }
    axiomLookupBaseT(">= flip", subst, _ => NilPT, (f, ax) => ax)
  }

  /**
   * Creates a new axiom tactic for flipping >
   * @return The axiom tactic.
   */
  def GreaterThanFlipT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case GreaterThan(sort, f, g) => Equiv(fml, LessThan(sort, g, f))
      case LessThan(sort, f, g) => Equiv(GreaterThan(sort, g, f), fml)
    }
    uncoverAxiomT("> flip", axiomInstance, _ => GreaterThanFlipBaseT)
  }
  /** Base tactic for greater than flip */
  private def GreaterThanFlipBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = {
      val (sort, f, g) = fml match {
        case Equiv(GreaterThan(s, ff, gg), _) => (s, ff, gg)
        case Equiv(LessThan(s, ff, gg), _) => (s, ff, gg)
      }
      val aF = Apply(Function("f", None, sort, sort), Anything)
      val aG = Apply(Function("g", None, sort, sort), Anything)
      SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil
    }
    axiomLookupBaseT("> flip", subst, _ => NilPT, (f, ax) => ax)
  }

  def NegateGreaterThanT: PositionTactic = new PositionTactic("> negate") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case GreaterThan(_, _, _) => true
      case Not(LessEqual(_, _, _)) => true
      case _ => false
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case GreaterThan(sort, s, t) =>
          Some(GreaterThanFlipT(p) & NegateLessThanT(p) & GreaterEqualFlipT(p.first))
        case Not(LessEqual(sort, s, t)) =>
          Some(GreaterEqualFlipT(p.first) & NegateLessThanT(p) & GreaterThanFlipT(p))
        case _ => None
      }
    }
  }

  def NegateLessEqualsT: PositionTactic = new PositionTactic("<= negate") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case LessEqual(_, _, _) => true
      case Not(GreaterThan(_, _, _)) => true
      case _ => false
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case LessEqual(sort, s, t) =>
          Some(GreaterEqualFlipT(p) & NegateGreaterEqualsT(p) & GreaterThanFlipT(p.first))
        case Not(GreaterThan(sort, s, t)) =>
          Some(GreaterThanFlipT(p.first) & NegateGreaterEqualsT(p) & GreaterEqualFlipT(p))
        case _ => None
      }
    }
  }

  def NegateBinaryRelationT[T: Manifest](name: String, rel: T => Option[(Sort, Term, Term)],
                                         neg: T => Option[(Sort, Term, Term)],
                                         relFactory: (Sort, Term, Term) => Formula,
                                         negFactory: (Sort, Term, Term) => Formula,
                                         baseTactic: PositionTactic) = new PositionTactic(name) {
    class Unapplyer(f: T => Option[(Sort, Term, Term)]) {
      def unapply(a: Any): Option[(Sort, Term, Term)] = {
        if (manifest[T].runtimeClass.isInstance(a)) f(a.asInstanceOf[T]) else None
      }
    }

    val Rel = new Unapplyer(rel)
    val Neg = new Unapplyer(neg)

    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
        case Rel(_, _, _) => true
        case Not(Neg(_, _, _)) => true
        case _ => false
      }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def prepareKMP = new ConstructionTactic("Prepare KMP") {
          override def applicable(node : ProofNode): Boolean = {
            val antePrgs = node.sequent.ante.filter({ case BoxModality(_, _) => true case _ => false }).
              map({ case BoxModality(prg, _) => prg })
            val succPrgs = node.sequent.succ.filter({ case BoxModality(_, _) => true case _ => false }).
              map({ case BoxModality(prg, _) => prg })
            antePrgs.intersect(succPrgs).nonEmpty
          }

          def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
            val (f, fPrg) = node.sequent.ante.filter({ case BoxModality(_, _) => true case _ => false }).
              map({ case b@BoxModality(prg, _) => (b, prg) }).last
            val g = node.sequent.succ.filter({ case BoxModality(prg, _) => prg == fPrg case _ => false }).
              map({ case b@BoxModality(_, _) => b }).last

            val pa = AntePosition(node.sequent.ante.length)
            val ps = SuccPosition(node.sequent.succ.length)
            Some(
              cutT(Some(Imply(f, g))) & onBranch (
                (cutUseLbl, ImplyT(pa) & (AxiomCloseT | debugT("Should not happen") & stopT)),
                (cutShowLbl, cohideT(ps))
              )
            )
          }
        }

        def cutShowTactic = {
          val ps = SuccPosition(node.sequent.succ.length)
          val ps0 = SuccPosition(0)

          cohideT(ps) & assertT(0, 1) & TacticLibrary.propositional & (
            ((prepareKMP & kModalModusPonensT(ps0) & goedelT & TacticLibrary.propositional)*)
            | TacticLibrary.propositional) & locate(baseTactic) & locate(NotT) & (AxiomCloseT | debugT("BAD 1") & stopT)
        }

        val pa = AntePosition(node.sequent.ante.length)
        getFormula(node.sequent, p) match {
          case Rel(sort, s, t) =>
            val replFormula = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
              override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = {
                Right(Not(negFactory(sort, s, t)))
              }
            }), node.sequent(p)) match {
              case Some(f) => f
              case None => throw new IllegalArgumentException("Checked by applies to never occur")
            }

            if (p.isAnte) {
              Some(
                cutT(Some(Imply(node.sequent(p), replFormula))) & onBranch(
                  (cutShowLbl, cutShowTactic),
                  (cutUseLbl, ImplyT(pa) && (AxiomCloseT | debugT("BAD 2") & stopT, hideT(p.topLevel))))
              )
            } else {
              Some(
                cutT(Some(Imply(replFormula, node.sequent(p)))) & onBranch(
                  (cutShowLbl, cutShowTactic),
                  (cutUseLbl, ImplyT(pa) && (hideT(p.topLevel), AxiomCloseT | debugT("BAD 3") & stopT)))
              )
            }
          case Not(Neg(sort, s, t)) =>
            val replFormula = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
              override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = {
                Right(relFactory(sort, s, t))
              }
            }), node.sequent(p)) match {
              case Some(f) => f
              case None => throw new IllegalArgumentException("Checked by applies to never occur")
            }

            if (p.isAnte) Some(
              cutT(Some(Imply(node.sequent(p), replFormula))) & onBranch(
                (cutShowLbl, cutShowTactic),
                (cutUseLbl, ImplyT(pa) && (AxiomCloseT | debugT("BAD 4") & stopT, hideT(p.topLevel))))
            )
            else Some(
              cutT(Some(Imply(replFormula, node.sequent(p)))) & onBranch(
                (cutShowLbl, cutShowTactic),
                (cutUseLbl, ImplyT(pa) && (hideT(p.topLevel), AxiomCloseT | debugT("BAD 5") & stopT)))
            )
        }
      }
    }
  }

  /**
   * Creates a new tactic for negating =: s!=t <-> !(s=t)
   * @return The tactic.
   */
  def NegateNotEqualsT = NegateBinaryRelationT("!= negate", NotEquals.unapply, Equals.unapply, NotEquals.apply,
    Equals.apply, NegateEqualsT)

  /**
   * Creates a new tactic for negating >=: s < t <-> !(s>=t)
   * @return The tactic.
   */
  def NegateGreaterEqualsT = NegateBinaryRelationT(">= negate", GreaterEqual.unapply, LessThan.unapply,
    GreaterEqual.apply, LessThan.apply, NegateLessThanT)

}