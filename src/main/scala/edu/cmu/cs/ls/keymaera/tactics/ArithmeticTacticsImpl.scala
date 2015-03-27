package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import TacticLibrary.{universalClosure,closeT,hideT,CloseTrueT, debugT}
import BuiltinHigherTactics.stepAt
import PropositionalTacticsImpl.{AndLeftT,NotLeftT,EquivLeftT,cohideT}
import SearchTacticsImpl.{locateAnte,locateSucc,onBranch}
import FOQuantifierTacticsImpl.instantiateT

import scala.collection.immutable.{List, Set, Seq}

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
    def qeApplicable(s: Sequent): Boolean =
      (s.ante ++ s.succ).foldLeft(true)((acc: Boolean, f: Formula) => acc && qeApplicable(f))

    def qeApplicable(f: Formula): Boolean = {
      var qeAble = true
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Modality(_, _) => qeAble = false
            case ApplyPredicate(_, _) => qeAble = false
            case PredicateConstant(_, _) => qeAble = false
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

    override def applicable(node: ProofNode): Boolean = qeApplicable(node.sequent)

    override def apply(tool: Tool, node: ProofNode): Unit = {
      val t: Tactic = new ConstructionTactic("Mathematica QE") {
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
                    case Forall(v, g) => {
                      val resG = reInst(g)
                      if (v.isEmpty) resG
                      else {
                        val vars = v.map({
                          case x: Variable => x
                          case _ => throw new IllegalArgumentException("Can only handle quantifiers over variables")
                        })
                        val tac = (for (n <- vars) yield instantiateT(n, n)(pos)).reduce(seqT)
                        resG match {
                          case Some(t) => Some(tac & t)
                          case None => Some(tac)
                        }
                      }
                    }
                    case _ => None
                  }
                  val contTactic = ((closeT | locateSucc(stepAt(true, false, true)) | locateAnte(stepAt(true, false, true, true))) *)
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
      t.scheduler = Tactics.MathematicaScheduler
      t.continuation = continuation
      t.dispatch(this, node)
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
  def NegateEqualsT = new AxiomTactic("= negate", "= negate") {
    override def applies(f: Formula): Boolean = f match {
      case Equals(_, _, _) => true
      case Not(NotEquals(_, _, _)) => true
      case _ => false
    }

    override def constructInstanceAndSubst(frm: Formula): Option[(Formula, List[SubstitutionPair])] = frm match {
      case Equals(sort, f, g) =>
        // TODO check that axiom is of the expected form s=t <-> !(s != t)
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance: s=t <-> !(s!=t)
        val h = Not(NotEquals(sort, f, g))
        val axiomInstance = Equiv(frm, h)

        Some(axiomInstance, subst)
      case Not(NotEquals(sort, f, g)) =>
        // TODO check that axiom is of the expected form s=t <-> !(s != t)
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance: s=t <-> !(s!=t)
        val h = Equals(sort, f, g)
        val axiomInstance = Equiv(h, frm)

        Some(axiomInstance, subst)
    }
  }

  /**
   * Creates a new axiom tactic for negating equality: s=t <-> !(s!=t)
   * @return The axiom tactic.
   */
  def NegateLessThanT = new AxiomTactic("< negate", "< negate") {
    override def applies(f: Formula): Boolean = f match {
      case LessThan(_, _, _) => true
      case Not(GreaterEqual(_, _, _)) => true
      case _ => false
    }

    override def constructInstanceAndSubst(frm: Formula): Option[(Formula, List[SubstitutionPair])] = frm match {
      case LessThan(sort, f, g) =>
        // TODO check that axiom is of the expected form s<t <-> !(s >= t)
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance: s<t <-> !(s>=t)
        val h = Not(GreaterEqual(sort, f, g))
        val axiomInstance = Equiv(frm, h)

        Some(axiomInstance, subst)
      case Not(GreaterEqual(sort, f, g)) =>
        // TODO check that axiom is of the expected form s<t <-> !(s >= t)
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance: s<t <-> !(s>=t)
        val h = LessThan(sort, f, g)
        val axiomInstance = Equiv(h, frm)

        Some(axiomInstance, subst)
    }
  }

  /**
   * Creates a new axiom tactic for splitting <=: s<=t <-> s < t | s=t
   * @return The axiom tactic.
   */
  def LessEqualSplitT = new AxiomTactic("<=", "<=") {
    override def applies(f: Formula): Boolean = f match {
      case LessEqual(_, _, _) => true
      case Or(LessThan(sort, s, t), Equals(sort2, s2, t2)) => sort == sort2 && s == s2 && t == t2
      case _ => false
    }

    override def constructInstanceAndSubst(frm: Formula): Option[(Formula, List[SubstitutionPair])] = frm match {
      case LessEqual(sort, f, g) =>
        // TODO check that axiom is of the expected form s<=t <-> (s < t | s=t)
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance: s<=t <-> (s < t | s=t)
        val h = Or(LessThan(sort, f, g), Equals(sort, f, g))
        val axiomInstance = Equiv(frm, h)

        Some(axiomInstance, subst)
      case Or(LessThan(sort, f, g), Equals(sort2, f2, g2)) if sort == sort2 && f == f2 && g == g2 =>
        // TODO check that axiom is of the expected form s<=t <-> (s < t | s=t)
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance: s<=t <-> (s < t | s=t)
        val h = LessEqual(sort, f, g)
        val axiomInstance = Equiv(h, frm)

        Some(axiomInstance, subst)
    }
  }

  /**
   * Creates a new axiom tactic for flipping >=
   * @return The axiom tactic.
   */
  def GreaterEqualFlipT = new AxiomTactic(">= flip", ">= flip") {
    override def applies(f: Formula): Boolean = f match {
      case GreaterEqual(_, _, _) => true
      case LessEqual(_, _, _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(frm: Formula): Option[(Formula, List[SubstitutionPair])] = frm match {
      case GreaterEqual(sort, f, g) =>
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance
        val h = LessEqual(sort, g, f)
        val axiomInstance = Equiv(frm, h)

        Some(axiomInstance, subst)
      case LessEqual(sort, f, g) =>
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, g), SubstitutionPair(aG, f))

        // construct axiom instance
        val h = GreaterEqual(sort, g, f)
        val axiomInstance = Equiv(h, frm)

        Some(axiomInstance, subst)
    }
  }

  /**
   * Creates a new axiom tactic for flipping >
   * @return The axiom tactic.
   */
  def GreaterThanFlipT = new AxiomTactic("> flip", "> flip") {
    override def applies(f: Formula): Boolean = f match {
      case GreaterThan(_, _, _) => true
      case LessThan(_, _, _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(frm: Formula): Option[(Formula, List[SubstitutionPair])] = frm match {
      case GreaterThan(sort, f, g) =>
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, f), SubstitutionPair(aG, g))

        // construct axiom instance
        val h = LessThan(sort, g, f)
        val axiomInstance = Equiv(frm, h)

        Some(axiomInstance, subst)
      case LessThan(sort, f, g) =>
        // construct substitution
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        val subst = List(SubstitutionPair(aF, g), SubstitutionPair(aG, f))

        // construct axiom instance
        val h = GreaterThan(sort, g, f)
        val axiomInstance = Equiv(h, frm)

        Some(axiomInstance, subst)
    }
  }


  def NegateGreaterThanT = new PositionTactic("> negate") {
    import TacticLibrary.TacticHelper.getFormula
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

  def NegateLessEqualsT = new PositionTactic("<= negate") {
    import TacticLibrary.TacticHelper.getFormula
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

    import TacticLibrary.TacticHelper.getFormula
    import TacticLibrary.locate
    import PropositionalTacticsImpl.{kModalModusPonensT, NotT, ImplyT}
    import FOQuantifierTacticsImpl.skolemizeT
    import TacticLibrary.abstractionT
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
        case Rel(_, _, _) => true
        case Not(Neg(_, _, _)) => true
        case _ => false
      }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode) = applies(node.sequent, p)

      import PropositionalTacticsImpl.{cutT, AxiomCloseT}
      import scala.language.postfixOps

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
            ((prepareKMP & debugT("Prepared KMP") & kModalModusPonensT(ps0) & abstractionT(ps0) & hideT(ps0) &
              skolemizeT(ps0) & ImplyT(ps0) & TacticLibrary.propositional)*)
              | TacticLibrary.propositional) & debugT("AFTER K/PROP") &
            locate(baseTactic) & locate(NotT) & (AxiomCloseT | debugT("BAD 1") & stopT)
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