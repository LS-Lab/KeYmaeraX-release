package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import TacticLibrary.{universalClosure,closeT,hideT,CloseTrueT}
import BuiltinHigherTactics.stepAt
import PropositionalTacticsImpl.{AndLeftT,NotLeftT,EquivLeftT}
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
   * Tactic to hide unnecessary equations in the antecedent.
   * @return The tactic.
   */
  protected[tactics] def hideUnnecessaryLeftEqT: Tactic = new ConstructionTactic("Hide Equations") {

    import Helper.names

    def collectEquations(s: Sequent): Seq[(Int, Term, Term)] =
      (for (i <- 0 until s.ante.length)
      yield s.ante(i) match {
          case Equals(_, a, b) if names(a).intersect(names(b)).isEmpty => Some((i, a, b))
          case _ => None
        }
        ).flatten

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val eqS: Seq[(Int, Term, Term)] = collectEquations(node.sequent)
      val s = node.sequent
      val anteNames = for (i <- 0 until s.ante.length)
      yield (i, Helper.certainlyFreeNames(s.ante(i)))

      val succNames = s.succ.map(Helper.certainlyFreeNames(_)).flatten

      val res = (for ((i, l, r) <- eqS)
      yield if (succNames.contains(l)
          || anteNames.filter((j: (Int, Set[NamedSymbol])) => i != j._1).map(_._2).flatten.contains(l)) None
        else Some(i)
        ).flatten.sortWith((i: Int, j: Int) => i > j)
      if (res.isEmpty) Some(NilT) else Some(res.map((i: Int) => hideT(AntePosition(i))).reduce(seqT(_, _)))
    }

    override def applicable(node: ProofNode): Boolean = true
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

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case Equals(sort, s, t) =>
        // TODO check that axiom is of the expected form s=t <-> !(s != t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s=t <-> !(s!=t)
        val g = Not(NotEquals(sort, s, t))
        val axiomInstance = Equiv(f, g)

        Some(axiomInstance, subst)
      case Not(NotEquals(sort, s, t)) =>
        // TODO check that axiom is of the expected form s=t <-> !(s != t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s=t <-> !(s!=t)
        val g = Equals(sort, s, t)
        val axiomInstance = Equiv(g, f)

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

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case LessThan(sort, s, t) =>
        // TODO check that axiom is of the expected form s<t <-> !(s >= t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s<t <-> !(s>=t)
        val g = Not(GreaterEqual(sort, s, t))
        val axiomInstance = Equiv(f, g)

        Some(axiomInstance, subst)
      case Not(GreaterEqual(sort, s, t)) =>
        // TODO check that axiom is of the expected form s<t <-> !(s >= t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s<t <-> !(s>=t)
        val g = LessThan(sort, s, t)
        val axiomInstance = Equiv(g, f)

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

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case LessEqual(sort, s, t) =>
        // TODO check that axiom is of the expected form s<=t <-> (s < t | s=t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s<=t <-> (s < t | s=t)
        val g = Or(LessThan(sort, s, t), Equals(sort, s, t))
        val axiomInstance = Equiv(f, g)

        Some(axiomInstance, subst)
      case Or(LessThan(sort, s, t), Equals(sort2, s2, t2)) if sort == sort2 && s == s2 && t == t2 =>
        // TODO check that axiom is of the expected form s<=t <-> (s < t | s=t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s<=t <-> (s < t | s=t)
        val g = LessEqual(sort, s, t)
        val axiomInstance = Equiv(g, f)

        Some(axiomInstance, subst)
    }
  }

  /**
   * Creates a new axiom tactic for splitting >=: s>=t <-> s > t | s=t
   * @return The axiom tactic.
   */
  def GreaterEqualSplitT = new AxiomTactic(">=", ">=") {
    override def applies(f: Formula): Boolean = f match {
      case GreaterEqual(_, _, _) => true
      case Or(GreaterThan(sort, s, t), Equals(sort2, s2, t2)) => sort == sort2 && s == s2 && t == t2
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case GreaterEqual(sort, s, t) =>
        // TODO check that axiom is of the expected form s>=t <-> (s > t | s=t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s>=t <-> (s > t | s=t)
        val g = Or(GreaterThan(sort, s, t), Equals(sort, s, t))
        val axiomInstance = Equiv(f, g)

        Some(axiomInstance, subst)
      case Or(GreaterThan(sort, s, t), Equals(sort2, s2, t2)) if sort == sort2 && s == s2 && t == t2 =>
        // TODO check that axiom is of the expected form s>=t <-> (s > t | s=t)
        // construct substitution
        val aS = Variable("s", None, sort)
        val aT = Variable("t", None, sort)
        val subst = Substitution(List(SubstitutionPair(aS, s), SubstitutionPair(aT, t)))

        // construct axiom instance: s>=t <-> (s > t | s=t)
        val g = GreaterEqual(sort, s, t)
        val axiomInstance = Equiv(g, f)

        Some(axiomInstance, subst)
    }
  }

  def NegateGreaterThanT = new PositionTactic("> negate") {
    override def applies(s: Sequent, p: Position): Boolean = {
      s(p) match {
        case GreaterThan(_, _, _) => true
        case Not(LessEqual(_, _, _)) => true
        case _ => false
      }
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      import PropositionalTacticsImpl.{cutT, NotRightT, AxiomCloseT, OrRightT, OrLeftT}
      import scala.language.postfixOps
      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case GreaterThan(sort, s, t) =>
          val cutSPos = SuccPosition(node.sequent.succ.length)
          val cutAPos = AntePosition(node.sequent.ante.length)
          if (p.isAnte) {
            Some(
              cutT(Some(Not(LessEqual(sort, s, t)))) &
                onBranch(
                  (cutShowLbl, NotRightT(cutSPos) & LessEqualSplitT(cutAPos) & OrLeftT(cutAPos) /* TODO */),
                  (cutUseLbl, hideT(p))
                )
            )
          } else {
            Some(
              cutT(Some(Not(LessEqual(sort, s, t)))) &
                onBranch(
                  (cutShowLbl, hideT(p)),
                  (cutUseLbl, NotLeftT(cutAPos) & LessEqualSplitT(cutSPos) & OrRightT(cutSPos) &
                    NegateLessThanT(cutSPos) & NotRightT(new SuccPosition(cutSPos.index + 1)) &
                    GreaterEqualSplitT(cutAPos) & OrLeftT(cutAPos) & AxiomCloseT))
            )
          }
        case Not(LessEqual(sort, s, t)) =>
          val sPos = SuccPosition(node.sequent.succ.length)
          val aPos = AntePosition(node.sequent.ante.length)
          if (p.isAnte) Some(NotLeftT(p) /* TODO */)
          else Some(NotRightT(p) /* TODO */)
      }
    }
  }

  def NegateBinaryRelationT[T: Manifest](name: String, rel: T => Option[(Sort, Term, Term)],
                                         neg: T => Option[(Sort, Term, Term)],
                                         negFactory: (Sort, Term, Term) => Formula,
                                         baseTactic: PositionTactic) = new PositionTactic(name) {
    class Unapplyer(f: T => Option[(Sort, Term, Term)]) {
      def unapply(a: Any): Option[(Sort, Term, Term)] = {
        if (manifest[T].runtimeClass.isInstance(a)) f(a.asInstanceOf[T]) else None
      }
    }

    val Rel = new Unapplyer(rel)
    val Neg = new Unapplyer(neg)

    override def applies(s: Sequent, p: Position): Boolean = {
      s(p) match {
        case Rel(_, _, _) => true
        case Not(Neg(_, _, _)) => true
        case _ => false
      }
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      import PropositionalTacticsImpl.{cutT, NotRightT, AxiomCloseT}
      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Rel(sort, s, t) =>
          val cutSPos = SuccPosition(node.sequent.succ.length)
          val cutAPos = AntePosition(node.sequent.ante.length)
          if (p.isAnte) {
            Some(
              cutT(Some(Not(negFactory(sort, s, t)))) &
                onBranch(
                  (cutShowLbl, NotRightT(cutSPos) & baseTactic(cutAPos) & NotLeftT(cutAPos) & AxiomCloseT),
                  (cutUseLbl, hideT(p)))
            )
          } else {
            Some(
              cutT(Some(Not(negFactory(sort, s, t)))) &
                onBranch(
                  (cutShowLbl, hideT(p)),
                  (cutUseLbl, NotLeftT(cutAPos) & baseTactic(cutSPos) & NotRightT(cutSPos) & AxiomCloseT))
            )
          }
        case Not(Neg(sort, s, t)) =>
          val sPos = SuccPosition(node.sequent.succ.length)
          val aPos = AntePosition(node.sequent.ante.length)
          if (p.isAnte) Some(NotLeftT(p) & baseTactic(sPos) & NotRightT(sPos))
          else Some(NotRightT(p) & baseTactic(aPos) & NotLeftT(aPos))
      }
    }
  }

  /**
   * Creates a new tactic for negating =: s!=t <-> !(s=t)
   * @return The tactic.
   */
  def NegateNotEqualsT = NegateBinaryRelationT("!= negate", NotEquals.unapply, Equals.unapply, Equals.apply,
    NegateEqualsT)

  /**
   * Creates a new tactic for negating >=: s < t <-> !(s>=t)
   * @return The tactic.
   */
  def NegateGreaterEqualsT = NegateBinaryRelationT(">= negate", GreaterEqual.unapply, LessThan.unapply, LessThan.apply,
    NegateLessThanT)
}