package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.AxiomTactic
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import PropositionalTacticsImpl.{hideT,AxiomCloseT,ImplyLeftT,ImplyRightT,cutT,AndRightT}
import TacticLibrary.{kModalModusPonensT,abstractionT,onBranch,Generator}
import SearchTacticsImpl.{locateSucc,locateAnte}

import scala.collection.immutable.{List,Seq}

/**
 * Implementation of tactics for handling hybrid programs.
 */
object HybridProgramTacticsImpl {

  /** *******************************************
    * Axiom Tactics
    * *******************************************
    */

  /**
   * Creates a new axiom tactic for box assignment [x := t;]
   * @return The axiom tactic.
   */
  protected[tactics] def boxAssignT: PositionTactic = new AxiomTactic("[:=] assignment equal", "[:=] assignment equal") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Assign(Variable(_, _,_), _), _) => true
      case _ => false
    }

    /**
     * Replace the old variable o by the new variable n.
     */
    def replace(f: Formula)(o: Variable, n: Variable): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case Forall(v, fa) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) n else name ), fa))
        case Exists(v, fa) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) n else name ), fa))
        case BoxModality(Assign(x: Variable, t), po) => if(x == o) Right(BoxModality(Assign(n, t), po)) else Right(e)
        case DiamondModality(Assign(x: Variable, t), po) => if(x == o) Right(DiamondModality(Assign(n, t), po)) else Right(e)
        case _ => Left(None)
      }
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
    }, f) match {
      case Some(g) => g
      case None => throw new IllegalStateException("Replacing one variable by another should not fail")
    }

    override def constructInstanceAndSubst(f: Formula, axiom: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(Assign(x:Variable, t), p) =>
        // construct substitution
        val aX = Variable("x", None, Real)
        val aT = Variable("t", None, Real)
        val aP = Function("p", None, Real, Bool)
        val l = List(new SubstitutionPair(aT, t), new SubstitutionPair(ApplyPredicate(aP, x), p))
        // construct a new name for the quantified variable
        val vars = Helper.names(f).map(n => (n.name, n.index)).filter(_._1 == x.name)
        require(vars.size > 0)
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
        val xx = Variable(x.name, tIdx, x.sort)


        // construct axiom instance: [x:=t]p(x) <-> \forall x_tIdx . (x_tIdx=t -> p(x_tIdx))
        val g = Forall(Seq(xx), Imply(Equals(Real, xx,t), replace(p)(x, xx)))
        val axiomInstance = Equiv(f, g)
        def alpha(left: Boolean) = new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(Assign(_, _), _), Forall(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              if(left)
                Some(TacticLibrary.alphaRenamingT(x.name, x.index, "x", None)(p.first)
                  & TacticLibrary.alphaRenamingT(xx.name, xx.index, "x", None)(p.second))
              else
                Some(TacticLibrary.alphaRenamingT(xx.name, xx.index, "x", None)(p.second))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
        //@TODO Also rename the quantified variable of the \forall x in the assignment axiom.
        // rename to match axiom if necessary
        val Equiv(lef, right) = axiom
        val (ax, cont) = if (x.name == "x" && x.index == None) (Equiv(lef, replace(right)(aX, xx)), Some(alpha(left = false))) else {
          (Equiv(replace(lef)(aX, x), replace(right)(aX, xx)), Some(alpha(left = true)))
        }
        Some(ax, axiomInstance, Substitution(l), cont)
      case _ => None
    }

  }

  /**
   * Creates a new axiom tactic for test [?H].
   * @return The new tactic.
   */
  protected[tactics] def boxTestT: PositionTactic = new AxiomTactic("[?] test", "[?] test") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Test(_), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Test(h), p) =>
        // construct substitution
        val aH = PredicateConstant("H")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aH, h), new SubstitutionPair(aP, p))
        // construct axiom instance: [?H]p <-> (H -> p).
        val g = Imply(h, p)
        val axiomInstance = Equiv(f, g)
        Some(axiomInstance, Substitution(l))
      case _ => None
    }

  }

  /**
   * Creates a new axiom tactic for non-deterministic assignment [x := *].
   * @return The new tactic.
   */
  protected[tactics] def boxNDetAssign: PositionTactic = new AxiomTactic("[:*] assignment", "[:*] assignment") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(NDetAssign(_), _) => true
      case _ => false
    }

    def replace(f: Formula)(o: Variable, n: Variable): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case Forall(v, fa) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) n else name ), fa))
        case Exists(v, fa) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) n else name ), fa))
        case _ => Left(None)
      }
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
    }, f) match {
      case Some(g) => g
      case None => throw new IllegalStateException("Replacing one variable by another should not fail")
    }

    override def constructInstanceAndSubst(f: Formula, axiom: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(NDetAssign(x), p) if Variable.unapply(x).isDefined =>
        val v = x.asInstanceOf[Variable]
        // construct substitution
        val aX = Variable("x", None, Real)
        val aP = Function("p", None, Real, Bool)
        val l = List(new SubstitutionPair(ApplyPredicate(aP, x), p))
        // construct axiom instance: [x:=*]p(x) <-> \forall x. p(x).
        val g = Forall(Seq(v), p)
        val axiomInstance = Equiv(f, g)
        val alpha = new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(NDetAssign(_), _), Forall(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(TacticLibrary.alphaRenamingT(v.name, v.index, "x", None)(p.first)
                & TacticLibrary.alphaRenamingT(v.name, v.index, "x", None)(p.second))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
        // rename to match axiom if necessary
        val (ax, cont) = if(v.name != "x" || v.index != None) (replace(axiom)(aX, v), Some(alpha)) else (axiom, None)
        Some(ax, axiomInstance, Substitution(l), cont)
      case _ => None
    }
  }

  /**
   * Creates a new axiom tactic for sequential composition [;]
   * @return The new tactic.
   */
  protected[tactics] def boxSeqT: PositionTactic = new AxiomTactic("[;] compose", "[;] compose") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Sequence(_, _), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Sequence(a, b), p) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aB, b), new SubstitutionPair(aP, p))
        // construct axiom instance: [ a; b ]p <-> [a][b]p.
        val g = BoxModality(a, BoxModality(b, p))
        val axiomInstance = Equiv(f, g)
        Some(axiomInstance, Substitution(l))
      case _ => None
    }

  }

  /**
   * Creates a new axiom tactic for box induction [*] I induction
   * @return The new tactic.
   */
  protected[tactics] def boxInductionT: PositionTactic = new AxiomTactic("I induction", "I induction") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Loop(_), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Loop(a), p) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aP, p))
        // construct axiom instance: (p & [a*](p -> [a] p)) -> [a*]p
        val g = And(p, BoxModality(Loop(a), Imply(p, BoxModality(a, p))))
        val axiomInstance = Imply(g, f)
        Some(axiomInstance, Substitution(l))
      case _ => None
    }

  }

  /**
   * Creates a new axiom tactic for box choice [++].
   * @return The new tactic.
   */
  protected[tactics] def boxChoiceT: PositionTactic = new AxiomTactic("[++] choice", "[++] choice") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Choice(_, _), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Choice(a, b), p) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aB, b), new SubstitutionPair(aP, p))
        // construct axiom instance: [ a ++ b ]p <-> [a]p & [b]p.
        val g = And(BoxModality(a, p), BoxModality(b, p))
        val axiomInstance = Equiv(f, g)
        Some(axiomInstance, Substitution(l))
      case _ => None
    }

  }

  /** *******************************************
    * Rule Tactics
    * *******************************************
    */

  /**
   * Creates a new position tactic to apply the induction rule.
   * @param inv The invariant.
   * @return The position tactic.
   */
  protected[tactics] def inductionT(inv: Option[Formula]): PositionTactic = new PositionTactic("induction") {
    def getBody(g: Formula): Option[Program] = g match {
      case BoxModality(Loop(a), _) => Some(a)
      case _ => None
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && getBody(s(p)).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def ind(cutSPos: Position, cont: Tactic) = boxInductionT(cutSPos) & AndRightT(cutSPos) & (LabelBranch("Close Next"), abstractionT(cutSPos) & hideT(cutSPos) & cont)
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
          val useCase = prepareKMP & hideT(cutAPos) & kModalModusPonensT(cutSPos) & abstractionT(cutSPos) & hideT(cutSPos) & LabelBranch(indUseCaseLbl)
          val branch1Tactic = ImplyLeftT(cutAPos) & (hideT(p) & LabelBranch(indInitLbl), useCase)
          val branch2Tactic = hideT(p) &
            ImplyRightT(cutSPos) &
            ind(cutSPos, hideT(cutAPos) & LabelBranch(indStepLbl)) &
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
      case Some(inv) => inductionT(Some(inv)).applies(s, p)
      case None => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = gen(node.sequent, p) match {
        case Some(inv) => Some(inductionT(Some(inv))(p))
        case None => None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /**
   * Creates a new position tactic for the assignment rule.
   * @return The assignment rule tactic.
   */
  protected[tactics] def assignment = new PositionTactic("Assignment") {
    // for now only on top level
    override def applies(s: Sequent, p: Position): Boolean = {
      (p.inExpr == HereP) && ((if (p.isAnte) s.ante else s.succ)(p.index) match {
        case BoxModality(Assign(Variable(_, _, _), _), _) => true
        case DiamondModality(Assign(Variable(_, _, _), _), _) => true
        case _ => false
      })
    }

    override def apply(p: Position): Tactic = Tactics.weakSeqT(TacticLibrary.uniquify(p), new ApplyRule(new AssignmentRule(p)) {
      override def applicable(n: ProofNode): Boolean = applies(n.sequent, p)
    })
  }

  // it would be great if we could access the same position to apply the imply right rule
  // FIXME: this only works for toplevel positions since there the positions are stable
  private def assignmentFindImpl = locateSucc(assignment & ImplyRightT) | locateAnte(assignment & ImplyLeftT)
}
