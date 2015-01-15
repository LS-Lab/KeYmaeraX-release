package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ConstructionTactic, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{AndRightT, diffCutT,
  alphaRenamingT, boxNDetAssign, skolemizeT, boxTestT, ImplyRightT}
import Tactics.NilT
import AlphaConversionHelper._

import scala.collection.immutable.List

/**
 * Created by smitsch on 1/9/15.
 * @author Stefan Mitsch
 */
object ODETactics {

  /**
   * Returns a tactic to use the solution of an ODE as a differential invariant.
   * @param solution The solution. If None, the tactic uses Mathematica to find a solution.
   * @return The tactic.
   */
  def diffSolution(solution: Option[Formula]): PositionTactic = new PositionTactic("differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case BoxModality(_: NFContEvolve, _) => true
      case BoxModality(_: ContEvolveProduct, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new Tactic("") {
      def applicable(node : ProofNode) : Boolean = applies(node.sequent, p)
      def apply  (tool : Tool, node : ProofNode) = {
        val t = constructTactic(p)
        t.scheduler = Tactics.MathematicaScheduler
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }

    private def constructTactic(p: Position) = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import BranchLabels.{cutShowLbl, cutUseLbl}
        def createTactic(solution: Formula, diffEqPos: Position) = {
          val cut = diffCutT(solution)(p) & AndRightT(p)
          val proveSol = onBranch(cutShowLbl, NilT/*differentialInduction(diffEqPos)*/)
          val useSol = onBranch(cutUseLbl, diffWeakenT(diffEqPos))
          Some(cut ~ proveSol ~ useSol)
        }

        // HACK assumes presence of variable t and variables for starting values
        // TODO ghost time
        // TODO ghosts for starting values
        val diffEq: Either[NFContEvolve, ContEvolveProduct] = node.sequent(p) match {
          case BoxModality(e: NFContEvolve, _) => Left(e)
          case BoxModality(e: ContEvolveProduct, _) => Right(e)
          case _ => ???
        }

        var actualTime: Variable = null
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          import ExpressionTraversal.stop
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case v@Variable(n, _, _) if n == "t" => actualTime = v.asInstanceOf[Variable]; Left(Some(stop))
            case _ => Left(None)
          }
        }, node.sequent(p))

        val theSolution = solution match {
          case sol@Some(_) => sol
          case None => tool match {
            case x: Mathematica if diffEq.isLeft => x.diffSolver.diffSol(diffEq.left.get, actualTime)
            case x: Mathematica if diffEq.isRight => x.diffSolver.diffSol(diffEq.right.get, actualTime)
            case _ => ???
          }
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          case Some(s) => createTactic(s, diffEqPos)
          case None => ???
        }
      }
    }
  }

  /**
   * Returns the differential weaken tactic.
   * @return The tactic.
   */
  def diffWeakenT: PositionTactic = new PositionTactic("DW differential weaken system") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case BoxModality(_: ContEvolveProduct, _) => true
      case BoxModality(_: NFContEvolve, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps
        node.sequent(p) match {
          case BoxModality(_: ContEvolveProduct, _) => Some(
            // introduce $$ markers
            diffWeakenSystemIntroT(p) &
            // pull out heads until empty
            ((diffWeakenSystemHeadT(p) & boxNDetAssign(p) & skolemizeT(p))*) &
            // remove empty marker and handle tests
            diffWeakenSystemNilT(p) & ((boxTestT(p) & ImplyRightT(p))*)
          )
        }
      }
    }
  }

  /**
   * Returns a tactic to introduce a marker around an ODE for differential weakening.
   * @return The tactic.
   */
  def diffWeakenSystemIntroT: PositionTactic = new AxiomTactic("DW differential weaken system introduce",
      "DW differential weaken system introduce") {
    def applies(f: Formula) = f match {
      case BoxModality(ContEvolveProduct(_, _), _) => true
      case _ => false
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(c: ContEvolveProduct, p) =>
        // construct instance
        val g = BoxModality(IncompleteSystem(c), p)
        val axiomInstance = Imply(g, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aC = ContEvolveProgramConstant("c")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aC, c))

        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  /**
   * Returns a tactic to pull out an ODE from a marked system of differential equations, and to convert
   * that ODE into a nondeterministic assignment and a test of its evolution domain constraint.
   * @return The tactic.
   */
  def diffWeakenSystemHeadT: PositionTactic = new AxiomTactic("DW differential weaken system head",
      "DW differential weaken system head") {
    def applies(f: Formula) = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), _)), _) => true
      case _ => false
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), c)), p) =>
        // construct instance
        val x = d.child match {
          case v: Variable => v
          case _ => throw new IllegalArgumentException("Normal form expects v in v' being a Variable")
        }
        val lhs = BoxModality(NDetAssign(x), BoxModality(IncompleteSystem(c), BoxModality(Test(h), p)))
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aX = Variable("x", None, Real)
        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
        val aT = Apply(Function("f", None, Real, Real), CDot)
        val aC = ContEvolveProgramConstant("c")
        import Substitution.freeVariables
        val l = List(new SubstitutionPair(aH, replace(h)(x, CDot)), new SubstitutionPair(aP, replace(p)(x, CDot)),
                     new SubstitutionPair(aT, replace(t)(x, CDot, Some(freeVariables(t)))), new SubstitutionPair(aC, c))

        // alpha renaming of x if necessary
        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replace(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), cont)
      case _ => None
    }
  }

  /**
   * Returns a tactic to weaken a system of differential equations where only the empty marker $$ remained (i.e., all
   * ODEs are already converted into nondeterministic assignments and tests of the evolution domain constraint).
   * @return The tactic.
   */
  def diffWeakenSystemNilT: PositionTactic = new AxiomTactic("DW differential weaken system nil",
    "DW differential weaken system nil") {
    def applies(f: Formula) = f match {
      case BoxModality(IncompleteSystem(_: EmptyContEvolveProgram), _) => true
      case _ => false
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(_: EmptyContEvolveProgram), BoxModality(b@Test(h), p)) =>
        // construct instance
        val lhs = BoxModality(b, p)
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aH = PredicateConstant("H")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aH, h))

        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  /**
   * Creates an alpha renaming tactic that fits the structure of weakening systems. The tactic renames the old symbol
   * to the new symbol.
   * @param oldSymbol The old symbol.
   * @param newSymbol The new symbol.
   * @return The alpha renaming tactic.
   */
  private def alphaInWeakenSystems(oldSymbol: NamedSymbol, newSymbol: NamedSymbol) = new PositionTactic("Alpha") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Imply(BoxModality(_: NDetAssign, _), BoxModality(_: ContEvolveProgram, _)) => true
      case Imply(BoxModality(_: NDetAssign, _), BoxModality(_: IncompleteSystem, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        Some(alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, None)(p.first)
          & alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, None)(p.second))

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }
}
