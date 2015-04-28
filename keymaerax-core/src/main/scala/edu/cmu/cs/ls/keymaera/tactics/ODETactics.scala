package edu.cmu.cs.ls.keymaera.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AxiomTactic.{uncoverAxiomT,uncoverConditionalAxiomT,axiomLookupBaseT}
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.skolemizeT
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl.boxAssignT
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.AndRightT
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.AxiomCloseT
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.EquivRightT
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.ImplyRightT
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{abstractionT, globalAlphaRenamingT, debugT, arithmeticT}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.{getFormula, freshNamedSymbol}
import AlphaConversionHelper._
import edu.cmu.cs.ls.keymaera.tools.{Mathematica, Tool}

import scala.collection.immutable.List
import scala.language.postfixOps

/**
 * Created by smitsch on 1/9/15.
 * @author Stefan Mitsch
 * @author aplatzer
 */
object ODETactics {

  /**
   * Creates a new tactic to solve ODEs in diamonds. The tactic introduces ghosts for initial values, asks Mathematica
   * for a solution, and proves that the returned solution is indeed correct.
   * @return The newly created tactic.
   */
//  def diamondDiffSolveT: PositionTactic = new PositionTactic("<'> differential solution") {
//    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
//      case DiamondModality(ODESystem(_, ODEProduct(AtomicODE(Derivative(_, _: Variable), _), _: EmptyODE), _), _) => true
//      case _ => false
//    }
//
//    override def apply(p: Position): Tactic = new Tactic("") {
//      def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
//
//      def apply(tool: Tool, node: ProofNode) = {
//        val t = constructTactic(p)
//        t.scheduler = Tactics.MathematicaScheduler
//        t.continuation = continuation
//        t.dispatch(this, node)
//      }
//    }
//
//    private def constructTactic(p: Position) = new ConstructionTactic(name) {
//      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
//
//      private def primedSymbols(ode: DifferentialProgram) = {
//        var primedSymbols = Set[Variable]()
//        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
//          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
//            case Derivative(_, ps: Variable) => primedSymbols += ps; Left(None)
//            case Derivative(_, _) => throw new IllegalArgumentException("Only derivatives of variables supported")
//            case _ => Left(None)
//          }
//        }, ode)
//        primedSymbols
//      }
//
//      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
//        def createTactic(ode: DifferentialProgram, solution: Term, time: Variable, iv: Map[Variable, Variable],
//                         diffEqPos: Position) = {
//          val primed = primedSymbols(ode)
//          val initialGhosts = primed.foldLeft(NilT)((a, b) =>
//            a & (discreteGhostT(Some(iv(b)), b)(diffEqPos) & boxAssignT(skolemizeToFnT(_))(diffEqPos)))
//
//          def g(t: Term): Term = SubstitutionHelper.replaceFree(solution)(time, t)
//
//          // equiv of diamondDiffSolveAxiomT is going to appear after all the ghost equalities
//          val axiomInstPos = AntePosition(node.sequent.ante.length + primed.size)
//          val solve = diamondDiffSolveAxiomT(g)(p) & onBranch(
//            (axiomUseLbl, AndRightT(p) && (
//              arithmeticT | debugT("Solution not valid initially") & stopT,
//              cohideT(p) & assertT(0,1) & SyntacticDerivationInContext.SyntacticDerivationT(p) & diffEffectT(p))
//              & goedelT & boxDerivativeAssignT(p) & (arithmeticT | debugT("Solution not provable") & stopT)),
//            (axiomShowLbl, equivRewriting(axiomInstPos, p))
//          )
//
//          Some(initialGhosts & solve)
//        }
//
//        val diffEq = getFormula(node.sequent, p) match {
//          case DiamondModality(ode: DifferentialProgram, _) => ode
//          case _ => throw new IllegalStateException("Checked by applies to never happen")
//        }
//
//        val iv = primedSymbols(diffEq).map(v => v -> freshNamedSymbol(v, node.sequent(p))).toMap
//        // boxAssignT will increment the index twice (universal quantifier, skolemization) -> tell Mathematica
//        val ivm = iv.map(e =>  (e._1, Function(e._2.name, Some(e._2.index.get + 2), Unit, e._2.sort))).toMap
//
//        val time = Variable("t", None, Real)
//        val theSolution = tool match {
//          case x: Mathematica => x.diffSolver.diffSol(diffEq, time, ivm)
//          case _ => None
//        }
//
//        val diffEqPos = SuccPosition(p.index)
//        theSolution match {
//          case Some(Equals(_, _, s)) => createTactic(diffEq, s, time, iv, diffEqPos)
//          case _ => None
//        }
//      }
//    }
//  }

  /**
   * Returns a tactic for diamond ODE solving. This tactic results in two open branches remaining: show that the
   * solution is a solution; use the solution.
   * @param g The symbolic solution of the ODE.
   * @return The newly created tactic.
   */
//  def diamondDiffSolveAxiomT(g: Term => Term): PositionTactic = new AxiomTactic("<'> differential solution", "<'> differential solution") {
//    override def applies(f: Formula): Boolean = f match {
//      case DiamondModality(ODESystem(_, ODEProduct(AtomicODE(Derivative(_, _: Variable), _), _: EmptyODE), _), _) => true
//      case _ => false
//    }
//
//    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, List[SubstitutionPair],
//      Option[PositionTactic], Option[PositionTactic])] = f match {
//      case DiamondModality(ODESystem(_, ODEProduct(AtomicODE(Derivative(Real, x: Variable), c), _: EmptyODE), h), p) =>
//        // (<x'=f(x)&H(x);>p(x) <-> \exists t . (t>=0 & (\forall s . ((0<=s&s=t) -> <x:=g(s);>H(x))) & <x:=g(t);>p(x))) <- (g(0)=x & [t'=1]g(t)'=f(g(t)))
//        val t = Variable("t", None, Real)
//        val s = Variable("s", None, Real)
//
//        val checkSol = And(
//          Equals(Real, g(Number(0)), x),
//          BoxModality(ODESystem(ODEProduct(AtomicODE(Derivative(Real, t), Number(1))), True),
//            Equals(Real, Derivative(Real, g(t)), SubstitutionHelper.replaceFree(c)(x, g(t))))
//        )
//        val equiv = Equiv(f, Exists(t::Nil, And(
//          GreaterEqual(Real, t, Number(0)),
//          And(
//            Forall(s::Nil, Imply(
//              And(LessEqual(Real, Number(0), s), LessEqual(Real, s, t)),
//              DiamondModality(Assign(x, g(s)), h)
//            )),
//            DiamondModality(Assign(x, g(t)), p)
//          )
//        )))
//
//        val axiomInstance = Imply(checkSol, equiv)
//
//        // construct substitution
//        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
//        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
//        val aF = Apply(Function("f", None, Real, Real), CDot)
//        val aG = Apply(Function("g", None, Real, Real), CDot)
//        val l = SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(x, CDot)) ::
//          SubstitutionPair(aH, SubstitutionHelper.replaceFree(h)(x, CDot)) ::
//          SubstitutionPair(aF, SubstitutionHelper.replaceFree(c)(x, CDot)) ::
//          SubstitutionPair(aG, g(CDot)) :: Nil
//
//        // rename to match axiom if necessary
//        val aX = Variable("x", None, Real)
//        val alpha = new PositionTactic("Alpha") {
//          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
//            case Equiv(_, Exists(_, _)) => true
//            case _ => false
//          }
//
//          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
//            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
//              Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))
//
//            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
//          }
//        }
//
//        val (axiom, cont) =
//          if (x.name != aX.name || x.index != aX.index) (replace(ax)(aX, x), Some(alpha))
//          else (ax, None)
//
//        Some(axiom, axiomInstance, l, None, cont)
//      case _ => None
//    }
//  }

  /**
   * Creates a new tactic to handle differential effect atomic/system.
   * @return The newly created tactic
   */
  def diffEffectT: PositionTactic = new PositionTactic("DE differential effect") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Box(ODESystem(_, _), _) => true
      case _ => false
    }

    // TODO just call appropriate tactic without scheduler (needs base class change: inspect sequent)
    override def apply(p: Position): Tactic = diffEffectAtomicT(p) | (debugT("Diff effect system") & diffEffectSystemT(p))
  }

  /**
   * Creates a new tactic for the differential effect axiom.
   * @return The newly created tactic
   */
  private def diffEffectAtomicT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), t), q), p) =>
        // [x'=f(x)&q(x);]p(x) <-> [x'=f(x)&q(x);][x':=f(x);]p(x)
        Equiv(fml, Box(ode, Box(DiffAssign(dx, t), p)))
      case _ => False
    }
    uncoverAxiomT("DE differential effect", axiomInstance, _ => diffEffectAtomicBaseT)
  }
  /** Base tactic for diff effect */
  private def diffEffectAtomicBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), t), q), p), _) =>
        val aP = PredOf(Function("p", None, Real, Bool), DotTerm)
        val aQ = PredOf(Function("q", None, Real, Bool), DotTerm)
        val aF = FuncOf(Function("f", None, Real, Real), DotTerm)
        SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(x, DotTerm)) ::
          SubstitutionPair(aQ, SubstitutionHelper.replaceFree(q)(x, DotTerm)) ::
          SubstitutionPair(aF, SubstitutionHelper.replaceFree(t)(x, DotTerm)) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), t), q), p), _) =>
        if (x.name != aX.name || x.index != aX.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              // TODO DiffSymbol :=
              case Equiv(Box(ODESystem(_, _), _), Box(ODESystem(_, _), Box(DiffAssign(DifferentialSymbol(_), _), _))) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(Box(ode@ODESystem(AtomicODE(dx@DifferentialSymbol(x), _), _), _), _) =>
        if (x.name != aX.name || x.index != aX.index) replace(axiom)(aX, x)
        else axiom
    }
    axiomLookupBaseT("DE differential effect", subst, alpha, axiomInstance)
  }

  /**
   * Whether diffSolution will work on the given Formula, because its differential equation is solvable.
   * @todo implement in a reliable way
   */
  def isDiffSolvable(f: Formula) = false

  /**
   * Returns a tactic to use the solution of an ODE as a differential invariant.
   * @param solution The solution. If None, the tactic uses Mathematica to find a solution.
   * @return The tactic.
   */
  def diffSolution(solution: Option[Formula]): PositionTactic = new PositionTactic("differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(odes: DifferentialProgram, _) => true
      case _ => false
    }) && (solution match {
      case Some(f) => true
      case None => MathematicaScheduler.isInitialized
    })

    /**
     * Searches for a time variable (some derivative x'=1) in the specified formula.
     * @param f The formula.
     * @return The time variable, if found. None, otherwise.
     */
    private def findTimeInOdes(f: Formula): Option[Variable] = {
      val odes = f match {
        case Box(prg: DifferentialProgram, _) => prg
        case _ => throw new IllegalStateException("Checked by applies to never happen")
      }

      var timeInOde: Option[Variable] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        import ExpressionTraversal.stop
        override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
          // TODO could be complicated 1
          case AtomicODE(DifferentialSymbol(v), theta) if theta == Number(1) =>
            timeInOde = Some(v); Left(Some(stop))
          case _ => Left(None)
        }
      }, odes)
      timeInOde
    }

    override def apply(p: Position): Tactic = new Tactic("") {
      def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def apply(tool: Tool, node: ProofNode) = {
        import FOQuantifierTacticsImpl.vacuousExistentialQuanT
        import SearchTacticsImpl.onBranch
        import BranchLabels.{equivLeftLbl,equivRightLbl}

        val (time, timeTactic, timeZeroInitially) = findTimeInOdes(node.sequent(p)) match {
          case Some(existingTime) => (existingTime, NilT, false)
          case None =>
            // HACK need some convention for internal names
            val initialTime: Variable = freshNamedSymbol(Variable("k4_t", None, Real), node.sequent)
            // universal quantifier and skolemization in ghost tactic (t:=0) will increment index twice
            val time = Variable(initialTime.name,
              initialTime.index match { case None => Some(1) case Some(a) => Some(a+2) }, initialTime.sort)
            // boxAssignT and equivRight will extend antecedent by 2 -> length + 1
            val lastAntePos = AntePosition(node.sequent.ante.length + 1)
            val introTime = nonAbbrvDiscreteGhostT(Some(initialTime), Number(0))(p) & boxAssignT(p) &
              diffAuxiliaryT(time, Number(0), Number(1))(p) & AndRightT(p) &&
              (EquivRightT(p) & onBranch((equivLeftLbl, vacuousExistentialQuanT(None)(p) &
                                                        AxiomCloseT(lastAntePos, p)),
                                         (equivRightLbl, skolemizeT(lastAntePos) & AxiomCloseT(lastAntePos, p))),
                NilT)

            (time, introTime, true)
        }

        val t = constructTactic(p, time, tIsZero = timeZeroInitially)
        t.scheduler = Tactics.MathematicaScheduler
        val diffSolTactic = timeTactic & t
        diffSolTactic.continuation = continuation
        diffSolTactic.dispatch(this, node)
      }
    }

    private def constructTactic(p: Position, time: Variable, tIsZero: Boolean) = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      private def primedSymbols(ode: DifferentialProgram) = {
        var primedSymbols = Set[Variable]()
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
            case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
            case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
            case _ => Left(None)
          }
        }, ode)
        primedSymbols
      }

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import HybridProgramTacticsImpl.{discreteGhostT, boxAssignT}

        def flattenConjunctions(f: Formula): List[Formula] = {
          var result: List[Formula] = Nil
          ExpressionTraversal.traverse(new ExpressionTraversalFunction {
            override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
              case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
              case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
            }
          }, f)
          result
        }

        def sizeOf[T](s: SetLattice[T]): Int = s.s match {
          case Left(_) => ???
          case Right(ts) => ts.size
        }

        def createTactic(ode: DifferentialProgram, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                         diffEqPos: Position) = {
          val initialGhosts = primedSymbols(ode).foldLeft(NilT)((a, b) =>
            a & (discreteGhostT(Some(iv(b)), b)(diffEqPos) & boxAssignT(skolemizeToFnT(_))(diffEqPos)))

          // flatten conjunctions and sort by number of right-hand side symbols to approximate ODE dependencies
          val flatSolution = flattenConjunctions(solution).
            sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size).reverse

          val cuts = flatSolution.foldLeft(diffWeakenT(p))((a, b) =>
            debugT(s"About to cut in $b at $p") & diffCutT(b)(p) & onBranch(
              (cutShowLbl, debugT(s"Prove Solution using DI at $p") & diffInvariantT(p)),
              (cutUseLbl, a)))

          Some(initialGhosts && cuts)
        }

        val diffEq = node.sequent(p) match {
          case Box(ode: DifferentialProgram, _) => ode
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        val iv = primedSymbols(diffEq).map(v => v -> freshNamedSymbol(v, node.sequent(p))).toMap
        // boxAssignT will increment the index twice (universal quantifier, skolemization) -> tell Mathematica
        val ivm = iv.map(e =>  (e._1, Function(e._2.name, Some(e._2.index.get + 2), Unit, e._2.sort))).toMap

        val theSolution = solution match {
          case sol@Some(_) => sol
          case None => tool match {
            case x: Mathematica if x.isInitialized => x.diffSol(diffEq, time, ivm)
            case _ => None
          }
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          // add relation to initial time
          case Some(s) =>
            val sol = And(if (tIsZero) s
                          else SubstitutionHelper.replaceFree(s)(time, Minus(time, FuncOf(ivm(time), Nothing))),
                          GreaterEqual(time, FuncOf(ivm(time), Nothing)))
            createTactic(diffEq, sol, time, iv, diffEqPos)
          case None => None
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Weakening Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Returns the differential weaken tactic.
   * @return The tactic.
   */
  def diffWeakenT: PositionTactic = new PositionTactic("DW differential weakening") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(ODESystem(_, _), _) => true
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ODESystem(_, _), _) =>
          Some(diffWeakenAxiomT(p) & abstractionT(p) & debugT("Skolemize in DiffWeaken") & (skolemizeT(p)*)
            & assertT(s => s(p) match { case Forall(_, _) => false case _ => true }, "Diff. weaken did not skolemize all quantifiers"))
        case _ => None
      }
    }
  }

  def diamondDiffWeakenAxiomT: PositionTactic = new ByDualityAxiomTactic(diffWeakenAxiomT)

  def diffWeakenAxiomT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(c, h), p) => Equiv(fml, Box(ode, Imply(h, p)))
      case _ => False
    }
    uncoverAxiomT("DW differential weakening", axiomInstance, _ => diffWeakenAxiomBaseT)
  }
  /** Base tactic for diff weaken */
  private def diffWeakenAxiomBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(Box(ode@ODESystem(c, h), p), _) =>
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        SubstitutionPair(aP, p) :: SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: Nil
    }
    axiomLookupBaseT("DW differential weakening", subst, _ => NilPT, (f, ax) => ax)
  }

  //////////////////////////////
  // Differential Cuts
  //////////////////////////////
  
  /**
   * Applies a differential cut with the given cut formula.
   * @author aplatzer
   */
  def diffCutT(diffcut: Formula): PositionTactic = new PositionTactic("DC differential cut") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(_: ODESystem, _) => true
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(ODESystem(_, _), _) =>
          val anteLength = node.sequent.ante.length
          Some(diffCutAxiomT(diffcut)(p) & onBranch(
            (axiomUseLbl,
              /* use axiom: here we have to show that our cut was correct */ LabelBranch(cutShowLbl)),
            (axiomShowLbl,
              /* show axiom: here we continue with equiv rewriting so that desired result remains */
              equivRewriting(AntePosition(anteLength), p) & LabelBranch(cutUseLbl) /*@TODO equalityRewriting(whereTheEquivalenceWentTo, p) apply the remaining diffcut equivalence to replace the original p */)
          ))
        case _ => None
      }
    }
  }

  /**
   * Adds an instance of the differential cut axiom for the given cut formula.
   * @author aplatzer
   * @author Stefan Mitsch
   */
  private def diffCutAxiomT(diffcut: Formula): PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ODESystem(c, h), p) =>
        val showDC = Box(ODESystem(c, h), diffcut)
        val useDC = Box(ODESystem(c, And(h,diffcut)), p)
        Imply(showDC, Equiv(fml, useDC))
      case _ => False
    }

    def condT: PositionTactic = new PositionTactic("Label") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = LabelBranch(cutShowLbl)
    }

    uncoverConditionalAxiomT("DC differential cut", axiomInstance, _ => condT, _ => diffCutAxiomBaseT(diffcut))
  }
  /** Base tactic for differential cuts */
  private def diffCutAxiomBaseT(diffcut: Formula): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(_, Equiv(Box(ODESystem(c, h), p), _)) =>
        val aC = DifferentialProgramConst("c")
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aR = PredOf(Function("r", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aH, h) :: SubstitutionPair(aP, p):: SubstitutionPair(aR, diffcut) :: Nil
    }
    axiomLookupBaseT("DC differential cut", subst, _ => NilPT, (f, ax) => ax)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Auxiliary Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def diffAuxiliaryT(x: Variable, t: Term, s: Term, psi: Option[Formula] = None): PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(c, h), p) if !StaticSemantics(ode).bv.contains(x) &&
          !StaticSemantics.symbols(t).contains(x) && !StaticSemantics.symbols(s).contains(x) =>
        // construct instance
        val q = psi match { case Some(pred) => pred case None => p }
        val lhs = And(Equiv(p, Exists(x :: Nil, q)), Box(ODESystem(DifferentialProduct(c,
          AtomicODE(DifferentialSymbol(x), Plus(Times(t, x), s))), h), q))
        Imply(lhs, fml)
      case _ => False
    }
    uncoverAxiomT("DA differential ghost", axiomInstance, _ => diffAuxiliaryBaseT(x, t, s, psi))
  }

  private def diffAuxiliaryBaseT(x: Variable, t: Term, s: Term, psi: Option[Formula]): PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(_, Box(ode@ODESystem(c, h), p)) =>
        val q = psi match { case Some(pred) => pred case None => p }
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aQ = PredOf(Function("q", None, Real, Bool), Anything)
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        val aC = DifferentialProgramConst("c")
        val aS = FuncOf(Function("s", None, Unit, Real), Nothing)
        val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
        SubstitutionPair(aP, p) :: SubstitutionPair(aQ, q) :: SubstitutionPair(aH, h) ::
          SubstitutionPair(aC, c) :: SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = {
      if (x.name != aX.name || x.index != aX.index) {
        new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Imply(And(Equiv(_, Exists(_, _)), _), _) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
      } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      if (x.name != aX.name || x.index != aX.index) replaceFree(axiom)(aX, x, None)
      else axiom
    }
    axiomLookupBaseT("DA differential ghost", subst, alpha, axiomInstance)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // DI for Systems of Differential Equations
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def diffInvariantAxiomT: PositionTactic = {
    def axiomInstance(fml: Formula): Formula = fml match {
      case Box(ode@ODESystem(c, h), p) =>
        //[c&H]p <- (p & [{c}&H](H->p')
        val g = Imply(h,
          And(p,
            Box(
              ode, DifferentialFormula(p)
            )
          ))
        Imply(g, fml)
      case _ => False
    }
    uncoverAxiomT("DI differential invariant", axiomInstance, _ => diffInvariantAxiomBaseT)
  }
  /** Base tactic for diff invariant */
  private def diffInvariantAxiomBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(Imply(_, And(_, Box(ODESystem(c, h), DifferentialFormula(p)))), _) =>
        val aC = DifferentialProgramConst("c")
        val aP = PredOf(Function("p", None, Real, Bool), Anything)
        val aH = PredOf(Function("H", None, Real, Bool), Anything)
        SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) :: SubstitutionPair(aH, h) :: Nil
    }
    axiomLookupBaseT("DI differential invariant", subst, _ => NilPT, (f, ax) => ax)
  }

  private def diffEffectSystemT: PositionTactic = new PositionTactic("DE differential effect (system)") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (getFormula(s, p) match {
      case Box(ODESystem(cp: DifferentialProduct, _),_) => cp match {
        case DifferentialProduct(AtomicODE(DifferentialSymbol(_), _), _) => true
        case _ => false
      }
      case f => println("Does not apply to: " + f.prettyString()); false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case f@Box(ODESystem(a, h), phi) => a match {
          case cp: DifferentialProduct => cp match {
            case DifferentialProduct(AtomicODE(d@DifferentialSymbol(x), t: Term), c: DifferentialProgram) =>
              val g = Box(
                ODESystem(DifferentialProduct(c, AtomicODE(d, t)), h),
                Box(DiffAssign(d, t), phi)
              )
              val instance = Equiv(f, g)

              //construct substitution
              val aF = FuncOf(Function("f", None, Real, Real), Anything)
              val aH = PredOf(Function("H", None, Real, Bool), Anything)
              val aC = DifferentialProgramConst("c")
              val aP = PredOf(Function("p", None, Real, Bool), Anything)

              val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, phi) ::
                SubstitutionPair(aH, h) :: Nil

              // alpha rename if necessary
              val aX = Variable("x", None, Real)
              val alpha =
                if (x.name != aX.name || x.index != aX.index) new PositionTactic("Alpha") {
                  override def applies(s: Sequent, p: Position): Boolean = s(p) match {
                    case Equiv(Box(ODESystem(_, _), _),
                               Box(ODESystem(_, _), Box(DiffAssign(_: DifferentialSymbol, _), _))) => true
                    case _ => false
                  }

                  override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
                    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                      Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

                    override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
                  }
                } else NilPT

              Some(diffEffectSystemT(instance, subst, alpha, x)(p))
          }
        }
      }
    }
  }
  /** Uncovering differential equation system from context */
  private def diffEffectSystemT(axInstance: Formula, subst: List[SubstitutionPair],
                                alpha: PositionTactic, x: Variable): PositionTactic = {
    uncoverAxiomT("DE differential effect (system)", _ => axInstance, _ => diffEffectSystemBaseT(subst, alpha, x))
  }
  /** Base tactic for DE differential effect (system) */
  private def diffEffectSystemBaseT(subst: List[SubstitutionPair], alpha: PositionTactic,
                                           x: Variable): PositionTactic = {
    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val aX = Variable("x", None, Real)
      if (x.name != aX.name || x.index != aX.index) replace(axiom)(aX, x)
      else axiom
    }
    axiomLookupBaseT("DE differential effect (system)", _ => subst, _ => alpha, axiomInstance)
  }

  /**
   * The "master" DI tactic for differential invariants.
   * @todo no testing yet.
   */
  def diffInvariantT: PositionTactic = new PositionTactic("DI differential invariant") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Box(_: ODESystem, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        node.sequent(p) match {
          case Box(ODESystem(ode, _), _) => {
            val n = {
              var numAtomics = 0
              ExpressionTraversal.traverse(new ExpressionTraversalFunction {
                override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
                  case _: AtomicODE => numAtomics += 1; Left(None)
                  case _ => Left(None)
                }
              }, ode)
              numAtomics
            }

            Some(diffInvariantAxiomT(p) & ImplyRightT(p) & AndRightT(p) & (
              debugT("left branch") & ((AxiomCloseT | PropositionalRightT(p))*) & arithmeticT,
              debugT("right branch") & (diffEffectT(p) * n) & debugT("differential effect complete") &
                debugT("About to NNF rewrite") & NNFRewrite(p.second) && debugT("Finished NNF rewrite") &
                SyntacticDerivationInContext.SyntacticDerivationT(p.second) ~ debugT("Done with syntactic derivation") &
                (boxDerivativeAssignT(p.second)*) & debugT("Box assignments complete") &
                diffWeakenT(p) & debugT("ODE removed") &
                (arithmeticT | NilT) & debugT("Finished result")
            ))
          }
        }
      }
    }
  }
}


