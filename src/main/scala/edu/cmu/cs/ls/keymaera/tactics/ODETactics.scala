package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{TacticHelper, debugT, globalAlphaRenamingT, diffCutT, arithmeticT, default}
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
      case BoxModality(odes: DifferentialProgram, _) => odes != EmptyODE()
      case _ => false
    })

    /**
     * Searches for a time variable (some derivative x'=1) in the specified formula.
     * @param f The formula.
     * @return The time variable, if found. None, otherwise.
     */
    private def findTimeInOdes(f: Formula): Option[Variable] = {
      val odes = f match {
        case BoxModality(prg: DifferentialProgram, _) => prg
        case _ => throw new IllegalStateException("Checked by applies to never happen")
      }

      var timeInOde: Option[Variable] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        import ExpressionTraversal.stop
        override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
          // TODO could be complicated 1
          case AtomicODE(Derivative(_, v: Variable), theta) if theta == Number(1) =>
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
            val initialTime: Variable = TacticHelper.freshNamedSymbol(Variable("k4_t", None, Real), node.sequent)
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
            case Derivative(_, ps: Variable) => primedSymbols += ps; Left(None)
            case Derivative(_, _) => throw new IllegalArgumentException("Only derivatives of variables supported")
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

          // flatten conjunctions and sort by free variables to approximate ODE dependencies
          val flatSolution = flattenConjunctions(solution).
            sortWith((f, g) => sizeOf(BindingAssessment.catVars(f).fv) < sizeOf(BindingAssessment.catVars(g).fv)).reverse

          var x = 0

          val cuts = flatSolution.foldLeft(diffWeakenT(p))((a, b) =>
            debugT(s"About to cut in $b at $p") & diffCutT(b)(p) & AndRightT(p) &&
            (debugT(s"Prove Solution using DI at $p") & diffInvariantT(p), a))

          Some(initialGhosts && cuts)
        }

        val diffEq = node.sequent(p) match {
          case BoxModality(ode: DifferentialProgram, _) => ode
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        val iv = primedSymbols(diffEq).map(v => v -> TacticHelper.freshNamedSymbol(v, node.sequent(p))).toMap
        // boxAssignT will increment the index twice (universal quantifier, skolemization) -> tell Mathematica
        val ivm = iv.map(e =>  (e._1, Function(e._2.name, Some(e._2.index.get + 2), Unit, e._2.sort))).toMap

        val theSolution = solution match {
          case sol@Some(_) => sol
          case None => tool match {
            case x: Mathematica => x.diffSolver.diffSol(diffEq, time, ivm)
            case _ => None
          }
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          // add relation to initial time
          case Some(s) =>
            val sol = And(if (tIsZero) s
                          else SubstitutionHelper.replaceFree(s)(time, Subtract(time.sort, time, Apply(ivm(time), Nothing))),
                          GreaterEqual(time.sort, time, Apply(ivm(time), Nothing)))
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
      case BoxModality(ODESystem(_, _, _), _) => true
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case BoxModality(ODESystem(_, _, _), _) =>
          Some(diffWeakenAxiomT(p) & TacticLibrary.abstractionT(p) & hideT(p) & debugT("Skolemize in DiffWeaken") & skolemizeT(p))
        case _ => None
      }
    }
  }

  def diffWeakenAxiomT: PositionTactic = new AxiomTactic("DW differential weakening", "DW differential weakening") {
    def applies(f: Formula) = f match {
      case BoxModality(ODESystem(_, _, _), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair])] = f match {
      case BoxModality(ode@ODESystem(_, c, h), p) =>
        // construct instance
        val g = BoxModality(ode, Imply(h, p))
        val axiomInstance = Equiv(f, g)

        // construct substitution
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        val aC = DifferentialProgramConstant("c")
        val aH = ApplyPredicate(Function("H", None, Real, Bool), Anything)
        val l = List(SubstitutionPair(aP, p), SubstitutionPair(aC, c), SubstitutionPair(aH, h))

        Some(axiomInstance, l)
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Auxiliary Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def diffAuxiliaryT(x: Variable, t: Term, s: Term, psi: Option[Formula] = None): PositionTactic =
      new AxiomTactic("DA differential ghost", "DA differential ghost") {
    import BindingAssessment.allNames
    def applies(f: Formula) = f match {
      case BoxModality(ode: ODESystem, _) => !BindingAssessment.catVars(ode).bv.contains(x) &&
        !allNames(t).contains(x) && !allNames(s).contains(x)
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
        Option[(Formula, Formula, List[SubstitutionPair], Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(ode@ODESystem(vars, c, h), p) =>
        // construct instance
        val q = psi match { case Some(pred) => pred case None => p }
        val lhs = And(Equiv(p, Exists(x :: Nil, q)), BoxModality(ODESystem(vars, ODEProduct(c,
          AtomicODE(Derivative(x.sort, x), Add(x.sort, Multiply(x.sort, t, x), s))), h), q))
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        val aQ = ApplyPredicate(Function("q", None, Real, Bool), Anything)
        val aH = ApplyPredicate(Function("H", None, Real, Bool), Anything)
        val aC = DifferentialProgramConstant("c")
        val aS = Apply(Function("s", None, Unit, Real), Nothing)
        val aT = Apply(Function("t", None, Unit, Real), Nothing)
        val l = List(SubstitutionPair(aP, p), SubstitutionPair(aQ, q), SubstitutionPair(aH, h),
          SubstitutionPair(aC, c), SubstitutionPair(aS, s), SubstitutionPair(aT, t))

        // rename to match axiom if necessary
        val aX = Variable("x", None, Real)
        val alpha = new PositionTactic("Alpha") {
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

        val (axiom, cont) =
          if (x.name != aX.name || x.index != aX.index) (replaceFree(ax)(aX, x, None), Some(alpha))
          else (ax, None)

        Some(axiom, axiomInstance, l, None, cont)
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Invariants Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Normal form differential invariant rule
   * Returns the differential invariant tactic for a single normal form ODE.
   * @return The tactic.
   */
  def diffInvariantNormalFormT: PositionTactic = new AxiomTactic("DI differential invariant", "DI differential invariant") {
    def applies(f: Formula) = {
      f match {
        case BoxModality(ODESystem(_, ODEProduct(_: AtomicODE, e:EmptyODE), _), _) => true
        case _ => false
      }
    }
    override def applies(s: Sequent, p: Position): Boolean = {
      val isntAnte = !p.isAnte
      val isInExpr = p.inExpr == HereP
      val superApplies = super.applies(s,p)
      isntAnte && isInExpr && superApplies
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, List[SubstitutionPair], Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(ode@ODESystem(vars, ODEProduct(AtomicODE(d: Derivative, t), empty: EmptyODE), h), p) => {
        // construct instance
        val x = d.child match {
          case v: Variable => v
          case _ => throw new IllegalArgumentException("Normal form expects primes of variables, not of entire terms.")
        }
        // [x'=f(x)&H(x);]p(x) <- ((H(x)->p(x)) & ([x'=f(x)&H(x);][x':=f(x);](p(x)')))
        val g = And(Imply(h, p), BoxModality(ode, BoxModality(Assign(d, t), FormulaDerivative(p))))
        val axiomInstance = Imply(g, f)


        // construct substitution
        // [x'=t&H;]p <- ([x'=t&H;](H->[x':=t;](p')))
        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
        val aT = Apply(Function("f", None, Real, Real), CDot)
        val l = List(
          SubstitutionPair(aH, SubstitutionHelper.replaceFree(h)(x, CDot)),
          SubstitutionPair(aP, SubstitutionHelper.replaceFree(p)(x, CDot)),
          SubstitutionPair(aT, SubstitutionHelper.replaceFree(t)(x, CDot)))

        val aX = Variable("x", None, Real)
        val alpha = new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Imply(And(Imply(_, _), BoxModality(ODESystem(_, ODEProduct(AtomicODE(_, _), _: EmptyODE), _),
                                                    BoxModality(Assign(Derivative(_, _), _), FormulaDerivative(_)))),
                       BoxModality(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }

        val (axiom, cont) =
          if (x.name != aX.name || x.index != aX.index) (replace(ax)(aX, x), Some(alpha))
          else (ax, None)

        Some(axiom, axiomInstance, l, None, cont)
      }
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // DI for Systems of Differential Equations
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /*
    Axiom "DI System Marker Intro".
      [c;]p <- p & [$$c$$;]p'
    End.
  */
  def diffInvariantSystemIntroT = new AxiomTactic("DI System Marker Intro", "DI System Marker Intro") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(ODESystem(_, _, _), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair])] = f match {
      case BoxModality(ODESystem(d, c, h), p) => {
        //[c&H]p <- (p & [{c}&H](H->p')

        //construct instance
        val g = Imply(h,
          And(p,
          BoxModality(
            ODESystem(d, IncompleteSystem(c), h), FormulaDerivative(p)
          )
        ))
        val axiomInstance = Imply(g, f)

        //construct substitution.
        val aC = DifferentialProgramConstant("c")
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        val aH = ApplyPredicate(Function("H", None, Real, Bool), Anything)
        val subst = List(
          SubstitutionPair(aC, c),
          SubstitutionPair(aP, p),
          SubstitutionPair(aH, h)
        )

        Some(axiomInstance, subst)
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Head Test".
      [$$x'=f(x), c$$ & H(x);]p(x) <- [$$c, x'$=$f(x)$$ & H(x);][x' := f(x);]p(x)
    End.
   */
  def diffInvariantSystemHeadT = new AxiomTactic("DI System Head Test", "DI System Head Test") {
    override def applies(f: Formula): Boolean = {
      f match {
//        case BoxModality(NFODEProduct(_, IncompleteSystem(ODEProduct(AtomicODE(Derivative(_, _: Variable), _), _)), _), _) => true
        case BoxModality(ODESystem(_, IncompleteSystem(cp: ODEProduct), _),_) => cp.normalize() match {
          case ODEProduct(AtomicODE(Derivative(_, _: Variable), _), _) => true
          case _ => false
        }
        case _ => println("Does not apply to: " + f.prettyString()); false
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, List[SubstitutionPair], Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(ODESystem(vars, a, h), p) => a match {
        //          case IncompleteSystem(ODEProduct(nfce:NFContEvolve, c:DifferentialProgram)) => {
        //            (nfce, c)
        //          }
        case IncompleteSystem(cp : ODEProduct) => cp.normalize() match {
          case ODEProduct(AtomicODE(d@Derivative(Real, x: Variable), t: Term), c: DifferentialProgram) =>
            val g = BoxModality(
              ODESystem(vars,
                IncompleteSystem(
                  ODEProduct(
                    c,
                    ODEProduct(CheckedContEvolveFragment(AtomicODE(d, t)))
                  )
                ), h),
              BoxModality(Assign(d, t), p)
            )
            val instance = Imply(g, f)

            //construct substitution
            val aT = Apply(Function("f", None, Real, Real), Anything) //@todo wow that's a bad name...
            val aH = ApplyPredicate(Function("H", None, Real, Bool), Anything)
            val aC = DifferentialProgramConstant("c")
            val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)

            val subst = List(
              SubstitutionPair(aT, t),
              SubstitutionPair(aC, c),
              SubstitutionPair(aP, p),
              SubstitutionPair(aH, h)
            )

            // alpha rename if necessary
            val aX = Variable("x", None, Real)
            val alpha = new PositionTactic("Alpha") {
              override def applies(s: Sequent, p: Position): Boolean = s(p) match {
                case Imply(BoxModality(ODESystem(_, _: IncompleteSystem, _), BoxModality(Assign(_: Derivative, _), _)),
                  BoxModality(ODESystem(_, _: IncompleteSystem, _), _)) => true
                case _ => false
              }

              override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
                override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                  Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

                override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
              }
            }

            val (axiom, cont) =
              if (x.name != aX.name || x.index != aX.index) (replace(ax)(aX, x), Some(alpha))
              else (ax, None)

            Some(axiom, instance, subst, None, cont)
        }
        case _ => throw new Exception("Should never get here.")
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Complete".
      [$$x' =` f(x), c$$ & H(x);]p(x) <- p(X)
    End.
  */
  def diffInvariantSystemTailT = new AxiomTactic("DI System Complete", "DI System Complete") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(ODESystem(_, IncompleteSystem(cp : ODEProduct), _), _) => cp.normalize() match {
        case ODEProduct(CheckedContEvolveFragment(_), _) => true
        case _ => false
      }
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, List[SubstitutionPair], Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(ODESystem(vars, IncompleteSystem(cp : ODEProduct), h), p) => {
        cp.normalize() match {
          case ODEProduct(CheckedContEvolveFragment(AtomicODE(Derivative(Real, x: Variable), t)), c) => {
            //construct instance
            val instance = Imply(p, f)

            //construct substitution.
            val aT = Apply(Function("f", None, Real, Real), Anything)

            val aH = ApplyPredicate(Function("H", None, Real, Bool), Anything)

            val aC = DifferentialProgramConstant("c")

            val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)

            val subst = List(
              new SubstitutionPair(aT, t),
              new SubstitutionPair(aC,c),
              new SubstitutionPair(aP, p),
              new SubstitutionPair(aH, h)
            )

            // alpha renaming if necessary
            val aX = Variable("x", None, Real)
            val alpha = new PositionTactic("Alpha") {
              override def applies(s: Sequent, p: Position): Boolean = s(p) match {
                case Imply(_, BoxModality(ODESystem(_, IncompleteSystem(_), _), _)) => true
                case _ => false
              }

              override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
                override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                  Some(globalAlphaRenamingT(x.name, x.index, aX.name, aX.index))

                override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
              }
            }

            val (axiom, cont) =
              if (x.name != aX.name || x.index != aX.index) (replace(ax)(aX, x), Some(alpha))
              else (ax, None)

            Some(axiom, instance, subst, None, cont)
          }
          case _ => None
        }
      }
      case _ => None
    }
  }

  /**
   * The "master" DI tactic.
   * @todo no testing yet.
   */
  def diffInvariantT: PositionTactic = new PositionTactic("DI differential invariant system") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case BoxModality(_: ODESystem, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps
        import SearchTacticsImpl.locateSucc
        node.sequent(p) match {
          case BoxModality(_: ODESystem, _) => {
            val finishingTouch = (AxiomCloseT | locateSucc(OrRightT) | locateSucc(NotRightT) |
              locateSucc(TacticLibrary.boxDerivativeAssignT) | locateSucc(ImplyRightT) | arithmeticT)*

            Some(diffInvariantSystemIntroT(p) & ImplyRightT(p) & AndRightT(p) & (
              debugT("left branch") & ((AxiomCloseT | PropositionalRightT(p))*) & arithmeticT,
              debugT("right branch") & (diffInvariantSystemHeadT(p) *) & debugT("head is now complete") &
                diffInvariantSystemTailT(p) &&
                debugT("About to NNF rewrite") & NNFRewrite(p) && debugT("Finished NNF rewrite") &
                SyntacticDerivationInContext.SyntacticDerivationT(p) && debugT("Done with syntactic derivation") &
                finishingTouch ~ debugT("Finished result")
            ))
          }
        }
      }
    }
  }
}


