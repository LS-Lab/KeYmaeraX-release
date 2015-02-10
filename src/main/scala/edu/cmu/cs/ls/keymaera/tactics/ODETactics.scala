package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.boxAssignT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.boxNDetAssign
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.boxTestT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.skolemizeT
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
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
      case BoxModality(odes: ContEvolveProgram, _) => odes != EmptyContEvolveProgram()
      case _ => false
    })

    /**
     * Searches for a time variable (some derivative x'=1) in the specified formula.
     * @param f The formula.
     * @return The time variable, if found. None, otherwise.
     */
    private def findTimeInOdes(f: Formula): Option[Variable] = {
      val odes = f match {
        case BoxModality(prg: ContEvolveProgram, _) => prg
        case _ => throw new IllegalStateException("Checked by applies to never happen")
      }

      var timeInOde: Option[Variable] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        import ExpressionTraversal.stop
        override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
          // TODO could be complicated 1
          case NFContEvolve(_, Derivative(_, v: Variable), theta, _) if theta == Number(1) =>
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
            val initialTime: Variable = TacticHelper.freshNamedSymbol(Variable("$t", None, Real), node.sequent)
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
        t.continuation = continuation
        (timeTactic & t).dispatch(this, node)
      }
    }

    private def constructTactic(p: Position, time: Variable, tIsZero: Boolean) = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      private def primedSymbols(ode: ContEvolveProgram) = {
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
        def createTactic(ode: ContEvolveProgram, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                         diffEqPos: Position) = {
          val initialGhosts = primedSymbols(ode).foldLeft(NilT)((a, b) =>
            a & (discreteGhostT(Some(iv(b)), b)(diffEqPos) & boxAssignT(diffEqPos)))
          val cut = diffCutT(solution)(p) & AndRightT(p)
          val proveSol = NilT //diffInvariantT(diffEqPos)
          val useSol = diffWeakenT(diffEqPos)
          Some(initialGhosts & cut & (proveSol, useSol))
        }

        val diffEq = node.sequent(p) match {
          case BoxModality(ode: ContEvolveProgram, _) => ode
          case _ => throw new IllegalStateException("Checked by applies to never happen")
        }

        val iv = primedSymbols(diffEq).map(v => v -> TacticHelper.freshNamedSymbol(v, node.sequent(p))).toMap
        // boxAssignT will increment the index twice (universal quantifier, skolemization) -> tell Mathematica
        val ivm = iv.map(e =>  (e._1, Variable(e._2.name, Some(e._2.index.get + 2), e._2.sort))).toMap

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
            val sol = And(if (tIsZero) s else replaceFree(s)(time, Subtract(time.sort, time, ivm(time))),
              GreaterEqual(time.sort, time, ivm(time)))
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
            (diffWeakenSystemIntroT(p) &
              // pull out heads until empty
              ((diffWeakenSystemHeadT(p) & boxNDetAssign(p) & skolemizeT(p)) *)) ~
              // remove empty marker and handle tests
              diffWeakenSystemNilT(p) & ((boxTestT(p) & ImplyRightT(p)) *)
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
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(c: ContEvolveProduct, p) =>
        // construct instance
        val g = BoxModality(IncompleteSystem(c), p)
        val axiomInstance = Imply(g, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aC = ContEvolveProgramConstant("c")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aC, c))

        Some(ax, axiomInstance, Substitution(l), None, None)
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
      case BoxModality(IncompleteSystem(_: ContEvolveProduct), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(cep: ContEvolveProduct), p) => cep.normalize() match {
        case ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), c) =>
          // construct instance
          val x = d.child match {
            case v: Variable => v
            case _ => throw new IllegalArgumentException("Normal form expects v in v' being a Variable")
          }
          val lhs = BoxModality(NDetAssign(x), BoxModality(IncompleteSystem(c), BoxModality(Test(h), p)))
          val axiomInstance = Imply(lhs, f)

          // construct substitution
          val aX = Variable("x", None, Real)
          val aH = ApplyPredicate(Function("H", None, Real, Bool), x)
          val aP = ApplyPredicate(Function("p", None, Real, Bool), x)
          val aT = Apply(Function("f", None, Real, Real), x)
          val aC = ContEvolveProgramConstant("c")
          val l = List(new SubstitutionPair(aH, h), new SubstitutionPair(aP, p),
            new SubstitutionPair(aT, t), new SubstitutionPair(aC, c))

          // alpha renaming of x on axiom if necessary
          val (axiom, anteCont) =
            if (x.name != aX.name || x.index != aX.index) (replace(ax)(aX, x), Some(alphaInWeakenSystems(aX, x)))
            else (ax, None)

          Some(axiom, axiomInstance, Substitution(l), anteCont, None)
        case _ => None
      }
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
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(_: EmptyContEvolveProgram), BoxModality(b@Test(h), p)) =>
        // construct instance
        val lhs = BoxModality(b, p)
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aH = PredicateConstant("H")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aH, h))

        Some(ax, axiomInstance, Substitution(l), None, None)
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
  private def alphaInWeakenSystems(oldSymbol: Variable, newSymbol: Variable) = new PositionTactic("Alpha") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Imply(BoxModality(_: NDetAssign, _), BoxModality(_: ContEvolveProgram, _)) => true
      case Imply(BoxModality(_: NDetAssign, _), BoxModality(_: IncompleteSystem, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      import TacticLibrary.{abstractionT,ImplyLeftT,ImplyRightT,hideT,instantiateQuanT}
      import PropositionalTacticsImpl.AxiomCloseT
      import HybridProgramTacticsImpl.v2vBoxAssignT
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        Some(alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, newSymbol.index)(p.first)
          & alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, newSymbol.index)(p.second)
          & (if (p.isAnte) ImplyLeftT(p) else ImplyRightT(p))
          & (ImplyRightT(SuccPosition(0)) & AxiomCloseT(AntePosition(0), SuccPosition(0)),
            // HACK need temporary name and not sure if newSymbol.index is max
            abstractionT(p) & hideT(p) &
              alphaRenamingT(newSymbol.name, newSymbol.index, "_$" + newSymbol.name, newSymbol.index)(p.first) &
              instantiateQuanT(newSymbol, newSymbol)(p) &
              v2vBoxAssignT(p) & ImplyRightT(SuccPosition(0))
          )
        )

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Auxiliary Section.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def diffAuxiliaryT(x: Variable, t: Term, s: Term, psi: Option[Formula] = None): PositionTactic =
      new AxiomTactic("DA differential ghost", "DA differential ghost") {
    def applies(f: Formula) = f match {
      case BoxModality(ode: ContEvolveProgram, _) => !Helper.names(ode).contains(x) && !Helper.names(t).contains(x) &&
        !Helper.names(s).contains(x)
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
        Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(ode: ContEvolveProgram, p) =>
        // construct instance
        val q = psi match { case Some(pred) => pred case None => p }
        val lhs = And(Equiv(p, Exists(x :: Nil, q)), BoxModality(ContEvolveProduct(ode, NFContEvolve(Nil,
          Derivative(x.sort, x), Add(x.sort, Multiply(x.sort, t, x), s), True)), q))
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aX = Variable("x", None, Real)
        val aQ = ApplyPredicate(Function("q", None, Real, Bool), x)
        val aC = ContEvolveProgramConstant("c")
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aQ, q), new SubstitutionPair(aC, ode),
          new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))

        // rename to match axiom if necessary
        val (axiom, succCont) =
          if (x.name != aX.name || x.index != aX.index) (replaceFree(ax)(aX, x, None), Some(alphaInDiffAuxiliary(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), succCont, None)
      case _ => None
    }
  }

  /**
   * Creates an alpha renaming tactic that fits the structure of differential auxiliaries. The tactic renames the old
   * symbol to the new symbol.
   * @param oldSymbol The old symbol.
   * @param newSymbol The new symbol.
   * @return The alpha renaming tactic.
   */
  private def alphaInDiffAuxiliary(oldSymbol: Variable, newSymbol: Variable) = new PositionTactic("Alpha") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Imply(And(Equiv(_, Exists(_, _)), BoxModality(_: ContEvolveProgram, _)), BoxModality(_: ContEvolveProgram, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      import TacticLibrary.{abstractionT,ImplyLeftT,ImplyRightT,hideT,instantiateQuanT}
      import PropositionalTacticsImpl.AxiomCloseT
      import HybridProgramTacticsImpl.v2vBoxAssignT
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        Some(ImplyRightT(SuccPosition(0))
          & ImplyLeftT(p)
          & (hideT(SuccPosition(0))
                & alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, newSymbol.index)(AntePosition(p.index, PosInExpr(0 :: 1 :: Nil)))
                & alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, newSymbol.index)(AntePosition(p.index, PosInExpr(1 :: Nil)))
                & AndLeftT(p) & abstractionT(AntePosition(1)) & hideT(AntePosition(1))
                & alphaRenamingT(newSymbol.name, newSymbol.index, "_$" + newSymbol.name, newSymbol.index)(AntePosition(1).first)
                & instantiateQuanT(newSymbol, newSymbol)(AntePosition(1)) & v2vBoxAssignT(AntePosition(1))
                & AndRightT(SuccPosition(0))
                & (hideT(AntePosition(1)), hideT(AntePosition(0))) & AxiomCloseT(AntePosition(0), SuccPosition(0)),
             /* axiom tactic takes care of it */ NilT
          )
        )

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
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
  def diffInvariantNormalFormT: PositionTactic = new AxiomTactic("DI differential invariant (system style)", "DI differential invariant (system style)") {
    def applies(f: Formula) = {
      f match {
        case BoxModality(ContEvolveProduct(_: NFContEvolve, e:EmptyContEvolveProgram),_) => true
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
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(ContEvolveProduct(NFContEvolve(vars, d: Derivative, t, h), empty:EmptyContEvolveProgram), p) => {
        // construct instance
        val x = d.child match {
          case v: Variable => v
          case _ => throw new IllegalArgumentException("Normal form expects primes of variables, not of entire terms.")
        }
        // [x'=t&H;]p <- ([x'=t&H;](H->[x':=t;](p')))
        val g = BoxModality(
          ContEvolveProduct(NFContEvolve(vars, Derivative(Real,x), t, h),empty:EmptyContEvolveProgram),
          Imply(
            h,
            BoxModality(
              Assign(Derivative(Real,x), t),
              FormulaDerivative(p)
            )
          )
        )
        val axiomInstance = Imply(g, f)


        // construct substitution
        // [x'=t&H;]p <- ([x'=t&H;](H->[x':=t;](p')))
        val aX = Variable("x", None, Real)
        val aH = PredicateConstant("H", None)
        val aP = PredicateConstant("p", None)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aH, h), new SubstitutionPair(aP, p), new SubstitutionPair(aT, t))

        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), None, cont)
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
      case BoxModality(ContEvolveProduct(_, _), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(c: ContEvolveProduct, p) => {
        //[c]p <- p & [{c}]p'

        //construct instance
        val g = And(
          p,
          BoxModality(
            IncompleteSystem(c), FormulaDerivative(p)
          )
        )
        val axiomInstance = Imply(g, f)

        //construct substitution.
        val aC = ContEvolveProgramConstant("c")
        val aP = PredicateConstant("p")
        val subst = Substitution(List(
          new SubstitutionPair(aC, c),
          new SubstitutionPair(aP, p)
        ))

        Some(ax, axiomInstance, subst, None, None)
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Head Test".
      [$$x'=f(x) & H(x), c$$;]p(x) <- [$$c, x'$=$f(x)$$;][x' := f(x);](H(x) -> p(x))
    End.
   */
  def diffInvariantSystemHeadT = new AxiomTactic("DI System Head Test", "DI System Head Test") {
    override def applies(f: Formula): Boolean = {
      f match {
        //      case BoxModality(IncompleteSystem(ContEvolveProduct(ContEvolve(Equals(_,Derivative(Real, x:Variable), t:Term)), _))) => true
        case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(_,Derivative(Real, x:Variable),_,h), _)), _) => true
        case _ => false
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(vars, Derivative(Real, x:Variable), t:Term, h), c:ContEvolveProgram)), p:Formula) => {

        val g = BoxModality(
          IncompleteSystem(
            ContEvolveProduct(
              c,
              ContEvolveProduct(
                CheckedContEvolveFragment(NFContEvolve(vars, Derivative(Real,x), t, h)),
                EmptyContEvolveProgram()
              )
            )
          ),
          BoxModality(
            Assign(Derivative(Real, x), t),
            Imply(h, p)
          )
        )
        val instance = Imply(g,f)

        //construct substitution
        import Substitution.maybeFreeVariables
        val aX = Variable("x", None, Real)

        val aT = Apply(Function("f", None, Real, Real), CDot)
        val t_cdot = replaceFree(t)(x, CDot, Some(maybeFreeVariables(t))) //@todo confused about when we want to use cdot and when not...

        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val h_cdot = replaceFree(h)(x, CDot, Some(maybeFreeVariables(h)))

        val aC = ContEvolveProgramConstant("c")

        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
        val p_cdot = replaceFree(p)(x, CDot, Some(maybeFreeVariables(p)))

        val subst = Substitution(List(
          new SubstitutionPair(aT, t_cdot),
          new SubstitutionPair(aC,c),
          new SubstitutionPair(aP, p_cdot),
          new SubstitutionPair(aH, h_cdot)
        ))

        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replace(ax)(aX, x), Some(alphaInWeakenSystems(aX, x)))
          else (ax, None)

        Some(axiom, instance, subst, None, cont)
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Complete".
      [$$x' =` f(x) & H(x), c$$;]p(x) <- p(X)
    End.
  */
  def diffInvariantSystemTailT = new AxiomTactic("DI System Complete", "DI System Complete") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(CheckedContEvolveFragment(_),_)), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(CheckedContEvolveFragment(NFContEvolve(bvs,Derivative(Real,x:Variable),t,h)), c)), p) => {
        //construct instance
        val instance = Imply(f, p)

        //construct substitution.
        import Substitution.maybeFreeVariables
        val aX = Variable("x", None, Real)

        val aT = Apply(Function("f", None, Real, Real), CDot)
        val t_cdot = replaceFree(t)(x, CDot, Some(maybeFreeVariables(t)))

        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val h_cdot = replaceFree(h)(x, CDot, Some(maybeFreeVariables(h)))

        val aC = ContEvolveProgramConstant("c")

        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
        val p_cdot = replaceFree(p)(x, CDot, Some(maybeFreeVariables(p)))

        val subst = Substitution(List(
          new SubstitutionPair(aT, t_cdot),
          new SubstitutionPair(aC,c),
          new SubstitutionPair(aP, p_cdot),
          new SubstitutionPair(aH, h_cdot)
        ))

        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replace(ax)(aX, x), Some(alphaInWeakenSystems(aX, x)))
          else (ax, None)

        Some(axiom, instance, subst, None, cont)
      }
      case _ => None
    }
  }

  /**
   * The "master" DI tactic.
   */
  def diffInvariantT: PositionTactic = new PositionTactic("DI differential invariant system") {
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
//            diffInvariantSystemIntroT(p) & TacticLibrary.locateAnte(SyntacticDerivationAxiomTactics.SyntacticDerivationT) & TacticLibrary.locateSucc(SyntacticDerivationAxiomTactics.SyntacticDerivationT) &
            diffInvariantSystemIntroT(p) & SyntacticDerivationAxiomTactics.SyntacticDerivationT(p) &
            (AndRightT(p) & (NilT & TacticLibrary.debugT("test seq"), (TacticLibrary.debugT("inv seq") & diffInvariantSystemHeadT(p)) *)) ~
            (diffInvariantSystemTailT(p) & ((TacticLibrary.boxAssignT(p) & ImplyRightT(p)) *))
          )
        }
      }
    }
  }
}


