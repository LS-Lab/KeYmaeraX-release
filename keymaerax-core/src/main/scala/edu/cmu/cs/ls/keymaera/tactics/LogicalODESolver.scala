package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.AxiomCloseT
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.skolemizeT
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tools.Tool
import TacticLibrary._

/**
 * Solves simple ODEs.
 * @todo get an exact characterization of the ODEs that this actually solves.
 * @author Nathan Fulton
 */
object LogicalODESolver {


  def solveT : PositionTactic = new PositionTactic("Solve ODE") {
    override def applies(s: Sequent, p: Position): Boolean = true //@todo

    override def apply(p: Position): Tactic = LogicalODESolver.setupTimeVar(p) & (
        (stepTactic(p) *) &
        cutTimeLB(p) &
        ODETactics.diffWeakenT(p) &
        arithmeticT
      )
  }

  def cutTimeLB : PositionTactic = new PositionTactic("DiffCut and prove a lower-bound on time.") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(odes:ODESystem, _) => true //@todo
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(program : DifferentialProgram, f) => {
          val t = timeVar(program).getOrElse(throw new Exception("Need time var"))

          //Should always be 0, but let's be safe.
          val timeInitialCondition : Term = node.sequent.ante.flatMap(extractInitialConditions).find(f => f match {
            case Equal(x, _) if x.equals(t) => true
            case _ => false
          }).getOrElse(throw new Exception("Need initial condition on time variable " + t)) match {
            case Equal(x, term) => term
            case _ => throw new Exception("find failed.")
          }

          val theCut = diffCutT(GreaterEqual(t, timeInitialCondition))(p) & onBranch(
            (BranchLabels.cutShowLbl, diffInvariant(p)),
            (BranchLabels.cutUseLbl, /*yield*/NilT)
          ) & debugT("yield from cutTimeLB")

          Some(theCut)
        }
      }


      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def setupTimeVar : PositionTactic = new PositionTactic("Introduce time into ODE") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(dp : DifferentialProgram, f) => timeVar(dp).isEmpty
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Box(program : DifferentialProgram, f) => {
          //Copied from DiffSolutionT
          // HACK need some convention for internal names
          val initialTime: Variable = freshNamedSymbol(Variable("k4_t", None, Real), node.sequent)
          // universal quantifier and skolemization in ghost tactic (t:=0) will increment index twice
          val time = Variable(initialTime.name,
            initialTime.index match { case None => Some(1) case Some(a) => Some(a+2) }, initialTime.sort)

          val lastAntePos = AntePos(node.sequent.ante.length + 1)

          val setTimer = HybridProgramTacticsImpl.nonAbbrvDiscreteGhostT(Some(initialTime), Number(0))(p) & boxAssignT(p)

          val introTime = setTimer &
            ODETactics.diffAuxiliaryT(time, Number(0), Number(1))(p) & PropositionalTacticsImpl.AndRightT(p) && (
              PropositionalTacticsImpl.EquivRightT(p) & onBranch(
                (equivLeftLbl, vacuousExistentialQuanT(None)(p) & AxiomCloseT(lastAntePos, p)),
                (equivRightLbl, skolemizeT(lastAntePos) & AxiomCloseT(lastAntePos, p))
              ),
              NilT //yield
            ) & debugT("yield from setupTimeVar")

          Some(introTime)
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /**
   * @return A tactic that cuts in a solution to an ODE in a system. This should be saturated.
   */
  def stepTactic : PositionTactic = new PositionTactic("Logical ODE Solver") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Box(program : DifferentialProgram, _) => {
        val hasNextStep = atomicODEs(program).filter(ode => !timeVar(program).getOrElse( () ).equals(ode.xp.e)).find(ode => isUnsolved(ode.xp.e, program)) match {
          case Some(_) => true
          case None => false
        }
        timeVar(program).isDefined && hasNextStep
      }
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val initialConditions : List[Formula] = node.sequent.ante.flatMap(extractInitialConditions).toList

        node.sequent(p) match {
          case Box(program : DifferentialProgram, f) => {
            val sortedOdes = sortAtomicOdes(atomicODEs(program))
            val nextOde = sortedOdes
              .filter(ode => !timeVar(program).getOrElse( () ).equals(ode.xp.e)) //Skip time var, which we deal with using diff solve instead of diff inv.
              .find(ode => isUnsolved(ode.xp.e, program)).getOrElse(throw new Exception("applies method failed."))
            val toCut = Equal(nextOde.xp.e, integralOf(nextOde.xp.e, program, initialConditions))



            Some(ODETactics.diffCutT(toCut)(p) & onBranch(
              (BranchLabels.cutUseLbl, /*yield*/NilT),
              (BranchLabels.cutShowLbl, ODETactics.diffInvariantT(p))
            ))
          }
          case _ => throw new Exception
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  private def extractInitialConditions(f : Formula) : List[Formula] = flattenAnds(f match {
    case And(l, r) => extractInitialConditions(l) ++ extractInitialConditions(r)
    case Equal(v:Variable, _) => f :: Nil
    case _ => Nil //ignore?
  })

  /**
   *
   * @param v
   * @param program
   * @return true if the program does not already contain a solution for v.
   */
  def isUnsolved(v : Variable, program : DifferentialProgram) = {
    val odes = atomicODEs(program)
    if(odes.find(_.xp.e.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
    else if(timeVar(program).equals(v)) false //Don't need to solve for the time var.
    //In non-special cases, check for a = evolution domain constraint in the ode.
    else {
      val vConstraints = odeConstraints(program).flatMap(decomposeAnds).find(_ match {
        case Equal(l, r) => l.equals(v)
        case _ => false
      })
      vConstraints.isEmpty
    }
  }

  private def decomposeAnds(f : Formula) : List[Formula] = f match {
    case And(l,r) => decomposeAnds(l) ++ decomposeAnds(r)
    case _ => f :: Nil
  }

  /**
   * @param odes
   * @return
   */
  private def sortAtomicOdes(odes : List[AtomicODE]) : List[AtomicODE] = {
    sortAtomicOdesHelper(odes).map(v => odes.find(_.xp.e.equals(v)).get)
  }

  //@tailrec
  //@todo check this implementation.
  private def sortAtomicOdesHelper(odes : List[AtomicODE], prevOdes : List[AtomicODE] = Nil) : List[Variable] = {
    var primedVars = odes.map(_.xp.e)

    def dependencies(v : Variable) : List[Variable] = {
      val vTerm = odes.find(_.xp.e.equals(v)).get.e
      //remove self-references to cope with the fact that t' = 0*t + 1, which is necessary due to DG.
      primedVars.filter(StaticSemantics.freeVars(vTerm).contains(_)).filter(!_.equals(v))
    }

    var nonDependentSet : List[Variable] = primedVars.filter(dependencies(_).isEmpty)
    val possiblyDependentOdes = odes.filter(ode => !nonDependentSet.contains(ode.xp.e))

    if(possiblyDependentOdes.isEmpty) nonDependentSet
    else {
      if(prevOdes.equals(possiblyDependentOdes)) throw new Exception("Cycle detected!")
      nonDependentSet ++ sortAtomicOdesHelper(possiblyDependentOdes, odes)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Integrals of a single ODE.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * If v' = term occurs in the system of ODEs, then this function computes the integral of term.
   * Assumes that the ODEs have a time variable, that a formula of the form v=f occurs in the initialConditions formulas,
   * and that the system of odes is blah blah.
   * @param v
   * @param program
   * @param initialConditions
   * @return Integral of f assuming v' = f occurs in ODEs.
   */
  def integralOf(v : Variable, program : DifferentialProgram, initialConditions : List[Formula]) : Term = {
    val termToIntegrate = resolveRecurrences(v, program, initialConditions)
    println("Integrating term " + termToIntegrate)

    val t = timeVar(program) match {
      case Some(t) => t
      case None    => throw new Exception("Could not find time variable in ODEs")
    }

    val v_0 : Term = conditionsToValues(initialConditions).get(v) match {
      case Some(x) => x
      case None => throw new Exception("Could not find initial condition for " + v.name)
    }

    Plus(integrator(termToIntegrate, t), v_0)
  }

  /**
   * A syntactic integrator for @todo something like sums of terms over polynomials univariable in t.
   * @param term The term
   * @param t Time variable
   * @return Integral term dt
   */
  private def integrator(term : Term, t : Variable) : Term = term match {
    case Plus(l, r) => Plus(integrator(l, t), integrator(r, t))
    case Minus(l, r) => Minus(integrator(l, t), integrator(r, t))
    case Times(c, x) if x.equals(t) && !StaticSemantics.freeVars(c).contains(t) => Times(Divide(c, Number(2)), Power(x, Number(2)))
    case Times(c, Power(x, exp)) if x.equals(t) && !StaticSemantics.freeVars(exp).contains(t) && !StaticSemantics.freeVars(c).contains(t) => {
      val newExp = exp match {
        case Number(n) => Number(n+1)
        case _ => Plus(exp, Number(1))
      }
      Times(Divide(c, newExp), Power(t, newExp))
    }
    case Power(base, exp) => exp match {
      case Number(n) =>
        if(n == 1) integrator(base, t)
        else       Times(Divide(Number(1), Number(n+1)), integrator(Power(base, Number(n-1)), t))
      case _ => throw new Exception("Cannot integrate terms with non-number exponents!")
    }
//    case Number(n) => Times(term, t) //@todo do we need a constant here?
//    case x : Variable => Times(x, t)
      //@todo is this more general case of the number/variable pattern sufficient?
    case x : Term if !StaticSemantics.freeVars(x).contains(t) => Times(x, t)
  }

  /**
   * Given x' = f, replaces all variables in f with their recurrences or initial conditions.
   * @todo this needs a better name.
   * @todo make thie private and figure out the private method helper thing.
   * @param v A variable s.t. v' = f occurs in the ODEs.
   * @param program ODE(s) with a time variable (some x s.t. x' = 1).
   * @param initialConditions Any initial conditions for the ODE.
   * @return f with all variables replaced by their recurrences or initial conditions.
   */
  def resolveRecurrences(v : Variable, program : DifferentialProgram, initialConditions : List[Formula]) : Term = {
    val odes         = atomicODEs(program)

    val time : Variable = timeVar(program) match {
      case Some(theTimeVar) => theTimeVar
      case None             => throw new Exception("A time variable should exist prior to calling solutionForVariable.")
    }

    //The assertion message is not technically true becuase the solution would just be zero.
    //But if the variable requested is not in the ODE, it's most likely this indicates a programming error rather than
    //an honest inquiry.
    assert(odes.find(ode => ode.xp.e.equals(v)).isDefined, "Cannot solve for a variable that does not occur in the ODE")

    //@todo check that this is always an OK cast Variable to NamedSymbol.
    val primedVariables : Set[Variable] = odes.map(_.xp.e).toSet

    //Compute the free variables in the ode corresponding to v'.
    val ode = odes.find(_.xp.e.equals(v)).getOrElse(throw new Exception("Could not find ODE associated with " + v))
    val varsInOde = StaticSemantics.freeVars(ode.e).toSet.map((x : NamedSymbol) => { x
        assert(x.isInstanceOf[Variable], "Only variables should occur as the child of the LHS of an ODE")
        x.asInstanceOf[Variable]
      })

    //Variables that occur in the term associated with v' and also occur primed in the ODE.
    val recurrenceVars : Set[Variable] = (varsInOde intersect primedVariables) //for lack of a better name.

    //Variables that occur in the term associated with v' but do not occur primed in the ODE.
    val nonRecurringVars : Set[Variable] = varsInOde -- recurrenceVars

    if(recurrenceVars.isEmpty) {
      // If x' = a where a is not a variable occurring in the system of odes, then the solution is
      // x = at + x_0 where t is the time variable and x_0 is the value in initialValues associated with
      val f_initValuesResolved = nonRecurringVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val x_0 = initValue(initialConditions, x)
        assert(x_0.isDefined, "Need an initial condition for non-recurring variable " + x + " while solve for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, x_0.get)
      })

      f_initValuesResolved
    }
    else {
      //@todo good variable names for these two passes.
      //Replace all instance of primed variables in the term assocaited with v'
      val f_substRecurrences = recurrenceVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val xSoln = recurrence(program, initialConditions, x)
        assert(xSoln.isDefined, "Need a solution for recurring variable " + x + " while solving for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, xSoln.get)
      })
      val f_substInitValues = nonRecurringVars.foldLeft[Term](f_substRecurrences)((currTerm, x) => {
        val x_0 = initValue(initialConditions, x)
        assert(x_0.isDefined, "Need an initial condition for non-recurring variable " + x + " while solve for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, x_0.get)
      })
      f_substInitValues
    }
  }

  /**
   * Converts formulas of the form x = term into a map x -> term, and ignores all formulas of other forms.
   * @todo think of a better name -- constraintsToConditions? formulasToConditions?
   */
  private def conditionsToValues(fs : List[Formula]) : Map[Variable, Term] = flattenAnds(fs)
    .map(f => f match {
    case Equal(left, right) => left match {
      case v : Variable => Some(v, right)
      case _ => None
    }
    case _ => None
  })
    .filter(_.isDefined)
    .map(e => (e.get._1 -> e.get._2))
    .toMap

  /**
   * @todo document.
   * @param program
   * @param initialConstraints
   * @param x
   * @return ???
   */
  private def recurrence(program : DifferentialProgram, initialConstraints : List[Formula], x : Variable) : Option[Term] = {
    val odeConditions = conditionsToValues(flattenAnds(odeConstraints(program)))
    val initialConditions = conditionsToValues(flattenAnds(initialConstraints))
    if(odeConditions.contains(x)) odeConditions.get(x)
    else if(initialConditions.contains(x)) initialConditions.get(x)
    else None
  }

  /**
   * Converts list of formulas possibly containing ANDs into list of formulas that does not contain any ANDs.
   * @param fs
   */
  private def flattenAnds(fs : List[Formula]) = fs.flatMap(f => f match {
    case And(l, r) => l :: r :: Nil
    case _ => f :: Nil
  })

  /**
   *
   * @param iniitalConstraints
   * @param x The variable whose initial value is requested.
   * @return The initial value of x.
   */
  private def initValue(iniitalConstraints : List[Formula], x : Variable) : Option[Term] = {
    val initialConditions = conditionsToValues(iniitalConstraints)
    initialConditions.get(x)
  }

  /**
   * @param ode
   * @return The list of atomic differential equations occurring in the differential program.
   * @author Nathan Fulton
   */
  private def odeConstraints(ode : DifferentialProgram) : List[Formula] = ode match {
    case AtomicODE(x,e)                   => Nil
    case ODESystem(ode, constraint)       => constraint :: Nil
    case DifferentialProduct(left, right) => odeConstraints(left) ++ odeConstraints(right)
  }

  /**
   * @param ode
   * @return The list of atomic differential equations occurring in the differential program.
   * @author Nathan Fulton
   */
  private def atomicODEs(ode : DifferentialProgram) : List[AtomicODE] = ode match {
    case AtomicODE(x, e)                  => AtomicODE(x,e) :: Nil
    case ODESystem(ode, constraint)       => atomicODEs(ode)
    case DifferentialProduct(left, right) => atomicODEs(left) ++ atomicODEs(right)
  }

  /**
   * @param ode Any differential program.
   * @return A variable x s.t. x'=1 occurs in ode.
   * @author Nathan Fulton
   */
  def timeVar(ode : DifferentialProgram) : Option[Variable] = {
    //The second value is the one that we cut in. @todo maybe actually we really need time to be 0*t + 1?
    def isTimeVar(atomic : AtomicODE) = atomic.e.equals(Number(1)) || atomic.e.equals(Plus(Times(Number(0), atomic.xp.e), Number(1)))

    ode match {
      case atomic:AtomicODE => if(isTimeVar(atomic)) Some(atomic.xp.e) else None
      case ODESystem(ode, constraint)       => timeVar(ode)
      case DifferentialProduct(left, right) => (timeVar(left), timeVar(right)) match {
        case (Some(t), Some(t2)) => if(t.equals(t2)) Some(t) else ???
        case (Some(t), None)     => Some(t)
        case (None, Some(t))     => Some(t)
        case (None, None)        => None
      }
    }
  }

  private def freshTimeVar(s : Sequent) : Variable =
    Variable("t",TacticHelper.freshIndexInSequent("t", s), Real)

  private def freshTimeVar(f : Formula) : Variable =
    Variable("t", TacticHelper.freshIndexInFormula("t", f), Real)
}
