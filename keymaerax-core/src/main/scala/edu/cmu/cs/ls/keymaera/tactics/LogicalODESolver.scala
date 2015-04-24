package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

/**
 * Solves simple ODEs.
 * @todo get an exact characterization of the ODEs that this actually solves.
 * @todo change file name...
 * @author Nathan Fulton
 */
object LogicalODESolver {

  /**
   * Computes the solution to v' = f where where v' = f is a component of "program"
   * @param v A variable s.t. v' = f occurs in the ODEs.
   * @param program ODE(s) with a time variable (some x s.t. x' = 1).
   * @param initialConditions Any initial conditions for the ODE.
   * @return The solution to a single ODE given a set of initial conditions and an ODE program (possibly with constraints).
   */
  def solutionForVariable(v : Variable, program : DifferentialProgram, initialConditions : List[Formula]) : Formula = {
    val odes         = atomicODEs(program)

    val time : Variable = timeVar(program) match {
      case Some(theTimeVar) => theTimeVar
      case None             => throw new Exception("A time variable should exist prior to calling solutionForVariable.")
    }

    //The assertion message is not technically true becuase the solution would just be zero.
    //But if the variable requested is not in the ODE, it's most likely this indicates a programming error rather than
    //an honest inquiry.
    assert(odes.find(ode => ode.xp.e.equals(v)).isDefined, "Cannot solve for a variable that does not occur in the ODE")

    //The initial value for v.
    val v_0 : Term = initValue(program, initialConditions)(v) match {
      case Some(term) => term
      case None    => Number(0)
    }

    //@todo check that this is always an OK cast Variable to NamedSymbol.
    val primedVariables : Set[Variable] = odes.map(_.xp.e).toSet

    //Compute the free variables in the ode corresponding to v'.
    val ode = odes.find(_.xp.e.equals(v)).getOrElse(throw new Exception("Could not find ODE associated with " + v))
    val varsInOde = StaticSemantics.freeVars(ode.e).toSet.map((x : NamedSymbol) => { x
        assert(x.isInstanceOf[Variable], "Only variables should occur as the child of the LHS of an ODE")
        x.asInstanceOf[Variable]
      })

    val recurrenceVars : Set[Variable] = (varsInOde intersect primedVariables) //for lack of a better name.
    if(recurrenceVars.isEmpty) {
      // If x' = a where a is not a variable occurring in the system of odes, then the solution is
      // x = at + x_0 where t is the time variable and x_0 is the value in initialValues associated with
      Equal(v, Plus(Times(ode.e, time), v_0))
    }
    else {
      //Replace all instance of primed variables in the term assocaited with v'
      val transformedTerm = recurrenceVars.foldLeft[Term](ode.e)((currTerm, x) => {
        val xSoln = initValue(program, initialConditions)(x)
        assert(xSoln.isDefined, "Need a solution for recurring variable " + x + " while solving for " + v)
        SubstitutionHelper.replaceFree(currTerm)(x, xSoln.get)
      })
      Equal(v, Plus(Times(transformedTerm, time), v_0))
    }
  }

  /**
   * If we topologically sort the ODEs of the system then we should end up with the equation with the fewest depednecies
   * as the first element of the list. If we can solve that ODE, then we can use the constraint in the next system and so on.
   * @param odes
   * @return Topological sort on the ODEs.
   */
  private def sortAtomicOdes(odes : List[AtomicODE]) : List[AtomicODE] = ???

  /**
   *
   * @param program
   * @param iniitalConstraints
   * @param x The variable whose initial value is requested.
   * @return The initial value of x in the ODE "program" subject to the initial conditions "initialConditions", where
   *         initial conditions in both the ODE's constraints and the initialConditiions are expressed in the form
   *         x = Term.
   */
  private def initValue(program : DifferentialProgram, iniitalConstraints : List[Formula])(x : Variable) : Option[Term] = {
    //Helper method that converts conditions of the form x = term into maps from variables to terms.
    def conditionsToValues(fs : List[Formula]) : Map[Variable, Term] = fs
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

    val odeConditions = conditionsToValues(odeConstraints(program))
    val initialConditions = conditionsToValues(iniitalConstraints)

    //Currently prerfering ode conditions. @todo check that this is OK.
    if(odeConditions.contains(x)) odeConditions.get(x)
    else if(initialConditions.contains(x)) initialConditions.get(x)
    else None
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
  private def timeVar(ode : DifferentialProgram) : Option[Variable] = ode match {
    case AtomicODE(x, e)                  => if(e.equals(Number(1))) Some(x.e) else None
    case ODESystem(ode, constraint)       => timeVar(ode)
    case DifferentialProduct(left, right) => (timeVar(left), timeVar(right)) match {
      case (Some(t), Some(t2)) => if(t.equals(t2)) Some(t) else ???
      case (Some(t), None)     => Some(t)
      case (None, Some(t))     => Some(t)
      case (None, None)        => None
    }
  }
}
