/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.Mathematica

/**
  * An Axiomatic ODE solver (second attempt)
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  */
object AxiomaticODESolver {
  //implicits for "by" notation and functional application of positions to sequents/formulas.
  import TacticFactory._
  import Augmentors._

  /** The main tactic. */
  def axiomaticSolve(implicit qeTool: QETool) = "axiomaticSolve" by ((pos:Position, s:Sequent) => {
    val odePos = subPosition(pos, 0::Nil)

    addTimeVarIfNecessary(odePos) & //@todo initialize time var so that there's always a t:=0 in front. Then munge positions.
    cutInSolns(qeTool)(pos)
  })

  //region Setup time variable

  /** The name of the explicit time variables. */
  private val TIMEVAR : String = "kyxtime"

  /** Adds a time variable to the ODE if there isn't one already; otherwise, does nothing.
    *
    * @see [[addTimeVar]] */
  val addTimeVarIfNecessary = "addTimeVarIfNecessary" by ((pos: Position, s:Sequent) => s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => addTimeVar(pos)
      case x:DifferentialProgram if timeVar(x).nonEmpty => Idioms.nil
      case x:ODESystem if timeVar(x).isEmpty => addTimeVar(pos)
      case x:ODESystem if timeVar(x).nonEmpty => Idioms.nil
      case _ => throw AxiomaticODESolverExn("Expected DifferentialProgram or ODESystem")
  })

  /** Rewrites [{c}]p to [{c, t'=1}]p whenever the system c does not already contain a clock.
    * The positional argument should point to the location of c, NOT the location of the box.
    * This tactic should work at any top-level position and also in any context.
    *
    * @note If we want an initial value for time (kyxtime:=0) then this is the place to add that functionality.
    */
  val addTimeVar = "addTimeVar" by((pos: Position, s:Sequent) => {
    s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => //ok
      case x:ODESystem if timeVar(x).isEmpty => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s(pos)} of type ${s(pos).getClass}.")
    }

    val modalityPos = parentPosition(pos)
    if(!s(modalityPos).isInstanceOf[Modal])
      throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")

    val t = TacticHelper.freshNamedSymbol(Variable(TIMEVAR), s)

    s(modalityPos) match {
      case Box(_,_) => {
        HilbertCalculus.DG(t, Number(0), Number(1))(modalityPos) &
        DebuggingTactics.error("Needs exists monotone") //@todo instantiate \exists t to an assignment [t:=0] or additional antecedent.
      }
      case Diamond(_,_) => throw noDiamondsForNowExn
    }
  })

  /** Returns the unique time variable in diffProgram, or None if no time variable can be found.
    *
    * @throws AxiomaticODESolverExn whenever diffProgram contains more than one time variable
    * @note this could be re-written as a tailrec fn. */
  private def timeVar(diffProgram: DifferentialProgram) : Option[Variable] = diffProgram match {
    case x:AtomicODE if isOne(x.e)  => Some(x.xp.x)
    case x:AtomicODE if !isOne(x.e) => None
    case x:DifferentialProgramConst => None
    case x:DifferentialProduct      => (timeVar(x.left), timeVar(x.right)) match {
      case (None, None)       => None
      case (None, Some(x))    => Some(x)
      case (Some(x), None)    => Some(x)
      case (Some(x), Some(y)) => throw AxiomaticODESolverExn(s"Expected one time variable but found many (${x} and ${y}) in ${diffProgram}")
    }
  }
  private def timeVar(system: ODESystem): Option[Variable] = timeVar(system.ode)

  private def isOne(t: Term) = t == Number(1) //@todo more robust implementation. E.g. QE.

  //endregion

  //region Cut in solutions

  def cutInSolns(implicit qeTool: QETool) = "cutInSolns" by ((pos: Position, s: Sequent) => {
    assert(s(pos).isInstanceOf[Modal], s"Expected a modality but found ${s(pos).prettyString}")
    val ode:DifferentialProgram = s(pos).asInstanceOf[Modal].program match {
      case x:ODESystem => x.ode
      case x:DifferentialProgram => x
    }

    val initialConditions = s.ante.flatMap(extractInitialConditions(None)).toList //@todo constrain to only true initial conditions by passing in Some(ode).

    val cuts = sortAtomicOdes(atomicODEs(ode))
      .filter(ode => !isOne(ode.e))
      .map(ode => Equal(ode.xp.x, integralOf(ode.xp.x, ode, initialConditions)))

    s(pos) match {
      case Box(ode, postcond) => {
        cuts.map(solnToCut => {
          DifferentialTactics.diffCut(solnToCut)(pos) <(
            Idioms.nil,
            DifferentialTactics.diffInd(qeTool)(pos) & DebuggingTactics.assertProved
          )
        })
        .reduce(_ & _)
      }
      case Diamond(ode, postcond) => throw noDiamondsForNowExn
    }
  })

  /**
    * Extracts all equalities that look like initial conditions from the formula f.
    *
    * @param ode Optionally an ODE; if None, then all equalities are extracted from f. This may include non-initial-conds.
    * @param f A formula containing conjunctions.
    * @return A list of equality formulas after deconstructing Ands. E.g., A&B&C -> A::B::C::Nil
    */
  private def extractInitialConditions(ode : Option[Program])(f : Formula) : List[Formula] =
    flattenAnds(f match {
      case And(l, r) => extractInitialConditions(ode)(l) ++ extractInitialConditions(ode)(r)
      case Equal(v: Variable, _) => {if(isPrimedVariable(v, ode)) (f :: Nil) else Nil}
      case Equal(_, v: Variable) => {if(isPrimedVariable(v, ode)) (f :: Nil) else Nil}
      case _ => Nil //@todo is it possible to allow set-valued initial conditiosn (e.g., inequalities, disjunctions, etc.)?
    })

  private def isPrimedVariable(v : Variable, ode : Option[Program]) = ode match {
    case Some(x) => StaticSemantics.boundVars(x).contains(v)
    case None => true //over-approximate set of initial conditions if no ODE is provided.
  }

  private def getPrimedVariables(ode : Program) : List[Variable] = ode match {
    case AtomicODE(pv, term) => pv.x :: Nil
    case ODESystem(ode, constraint) => getPrimedVariables(ode)
    case DifferentialProduct(l,r) => getPrimedVariables(l) ++ getPrimedVariables(r)
    case _: AtomicDifferentialProgram => ???
    case _ => throw AxiomaticODESolverExn(s"Expected a differnetial program or ode system but found ${ode.getClass}")
  }

  /**
    * Converts list of formulas possibly containing Ands into list of formulas that does not contain any ANDs.
    *
    * @param fs A list of formulas, possibly containing Ands.
    */
  private def flattenAnds(fs : List[Formula]) = fs.flatMap(decomposeAnds)

  /**
    *
    * @param f A formula.
    * @return A list of formulas with no top-level Ands.
    */
  private def decomposeAnds(f : Formula) : List[Formula] = f match {
    case And(l,r) => decomposeAnds(l) ++ decomposeAnds(r)
    case _ => f :: Nil
  }

  /**
    * @param odes
    * @return
    */
  private def sortAtomicOdes(odes : List[AtomicODE]) : List[AtomicODE] = {
    sortAtomicOdesHelper(odes).map(v => odes.find(_.xp.x.equals(v)).get)
  }

  //@todo check this implementation.
  private def sortAtomicOdesHelper(odes : List[AtomicODE], prevOdes : List[AtomicODE] = Nil) : List[Variable] = {
    var primedVars = odes.map(_.xp.x)

    def dependencies(v : Variable) : List[Variable] = {
      val vTerm = odes.find(_.xp.x.equals(v)).get.e
      //remove self-references to cope with the fact that t' = 0*t + 1, which is necessary due to DG.
      primedVars.filter(StaticSemantics.freeVars(vTerm).contains(_)).filter(!_.equals(v))
    }

    var nonDependentSet : List[Variable] = primedVars.filter(dependencies(_).isEmpty)
    val possiblyDependentOdes = odes.filter(ode => !nonDependentSet.contains(ode.xp.x))

    if(possiblyDependentOdes.isEmpty) nonDependentSet
    else {
      if(prevOdes.equals(possiblyDependentOdes)) throw new Exception("Cycle detected!")
      nonDependentSet ++ sortAtomicOdesHelper(possiblyDependentOdes, odes)
    }
  }

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
    * Converts formulas of the form x = term into a map x -> term, and ignores all formulas of other forms.
    *
    * @param fs A list of formulas.
    * @return A map (f -> term) which maps each f in fs of the foram f=term to term.
    */
  private def conditionsToValues(fs : List[Formula]) : Map[Variable, Term] = {
    val flattened = flattenAnds(fs)
    val vOnLhs = flattened.map({
      case Equal(left, right) => left match {
        case v : Variable => Some(v, right)
        case _ => None
      }
      case _ => None
    })

    val vOnRhs = flattened.map({
      case Equal(left, right) => right match {
        case v : Variable => Some(v, left)
        case _ => None
      }
      case _ => None
    })

    (vOnLhs ++ vOnRhs)
      .filter(_.isDefined)
      .map(e => e.get._1 -> e.get._2)
      .toMap
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
    *
    * @param v A variable occuring in the odes program.
    * @param program An ode system.
    * @return true if the program does not already contain an = constraint (a.k.a. sol'n) for v in the evolution domain.
    */
  def isUnsolved(v : Variable, program : DifferentialProgram) = {
    val odes = atomicODEs(program)
    if(odes.find(_.xp.x.equals(v)).isEmpty) false //Variables that don't occur in the ODE are trivially already solved.
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

  //endregion

  //region Simple integrator

  /**
    * If v' = term occurs in the system of ODEs, then this function computes the integral of term.
    * Assumes that the ODEs have a time variable, that a formula of the form v=f occurs in the initialConditions formulas,
    * and that the system of odes is blah blah.
    *
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
    *
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
    case Neg(c) => Neg(integrator(c, t))
    case Power(base, exp) => exp match {
      case Number(n) =>
        if(n == 1) integrator(base, t)
        else       Times(Divide(Number(1), Number(n+1)), integrator(Power(base, Number(n-1)), t))
      case _ => throw new Exception("Cannot integrate terms with non-number exponents!")
    }
    case x : Term if !StaticSemantics.freeVars(x).contains(t) => Times(x, t)
  }

  /**
    * Given x' = f, replaces all variables in f with their recurrences or initial conditions.
    *
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
    assert(odes.find(ode => ode.xp.x.equals(v)).isDefined, "Cannot solve for a variable that does not occur in the ODE")

    val primedVariables : Set[Variable] = odes.map(_.xp.x).toSet

    //Compute the free variables in the ode corresponding to v'.
    val ode = odes.find(_.xp.x.equals(v)).getOrElse(throw new Exception("Could not find ODE associated with " + v))
    val varsInOde = StaticSemantics.freeVars(ode.e).toSet.map((x : NamedSymbol) => {
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
    * @param program (An system of) odes.
    * @param initialConstraints Formulas describing initial values.
    * @param x A variable that occurs on the left hand side of some ode.
    * @return Some(term) if x = term occurs in either the ev.dom. constraint or the initial constraints. Otherwise, None.
    */
  private def recurrence(program : DifferentialProgram, initialConstraints : List[Formula], x : Variable) : Option[Term] = {
    val odeConditions = conditionsToValues(flattenAnds(odeConstraints(program)))
    val initialConditions = conditionsToValues(flattenAnds(initialConstraints))
    if(odeConditions.contains(x)) odeConditions.get(x)
    else if(initialConditions.contains(x)) initialConditions.get(x)
    else None
  }

  //endregion

  //region Misc.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
  val noDiamondsForNowExn = AxiomaticODESolverExn("No diamonds for now.")

//  def childPosition(pos: Position) =
//    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.child)
//    else SuccPosition(pos.checkSucc.top, pos.inExpr.child)

  def parentPosition(pos: Position) =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.parent)
    else SuccPosition(pos.checkSucc.top, pos.inExpr.parent)

  def subPosition(pos: Position, sub: PosInExpr) =
    if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr + sub)
    else SuccPosition(pos.checkSucc.top, pos.inExpr + sub)
  def subPosition(pos: Position, sub: List[Int]) = subPosition(pos, PosInExpr(sub))

  //endregion
}

/*
Todo list:
 1. Implement differential ghosts and inverse differential ghosts.
 2. Add t' = 1 if it's not already present
 3. Re-order the ODE so that it's in the correct dependency ordering.
 ...
 */