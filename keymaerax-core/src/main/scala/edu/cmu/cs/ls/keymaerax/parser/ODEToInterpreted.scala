package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{And, Assign, AssignAny, AtomicODE, AtomicProgram, Choice, Compose, CompositeProgram, Diamond, Differential, DifferentialProduct, DifferentialProgram, DifferentialProgramConst, DifferentialSymbol, DotTerm, Equal, FuncOf, Function, Neg, Number, ODESystem, Program, Real, SetLattice, StaticSemantics, Term, True, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor

import scala.collection.immutable.Seq

object ODEToInterpreted {

  case class FromProgramException(msg: String) extends Exception

  /**
   * Parse program input for differential equation definitions, e.g.
   *      {s:=0;c:=0;} {s'=c,c'=-s}
   *      {e:=1;} {e'=e}
   * into the form needed for `convert` (used by the parser).
   */
  def fromProgram(system: Program, t: Variable = Variable("t"), t0: Term = Number(0)): Seq[Function] =
    system match {
      case Compose(assgns, ODESystem(ode, True)) =>
        def unfoldAssgns(x: Program): Map[Variable, Term] = x match {
          case Assign(v,e) => Map(v -> e)
          case Compose(l,r) => unfoldAssgns(l) ++ unfoldAssgns(r)
          case _ => throw FromProgramException("Left side of compose not made of assignments!")
        }
        def unfoldODE(x: DifferentialProgram): Map[Variable, Term] = x match {
          case AtomicODE(DifferentialSymbol(v),e) => Map(v -> e)
          case DifferentialProduct(l,r) => unfoldODE(l) ++ unfoldODE(r)
        }
        val assgnMap = unfoldAssgns(assgns)
        val odeMap = unfoldODE(ode)

        fromSystem(assgnMap.toIndexedSeq.map{case(v,init) =>
          (v,odeMap(v),init)
        }, t, t0)
      case _ => throw FromProgramException("Program not of the form Compose(initAssignments, ode)")
    }

  /**
   * Converts a system of differential equations to
   * interpreted functions. The input is a sequence of
   *     (variable, differential, initial value)
   * tuples, one for each time-evolving function.
   *
   * Functions will be named after the variables used
   * to represent them.
   *
   * Example input system for defining sin and cos:
   *        (sin, cos, 0),
   *        (cos, -sin, 1)
   *
   * @note Differential expressions ( )' cannot appear in the
   * input differentials.
   *
   * @param system seq of (function, differential, initial value)
   * @param tVar the time variable used in input differentials
   * @param t0 initial time
   * @return
   */
  def fromSystem(system: Seq[(Variable, Term, Term)], tVar: Variable = Variable("t"), t0: Term = Number(0)): Seq[Function] = {
    assert(system.nonEmpty)
    assert(system.map(_._1).distinct == system.map(_._1)) // Input variables are all distinct
    assert(system.forall{case(_,diff,init) =>
      StaticSemantics.freeVars(init).isEmpty && // Init should be constant
      StaticSemantics.freeVars(diff).subsetOf(SetLattice(system.map(_._1))) // Diff should be free only in input variables
    })

    val forwardODE = ODESystem((
      // ODE variable differentials
      system.map{case(v, diff, _) =>
        AtomicODE(DifferentialSymbol(v),diff)
      } :+ // Time variable diff
        AtomicODE(DifferentialSymbol(tVar),Number(1))
      ).reduce[DifferentialProgram](DifferentialProduct(_,_)))

    val backwardODE = ODESystem((
      // ODE variable diffs
      system.map{case(v, diff, _) =>
        AtomicODE(DifferentialSymbol(v),Neg(diff))
      } :+ // Time variable diff
        AtomicODE(DifferentialSymbol(tVar),Neg(Number(1)))
      ).reduce[DifferentialProgram](DifferentialProduct(_,_)))

    val goal = system.map{case(v,_,i) => Equal(v, i)}.reduceRight(And)

    system.map{case(v,_,_) =>
      val otherVars = system.map(_._1).filter(_ != v)

      val assignments = otherVars.map(AssignAny).foldRight(
        Compose(Assign(v, DotTerm(idx=Some(0))),Assign(tVar,DotTerm(idx=Some(1))))
      )(Compose)

      Function(v.name, v.index, domain=Real, sort=Real, interp=Some(
        Diamond(
          Compose(assignments, Choice(backwardODE,forwardODE))
          , goal)
      ))
    }
  }
}
