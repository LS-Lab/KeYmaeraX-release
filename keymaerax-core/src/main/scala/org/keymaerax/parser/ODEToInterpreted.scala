/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core.{
  And,
  Assign,
  AssignAny,
  AtomicODE,
  Choice,
  Compose,
  Diamond,
  DifferentialProduct,
  DifferentialProgram,
  DifferentialSymbol,
  DotTerm,
  Equal,
  Function,
  Neg,
  Number,
  ODESystem,
  Program,
  Real,
  SetLattice,
  StaticSemantics,
  Term,
  True,
  Variable,
}

import scala.collection.immutable.Seq

object ODEToInterpreted {

  case class FromProgramException(msg: String) extends Exception

  /**
   * Parse program input for differential equation definitions, e.g.
   * {{{
   * {s:=0;c:=0;t:=0} {s'=c,c'=-s,t'=1}
   * {e:=1;} {e'=e}
   * }}}
   * into the form needed for `convert` (used by the parser).
   */
  def fromProgram(system: Program, t: Variable): Seq[Function] = system match {
    case Compose(assgns, ODESystem(ode, True)) =>
      def unfoldAssgns(x: Program): Map[Variable, Term] = x match {
        case Assign(v, e) => Map(v -> e)
        case Compose(l, r) => unfoldAssgns(l) ++ unfoldAssgns(r)
        case _ => throw FromProgramException("Unable to unfold initial conditions to a list of assignments.")
      }

      def unfoldODE(x: DifferentialProgram): Map[Variable, Term] = x match {
        case AtomicODE(DifferentialSymbol(v), e) => Map(v -> e)
        case DifferentialProduct(l, r) => unfoldODE(l) ++ unfoldODE(r)
        case _ => throw FromProgramException("Unable to unfold ODEs to a list of atomic ODEs.")
      }

      val assgnMap = unfoldAssgns(assgns)
      val odeMap = unfoldODE(ode)

      if (assgnMap.contains(t) != odeMap.contains(t)) throw FromProgramException(
        "ODE and initial condition for " + t + " must be both given explicitly or both omitted."
      )

      // Time ODE defaults to initial time 0
      val t0 = assgnMap.get(t) match {
        case None => {
          if (odeMap.values.exists(e => StaticSemantics.freeVars(e).contains(t))) throw FromProgramException(
            "Time-dependent ODEs must have time variables explicit in initial condition and ODEs."
          )
          Number(0)
        }
        case Some(tt) =>
          if (odeMap(t) != Number(1)) { throw FromProgramException("Time ODE must have RHS 1.") }
          tt
      }

      fromSystem((assgnMap.-(t)).toIndexedSeq.map { case (v, init) => (v, odeMap(v), init) }, t, t0)

    case _ => throw FromProgramException("Program not of the form Compose(initAssignments, ode)")
  }

  /**
   * Converts a system of differential equations to interpreted functions. The input is a sequence of `(variable,
   * differential, initial value)` tuples, one for each time-evolving function.
   *
   * Functions will be named after the variables used to represent them.
   *
   * Example input system for defining sin and cos:
   * {{{
   * (sin, cos, 0),
   * (cos, -sin, 1)
   * }}}
   *
   * @note
   *   Differential expressions `( )'` cannot appear in the input differentials.
   *
   * @param system
   *   seq of (function, differential, initial value)
   * @param tVar
   *   the time variable used in input differentials
   * @param t0
   *   initial time
   * @return
   *   List of implicitly defined functions by the system of ODEs from the given initial time
   */
  def fromSystem(system: Seq[(Variable, Term, Term)], tVar: Variable, t0: Term): Seq[Function] = {
    require(system.nonEmpty, "Must define at least one function.")

    val syst = system :+ (tVar, Number(1), t0)

    val vars = syst.map(_._1)
    require(vars.toSet.size == vars.size, "Function names must be distinct.")

    require(
      syst.forall { case (_, diff, init) =>
        StaticSemantics.freeVars(init).isEmpty && // Init should be constant
        StaticSemantics
          .freeVars(diff)
          .subsetOf(SetLattice(syst.map(_._1))) // ODEs should be free only in input variables
      },
      "Initial condition must not mention free variables and ODEs must not mention additional free variables.",
    )

    val forwardODE = ODESystem(
      // ODE variable differentials
      syst
        .map { case (v, diff, _) => AtomicODE(DifferentialSymbol(v), diff) }
        .reduce[DifferentialProgram](DifferentialProduct(_, _))
    )

    val backwardODE = ODESystem(
      // ODE variable diffs
      syst
        .map { case (v, diff, _) => AtomicODE(DifferentialSymbol(v), Neg(diff)) }
        .reduce[DifferentialProgram](DifferentialProduct(_, _))
    )

    val goal = syst.map { case (v, _, i) => Equal(v, i) }.reduceRight(And)

    system.map { case (v, _, _) =>
      val otherVars = system.map(_._1).filter(_ != v)

      val assignments = otherVars
        .map(AssignAny)
        .foldRight(Compose(Assign(v, DotTerm(idx = Some(0))), Assign(tVar, DotTerm(idx = Some(1)))))(Compose)

      Function(
        v.name,
        v.index,
        domain = Real,
        sort = Real,
        interp = Some(Diamond(Compose(assignments, Choice(backwardODE, forwardODE)), goal)),
      )
    }
  }
}
