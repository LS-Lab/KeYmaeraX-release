/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.robustify

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, BelleExpr, BelleValue, DependentTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.{DifferentialHelper, ProgramHelpers}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
  * Adds sensor noise to a provably correct model without any sensor noise. The Provable's conclusion must have the form:
  * {{{
  *   ⊢ ...blah & s ~ t & blah... -> [choiceOfGuardedAssignments; ODE]P(s)
  *
  *   with ~ \in = >= <=
  *
  *   where choiceOfGuardedAssignments is a choice among a sequence of optionally guarded assignments:
  *
  *   ?H_1; a_1 := t_1 ++ ... ++ a_m := t_m ++ ... ++ ?H_n; a_n := t_n
  *
  *   with the guards in each case optional.
  * }}}
  *
  * @author Nathan Fulton
  */
object SensorUncertainty {
  //@todo incorrect setup -- should be an applied DependentInputTactic.
  def apply(sensor: Variable) : DependentTactic = new DependentTactic("robustify.SensorUncertainty") {
    override def computeExpr(p: ProvableSig): BelleExpr = {
      assert(p.isProved, "Cannot robustify an unproven model.")
      assert(shapeAnalysis(p, sensor), "The Provable's conclusion does not have the correct shape to robustify against sensor uncertainty.")
      ???
    }
  }

  /** Returns true if the Provable's conclusion has the correct shape. */
  private def shapeAnalysis(p: ProvableSig, sensor: Variable): Boolean =
    p.conclusion.succ.length == 1 &&
    p.conclusion.ante.length == 0 &&
    (p.conclusion.succ.head match {
      case Imply(precond, Box(program, conclusion)) =>
        preconditionShapeAnalysis(sensor, precond).isDefined &&
        programShapeAnalysis(sensor, program).isDefined
      case _ => false
    })

  /** Checks that the preconditions are a sequence of And's that contains some ComparisonFormula placing initial conditions on the sensor variable.
    * @returns Some ComparisonFormula containing only the sensor variable on the left or right-hand side, or else None. */
  private def preconditionShapeAnalysis(sensor: Variable, preconditions: Formula): Option[ComparisonFormula] = {
    val sensorPreconds = DifferentialHelper.flattenAnds(preconditions :: Nil).filter({
      case cmp: ComparisonFormula => cmp.left == sensor || cmp.right == sensor //@todo could make the tactic more robust by supporting anything s.t. filter(freeVars(_).contains(sensors))
      case _ => false
    })
    if(sensorPreconds.length == 1) Some(sensorPreconds.head.asInstanceOf[ComparisonFormula]) //this cast necessarily succeeds
    else None
  }

  /** Checks that the program is a choice between sequences of programs, each of which is a single test followed by a
    * sequence of assignments.
    * @returns Some list of control branches that write to the sensor variable, or None if the program does not have the correct shape. */
  private def programShapeAnalysis(sensor: Variable, program: Program): Option[List[Program]] = {

    val choices = program match {
      //@todo This is wrong -- want to support {{blah ++ blah}; ODE}* but only support {blah ++ blah}*
      case Loop(subprogram) => ProgramHelpers.decomposeChoices(program)
      case _ => ProgramHelpers.decomposeChoices(program)
    }

    //Each of the choices should be an optionally guarded assignment
    if(!choices.forall(ProgramHelpers.optionallyGuardedAssignments)) None
    else {
      //Find the branch of the program that contains an assignment to the sensor variable.
      Some(choices.filter({
        case Compose(Test(_), assignments) => ProgramHelpers.containsAssignmentTo(assignments, sensor)
        case _ => false
      })) //could be Some(Nil), that's OK.
    }
  }
}
