/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.codegen

import org.keymaerax.codegen.CFormulaTermGenerator._
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.parser.Declaration

import scala.annotation.nowarn

object CMonitorGenerator {

  /** The name of the monitor function argument representing the previous state. */
  private val MONITOR_PRE_STATE_NAME = CPrettyPrinter.PRE

  /** The name of the monitor function argument representing the current state. */
  private val MONITOR_CURR_STATE_NAME = CPrettyPrinter.CURR

  /** The name of the monitor function argument representing monitor parameters. */
  private val MONITOR_PARAMS_NAME = CPrettyPrinter.PARAMS

  /** The name of the monitor function argument representing controller inputs. */
  private val INPUT_NAME = "in"

  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  def termContainer(expr: Expression, params: Set[NamedSymbol]): String = expr match {
    case t: Variable if params.contains(t) => MONITOR_PARAMS_NAME + "->"
    case t: Variable if !params.contains(t) && t.name.endsWith("post") => MONITOR_CURR_STATE_NAME + "."
    case t: Variable if !params.contains(t) => MONITOR_PRE_STATE_NAME + "."
    case FuncOf(fn, Nothing) if params.contains(fn) => MONITOR_PARAMS_NAME + "->"
    case FuncOf(fn @ Function(fname, _, _, _, _), Nothing) if !params.contains(fn) && fname.endsWith("post") =>
      MONITOR_CURR_STATE_NAME + "."
    case FuncOf(fn, Nothing) if !params.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  }
}

/**
 * Generates a monitor from a ModelPlex expression.
 * @author
 *   Stefan Mitsch
 */
class CMonitorGenerator(conjunctionsAs: Symbol, defs: Declaration)
    extends MonitorGenerator(conjunctionsAs, defs, CPrettyPrinter, CMonitorGenerator.termContainer) {

  /** Some reserved names, such as: main, Main */
  private val RESERVED_NAMES = Set("main", "Main")

  /** @inheritdoc */
  override def apply(
      expr: Expression,
      stateVars: Set[BaseVariable],
      inputVars: Set[BaseVariable],
      modelName: String,
  ): (String, String) = generateMonitoredCtrlCCode(expr, stateVars)

  /**
   * Generates a monitor `expr` that switches between a controller and a fallback controller depending on the monitor
   * outcome.
   */
  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  private def generateMonitoredCtrlCCode(expr: Expression, stateVars: Set[BaseVariable]): (String, String) = {
    val symbols = StaticSemantics.symbols(expr)
    val names = symbols.map(nameIdentifier)
    require(names.size == symbols.size, "Expect unique name_index identifiers for code generation")
    require(
      names.intersect(RESERVED_NAMES).isEmpty,
      "Unexpected reserved C names encountered: " + names.intersect(RESERVED_NAMES).mkString(","),
    )

    val parameters = CodeGenerator.getParameters(defs.exhaustiveSubst(expr), stateVars)

    import CMonitorGenerator._

    val monitorDistFuncHead =
      s"""/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */
         |verdict boundaryDist(state $MONITOR_PRE_STATE_NAME, state $MONITOR_CURR_STATE_NAME, const parameters* const $MONITOR_PARAMS_NAME)"""
        .stripMargin

    val monitorSatFuncHead =
      s"""/* Evaluates monitor condition in prior and current state */
         |bool monitorSatisfied(state $MONITOR_PRE_STATE_NAME, state $MONITOR_CURR_STATE_NAME, const parameters* const $MONITOR_PARAMS_NAME)"""
        .stripMargin

    val monitoredCtrlFuncHead =
      s"""/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */
         |state monitoredCtrl(state $MONITOR_CURR_STATE_NAME, const parameters* const $MONITOR_PARAMS_NAME, const input* const $INPUT_NAME,
         |                    state (*ctrl)(state,const parameters* const,const input* const),
         |                    state (*fallback)(state,const parameters* const,const input* const))""".stripMargin

    val monitoredCtrlFuncBody =
      s"""  state $MONITOR_PRE_STATE_NAME = $MONITOR_CURR_STATE_NAME;
         |  state post = (*ctrl)($MONITOR_PRE_STATE_NAME,$MONITOR_PARAMS_NAME,$INPUT_NAME);
         |  if (!monitorSatisfied($MONITOR_PRE_STATE_NAME,post,$MONITOR_PARAMS_NAME)) return (*fallback)($MONITOR_PRE_STATE_NAME,$MONITOR_PARAMS_NAME,$INPUT_NAME);
         |  else return post;""".stripMargin

    // @note negate to turn into safety distance >=0 satisfied, <0 unsatisfied monitor
    def negate(s: String): String = "-(" + s + ")"
    val ((distDefs, distBody), satBody) = expr match {
      // @note when translated expression came in metric form or as a program, boundaryDist outputs a distance measure.
      // otherwise interpret the result as C boolean (0 is false, != 0 is true)
      // and turn into boundary distance >=0 is satisfied monitor <0 is unsatisfied
      case LessEqual(l, r) =>
        val lhsMonitor = printMonitor(l, parameters)
        val rhsMonitor = printMonitor(r, parameters)
        val lhs = negate(lhsMonitor._2)
        val rhs = negate(rhsMonitor._2)
        (
          (lhsMonitor._1 + rhsMonitor._1, s"return $lhs"),
          s"boundaryDist($MONITOR_PRE_STATE_NAME,$MONITOR_CURR_STATE_NAME,$MONITOR_PARAMS_NAME).val >= " + rhs,
        )
      case Less(l, r) =>
        val lhsMonitor = printMonitor(l, parameters)
        val rhsMonitor = printMonitor(r, parameters)
        val lhs = negate(lhsMonitor._2)
        val rhs = negate(rhsMonitor._2)
        (
          (lhsMonitor._1 + rhsMonitor._1, s"return $lhs"),
          s"boundaryDist($MONITOR_PRE_STATE_NAME,$MONITOR_CURR_STATE_NAME,$MONITOR_PARAMS_NAME).val > " + rhs,
        )
      case f: Formula if f.isFOL =>
        val monitor = printMonitor(expr, parameters)
        (
          (
            monitor._1,
            s"verdict result = { .id=(${monitor._2} ? 1 : -1), .val=(${monitor._2} ? 1.0L : -1.0L) }; return result",
          ),
          s"boundaryDist($MONITOR_PRE_STATE_NAME,$MONITOR_CURR_STATE_NAME,$MONITOR_PARAMS_NAME).val >= 0.0L",
        )
      case f: Formula if !f.isFOL =>
        (
          printMonitor(expr, parameters),
          s"boundaryDist($MONITOR_PRE_STATE_NAME,$MONITOR_CURR_STATE_NAME,$MONITOR_PARAMS_NAME).val >= 0.0L",
        )
    }

    (
      s"""$monitorDistFuncHead {
         |  $distBody;
         |}
         |
         |$monitorSatFuncHead {
         |  return $satBody;
         |}
         |
         |$monitoredCtrlFuncHead {
         |$monitoredCtrlFuncBody
         |}
         |
         |""".stripMargin,
      distDefs.trim,
    )
  }
}
