/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.codegen

import org.keymaerax.codegen.CFormulaTermGenerator.nameIdentifier
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.parser.Declaration

object PythonMonitorGenerator {

  /** The name of the monitor/control function argument representing the current state. */
  private val MONITOR_CURR_STATE_NAME = PythonPrettyPrinter.CURR

  /** The name of the monitor/control function argument representing the previous state. */
  private val MONITOR_PRE_STATE_NAME = PythonPrettyPrinter.PRE

  /** The name of the monitor/control function argument representing the next state. */
  private val MONITOR_POST_STATE_NAME = "post"

  /** The name of the monitor/control function argument representing monitor parameters. */
  private val MONITOR_PARAMS_NAME = PythonPrettyPrinter.PARAMS

  /**
   * The name of the control function argument representing inputs (resolves picking values for non-deterministically
   * assigned discrete variables in the model).
   */
  private val INPUT_NAME = "inp"

  def termContainer(expr: Expression, parameters: Set[NamedSymbol]): String = expr match {
    case t: Variable if parameters.contains(t) => MONITOR_PARAMS_NAME + "."
    case t: Variable if !parameters.contains(t) && t.name.endsWith("post") => MONITOR_CURR_STATE_NAME + "."
    case t: Variable if !parameters.contains(t) => MONITOR_PRE_STATE_NAME + "."
    case FuncOf(fn, Nothing) if parameters.contains(fn) => MONITOR_PARAMS_NAME + "."
    case FuncOf(fn @ Function(fname, _, _, _, _), Nothing) if !parameters.contains(fn) && fname.endsWith("post") =>
      MONITOR_CURR_STATE_NAME + "."
    case FuncOf(fn, Nothing) if !parameters.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException(
        "Non-posterior, non-parameter function symbol is not supported: " + fn.prettyString
      )
  }
}

/**
 * Generates a monitor from a ModelPlex expression.
 * @author
 *   Stefan Mitsch
 */
class PythonMonitorGenerator(conjunctionsAs: Symbol, defs: Declaration)
    extends MonitorGenerator(conjunctionsAs, defs, PythonPrettyPrinter, PythonMonitorGenerator.termContainer) {

  /** @inheritdoc */
  override def apply(
      expr: Expression,
      stateVars: Set[BaseVariable],
      inputVars: Set[BaseVariable],
      modelName: String,
  ): (String, String) = generateMonitoredCtrlPythonCode(expr, stateVars)

  /**
   * Generates a monitor `expr` that switches between a controller and a fallback controller depending on the monitor
   * outcome.
   */
  private def generateMonitoredCtrlPythonCode(expr: Expression, stateVars: Set[BaseVariable]): (String, String) = {
    val symbols = StaticSemantics.symbols(expr)
    val names = symbols.map(nameIdentifier)
    require(names.size == symbols.size, "Expect unique name_index identifiers for code generation")
    require(
      names.intersect(PythonGenerator.RESERVED_NAMES).isEmpty,
      "Unexpected reserved C names encountered: " + names.intersect(PythonGenerator.RESERVED_NAMES).mkString(","),
    )

    val parameters = CodeGenerator.getParameters(defs.exhaustiveSubst(expr), stateVars)

    import PythonMonitorGenerator._
    val monitorDistFuncHead =
      s"""def boundaryDist($MONITOR_PRE_STATE_NAME: State, $MONITOR_CURR_STATE_NAME: State, $MONITOR_PARAMS_NAME: Params) -> Verdict:
         |  '''
         |  Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe)
         |  '''""".stripMargin

    val monitorSatFuncHead =
      s"""def monitorSatisfied($MONITOR_PRE_STATE_NAME: State, $MONITOR_CURR_STATE_NAME: State, $MONITOR_PARAMS_NAME: Params) -> bool:
         |  '''
         |  Evaluates monitor condition in prior and current state
         |  '''""".stripMargin

    val monitoredCtrlFuncHead =
      s"""def monitoredCtrl($MONITOR_CURR_STATE_NAME: State, $MONITOR_PARAMS_NAME: Params, $INPUT_NAME: State,
         |                  ctrl: Callable[[State, State, Params], State],
         |                  fallback: Callable[[State, State, Params], State]) -> State:
         |  '''
         |  Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor
         |  '''""".stripMargin

    val monitoredCtrlFuncBody =
      s"""$MONITOR_PRE_STATE_NAME = $MONITOR_CURR_STATE_NAME
         |  $MONITOR_POST_STATE_NAME = ctrl($MONITOR_PRE_STATE_NAME,$MONITOR_PARAMS_NAME,$INPUT_NAME)
         |  if monitorSatisfied($MONITOR_PRE_STATE_NAME,$MONITOR_POST_STATE_NAME,$MONITOR_PARAMS_NAME) == True:
         |    return $MONITOR_POST_STATE_NAME
         |  else:
         |    return fallback($MONITOR_PRE_STATE_NAME,$MONITOR_PARAMS_NAME,$INPUT_NAME)""".stripMargin

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
          (monitor._1, s"result = Verdict((1 if ${monitor._2} else -1), (1 if ${monitor._2} else -1) )\nreturn result"),
          s"boundaryDist($MONITOR_PRE_STATE_NAME,$MONITOR_CURR_STATE_NAME,$MONITOR_PARAMS_NAME).val >= 0",
        )
      case f: Formula if !f.isFOL =>
        (
          printMonitor(expr, parameters),
          s"boundaryDist($MONITOR_PRE_STATE_NAME,$MONITOR_CURR_STATE_NAME,$MONITOR_PARAMS_NAME).val >= 0",
        )
    }

    (
      s"""
         |
         |$monitorDistFuncHead
         |${distBody.linesWithSeparators.map("  " + _).mkString}
         |
         |$monitorSatFuncHead
         |  return $satBody
         |
         |$monitoredCtrlFuncHead
         |  $monitoredCtrlFuncBody
         |""".stripMargin,
      distDefs.trim,
    )
  }
}
