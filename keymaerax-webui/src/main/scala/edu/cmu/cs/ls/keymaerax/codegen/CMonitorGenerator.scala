/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.codegen.CFormulaTermGenerator._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.Declaration

object CMonitorGenerator {

  /** The name of the monitor function argument representing the current state. */
  private val MONITOR_CURR_STATE_NAME = "curr"
  /** The name of the monitor function argument representing monitor parameters. */
  private val MONITOR_PARAMS_NAME = "params"
  /** The name of the monitor function argument representing controller inputs. */
  private val INPUT_NAME = "in"

  def termContainer(expr: Expression, params: Set[NamedSymbol]): String = expr match {
    case t: Variable if  params.contains(t) => "params->"
    case t: Variable if !params.contains(t) && t.name.endsWith("post") => "curr."
    case t: Variable if !params.contains(t) => "pre."
    case FuncOf(fn, Nothing) if  params.contains(fn) => "params->"
    case FuncOf(fn@Function(fname, _, _, _, _), Nothing) if !params.contains(fn) && fname.endsWith("post") => "curr."
    case FuncOf(fn, Nothing) if !params.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  }
}

/**
  * Generates a monitor from a ModelPlex expression.
  * @author Stefan Mitsch
  */
class CMonitorGenerator(conjunctionsAs: Symbol, defs: Declaration) extends MonitorGenerator(conjunctionsAs, defs,
  CPrettyPrinter, CMonitorGenerator.termContainer) {

  /** Some reserved names, such as: main, Main */
  private val RESERVED_NAMES = Set("main", "Main")

  /** @inheritdoc */
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                     modelName: String): (String, String) =
    generateMonitoredCtrlCCode(expr, stateVars)

  /** Generates a monitor `expr` that switches between a controller and a fallback controller depending on the monitor outcome. */
  private def generateMonitoredCtrlCCode(expr: Expression, stateVars: Set[BaseVariable]): (String, String) = {
    val symbols = StaticSemantics.symbols(expr)
    val names = symbols.map(nameIdentifier)
    require(names.size == symbols.size, "Expect unique name_index identifiers for code generation")
    require(names.intersect(RESERVED_NAMES).isEmpty, "Unexpected reserved C names encountered: " + names.intersect(RESERVED_NAMES).mkString(","))

    val parameters = CodeGenerator.getParameters(defs.exhaustiveSubst(expr), stateVars)

    import CMonitorGenerator._

    val monitorDistFuncHead =
      s"""/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */
         |verdict boundaryDist(state pre, state curr, const parameters* const params)""".stripMargin

    val monitorSatFuncHead =
      s"""/* Evaluates monitor condition in prior and current state */
        |bool monitorSatisfied(state pre, state curr, const parameters* const params)""".stripMargin

    val monitoredCtrlFuncHead =
      s"""/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */
        |state monitoredCtrl(state $MONITOR_CURR_STATE_NAME, const parameters* const $MONITOR_PARAMS_NAME, const input* const $INPUT_NAME,
        |                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const))""".stripMargin

    val monitoredCtrlFuncBody =
      s"""  state pre = curr;
         |  state post = (*ctrl)(pre,params,in);
         |  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);
         |  else return post;""".stripMargin

    // @note negate to turn into safety distance >=0 satisfied, <0 unsatisfied monitor
    def negate(s: String): String = "-(" + s + ")"
    val ((distDefs, distBody), satBody) = expr match {
      //@note when translated expression came in metric form or as a program, boundaryDist outputs a distance measure.
      // otherwise interpret the result as C boolean (0 is false, != 0 is true)
      // and turn into boundary distance >=0 is satisfied monitor <0 is unsatisfied
      case LessEqual(l, r) =>
        val lhsMonitor = printMonitor(l, parameters)
        val rhsMonitor = printMonitor(r, parameters)
        val lhs = negate(lhsMonitor._2)
        val rhs = negate(rhsMonitor._2)
        ((lhsMonitor._1 + rhsMonitor._1, s"return $lhs"), "boundaryDist(pre,curr,params).val >= " + rhs)
      case Less(l, r) =>
        val lhsMonitor = printMonitor(l, parameters)
        val rhsMonitor = printMonitor(r, parameters)
        val lhs = negate(lhsMonitor._2)
        val rhs = negate(rhsMonitor._2)
        ((lhsMonitor._1 + rhsMonitor._1, s"return $lhs"), "boundaryDist(pre,curr,params).val > " + rhs)
      case f: Formula if f.isFOL =>
        val monitor = printMonitor(expr, parameters)
        ((monitor._1, s"verdict result = { .id=(${monitor._2} ? 1 : -1), .val=(${monitor._2} ? 1.0L : -1.0L) }; return result"), "boundaryDist(pre,curr,params).val >= 0.0L")
      case f: Formula if !f.isFOL => (printMonitor(expr, parameters), "boundaryDist(pre,curr,params).val >= 0.0L")
    }

    (s"""$monitorDistFuncHead {
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
       |""".stripMargin, distDefs.trim)
  }
}
