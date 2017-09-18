/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.codegen.CFormulaTermGenerator._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

/**
  * Generates a monitor from a ModelPlex expression.
  * @author Stefan Mitsch
  */
class CMonitorGenerator(val kind: String = "boolean") extends CodeGenerator {
  override def apply(expr: Expression, stateVars: Set[BaseVariable], modelName: String): String =
    generateMonitoredCtrlCCode(expr, stateVars)

  /** Generates a monitor `expr` that switches between a controller and a fallback controller depending on the monitor outcome. */
  private def generateMonitoredCtrlCCode(expr: Expression, stateVars: Set[BaseVariable]) : String = {
    val symbols = StaticSemantics.symbols(expr)
    val names = symbols.map(nameIdentifier)
    require(names.size == symbols.size, "Expect unique name_index identifiers for code generation")
    require(names.intersect(RESERVED_NAMES).isEmpty, "Unexpected reserved C names encountered: " + names.intersect(RESERVED_NAMES).mkString(","))

    val parameters = getParameters(expr, stateVars)

    val monitorDistFuncHead =
      s"""/* Computes distance to safety boundary on prior and current state (negative == safe, positive == unsafe) */
         |long double boundaryDist(state pre, state curr, const parameters* const params)""".stripMargin

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

    val (distBody, satBody) = kind match {
      case "boolean" => (printMonitor(expr, parameters) + " ? 0.0 : 1.0", "boundaryDist(pre,curr,params) <= 0.0")
      case "metric" =>
        assert(expr.isInstanceOf[LessEqual] || expr.isInstanceOf[Less], "Expected <= or < expression as monitor, but got " + expr.prettyString)
        val monitor = printMonitor(expr, parameters)
        (monitor.substring(0, monitor.indexOf("<")), "boundaryDist(pre,curr,params)" + monitor.substring(monitor.indexOf("<")))
    }

    s"""$monitorDistFuncHead {
       |  return $distBody;
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
       |""".stripMargin
  }

  /** The name of the monitor function argument representing the current state. */
  private val MONITOR_CURR_STATE_NAME = "curr"
  /** The name of the monitor function argument representing monitor parameters. */
  private val MONITOR_PARAMS_NAME = "params"
  /** The name of the monitor function argument representing controller inputs. */
  private val INPUT_NAME = "in"

  /** Some reserved names, such as: main, Main */
  private val RESERVED_NAMES = Set("main", "Main")

  /**
    * Returns a set of names (excluding names in `vars` and interpreted functions) that are immutable parameters of the
    * expression `expr`. */
  private def getParameters(expr: Expression, exclude: Set[BaseVariable]): Set[NamedSymbol] =
    StaticSemantics.symbols(expr)
      .filter({
        case Function("abs", None, Real, Real, true) => false
        case Function("min" | "max", None, Tuple(Real, Real), Real, true) => false
        case Function(name, _, Unit, _, _) => !exclude.exists(v => v.name == name.stripSuffix("post"))
        case _: Function => false
        case BaseVariable(name, _, _) => !exclude.exists(v => v.name == name.stripSuffix("post"))
      })

  /** Compiles primitive expressions with the appropriate params/curr/pre struct location. */
  private def primitiveExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator({
    case t: Variable if  parameters.contains(t) => "params->"
    case t: Variable if !parameters.contains(t) => "pre."
    case FuncOf(fn, Nothing) if  parameters.contains(fn) => "params->"
    case FuncOf(fn@Function(fname, _, _, _, _), Nothing) if !parameters.contains(fn) && fname.endsWith("post") => "curr."
    case FuncOf(fn, Nothing) if !parameters.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  })

  /**
    * Compiles the expression `e` to C code as a body of a monitored controller execution function.
    * Names in `stateVars` are fields of the monitor function's argument "curr", names in `parameters` are fields of
    * the argument "params".
    */
  private def printMonitor(e: Expression, parameters: Set[NamedSymbol]): String = e match {
    case f: Formula if f.isFOL => primitiveExprGenerator(parameters)(f)
    case _ => throw new CodeGenerationException("The input expression: \n" + KeYmaeraXPrettyPrinter(e) + "\nis expected to be a FOL formula.")
  }
}
