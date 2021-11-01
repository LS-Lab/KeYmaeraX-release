/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.{ModelPlex, SimplifierV3}
import edu.cmu.cs.ls.keymaerax.codegen.CFormulaTermGenerator._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, InterpretedSymbols, KeYmaeraXPrettyPrinter}

/**
  * Generates a monitor from a ModelPlex expression.
  * @author Stefan Mitsch
  */
class CMonitorGenerator(conjunctionsAs: Symbol, defs: Declaration = Declaration(Map.empty)) extends CodeGenerator {
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

  /** The name of the monitor function argument representing the current state. */
  private val MONITOR_CURR_STATE_NAME = "curr"
  /** The name of the monitor function argument representing monitor parameters. */
  private val MONITOR_PARAMS_NAME = "params"
  /** The name of the monitor function argument representing controller inputs. */
  private val INPUT_NAME = "in"

  /** Some reserved names, such as: main, Main */
  private val RESERVED_NAMES = Set("main", "Main")

  private val errorIds = scala.collection.mutable.HashMap[Formula, Int]()

  private def errorId(fml: Formula): Int = {
    if (!errorIds.contains(fml)) errorIds.put(fml, if (errorIds.isEmpty) -1 else errorIds.minBy(_._2)._2-1)
    errorIds(fml)
  }

  /**
    * Returns a set of names (excluding names in `vars` and interpreted functions) that are immutable parameters of the
    * expression `expr`. */
  private def getParameters(expr: Expression, exclude: Set[BaseVariable]): Set[NamedSymbol] =
    StaticSemantics.symbols(expr)
      .filter({
        case Function("abs", None, Real, Real, true) => false
        case Function("min" | "max", None, Tuple(Real, Real), Real, true) => false
        case Function(name, _, Unit, _, _) => !exclude.exists(_.name == name.stripSuffix("post"))
        case _: Function => false
        case BaseVariable(name, _, _) => !exclude.exists(_.name == name.stripSuffix("post"))
      })

  private def onlyEqualities(fml: Formula): Boolean = fml match {
    case _: Equal => true
    case And(l, r) => onlyEqualities(l) && onlyEqualities(r)
    case _ => false
  }

  /** Compiles primitive expressions with the appropriate params/curr/pre struct location. */
  private def primitiveExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator({
    case t: Variable if  parameters.contains(t) => "params->"
    case t: Variable if !parameters.contains(t) && t.name.endsWith("post") => "curr."
    case t: Variable if !parameters.contains(t) => "pre."
    case FuncOf(fn, Nothing) if  parameters.contains(fn) => "params->"
    case FuncOf(fn@Function(fname, _, _, _, _), Nothing) if !parameters.contains(fn) && fname.endsWith("post") => "curr."
    case FuncOf(fn, Nothing) if !parameters.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  })

  private def structuredExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator({
    case t: Variable if  parameters.contains(t) => "params->"
    case t: Variable if !parameters.contains(t) && t.name.endsWith("post") => "curr."
    case t: Variable if !parameters.contains(t) => "pre."
    case FuncOf(fn, Nothing) if  parameters.contains(fn) => "params->"
    case FuncOf(fn@Function(fname, _, _, _, _), Nothing) if !parameters.contains(fn) && fname.endsWith("post") => "curr."
    case FuncOf(fn, Nothing) if !parameters.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  }) {
    override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                       modelName: String): (String, String) = expr match {
      case f: Formula if f.isFOL => super.apply(f, stateVars, inputVars, modelName)
      case f: Formula if !f.isFOL => CPrettyPrinter(compileProgramFormula(f, Number(0)))
      case t: Term => super.apply(t, stateVars, inputVars, modelName)
    }

    //@todo preprocess `f` to collect distance measure `dist` by proof instead of here:
    // transform <?s=t><?x<=y><?a<=b>true into <?s=t><?x<=y><?a<=b>min(x-y,a-b)>=0
    private def compileProgramFormula(f: Formula, dist: Term): CProgram = f match {
      case Or(Diamond(Test(p), ifP), Diamond(Test(Not(q)), elseP)) if p==q =>
        val ifDist = if (onlyEqualities(p)) dist else ModelPlex.toMetric(p) match {
          //@todo toMetric returns negated to what we assume here
          case c: ComparisonFormula => Plus(dist, Neg(c.left))
        }
        val elseDist = if (onlyEqualities(p)) dist else ModelPlex.toMetric(Not(q)) match {
          //@todo toMetric returns negated to what we assume here
          case c: ComparisonFormula => Plus(dist, Neg(c.left))
        }
        CIfThenElse(compileFormula(p), compileProgramFormula(ifP, ifDist), compileProgramFormula(elseP, elseDist))
      case Or(l, r) => COrProgram(compileProgramFormula(l, Number(0)), compileProgramFormula(r, Number(0)))
      case And(l, r) => CAndProgram(compileProgramFormula(l, Number(0)), compileProgramFormula(r, Number(0)))
      case True => CReturn(compileTerm(dist))
      case Diamond(Test(p), q) =>
        val (pMetric: Term, pSatDist) = conjunctionsAs match {
          case 'min => printAndMin(p, dist)
          case 'resist => printAndParallelResistors(p, dist)
        }
        //@note offset error distance from -1 since weak inequalities may otherwise result in safe distance 0
        val errorDist = CPlus(CNumber(-1), compileTerm(pMetric))
        CIfThenElse(compileFormula(p), compileProgramFormula(q, pSatDist), CError(errorId(p), errorDist, p.prettyString))
    }
  }

  /** Combines conjunction of distance `dist` and metric of `p` with min. */
  private def printAndMin(p: Formula, dist: Term) = ModelPlex.toMetric(p) match {
    //@note when all nested ifs are satisfied, dist>=0; otherwise dist<=0. Resulting first term has same property.
    case c: ComparisonFormula =>
      assert(c.right == Number(0))
      // we want safety margin>=0 when formula is true
      val margin: Term = c match {
        //@note incorrect translation of greater/less prevented with outside if(x>y) margin else error
        case _: GreaterEqual | _: Greater => c.left
        case _: LessEqual | _: Less => Neg(c.left)
        case _: Equal => Neg(FuncOf(InterpretedSymbols.absF, c.left))
        case _: NotEqual => FuncOf(InterpretedSymbols.absF, c.left)
      }
      val simpMargin = SimplifierV3.termSimp(margin, scala.collection.immutable.HashSet.empty, SimplifierV3.defaultTaxs)._1
      val errorMargin = simpMargin
      val combinedMargin = FuncOf(InterpretedSymbols.minF, Pair(dist, simpMargin))
      (errorMargin, if (onlyEqualities(p)) dist else combinedMargin)
  }

  /** Combines conjunction of distance `dist` and metric of `p` in analogy to total resistance of parallel resistors 1/(1/dist + 1/metric(p))) */
  private def printAndParallelResistors(p: Formula, dist: Term) = ModelPlex.toMetric(p) match {
    //@note when all nested ifs are satisfied, dist>=0; otherwise dist<=0. Resulting first term has same property.
    // Encode And as 1/(1/x+1/y) (instead of min) has the advantage that changes in each conjunct
    // are reflected in the combined safety distance
    case c: ComparisonFormula =>
      assert(c.right == Number(0))
      // we want safety margin>=0 when formula is true
      val margin: Term = c match {
        //@note incorrect translation of greater/less prevented with outside if(x>y) margin else error
        case _: GreaterEqual | _: Greater => c.left
        case _: LessEqual | _: Less => Neg(c.left)
        case _: Equal => Neg(FuncOf(InterpretedSymbols.absF, c.left))
        case _: NotEqual => FuncOf(InterpretedSymbols.absF, c.left)
      }
      val simpMargin = SimplifierV3.termSimp(margin, scala.collection.immutable.HashSet.empty, SimplifierV3.defaultTaxs)._1
      val (errorMargin, combinedMargin) = dist match {
        case Number(n) if n == 0 => (simpMargin, simpMargin)
        case Divide(Number(n), Plus(l: Divide, r)) if n == 1 =>
          //@note parallel composition of successive tests (n-ary conjunction)
          (simpMargin, Divide(Number(1), Plus(l, Plus(r, Divide(Number(1), simpMargin)))))
        case _ =>
          //@todo other non-obvious divisions by zero
          (simpMargin, Divide(Number(1), Plus(Divide(Number(1), dist), Divide(Number(1), simpMargin))))
      }
      (errorMargin, if (onlyEqualities(p)) dist else combinedMargin)
  }

  /**
    * Compiles the expression `e` to C code as a body of a monitored controller execution function.
    * Names in `stateVars` are fields of the monitor function's argument "curr", names in `parameters` are fields of
    * the argument "params".
    */
  private def printMonitor(e: Expression, parameters: Set[NamedSymbol]): (String, String) = e match {
    case f: Formula if f.isFOL => primitiveExprGenerator(parameters)(f)
    case f: Formula if !f.isFOL => structuredExprGenerator(parameters)(f)
    case t: Term => primitiveExprGenerator(parameters)(t)
    case _ => throw new CodeGenerationException("The input expression: \n" + KeYmaeraXPrettyPrinter(e) + "\nis expected to be a formula or term.")
  }
}
