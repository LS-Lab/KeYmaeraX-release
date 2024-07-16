/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.codegen

import org.keymaerax.codegen.CFormulaTermGenerator._
import org.keymaerax.core._
import org.keymaerax.parser.Declaration

import scala.annotation.nowarn

/**
 * Generates a controller from a hybrid program without loops and ODEs. A controller transforms an input state by
 * choosing control set values depending on inputs and parameters.
 * @author
 *   Stefan Mitsch
 */
class CControllerGenerator(defs: Declaration) extends CodeGenerator {
  override def apply(
      expr: Expression,
      stateVars: Set[BaseVariable],
      inputVars: Set[BaseVariable],
      modelName: String,
  ): (String, String) = expr match {
    case ctrl: Program =>
      implicit val exprGenerator: CFormulaTermGenerator = createExprGenerator(getParams(ctrl))
      // @todo check success before returning result
      (
        "",
        programHeader + " {\n  " + programBodySetup + "\n" + generateProgramBody(ctrl, "  ") +
          "\n  return prg.state;\n}",
      )
    case _ => throw new CodeGenerationException("Expected program, but got " + expr.prettyString)
  }

  private val PARAMS_NAME = "params"
  private val CURR_STATE_NAME = "prg.state"
  private val INPUTS_NAME = "in"

  /** Determines parameters of the program `prg`. */
  private def getParams(prg: Program): Set[NamedSymbol] = StaticSemantics.symbols(prg) --
    StaticSemantics.boundVars(prg).toSet

  private lazy val programHeader: String = {
    "state ctrlStep(state curr, const parameters* const params, const input* const in)"
  }

  private lazy val programBodySetup: String = "struct { state state; int success; } prg = { .state=curr, .success=0 };"

  /** Compiles expressions with the appropriate params/curr/pre struct location. */
  private def createExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator(
    {
      case FuncOf(Function(name, idx, _, _, _), Nothing) if parameters.exists(p => p.name == name && p.index == idx) =>
        PARAMS_NAME + "->"
      case t: NamedSymbol if parameters.exists(p => p.name == t.name && p.index == t.index) => PARAMS_NAME + "->"
      case _ => CURR_STATE_NAME + "."
    },
    defs,
  )

  @nowarn("msg=match may not be exhaustive")
  private def generateProgramBody(prg: Program, indent: String)(implicit
      exprGenerator: Expression => (String, String)
  ): String = prg match {
    case Assign(x, t) => indent + exprGenerator(x)._2 + " = " + exprGenerator(t)._2 + "; prg.success = 1;"
    case AssignAny(x) => indent + exprGenerator(x)._2 + " = " + INPUTS_NAME + "->" + nameIdentifier(x) +
        "; prg.success = 1;"
    case Test(f) => indent + "prg.success = (" + exprGenerator(f)._2 + ");"
    case Loop(c) => indent + "while (!prg.success) {\n" + generateProgramBody(c, indent + "  ") + "\n" + indent + "}"
    case _: ODESystem => indent + "prg.success = 1; /* done choosing actuator set values */"
    case Compose(a, b) => {
      s"""$indent{
         |${generateProgramBody(a, indent + "  ")}
         |$indent}
         |${indent}if (prg.success) {
         |${generateProgramBody(b, indent + "  ")}
         |$indent}""".stripMargin
    }
    case Choice(a, b) => {
      s"""$indent{
         |$indent  state reset = prg.state;
         |${generateProgramBody(a, indent + "  ")}
         |$indent  if (!prg.success) prg.state = reset;
         |$indent}
         |${indent}if (!prg.success) {
         |$indent  state reset = prg.state;
         |${generateProgramBody(b, indent + "  ")}
         |$indent  if (!prg.success) prg.state = reset;
         |$indent}""".stripMargin
    }
  }
}

class CMpfrControllerGenerator(defs: Declaration) extends CodeGenerator {
  override def apply(
      expr: Expression,
      stateVars: Set[BaseVariable],
      inputVars: Set[BaseVariable],
      modelName: String,
  ): (String, String) = expr match {
    case ctrl: Program =>
      implicit val exprGenerator: CFormulaTermGenerator = createExprGenerator(getParams(ctrl))
      // @todo check success before returning result
      (
        "",
        programHeader + " {\n  " + programBodySetup + "\n" + generateProgramBody(ctrl, "  ") +
          "\n  return prg.state;\n}",
      )
    case _ => throw new CodeGenerationException("Expected program, but got " + expr.prettyString)
  }

  private val PARAMS_NAME = "params"
  private val CURR_STATE_NAME = "prg.state"
  private val INPUTS_NAME = "in"

  /** Determines parameters of the program `prg`. */
  private def getParams(prg: Program): Set[NamedSymbol] = StaticSemantics.symbols(prg) --
    StaticSemantics.boundVars(prg).toSet

  private lazy val programHeader: String = {
    "state ctrlStep(state curr, const parameters* const params, const input* const in)"
  }

  private lazy val programBodySetup: String = "struct { state state; int success; } prg = { .state=curr, .success=0 };"

  /** Compiles expressions with the appropriate params/curr/pre struct location. */
  private def createExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator(
    {
      case FuncOf(Function(name, idx, _, _, _), Nothing) if parameters.exists(p => p.name == name && p.index == idx) =>
        PARAMS_NAME + "->"
      case t: NamedSymbol if parameters.exists(p => p.name == t.name && p.index == t.index) => PARAMS_NAME + "->"
      case _ => CURR_STATE_NAME + "."
    },
    defs,
  )

  private def printPlain(e: Expression)(implicit exprGenerator: Expression => (String, String)): (String, String) = {
    val printer = CPrettyPrinter.printer
    CPrettyPrinter.printer = new CExpressionPlainPrettyPrinter(printDebugOut = false)
    val result = exprGenerator(e)
    CPrettyPrinter.printer = printer
    result
  }

  private def extractInlineMpfr(mpfr: String, indent: String): String = {
    val parts = mpfr.split("void")
    val decls = parts(0).trim()
    val init = """mpfrInit\(\) \{([^\}]*)\}""".r.findFirstMatchIn(parts(1)).get.group(1)
    val compute = """mpfrCompute\([^\)]*\) \{([^\}]*)\}""".r.findFirstMatchIn(parts(2)).get.group(1)
    decls + "\n" + indent + init.trim() + "\n" + indent + compute.trim()
  }

  @nowarn("msg=match may not be exhaustive")
  private def generateProgramBody(prg: Program, indent: String)(implicit
      exprGenerator: Expression => (String, String)
  ): String = prg match {
    case Assign(x, t) =>
      val tCode = exprGenerator(t)
      s"""$indent${extractInlineMpfr(tCode._1, indent)}
         |$indent${printPlain(x)._2} = ${tCode._2}
         |${indent}prg.success = 1;""".stripMargin
    case AssignAny(x) => indent + printPlain(x)._2 + " = " + INPUTS_NAME + "->" + nameIdentifier(x) +
        "; prg.success = 1;"
    case Test(f) =>
      val fCode = exprGenerator(f)
      s"""$indent${extractInlineMpfr(fCode._1, indent)}
         |${indent}prg.success = ${fCode._2};""".stripMargin
    case Loop(c) => indent + "while (!prg.success) {\n" + generateProgramBody(c, indent + "  ") + "\n" + indent + "}"
    case _: ODESystem => indent + "prg.success = 1; /* done choosing actuator set values */"
    case Compose(a, b) => {
      s"""$indent{
         |${generateProgramBody(a, indent + "  ")}
         |$indent}
         |${indent}if (prg.success) {
         |${generateProgramBody(b, indent + "  ")}
         |$indent}""".stripMargin
    }
    case Choice(a, b) => {
      s"""$indent{
         |$indent  state reset = prg.state;
         |${generateProgramBody(a, indent + "  ")}
         |$indent  if (!prg.success) prg.state = reset;
         |$indent}
         |${indent}if (!prg.success) {
         |$indent  state reset = prg.state;
         |${generateProgramBody(b, indent + "  ")}
         |$indent  if (!prg.success) prg.state = reset;
         |$indent}""".stripMargin
    }
  }
}

/**
 * Generates a controller from a hybrid program with only deterministic statements. A controller transforms an input
 * state by choosing control set values depending on inputs and parameters.
 * @author
 *   Stefan Mitsch
 */
class CDetControllerGenerator(defs: Declaration) extends CodeGenerator {
  override def apply(
      expr: Expression,
      stateVars: Set[BaseVariable],
      inputVars: Set[BaseVariable],
      modelName: String,
  ): (String, String) = expr match {
    case ctrl: Program =>
      implicit val exprGenerator: CFormulaTermGenerator = createExprGenerator(getParams(ctrl))
      // @todo check success before returning result
      ("", programHeader + " {\n" + generateProgramBody(ctrl, "  ") + "\n  return curr;\n}")
    case _ => throw new CodeGenerationException("Expected program, but got " + expr.prettyString)
  }

  private val PARAMS_NAME = "params"
  private val CURR_STATE_NAME = "curr"
  private val INPUTS_NAME = "in"

  /** Determines parameters of the program `prg`. */
  private def getParams(prg: Program): Set[NamedSymbol] = StaticSemantics.symbols(prg) --
    StaticSemantics.boundVars(prg).toSet

  private lazy val programHeader: String = {
    "state ctrlStep(state curr, const parameters* const params, const input* const in)"
  }

  /** Compiles expressions with the appropriate params/curr/pre struct location. */
  private def createExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator(
    {
      case FuncOf(Function(name, idx, _, _, _), Nothing) if parameters.exists(p => p.name == name && p.index == idx) =>
        PARAMS_NAME + "->"
      case t: NamedSymbol if parameters.exists(p => p.name == t.name && p.index == t.index) => PARAMS_NAME + "->"
      case _ => CURR_STATE_NAME + "."
    },
    defs,
  )

  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  private def generateProgramBody(prg: Program, indent: String)(implicit
      exprGenerator: Expression => (String, String)
  ): String = prg match {
    case Assign(x, t) => indent + exprGenerator(x)._2 + " = " + exprGenerator(t)._2 + ";"
    case AssignAny(x) => indent + exprGenerator(x)._2 + " = " + INPUTS_NAME + "->" + nameIdentifier(x) + ";"
    case Test(_) => throw new IllegalArgumentException("Compiling tests is not supported")
    case Loop(_) => throw new IllegalArgumentException("Compiling loops is not supported")
    case _: ODESystem => throw new IllegalArgumentException("Compiling ODEs is not supported")
    case Compose(a, b) => s"""${generateProgramBody(a, indent)}
                             |${generateProgramBody(b, indent)}""".stripMargin
    case Choice(Compose(Test(p), a), Compose(Test(Not(q)), Test(True))) if p == q =>
      // standalone if (without else)
      s"""${indent}if (${exprGenerator(p)._2}) {
         |${generateProgramBody(a, indent + "  ")}
         |$indent}""".stripMargin
    case Choice(Compose(Test(p), a), Compose(Test(Not(q)), b)) if p == q =>
      // find leading tests
      s"""${indent}if (${exprGenerator(p)._2}) {
         |${generateProgramBody(a, indent + "  ")}
         |$indent} else {
         |${generateProgramBody(b, indent + "  ")}
         |$indent}""".stripMargin
  }
}
