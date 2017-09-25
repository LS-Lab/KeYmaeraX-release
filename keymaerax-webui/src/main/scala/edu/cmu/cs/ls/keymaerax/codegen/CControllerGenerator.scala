/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.codegen.CFormulaTermGenerator._
import edu.cmu.cs.ls.keymaerax.core._

/**
  * Generates a controller from a hybrid program without loops and ODEs.
  * A controller transforms an input state by choosing control set values depending on inputs and parameters.
  * @author Stefan Mitsch
  */
class CControllerGenerator extends CodeGenerator {
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                     modelName: String): String = expr match {
    case ctrl: Program =>
      implicit val exprGenerator = createExprGenerator(getParams(ctrl))
      //@todo check success before returning result
      programHeader + " {\n  " + programBodySetup + "\n" + generateProgramBody(ctrl, "  ") + "\n  return prg.state;\n}"
    case _ => throw new CodeGenerationException("Expected program, but got " + expr.prettyString)
  }

  private val PARAMS_NAME = "params"
  private val CURR_STATE_NAME = "prg.state"
  private val INPUTS_NAME = "in"

  /** Determines parameters of the program `prg`. */
  private def getParams(prg: Program): Set[NamedSymbol] = StaticSemantics.symbols(prg) -- StaticSemantics.boundVars(prg).toSet

  private lazy val programHeader: String = {
    """/* Replace with your favorite correct(!) stack implementation. */
      |typedef struct stateStack {
      |  int top;
      |  state items[10];
      |} stateStack;
      |stateStack initStack() { return (stateStack) { .top = -1 }; }
      |void push(stateStack* const s, state item) { s->items[++s->top] = item; }
      |state pop(stateStack* const s) { return s->items[s->top--]; }
      |state ctrlStep(state curr, const parameters* const params, const input* const in)""".stripMargin
  }

  private lazy val programBodySetup: String =
    "struct { state state; stateStack reset; int success; } prg = { .state=curr, .reset=initStack(), .success=0 };"

  /** Compiles expressions with the appropriate params/curr/pre struct location. */
  private def createExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator({
    case FuncOf(Function(name, idx, _, _, _), Nothing) if parameters.exists(p => p.name == name && p.index == idx) => PARAMS_NAME + "->"
    case t: NamedSymbol if parameters.exists(p => p.name == t.name && p.index == t.index) => PARAMS_NAME + "->"
    case _ => CURR_STATE_NAME + "."
  })

  private def generateProgramBody(prg: Program, indent: String)(implicit exprGenerator: Expression => String): String = prg match {
    case Assign(x, t) => indent + exprGenerator(x) + " = " + exprGenerator(t) + "; prg.success = 1;"
    case AssignAny(x) => indent + exprGenerator(x) + " = " + INPUTS_NAME + "->" + nameIdentifier(x) + "; prg.success = 1;"
    case Test(f) => indent + "prg.success = (" + exprGenerator(f) + ");"
    case Loop(c) => indent + "while (!prg.success) {\n" + generateProgramBody(c, indent + "  ") + "\n" + indent + "}"
    case _: ODESystem => indent + "prg.success = 1; /* done choosing actuator set values */"
    case Compose(a, b) =>
      s"""$indent{
        |${generateProgramBody(a, indent + "  ")}
        |$indent}
        |${indent}if (prg.success) {
        |${generateProgramBody(b, indent + "  ")}
        |$indent}""".stripMargin
    case Choice(a, b) =>
      s"""$indent{
         |$indent  push(&prg.reset, prg.state);
         |${generateProgramBody(a, indent + "  ")}
         |$indent  if (!prg.success) prg.state = pop(&prg.reset);
         |$indent  else pop(&prg.reset);
         |$indent}
         |${indent}if (!prg.success) {
         |$indent  push(&prg.reset, prg.state);
         |${generateProgramBody(b, indent + "  ")}
         |$indent  if (!prg.success) prg.state = pop(&prg.reset);
         |$indent  else pop(&prg.reset);
         |$indent}""".stripMargin
  }
}
