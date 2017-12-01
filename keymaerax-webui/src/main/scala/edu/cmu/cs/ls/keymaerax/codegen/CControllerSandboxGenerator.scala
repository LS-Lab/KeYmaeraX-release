/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.{ExpressionTraversal, ModelPlex}
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.mutable.ListBuffer

/**
  * Generates a controller sandbox from a hybrid program without loops and ODEs.
  * A controller sandbox safeguards control decisions with a controller monitor by switching to a fallback controller
  * upon controller monitor violation.
  * @param monitorKind How to evaluate monitors, either "boolean" or "metric".
  * @param logEval Whether or not to generate code that logs reasons for why terms/formulas have their value
  * @author Stefan Mitsch
  */
class CControllerSandboxGenerator(val monitorKind: String, val logEval: Boolean) extends CodeGenerator {
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                     modelName: String): String = expr match {
    case ctrl: Program =>
      val vars = StaticSemantics.boundVars(ctrl).symbols[NamedSymbol].
        filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
      assert(vars == stateVars, s"All program variables should be state variables, expected $vars but got $stateVars")
      val ivars = ListBuffer[BaseVariable]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
          case AssignAny(v: BaseVariable) => ivars.append(v); Left(None)
          case _ => Left(None)
        }
      }, ctrl)
      val prgIVars = ivars.toSet
      assert(prgIVars == inputVars, s"All and only nondeterministically assigned variables should be inputs: expected $prgIVars but got $inputVars")

      CPrettyPrinter.printer = if (logEval) new CExpressionLogPrettyPrinter else new CExpressionPlainPrettyPrinter

      val fallbackCode = new CControllerGenerator()(ctrl, vars, inputVars)

      val inputModel = Imply(True, Box(ctrl, True))
      val monitorFml = ModelPlex(inputModel, 'ctrl)
      val monitor = monitorKind match {
        case "boolean" => monitorFml
        case "metric" => ModelPlex.toMetric(monitorFml)
      }

      val monitorCode = new CMonitorGenerator(monitorKind)(monitor, vars, inputVars)
      val params = CGenerator.getParameters(monitor, vars)
      val declarations = CGenerator.printParameterDeclaration(params) + "\n" +
        CGenerator.printStateDeclaration(vars) + "\n" +
        CGenerator.printInputDeclaration(inputVars)

      s"""
         |${CGenerator.printHeader(modelName)}
         |${CGenerator.INCLUDE_STATEMENTS}
         |#include <stdio.h>
         |#include <stdarg.h>
         |#include <stdlib.h>
         |${if (logEval) new CExpressionLogPrettyPrinter().printOperators else ""}
         |$declarations
         |$fallbackCode
         |${monitorCode.toString.trim}
         |""".stripMargin
    case _ => throw new CodeGenerationException("Expected program, but got " + expr.prettyString)
  }
}
