/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.codegen.PythonPrettyPrinter.{CURR, PARAMS, PRE}
import edu.cmu.cs.ls.keymaerax.core.{Bool, NamedSymbol, Real, Sort, Tuple, Unit}

object PythonPrettyPrinter extends (CExpression => (String, String)) {
  val CURR = "curr"
  val PARAMS = "params"
  val PRE = "pre"

  var printer: CExpression => (String, String) = new PythonExpressionPrettyPrinter(printDebugOut = false)
  override def apply(e: CExpression): (String, String) = printer(e)

  def printSort(s: Sort): String = s match {
    case Unit => "None"
    case Real => "np.float64"
    case Bool => "bool"
    case Tuple(l, r) => "tuple[" + printSort(l) + ", " + printSort(r) + "]"
    case _ => s.toString
  }

  def numberLiteral(n: BigDecimal): String = {
    val string = n.underlying().toString
    if (string.contains(".")) printSort(Real) + "(" + string + ")"
    else printSort(Real) + "(" + string + ".0)"
  }

  def nameIdentifier(s: NamedSymbol): String = CFormulaTermGenerator.nameIdentifier(s)
}

class PythonExpressionPrettyPrinter(printDebugOut: Boolean) extends (CExpression => (String, String)) {

  private val INDENT = "  "

  private def numberLiteral(n: BigDecimal): String = PythonPrettyPrinter.numberLiteral(n)

  def printDefinitions(e: CExpression): String = e match {
    case COrProgram(l, r) =>
      s"""${printDefinitions(l)}
         |${printDefinitions(r)}
         |
         |def OrLeft${uniqueName(l)}($PRE, $CURR, $PARAMS):
         |${print(l).linesWithSeparators.map("  " + _).mkString}
         |
         |def OrRight${uniqueName(r)}($PRE, $CURR, $PARAMS):
         |${print(r).linesWithSeparators.map("  " + _).mkString}
         |
         |""".stripMargin
    case CAndProgram(l, r) =>
      s"""${printDefinitions(l)}
         |${printDefinitions(r)}
         |
         |def AndLeft${uniqueName(l)}($PRE, $CURR, $PARAMS):
         |${print(l).linesWithSeparators.map("  " + _).mkString}
         |
         |def AndRight${uniqueName(r)}($PRE, $CURR, $PARAMS):
         |${print(r).linesWithSeparators.map("  " + _).mkString}
         |
         |""".stripMargin
    case CIfThenElse(_, ifP, elseP) => printDefinitions(ifP) + "\n" + printDefinitions(elseP)
    case _ => ""
  }

  override def apply(e: CExpression): (String, String) = (printDefinitions(e), print(e))

  private def uniqueName(fml: CExpression): String = {
    val hashcode = fml.hashCode()
    if (hashcode < 0) hashcode.toString.replace("-", "_")
    else hashcode.toString
  }

  //@todo print only necessary parentheses
  private def print(e: CExpression): String = e match {
    case CNothing => ""
    case CNumber(n) if n>=0 => numberLiteral(n)
    case CNumber(n) if n<0 => "(" + numberLiteral(n) + ")"
    case CVariable(n) => n
    case CUnaryFunction(n, CNothing) => n + "(" + PARAMS + ")" //@see [[PythonGenerator.printFuncDefs]]
    case CUnaryFunction(n, arg) => n + "(" + PARAMS + "," + print(arg) + ")" //@see [[PythonGenerator.printFuncDefs]]
    case CPair(l, r) => print(l) + "," + print(r)
    case CNeg(c) => "-(" + print(c) + ")"
    case CPlus(l, r) => "(" + print(l) + ")+(" + print(r) + ")"
    case CMinus(l, r) => "(" + print(l) + ")-(" + print(r) + ")"
    case CTimes(l, r) => "(" + print(l) + ")*(" + print(r) + ")"
    case CDivide(l, r) => "(" + print(l) + ")/(" + print(r) + ")"
    case CPower(l, r) => "(" + print(l) + ")**(" + print(r) + ")"
    case CMin(l, r) => "min(" + print(l) + ", " + print(r) + ")"
    case CMax(l, r) => "max(" + print(l) + ", " + print(r) + ")"
    case CAbs(c) => "abs(" + print(c) + ")"

    case CLess(l, r) => print(l) + " < " + print(r)
    case CLessEqual(l, r) => print(l) + " <= " + print(r)
    case CEqual(l, r) => print(l) + " == " + print(r)
    case CGreaterEqual(l, r) => print(l) + " >= " + print(r)
    case CGreater(l, r) => print(l) + " > " + print(r)
    case CNotEqual(l, r) => print(l) + " != " + print(r)
    case CNot(c) => "not(" + print(c) + ")"
    case CAnd(l, r) => "(" + print(l) + ") and (" + print(r) + ")"
    case COr(l, r) => "(" + print(l) + ") or (" + print(r) + ")"

    case CTrue => "True"
    case CFalse => "False"

    case CIfThenElse(f, ifP, elseP) => "if " + print(f) + ":\n" + print(ifP).linesWithSeparators.map(INDENT + _).mkString + "\nelse:\n" + print(elseP).linesWithSeparators.map(INDENT + _).mkString
    case CReturn(e: CExpression) => "result = Verdict(1, " + print(e) + ")\nreturn result"
    case CError(id: Int, retVal: CExpression, _: String) => s"result = Verdict($id, ${print(retVal)})\nreturn result"
    case COrProgram(l, r) /* if kind=="boolean" */ =>
      if (printDebugOut)
        s"""leftDist = OrLeft${uniqueName(l)}($PRE, $CURR, $PARAMS)
           |rightDist = OrRight${uniqueName(r)}($PRE, $CURR, $PARAMS)
           |verdictId = leftDist.id if leftDist.val >= rightDist.val else rightDist.id
           |result = Verdict(verdictId, max(leftDist.val, rightDist.val));
           |return result""".stripMargin
      else
        s"""leftDist = OrLeft${uniqueName(l)}($PRE, $CURR, $PARAMS)
           |rightDist = OrRight${uniqueName(r)}($PRE, $CURR, $PARAMS)
           |verdictId = leftDist.id if leftDist.val >= rightDist.val else rightDist.id
           |result = Verdict(verdictId, max(leftDist.val, rightDist.val))
           |return result""".stripMargin
    case CAndProgram(l, r) /* if kind=="boolean" */ =>
      if (printDebugOut)
        s"""leftDist = AndLeft${uniqueName(l)}($PRE, $CURR, $PARAMS);
           |rightDist = AndRight${uniqueName(r)}($PRE, $CURR, $PARAMS);
           |verdictId = leftDist.id if leftDist.val <= rightDist.val else rightDist.id
           |result = Verdict(verdictId, min(leftDist.val, rightDist.val))
           |return result""".stripMargin
      else
        s"""leftDist = AndLeft${uniqueName(l)}($PRE, $CURR, $PARAMS)
           |rightDist = AndRight${uniqueName(r)}($PRE, $CURR, $PARAMS)
           |verdictId = leftDist.id if leftDist.val <= rightDist.val else rightDist.id
           |result = Verdict(verdictId, min(leftDist.val, rightDist.val))
           |return result""".stripMargin
  }

}