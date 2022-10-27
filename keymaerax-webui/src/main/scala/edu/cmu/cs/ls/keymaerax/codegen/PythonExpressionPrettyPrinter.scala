/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.codegen.PythonPrettyPrinter.{CURR, PARAMS, PRE}
import edu.cmu.cs.ls.keymaerax.core.{Bool, NamedSymbol, Real, Sort, Tuple, Unit}

object PythonPrettyPrinter extends CodePrettyPrinter {
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

  private def flattenDisjuncts(p: CProgram): Set[CProgram] = p match {
    case CDisjunctiveSafetyMargin(l, r) => flattenDisjuncts(l) ++ flattenDisjuncts(r)
    case _ => Set(p)
  }

  private def flattenConjuncts(p: CProgram): Set[CProgram] = p match {
    case CConjunctiveSafetyMargin(l, r) => flattenConjuncts(l) ++ flattenConjuncts(r)
    case _ => Set(p)
  }

  def printDefinitions(e: CExpression): String = e match {
    case d: CDisjunctiveSafetyMargin =>
      val disjuncts = flattenDisjuncts(d)
      val nestedDefs = disjuncts.map(printDefinitions).mkString("\n")
      val disjunctDefs = disjuncts.
        filter({ case _: CConjunctiveSafetyMargin => true case _: CIfThenElse => true case _ => false }).
        map(d => {
          s"""def Or${uniqueName(d)}($PRE, $CURR, $PARAMS):
             |${print(d).linesWithSeparators.map("  " + _).mkString}""".stripMargin
        }).mkString("\n")
      nestedDefs + "\n" + disjunctDefs
    case c: CConjunctiveSafetyMargin =>
      val conjuncts = flattenConjuncts(c)
      val nestedDefs = conjuncts.map(printDefinitions).mkString("\n")
      val conjunctDefs = conjuncts.
        filter({ case _: CDisjunctiveSafetyMargin => true case _: CIfThenElse => true case _ => false }).
        map(d => {
          s"""def And${uniqueName(d)}($PRE, $CURR, $PARAMS):
             |${print(d).linesWithSeparators.map("  " + _).mkString}""".stripMargin
        }).mkString("\n")
      nestedDefs + "\n" + conjunctDefs
    case CIfThenElse(_, ifP, elseP: CIfThenElse) =>
      val elsePDef =
        s"""def IfThenElse${uniqueName(elseP)}($PRE, $CURR, $PARAMS):
           |${print(elseP).linesWithSeparators.map("  " + _).mkString}""".stripMargin
      s"""${printDefinitions(ifP)}
         |${printDefinitions(elseP)}
         |$elsePDef""".stripMargin
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
    case CNothing => "???"
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

    case CPredicate(n, CNothing) => n + "(" + PARAMS + ")"
    case CPredicate(n, arg) => n + "(" + PARAMS + "," + print(arg) + ")"
    case CLess(l, r) => print(l) + " < " + print(r)
    case CLessEqual(l, r) => print(l) + " <= " + print(r)
    case CEqual(l, r) => print(l) + " == " + print(r)
    case CGreaterEqual(l, r) => print(l) + " >= " + print(r)
    case CGreater(l, r) => print(l) + " > " + print(r)
    case CNotEqual(l, r) => print(l) + " != " + print(r)
    case CNot(c) => "not(" + print(c) + ")"
    case CAnd(l, r) => "(" + print(l) + ") and (" + print(r) + ")"
    case COr(l, r) => "(" + print(l) + ") or (" + print(r) + ")"

    case comment: CComment => "(\n# " + comment.comment + "\n)"

    case CTrue => "True"
    case CFalse => "False"
    case CIfThenElse(f, ifP, elseP: CIfThenElse) =>
      s"""if ${print(f)}:
         |${print(ifP).linesWithSeparators.map(INDENT + _).mkString}
         |else:
         |  IfThenElse${uniqueName(elseP)}($PRE, $CURR, $PARAMS)""".stripMargin
    case CIfThenElse(f, ifP, elseP: CErrorMargin) =>
      s"""if ${print(f)}:
         |${print(ifP).linesWithSeparators.map(INDENT + _).mkString}
         |else:
         |  return ${print(elseP).linesWithSeparators.map(INDENT + _).mkString.stripPrefix(INDENT)}""".stripMargin
    case CIfThenElse(f, ifP, elseP) =>
      s"""if ${print(f)}:
         |${print(ifP).linesWithSeparators.map(INDENT + _).mkString}
         |else:
         |${print(elseP).linesWithSeparators.map(INDENT + _).mkString}""".stripMargin
    case CMeasureZeroMargin(e: CExpression) => s"Verdict(0, ${print(e)})"
    case CSafetyMargin(e: CExpression) => s"Verdict(1, ${print(e)})"
    case CErrorMargin(id: Int, v: CExpression, _: String) => s"Verdict($id, ${print(v)})"
    case d: CDisjunctiveSafetyMargin =>
      val disjuncts = flattenDisjuncts(d)
      val (complexDisjuncts, atomicDisjuncts) = disjuncts.
        partition({ case _: CConjunctiveSafetyMargin => true case _: CIfThenElse => true case _ => false })
      s"""verdicts = [
         | ${atomicDisjuncts.map(print).mkString(",\n ")}${if (atomicDisjuncts.nonEmpty && complexDisjuncts.nonEmpty) "," else ""}
         | ${complexDisjuncts.map(d => s"Or${uniqueName(d)}($PRE, $CURR, $PARAMS)").mkString(",\n ")}
         |]
         |nonMeasureZeroVerdicts = filter(lambda v: v.id != 0, verdicts)
         |return max(nonMeasureZeroVerdicts, key=lambda v: v.val, default=Verdict(0, True))""".stripMargin
    case c: CConjunctiveSafetyMargin =>
      val conjuncts = flattenConjuncts(c)
      val (complexConjuncts, atomicConjuncts) = conjuncts.
        partition({ case _: CDisjunctiveSafetyMargin => true case _: CIfThenElse => true case _ => false })
      s"""verdicts = [
         | ${atomicConjuncts.map(print).mkString(",\n ")}${if (atomicConjuncts.nonEmpty && complexConjuncts.nonEmpty) "," else ""}
         | ${complexConjuncts.map(d => s"And${uniqueName(d)}($PRE, $CURR, $PARAMS)").mkString(",\n ")}
         |]
         |nonMeasureZeroVerdicts = filter(lambda v: v.id != 0, verdicts)
         |return min(nonMeasureZeroVerdicts, key=lambda v: v.val, default=Verdict(0, True))""".stripMargin
  }

}