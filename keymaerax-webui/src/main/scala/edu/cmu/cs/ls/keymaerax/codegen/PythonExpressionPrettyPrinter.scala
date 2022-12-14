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

  /** Prints nested definitions, introduces one Python function per atomic comparisons in `prgs`, one per if-then-else program,
   * and one per "complex" program as identified by `filter`. Prefixes the complex function names with `prefix`. */
  private def printDefs(prgs: Set[CProgram], filter: CProgram=>Boolean, prefix: String): List[(CExpression, String)] = {
    val nestedDefs = prgs.map(printDefinitions).reduceOption(_++_).getOrElse(List.empty)
    val atomicComparisonDefs = prgs.
      filter({ case _: CSafetyMargin => true case _ => false }).
      map({
        case CSafetyMargin(d) =>
          d -> s"""def Cond${uniqueName(d)}($PRE, $CURR, $PARAMS):
                  |  return ${print(d)}""".stripMargin
      })
    val prgsDefs = prgs.
      filter({ case _: CIfThenElse => true case p => filter(p) }).
      map(d => {
        d ->
          s"""def $prefix${uniqueName(d)}($PRE, $CURR, $PARAMS):
             |${print(d).linesWithSeparators.map("  " + _).mkString}""".stripMargin
      })
    nestedDefs ++ atomicComparisonDefs ++ prgsDefs
  }

  /** Prints Python function definitions for (some) duplicate elements in `e`. */
  def printDefinitions(e: CExpression): List[(CExpression, String)] = e match {
    case d: CDisjunctiveSafetyMargin => printDefs(flattenDisjuncts(d), _.isInstanceOf[CConjunctiveSafetyMargin], "Or")
    case c: CConjunctiveSafetyMargin => printDefs(flattenConjuncts(c), _.isInstanceOf[CDisjunctiveSafetyMargin], "And")
    case CIfThenElse(cond, ifP, elseP) =>
      val condDefText = print(cond)
      val condDef =
        if (condDefText.length > 100) {
          List(cond ->
            s"""def Cond${uniqueName(cond)}($PRE, $CURR, $PARAMS):
               |  return $condDefText""".stripMargin)
        } else List.empty
      val ifPDef = printDefinitions(ifP)
      condDef ++ ifPDef ++ printDefinitions(elseP) ++ (elseP match {
        case nestedIf: CIfThenElse =>
          List(elseP -> s"""def IfThenElse${uniqueName(nestedIf)}($PRE, $CURR, $PARAMS):
                           |${print(nestedIf).linesWithSeparators.map("  " + _).mkString}""".stripMargin)
        case _ => List.empty
      })
    case CSafetyMargin(d) =>
      List(d ->
        s"""def Margin${uniqueName(d)}($PRE, $CURR, $PARAMS):
         |  return ${print(d)}""".stripMargin)
    case CErrorMargin(_, CNeg(d), _) =>
      List(d ->
        s"""def Margin${uniqueName(d)}($PRE, $CURR, $PARAMS):
           |  return ${print(d)}""".stripMargin)
    case CErrorMargin(_, d, _) =>
      List(d ->
        s"""def Cond${uniqueName(d)}($PRE, $CURR, $PARAMS):
           |  return ${print(d)}""".stripMargin)
    case _ => List.empty
  }

  override def apply(e: CExpression): (String, String) = {
    //@todo change signature
    val defs = printDefinitions(e)
    (defs.distinct.map(_._2).mkString("\n"), print(e))
  }

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
    case CIfThenElse(f, ifP, elseP) =>
      val condDefText = print(f)
      val cond = if (condDefText.length > 100) s"Cond${uniqueName(f)}($PRE, $CURR, $PARAMS)" else condDefText
      val elsePText = elseP match {
        case _: CIfThenElse => s"IfThenElse${uniqueName(elseP)}($PRE, $CURR, $PARAMS)"
        case _: CErrorMargin => s"return ${print(elseP).linesWithSeparators.map(INDENT + _).mkString.stripPrefix(INDENT)}"
        case _ => s"${print(elseP).linesWithSeparators.map(INDENT + _).mkString}"
      }
      s"""if $cond:
         |${print(ifP).linesWithSeparators.map(INDENT + _).mkString}
         |else:
         |  $elsePText""".stripMargin
    case CMeasureZeroMargin(e: CExpression) => s"Verdict(0, ${print(e)})"
    case CSafetyMargin(e) => s"Verdict(1, Margin${uniqueName(e)}($PRE, $CURR, $PARAMS))"
    case CErrorMargin(id: Int, CNeg(v), _: String) => s"Verdict($id, -Margin${uniqueName(v)}($PRE, $CURR, $PARAMS))"
    case CErrorMargin(id: Int, v, _) => s"Verdict($id, Margin${uniqueName(v)}($PRE, $CURR, $PARAMS))"
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