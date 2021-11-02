/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

/**
  * C expressions.
  *
  * @author Stefan Mitsch
  */
trait CExpression {

}

trait CTerm extends CExpression {}
trait CFormula extends CExpression {}
trait CProgram extends CExpression {}
trait CComment {
  val comment: String
}

case class CTermComment(comment: String) extends CTerm with CComment {}
case class CFormulaComment(comment: String) extends CFormula with CComment {}
case class CProgramComment(comment: String) extends CProgram with CComment {}

case object CNothing extends CTerm {}
case class CNumber(n: BigDecimal) extends CTerm {}
case class CVariable(name: String) extends CTerm {}
case class CUnaryFunction(name: String, arg: CTerm) extends CTerm {}
case class CPair(l: CTerm, r: CTerm) extends CTerm {}

case class CNeg(c: CTerm) extends CTerm {}
case class CPlus(l: CTerm, r: CTerm) extends CTerm {}
case class CMinus(l: CTerm, r: CTerm) extends CTerm {}
case class CTimes(l: CTerm, r: CTerm) extends CTerm {}
case class CDivide(l: CTerm, r: CTerm) extends CTerm {}
case class CPower(l: CTerm, r: CTerm) extends CTerm {}

case class CMin(l: CTerm, r: CTerm) extends CTerm {}
case class CMax(l: CTerm, r: CTerm) extends CTerm {}
case class CAbs(c: CTerm) extends CTerm {}

case class CPredicate(name: String, arg: CTerm) extends CFormula {}
case class CLess(l: CTerm, r: CTerm) extends CFormula {}
case class CLessEqual(l: CTerm, r: CTerm) extends CFormula {}
case class CEqual(l: CTerm, r: CTerm) extends CFormula {}
case class CGreaterEqual(l: CTerm, r: CTerm) extends CFormula {}
case class CGreater(l: CTerm, r: CTerm) extends CFormula {}
case class CNotEqual(l: CTerm, r: CTerm) extends CFormula {}

case class CNot(c: CFormula) extends CFormula {}
case class CAnd(l: CFormula, r: CFormula) extends CFormula {}
case class COr(l: CFormula, r: CFormula) extends CFormula {}

object CTrue extends CFormula {}
object CFalse extends CFormula {}

case class CIfThenElse(f: CFormula, ifP: CProgram, elseP: CProgram) extends CProgram
case class COrProgram(l: CProgram, r: CProgram) extends CProgram
case class CAndProgram(l: CProgram, r: CProgram) extends CProgram
case class CError(id: Int, retVal: CExpression, msg: String) extends CProgram
case class CReturn(e: CExpression) extends CProgram
object CNoop extends CProgram


/** Prints C expressions. */
object CPrettyPrinter extends (CExpression => (String, String)) {
  var printer: (CExpression => (String, String)) = new CExpressionPlainPrettyPrinter(printDebugOut = false)
  override def apply(e: CExpression): (String, String) = printer(e)
}

/** Prints expressions in plain C. */
class CExpressionPlainPrettyPrinter(printDebugOut: Boolean) extends (CExpression => (String, String)) {

  /** Ensure to print literals as long double literals to avoid truncation. */
  private def longDoubleLiteral(n: BigDecimal): String = {
    val string = n.underlying().toString
    if (string.contains(".")) string + "L"
    else string + ".0L"
  }

  def printDefinitions(e: CExpression): String = e match {
    case COrProgram(l, r) =>
      s"""${printDefinitions(l)}
         |${printDefinitions(r)}
         |
         |verdict OrLeft${uniqueName(l)}(state pre, state curr, const parameters* const params) {
         |  ${print(l)}
         |}
         |
         |verdict OrRight${uniqueName(r)}(state pre, state curr, const parameters* const params) {
         |  ${print(r)}
         |}""".stripMargin
    case CAndProgram(l, r) =>
      s"""${printDefinitions(l)}
         |${printDefinitions(r)}
         |
         |verdict AndLeft${uniqueName(l)}(state pre, state curr, const parameters* const params) {
         |  ${print(l)}
         |}
         |
         |verdict AndRight${uniqueName(r)}(state pre, state curr, const parameters* const params) {
         |  ${print(r)}
         |}""".stripMargin
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
    case CNumber(n) if n>=0 => longDoubleLiteral(n)
    case CNumber(n) if n<0 => "(" + longDoubleLiteral(n) + ")"
    case CVariable(n) => n
    case CUnaryFunction(n, arg) => n + "(" + print(arg) + ")"
    case CPair(l, r) => print(l) + "," + print(r)
    case CNeg(c) => "-(" + print(c) + ")"
    case CPlus(l, r) => "(" + print(l) + ")+(" + print(r) + ")"
    case CMinus(l, r) => "(" + print(l) + ")-(" + print(r) + ")"
    case CTimes(l, r) => "(" + print(l) + ")*(" + print(r) + ")"
    case CDivide(l, r) => "(" + print(l) + ")/(" + print(r) + ")"
    case CPower(l, r) => "pow(" + print(l) + "," + print(r) + ")"
    /** Convert interpreted functions to corresponding C functions.
      *
      * C 99 standard:
      *   double fabs()
      *   float fabsf()
      *   long double fabsl()
      */
    case CMin(l, r) => "fminl(" + print(l) + ", " + print(r) + ")"
    case CMax(l, r) => "fmaxl(" + print(l) + ", " + print(r) + ")"
    case CAbs(c) => "fabsl(" + print(c) + ")"

    case CPredicate(n, arg) => n + "(" + print(arg) + ")"
    case CLess(l, r) => print(l) + " < " + print(r)
    case CLessEqual(l, r) => print(l) + " <= " + print(r)
    case CEqual(l, r) => print(l) + " == " + print(r)
    case CGreaterEqual(l, r) => print(l) + " >= " + print(r)
    case CGreater(l, r) => print(l) + " > " + print(r)
    case CNotEqual(l, r) => print(l) + " != " + print(r)
    case CNot(c) => "!(" + print(c) + ")"
    case CAnd(l, r) => "(" + print(l) + ") && (" + print(r) + ")"
    case COr(l, r) => "(" + print(l) + ") || (" + print(r) + ")"

    case comment: CComment => "/*" + comment.comment + "*/"

    case CTrue => "1.0L"
    case CFalse => "-1.0L"

    case CIfThenElse(f, ifP, elseP) => "if (" + print(f) + ") {\n" + print(ifP) + "\n} else {\n" + print(elseP) + "\n}"
    case CReturn(e: CExpression) => "verdict result = { .id=1, .val=" + print(e) + " }; return result;"
    case CError(id: Int, retVal: CExpression, msg: String) =>
      if (printDebugOut) s"""printf("Failed %d=%s\\n", $id, "$msg"); verdict result = { .id=$id, .val=${print(retVal)} }; return result;"""
      else s"verdict result = { .id=$id, .val=${print(retVal)} }; return result;"
    case COrProgram(l, r) /* if kind=="boolean" */ =>
      if (printDebugOut)
        s"""verdict leftDist = OrLeft${uniqueName(l)}(pre,curr,params);
         |verdict rightDist = OrRight${uniqueName(r)}(pre,curr,params);
         |printf("Or distances: %s=%Lf %s=%Lf\\n", "OrLeft${uniqueName(l)}", leftDist, "OrRight${uniqueName(r)}", rightDist);
         |int verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;
         |verdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };
         |return result;""".stripMargin
      else
        s"""verdict leftDist = OrLeft${uniqueName(l)}(pre,curr,params);
         |verdict rightDist = OrRight${uniqueName(r)}(pre,curr,params);
         |int verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;
         |verdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };
         |return result;""".stripMargin
    case CAndProgram(l, r) /* if kind=="boolean" */ =>
      if (printDebugOut)
        s"""verdict leftDist = AndLeft${uniqueName(l)}(pre,curr,params);
         |verdict rightDist = AndRight${uniqueName(r)}(pre,curr,params);
         |printf("And distances: %s=%Lf %s=%Lf\\n", "AndLeft${uniqueName(l)}", leftDist, "AndRight${uniqueName(r)}", rightDist);
         |int verdictId = leftDist.val <= rightDist.val ? leftDist.id : rightDist.id;
         |verdict result = { .id=verdictId, .val=fminl(leftDist.val, rightDist.val) };
         |return result;""".stripMargin
      else
        s"""verdict leftDist = AndLeft${uniqueName(l)}(pre,curr,params);
         |verdict rightDist = AndRight${uniqueName(r)}(pre,curr,params);
         |int verdictId = leftDist.val <= rightDist.val ? leftDist.id : rightDist.id;
         |verdict result = { .id=verdictId, .val=fminl(leftDist.val, rightDist.val) };
         |return result;""".stripMargin
  }

}

/** Prints C expressions that keep track of the reason for their value. */
class CExpressionLogPrettyPrinter extends (CExpression => (String, String)) {

  override def apply(e: CExpression): (String, String) = {
    ("", "eval(" + print(e) + ")")
  }

  def printOperators: String = {
    """typedef struct expr {
      |  long double value;
      |  const char* source;
      |} expr;
      |
      |const char* klog(const char* format, ...) {
      |  va_list args;
      |  va_start(args, format);
      |  /* don't care about memory leak */
      |  char* res = (char*)malloc(2048 * sizeof(char));
      |  vsnprintf(res, 2048, format, args);
      |  va_end(args);
      |  return res;
      |}
      |
      |expr number(long double v) {
      |  return (expr) {
      |    .value = v,
      |    .source = klog("%Lf", v)
      |  };
      |}
      |
      |expr variable(long double v, const char* name) {
      |  return (expr) {
      |    .value = v,
      |    .source = klog("%s", name)
      |  };
      |}
      |
      |expr neg(expr c) {
      |  return (expr) {
      |    .value = -c.value,
      |    .source = klog("-(%s)", c.source)
      |  };
      |}
      |
      |expr minus(expr l, expr r) {
      |  return (expr) {
      |    .value  = l.value - r.value,
      |    .source = klog("(%s) - (%s)", l.source, r.source)
      |  };
      |}
      |expr plus(expr l, expr r) {
      |  return (expr) {
      |    .value  = l.value + r.value,
      |    .source = klog("(%s) + (%s)", l.source, r.source)
      |  };
      |}
      |expr times(expr l, expr r) {
      |  return (expr) {
      |    .value  = l.value * r.value,
      |    .source = klog("(%s) * (%s)", l.source, r.source)
      |  };
      |}
      |expr divide(expr l, expr r) {
      |  return (expr) {
      |    .value  = l.value / r.value,
      |    .source = klog("(%s) / (%s)", l.source, r.source)
      |  };
      |}
      |expr power(expr l, expr r) {
      |  return (expr) {
      |    .value  = pow(l.value, r.value),
      |    .source = klog("(%s)^(%s)", l.source, r.source)
      |  };
      |}
      |expr kmin(expr l, expr r) {
      |  return (expr) {
      |    .value  = fminl(l.value, r.value),
      |    .source = fminl(l.value, r.value)==l.value ? l.source : r.source
      |  };
      |}
      |expr kmax(expr l, expr r) {
      |  return (expr) {
      |    .value  = fmaxl(l.value, r.value),
      |    .source = fmaxl(l.value, r.value)==l.value ? l.source : r.source
      |  };
      |}
      |expr kabs(expr c) {
      |  return (expr) {
      |    .value = fabsl(c.value),
      |    .source = klog("abs(%s)", c.source)
      |  };
      |};
      |expr lt(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value < r.value),
      |    .source = klog("%s < %s", l.source, r.source)
      |  };
      |}
      |expr leq(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value <= r.value),
      |    .source = klog("%s <= %s", l.source, r.source)
      |  };
      |}
      |expr eq(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value == r.value),
      |    .source = klog("%s == %s", l.source, r.source)
      |  };
      |}
      |expr neq(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value != r.value),
      |    .source = klog("%s != %s", l.source, r.source)
      |  };
      |}
      |expr geq(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value >= r.value),
      |    .source = klog("%s >= %s", l.source, r.source)
      |  };
      |}
      |expr gt(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value > r.value),
      |    .source = klog("%s > %s", l.source, r.source)
      |  };
      |}
      |expr and(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value && r.value),
      |    .source = l.value ? (r.value ? klog("%s&&%s", l.source, r.source) : r.source) : l.source
      |  };
      |}
      |expr or(expr l, expr r) {
      |  return (expr) {
      |    .value = (l.value || r.value),
      |    .source = l.value ? l.source : (r.value ? r.source : klog("%s||%s", l.source, r.source))
      |  };
      |}
      |expr not(expr c) {
      |  return (expr) {
      |    .value = !c.value,
      |    .source = klog("!(%s)", c.source)
      |  };
      |}
      |long double eval(expr e) {
      |  printf("expr = %Lf from %s\r\n", e.value, e.source);
      |  return e.value;
      |}
    """.stripMargin
  }

  //@todo print only necessary parentheses
  private def print(e: CExpression): String = e match {
    case CNumber(n) => "number(" + n.underlying().toString + ")"
    case CVariable(n) => "variable(" + n + ", \"" + n + "\")"
    case CUnaryFunction(n, arg) => n + "(" + print(arg) + ")"
    case CPair(l, r) => print(l) + "," + print(r)
    case CNeg(c) => "neg(" + print(c) + ")"
    case CPlus(l, r) => "plus(" + print(l) + ", " + print(r) + ")"
    case CMinus(l, r) => "minus(" + print(l) + ", " + print(r) + ")"
    case CTimes(l, r) => "times(" + print(l) + ", " + print(r) + ")"
    case CDivide(l, r) => "divide(" + print(l) + ", " + print(r) + ")"
    case CPower(l, r) => "power(" + print(l) + ", " + print(r) + ")"
    /** Convert interpreted functions to corresponding C functions.
      *
      * C 99 standard:
      *   double fabs()
      *   float fabsf()
      *   long double fabsl()
      */
    case CMin(l, r) => "kmin(" + print(l) + ", " + print(r) + ")"
    case CMax(l, r) => "kmax(" + print(l) + ", " + print(r) + ")"
    case CAbs(c) => "kabs(" + print(c) + ")"

    case CLess(l, r) => "lt(" + print(l) + ", " + print(r) + ")"
    case CLessEqual(l, r) => "leq(" + print(l) + ", " + print(r) + ")"
    case CEqual(l, r) => "eq(" + print(l) + ", " + print(r) + ")"
    case CGreaterEqual(l, r) => "geq(" + print(l) + ", " + print(r) + ")"
    case CGreater(l, r) => "gt(" + print(l) + ", " + print(r) + ")"
    case CNotEqual(l, r) => "neq(" + print(l) + ", " + print(r) + ")"
    case CNot(c) => "not(" + print(c) + ")"
    case CAnd(l, r) => "and(" + print(l) + ", " + print(r) + ")"
    case COr(l, r) => "or(" + print(l) + ", " + print(r) + ")"
  }

}

/** Prints C expressions that keep track of the reason for their value. NOT interval arithmetic, intervals are for
  * comparisons and formulas. Logs original formula and does unverified metric conversion to measure safety. */
class CExpressionIntervalLaTeXLogPrettyPrinter extends (CExpression => String) {

  override def apply(e: CExpression): String = {
    "eval(" + print(e) + ")"
  }

  def printOperators: String = {
    """typedef struct expr {
      |  long double low;
      |  long double high;
      |  const char* source;
      |} expr;
      |
      |const char* klog(const char* format, ...) {
      |  va_list args;
      |  va_start(args, format);
      |  /* don't care about memory leak */
      |  char* res = (char*)malloc(32758 * sizeof(char));
      |  vsnprintf(res, 32758, format, args);
      |  va_end(args);
      |  return res;
      |}
      |
      |expr number(long double v) {
      |  return (expr) {
      |    .low = v,
      |    .high = v,
      |    .source = klog("%Lf", v)
      |  };
      |}
      |
      |expr variable(long double v, const char* name) {
      |  return (expr) {
      |    .low = v,
      |    .high = v,
      |    .source = klog("\\overset{%Lf}{\\text{%s}}", name, v)
      |  };
      |}
      |
      |expr neg(expr c) {
      |  return (expr) {
      |    .low = -c.high,
      |    .high = -c.low,
      |    .source = klog("-(%s)", c.source)
      |  };
      |}
      |
      |expr minus(expr l, expr r) {
      |  return (expr) {
      |    .low  = l.low - r.low,
      |    .high = l.high - r.high,
      |    .source = klog("(%s) - (%s)", l.source, r.source)
      |  };
      |}
      |expr plus(expr l, expr r) {
      |  return (expr) {
      |    .low = l.low + r.low,
      |    .high = l.high + r.high,
      |    .source = klog("(%s) + (%s)", l.source, r.source)
      |  };
      |}
      |expr times(expr l, expr r) {
      |  return (expr) {
      |    .low  = l.low * r.low,
      |    .high = l.high * r.high,
      |    .source = klog("(%s) * (%s)", l.source, r.source)
      |  };
      |}
      |expr divide(expr l, expr r) {
      |  return (expr) {
      |    .low  = l.low / r.low,
      |    .high = l.high / r.high,
      |    .source = klog("(%s) / (%s)", l.source, r.source)
      |  };
      |}
      |expr power(expr l, expr r) {
      |  return (expr) {
      |    .low = pow(l.low, r.low),
      |    .high = pow(l.high, r.high),
      |    .source = klog("(%s)^(%s)", l.source, r.source)
      |  };
      |}
      |expr kmin(expr l, expr r) {
      |  return (expr) {
      |    .low  = fminl(l.low, r.low),
      |    .high = fminl(l.high, r.high),
      |    .source = fminl(l.low, r.low)==l.low ? klog("min(%s, _)", l.source) : klog("min(_, %s)", r.source)
      |  };
      |}
      |expr kmax(expr l, expr r) {
      |  return (expr) {
      |    .low = fmaxl(l.low, r.low),
      |    .high = fmaxl(l.high, r.high),
      |    .source = fmaxl(l.low, r.low)==l.low ? klog("max(%s, _)", l.source, l.low) : klog("max(_, %s)", r.source, r.low),
      |  };
      |}
      |expr kabs(expr c) {
      |  return (expr) {
      |    .low = fabsl(c.low),
      |    .high = fabsl(c.high),
      |    .source = klog("abs(%s)", c.source)
      |  };
      |}
      |expr lt(expr l, expr r) {
      |  return (expr) {
      |    .low = l.low - r.low, /* todo: wrong answer when == */
      |    .high = l.low - r.low,
      |    .source = klog("%s \\overset{%Lf}{<} %s", l.source, l.low-r.low, r.source)
      |  };
      |}
      |expr leq(expr l, expr r) {
      |  return (expr) {
      |    .low = l.low - r.low,
      |    .high = l.low - r.low,
      |    .source = klog("%s \\overset{%Lf}{\\leq} %s", l.source, l.low-r.low, r.source)
      |  };
      |}
      |expr eq(expr l, expr r) {
      |  return (expr) {
      |    .low = -fabsl(l.low - r.low),
      |    .high = -fabsl(l.low - r.low),
      |    .source = klog("%s \\overset{%Lf}{=} %s", l.source, -fabsl(l.low-r.low), r.source)
      |  };
      |}
      |expr neq(expr l, expr r) {
      |  return (expr) {
      |    .low = fabsl(l.low - r.low), /* note: wrong answer when == */
      |    .high = fabsl(l.low - r.low),
      |    .source = klog("%s \\overset{%Lf}{\\neq} %s", l.source, fabsl(l.low-r.low), r.source)
      |  };
      |}
      |expr geq(expr l, expr r) {
      |  return (expr) {
      |    .low = r.low - l.low,
      |    .high = r.low - l.low,
      |    .source = klog("%s \\overset{%Lf}{\\geq} %s", l.source, r.low-l.low, r.source)
      |  };
      |}
      |expr gt(expr l, expr r) {
      |  return (expr) {
      |    .low = r.low - l.low, /* todo: wrong answer when == */
      |    .high = r.low - l.low,
      |    .source = klog("%s \\overset{%Lf}{>} %s", l.source, r.low-l.low, r.source)
      |  };
      |}
      |expr and(expr l, expr r) {
      |  return (expr) {
      |    .low = fminl(l.low, r.low),
      |    .high = fmaxl(l.high, r.high),
      |    .source = l.high <= 0 ? (r.high <= 0 ? klog("%s \\overset{[%Lf,%Lf]}{\\wedge} %s", l.source, fminl(l.low, r.low), fmaxl(l.high, r.high), r.source) : klog("\\_ \\overset{[%Lf,%Lf]}{\\wedge} %s", r.source, fminl(l.low, r.low), fmaxl(l.high, r.high))) : klog("%s \\overset{[%Lf,%Lf]}{\\wedge} \\_", l.source, fminl(l.low, r.low), fmaxl(l.high, r.high))
      |  };
      |}
      |expr or(expr l, expr r) {
      |  return (expr) {
      |    .low = fmaxl(l.low, r.low),
      |    .high = fminl(l.high, r.high),
      |    .source = l.low <= 0 ? klog("%s \\overset{[%Lf,%Lf]}{\\vee} \\_", l.source, fmaxl(l.low, r.low), fminl(l.high, r.high)) : (r.low <= 0 ? klog("\\_ \\overset{[%Lf,%Lf]}{\\vee} %s", r.source, fmaxl(l.low, r.low), fminl(l.high, r.high)) : klog("%s \\overset{[%Lf,%Lf]}{\\vee} %s", l.source, fmaxl(l.low, r.low), fminl(l.high, r.high), r.source))
      |  };
      |}
      |expr not(expr c) {
      |  return (expr) {
      |    .low = c.high,
      |    .high = c.low,
      |    .source = klog("\\overset{[%Lf,%Lf]}{\\neg}(%s)", c.source, c.high, c.low)
      |  };
      |}
      |long double eval(expr e) {
      |  printf("expr = [%Lf,%Lf] from %s\r\n", e.low, e.high, e.source);
      |  return e.high;
      |}
    """.stripMargin
  }

  //@todo print only necessary parentheses
  private def print(e: CExpression): String = e match {
    case CNumber(n) => "number(" + n.underlying().toString + ")"
    case CVariable(n) => "variable(" + n + ", \"" + n + "\")"
    case CUnaryFunction(n, arg) => n + "(" + print(arg) + ")"
    case CPair(l, r) => print(l) + "," + print(r)
    case CNeg(c) => "neg(" + print(c) + ")"
    case CPlus(l, r) => "plus(" + print(l) + ", " + print(r) + ")"
    case CMinus(l, r) => "minus(" + print(l) + ", " + print(r) + ")"
    case CTimes(l, r) => "times(" + print(l) + ", " + print(r) + ")"
    case CDivide(l, r) => "divide(" + print(l) + ", " + print(r) + ")"
    case CPower(l, r) => "power(" + print(l) + ", " + print(r) + ")"
    /** Convert interpreted functions to corresponding C functions.
      *
      * C 99 standard:
      *   double fabs()
      *   float fabsf()
      *   long double fabsl()
      */
    case CMin(l, r) => "kmin(" + print(l) + ", " + print(r) + ")"
    case CMax(l, r) => "kmax(" + print(l) + ", " + print(r) + ")"
    case CAbs(c) => "kabs(" + print(c) + ")"

    case CLess(l, r) => "lt(" + print(l) + ", " + print(r) + ")"
    case CLessEqual(l, r) => "leq(" + print(l) + ", " + print(r) + ")"
    case CEqual(l, r) => "eq(" + print(l) + ", " + print(r) + ")"
    case CGreaterEqual(l, r) => "geq(" + print(l) + ", " + print(r) + ")"
    case CGreater(l, r) => "gt(" + print(l) + ", " + print(r) + ")"
    case CNotEqual(l, r) => "neq(" + print(l) + ", " + print(r) + ")"
    case CNot(c) => "not(" + print(c) + ")"
    case CAnd(l, r) => "and(" + print(l) + ", " + print(r) + ")"
    case COr(l, r) => "or(" + print(l) + ", " + print(r) + ")"
  }

}

/** Pretty prints expressions with the GNU MPFR library operators. */
class CMpfrPrettyPrinter(precision: Int = 200, roundingMode: String = "MPFR_RNDD") extends (CExpression => (String, String)) {

  private val mpfrVars: scala.collection.mutable.Map[CTerm, String] = scala.collection.mutable.Map.empty
  private val topExpressions: scala.collection.mutable.ListBuffer[CExpression] = scala.collection.mutable.ListBuffer.empty

  private def printMpfr(): String = {
    val arithmetic = topExpressions.map(printMpfrArithmetic).filter(_.nonEmpty).mkString("\n")
    val mpfrInit =
      mpfrVars.toList.sortBy(_._2).map(e => e._2 + s" /* ${new CExpressionPlainPrettyPrinter(printDebugOut=false)(e._1)._2} */").mkString("mpfr_t ", ",\n  ", ";\n\n") +
        mpfrVars.values.toList.sorted.map("mpfr_init2(" + _ + ", " + precision + ")").mkString("void mpfrInit() {\n  ", ";\n  ", ";\n}\n")
    val mpfrCompute = {
      val (mpfrVarsLiterals, mpfrTerms) = mpfrVars.toList.partition(_._1 match { case _: CVariable => true case _: CNumber => true case _ => false })
      mpfrVarsLiterals.sortBy(_._2).map({
        case (n: CVariable, _) => "mpfr_set_ld(" + mpfrVars(n) + ", " + n.name + ", " + roundingMode + ");"
        case (n: CNumber, _) => longDoubleLiteral(n)
      }).filter(_.nonEmpty).mkString(
        "void mpfrCompute(state pre, state curr, parameters const* const params) {\n  ",
        "\n  ",
        "\n  " + arithmetic.trim().replaceAllLiterally("\n", "\n  ") + "\n}")
    }
    mpfrInit + "\n" + mpfrCompute
  }

  def printDefinitions(e: CExpression): String = e match {
    case COrProgram(l, r) =>
      s"""${printDefinitions(l)}
         |${printDefinitions(r)}
         |
         |long double OrLeft${uniqueName(l)}(state pre, state curr, const parameters* const params) {
         |  ${print(l)}
         |}
         |
         |long double OrRight${uniqueName(r)}(state pre, state curr, const parameters* const params) {
         |  ${print(r)}
         |}""".stripMargin
    case CAndProgram(l, r) =>
      s"""${printDefinitions(l)}
         |${printDefinitions(r)}
         |
         |long double AndLeft${uniqueName(l)}(state pre, state curr, const parameters* const params) {
         |  ${print(l)}
         |}
         |
         |long double AndRight${uniqueName(r)}(state pre, state curr, const parameters* const params) {
         |  ${print(r)}
         |}""".stripMargin
    case CIfThenElse(cond, ifP, elseP) =>
      topExpressions.append(cond)
      printDefinitions(ifP) + "\n" + printDefinitions(elseP)
    case _ => ""
  }

  override def apply(e: CExpression): (String, String) = {
    mpfrVars.clear
    topExpressions.clear
    topExpressions.append(e)
    createMpfrVars(e)
    (printMpfr() + printDefinitions(e), print(e))
  }

  private def createMpfrVar(e: CTerm) = {
    if (!mpfrVars.contains(e)) {
      e match {
        case v@CVariable(n) =>
          mpfrVars.put(v, n.
            replace("params->", "params_").
            replace("pre.", "pre_").
            replace("curr.", "curr_").
            replace("prg.state.", "prg_state_"))
          mpfrVars(v)
        case t: CTerm if !mpfrVars.contains(t) =>
          mpfrVars.put(t, "_t_" + mpfrVars.size)
          mpfrVars(t)
        case _ => //@note formula comparisons and conjunctions can be computed inline
      }
    }
  }

  private def uniqueName(fml: CExpression): String = {
    val hashcode = fml.hashCode()
    if (hashcode < 0) hashcode.toString.replace("-", "_")
    else hashcode.toString
  }

  private def longDoubleLiteral(n: CNumber): String = {
    val string = n.n.underlying().toString
    "mpfr_set_ld(" + mpfrVars(n) + ", " + string + "L, " + roundingMode + ");"
  }

  private def unaryTermOp(op: String, t: CTerm, c: CTerm): String = {
    printMpfrArithmetic(c) + "mpfr_" + op + "(" + mpfrVars(t) + ", " + mpfrVars(c) + ", " + roundingMode + ");\n"
  }

  private def binaryTermOp(op: String, t: CTerm, l: CTerm, r: CTerm): String = {
    printMpfrArithmetic(l) + printMpfrArithmetic(r) + "mpfr_" + op + "(" + mpfrVars(t) + ", " + mpfrVars(l) + ", " + mpfrVars(r) + ", " + roundingMode + ");\n"
  }

  private def createMpfrVars(e: CExpression): Unit = e match {
    case t: CVariable => createMpfrVar(t)
    case t: CNumber => createMpfrVar(t)

    case CTrue | CFalse =>
    case COrProgram(l, r) => createMpfrVars(l); createMpfrVars(r)
    case CIfThenElse(cond, ifP, elseP) => createMpfrVars(cond); createMpfrVars(ifP); createMpfrVars(elseP)
    case CReturn(r) => createMpfrVars(r)
    case CError(_, r, _) => createMpfrVars(r)

    case t@CNeg(c) => createMpfrVar(t); createMpfrVars(c)
    case t@CPlus(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CMinus(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CTimes(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CDivide(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CPower(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CMin(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CMax(l, r) => createMpfrVar(t); createMpfrVars(l); createMpfrVars(r)
    case t@CAbs(c) => createMpfrVar(t); createMpfrVars(c)

    case CLess(l, r) => createMpfrVars(l); createMpfrVars(r)
    case CLessEqual(l, r) => createMpfrVars(l); createMpfrVars(r)
    case CEqual(l, r) => createMpfrVars(l); createMpfrVars(r)
    case CGreaterEqual(l, r) => createMpfrVars(l); createMpfrVars(r)
    case CGreater(l, r) => createMpfrVars(l); createMpfrVars(r)
    case CNotEqual(l, r) => createMpfrVars(l); createMpfrVars(r)

    case CNot(c) => createMpfrVars(c)
    case CAnd(l, r) => createMpfrVars(l); createMpfrVars(r)
    case COr(l, r) => createMpfrVars(l); createMpfrVars(r)

    case _ => ??? //createMpfrVar(e)
  }

  private def printMpfrArithmetic(e: CExpression): String = e match {
    case n: CVariable => "" //@note computed once in the initialization code
    case n: CNumber => "" //@note computed once in the initialization code
    case CUnaryFunction(n, arg) => ??? //n + "(" + print(arg) + ")"
    case CPair(l, r) => ??? //print(l) + "," + print(r)
    case t@CNeg(c) => unaryTermOp("neg", t, c)
    case t@CPlus(l, r) => binaryTermOp("add", t, l, r)
    case t@CMinus(l, r) => binaryTermOp("sub", t, l, r)
    case t@CTimes(l, r) => binaryTermOp("mul", t, l, r)
    case t@CDivide(l, r) => binaryTermOp("div", t, l, r)
    case t@CPower(l, r) => binaryTermOp("pow", t, l, r)
    case t@CMin(l, r) => binaryTermOp("min", t, l, r)
    case t@CMax(l, r) => binaryTermOp("max", t, l, r)
    case t@CAbs(c) => unaryTermOp("abs", t, c)

    case CLess(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CLessEqual(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CEqual(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CGreaterEqual(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CGreater(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CNotEqual(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)

    case CNot(c) => printMpfrArithmetic(c)
    case CAnd(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case COr(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CTrue => ""
    case CFalse => ""

    case COrProgram(l, r) => printMpfrArithmetic(l) + printMpfrArithmetic(r)
    case CIfThenElse(cond, ifP, elseP) => printMpfrArithmetic(cond) + printMpfrArithmetic(ifP) + printMpfrArithmetic(elseP)
    case CReturn(r) => printMpfrArithmetic(r)
    case CError(_, r, _) => printMpfrArithmetic(r)
  }

  //@todo print only necessary parentheses
  private def print(e: CExpression): String = e match {
//    case CLess(l, r) => "mpfr_cmp(" + mpfrVars(l) + ", " + mpfrVars(r) + ") < 0"
//    case CLessEqual(l, r) => "mpfr_cmp(" + mpfrVars(l) + ", " + mpfrVars(r) + ") <= 0"
//    case CEqual(l, r) => "mpfr_cmp(" + mpfrVars(l) + ", " + mpfrVars(r) + ") == 0"
//    case CGreaterEqual(l, r) => "mpfr_cmp(" + mpfrVars(r) + ", " + mpfrVars(l) + ") <= 0"
//    case CGreater(l, r) => "mpfr_cmp(" + mpfrVars(r) + ", " + mpfrVars(l) + ") < 0"
//    case CNotEqual(l, r) => "mpfr_cmp(" + mpfrVars(l) + ", " + mpfrVars(r) + ") != 0"

    //@note double comparisons, since we convert MPFR results of controller to rounded-down doubles
    case CLess(l, r) => s"mpfr_get_ld(${mpfrVars(l)}, $roundingMode) < mpfr_get_ld(${mpfrVars(r)}, $roundingMode)"
    case CLessEqual(l, r) => s"mpfr_get_ld(${mpfrVars(l)}, $roundingMode) <= mpfr_get_ld(${mpfrVars(r)}, $roundingMode)"
    case CEqual(l, r) => s"mpfr_get_ld(${mpfrVars(l)}, $roundingMode) == mpfr_get_ld(${mpfrVars(r)}, $roundingMode)"
    case CGreaterEqual(l, r) => s"mpfr_get_ld(${mpfrVars(l)}, $roundingMode) >= mpfr_get_ld(${mpfrVars(r)}, $roundingMode)"
    case CGreater(l, r) => s"mpfr_get_ld(${mpfrVars(l)}, $roundingMode) > mpfr_get_ld(${mpfrVars(r)}, $roundingMode)"
    case CNotEqual(l, r) => s"mpfr_get_ld(${mpfrVars(l)}, $roundingMode) != mpfr_get_ld(${mpfrVars(r)}, $roundingMode)"

    case CNot(c) => "!(" + print(c) + ")"
    case CAnd(l, r) => "(" + print(l) + ") && (" + print(r) + ")"
    case COr(l, r) => "(" + print(l) + ") || (" + print(r) + ")"

    case CTrue => "1.0L"
    case CFalse => "-1.0L"

    case CIfThenElse(f, ifP, elseP) => "if (" + print(f) + ") {\n" + print(ifP) + "\n} else {\n" + print(elseP) + "\n}"
    case CReturn(e: CTerm) => s"return mpfr_get_ld(${mpfrVars(e)}, $roundingMode);"
    case CError(_, retVal: CFormula, msg: String) => s"""printf("Failed %s\\n", "$msg"); return ${print(retVal)};"""
    case CError(_, retVal: CTerm, msg: String) =>
      s"""printf("Failed %s\\n", "$msg"); return mpfr_get_ld(${mpfrVars(retVal)}, $roundingMode);"""
    case COrProgram(l, r) /* if kind=="boolean" */ =>
      s"""long double leftDist = OrLeft${uniqueName(l)}(pre,curr,params);
         |long double rightDist = OrRight${uniqueName(r)}(pre,curr,params);
         |printf("Or distances: %s=%Lf %s=%Lf\\n", "OrLeft${uniqueName(l)}", leftDist, "OrRight${uniqueName(r)}", rightDist);
         |return fmaxl(leftDist, rightDist);""".stripMargin
    case CAndProgram(l, r) /* if kind=="boolean" */ =>
      s"""long double leftDist = AndLeft${uniqueName(l)}(pre,curr,params);
         |long double rightDist = AndRight${uniqueName(r)}(pre,curr,params);
         |printf("And distances: %s=%Lf %s=%Lf\\n", "AndLeft${uniqueName(l)}", leftDist, "AndRight${uniqueName(r)}", rightDist);
         |return fminl(leftDist, rightDist);""".stripMargin
    case t: CTerm =>
      s"mpfr_get_ld(${mpfrVars(t)}, $roundingMode);" //@note terms cannot be evaluated inline -> are computed in the definitions block
  }

}
