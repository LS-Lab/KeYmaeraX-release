/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

/**
  * C expressions.
  * @author Stefan Mitsch
  */
trait CExpression {

}

trait CTerm extends CExpression {}
trait CFormula extends CExpression {}
trait CProgram extends CExpression {}

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
case class CError(retVal: CExpression, msg: String) extends CProgram
case class CReturn(e: CExpression) extends CProgram
object CNoop extends CProgram


/** Prints C expressions. */
object CPrettyPrinter extends (CExpression => (String, String)) {
  var printer: (CExpression => (String, String)) = new CExpressionPlainPrettyPrinter
  override def apply(e: CExpression): (String, String) = printer(e)
}

/** Prints expressions in plain C. */
class CExpressionPlainPrettyPrinter extends (CExpression => (String, String)) {

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

    case CLess(l, r) => print(l) + " < " + print(r)
    case CLessEqual(l, r) => print(l) + " <= " + print(r)
    case CEqual(l, r) => print(l) + " == " + print(r)
    case CGreaterEqual(l, r) => print(l) + " >= " + print(r)
    case CGreater(l, r) => print(l) + " > " + print(r)
    case CNotEqual(l, r) => print(l) + " != " + print(r)
    case CNot(c) => "!(" + print(c) + ")"
    case CAnd(l, r) => "(" + print(l) + ") && (" + print(r) + ")"
    case COr(l, r) => "(" + print(l) + ") || (" + print(r) + ")"

    case CTrue => "1.0L"
    case CFalse => "-1.0L"

    case CIfThenElse(f, ifP, elseP) => "if (" + print(f) + ") {\n" + print(ifP) + "\n} else {\n" + print(elseP) + "\n}"
    case CReturn(e: CExpression) => "return " + print(e) + ";"
    case CError(retVal: CExpression, msg: String) => s"""printf("Failed %s\\n", "$msg"); return ${print(retVal)};"""
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
