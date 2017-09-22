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

/** Prints C expressions. */
object CPrettyPrinter extends (CExpression => String) {
  var printer: (CExpression => String) = new CExpressionPlainPrettyPrinter
  override def apply(e: CExpression): String = printer(e)
}

/** Prints expressions in plain C. */
class CExpressionPlainPrettyPrinter extends (CExpression => String) {

  /** Ensure to print literals as long double literals to avoid truncation. */
  private def longDoubleLiteral(n: BigDecimal): String = {
    val string = n.underlying().toString
    if (string.contains(".")) string + "L"
    else string + ".0L"
  }

  //@todo print only necessary parentheses
  override def apply(e: CExpression): String = e match {
    case CNumber(n) if n>=0 => longDoubleLiteral(n)
    case CNumber(n) if n<0 => "(" + longDoubleLiteral(n) + ")"
    case CVariable(n) => n
    case CUnaryFunction(n, arg) => n + "(" + apply(arg) + ")"
    case CPair(l, r) => apply(l) + "," + apply(r)
    case CNeg(c) => "-(" + apply(c) + ")"
    case CPlus(l, r) => "(" + apply(l) + ")+(" + apply(r) + ")"
    case CMinus(l, r) => "(" + apply(l) + ")-(" + apply(r) + ")"
    case CTimes(l, r) => "(" + apply(l) + ")*(" + apply(r) + ")"
    case CDivide(l, r) => "(" + apply(l) + ")/(" + apply(r) + ")"
    case CPower(l, r) => "pow(" + apply(l) + "," + apply(r) + ")"
    /** Convert interpreted functions to corresponding C functions.
      *
      * C 99 standard:
      *   double fabs()
      *   float fabsf()
      *   long double fabsl()
      */
    case CMin(l, r) => "fminl(" + apply(l) + ", " + apply(r) + ")"
    case CMax(l, r) => "fmaxl(" + apply(l) + ", " + apply(r) + ")"
    case CAbs(c) => "fabsl(" + apply(c) + ")"

    case CLess(l, r) => apply(l) + " < " + apply(r)
    case CLessEqual(l, r) => apply(l) + " <= " + apply(r)
    case CEqual(l, r) => apply(l) + " == " + apply(r)
    case CGreaterEqual(l, r) => apply(l) + " >= " + apply(r)
    case CGreater(l, r) => apply(l) + " > " + apply(r)
    case CNotEqual(l, r) => apply(l) + " != " + apply(r)
    case CNot(c) => "!(" + apply(c) + ")"
    case CAnd(l, r) => "(" + apply(l) + ") && (" + apply(r) + ")"
    case COr(l, r) => "(" + apply(l) + ") || (" + apply(r) + ")"
  }

}

/** Prints C expressions that keep track of the reason for their value. */
class CExpressionLogPrettyPrinter extends (CExpression => String) {

  override def apply(e: CExpression): String = {
    "eval(" + print(e) + ")"
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