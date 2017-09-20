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

object CPrettyPrinter extends (CExpression => String) {
  var printer = new CExpressionPlainPrettyPrinter
  override def apply(e: CExpression): String = printer(e)
}

class CExpressionPlainPrettyPrinter extends (CExpression => String) {

  //@todo print only necessary parentheses
  override def apply(e: CExpression): String = e match {
    case CNumber(n) if n>=0 => n.underlying().toString
    case CNumber(n) if n<0 => "(" + n.underlying().toString + ")"
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