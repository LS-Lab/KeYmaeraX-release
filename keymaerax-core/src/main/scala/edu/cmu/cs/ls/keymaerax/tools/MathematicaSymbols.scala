/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.MExpr

/**
 * This is a symbol table used to check for matches using .equals()
 * This is mostly copied from the original KeYmaera implementation by
 * Jan-David.
 */
private object MathematicaSymbols {
  val keywords = Seq("False", "True", "Not", "Rational", "Plus", "Subtract", "Minus",
      "Times", "Divide", "Power", "Equal", "Unequal", "Less", "LessEqual",
      "Greater", "GreaterEqual", "Inequality", "ForAll", "Exists", "And",
      "Or", "Implies", "Equivalent", "InverseFunction", "Integrate", "Rule",
      "List", "Reduce", "Reals")

  def FALSE = new MExpr(Expr.SYMBOL, "False")
  def TRUE = new MExpr(Expr.SYMBOL, "True")
  def NOT = new MExpr(Expr.SYMBOL, "Not")
  def RATIONAL = new MExpr(Expr.SYMBOL, "Rational") //No special case; works with numberQ
  def PLUS = new MExpr(Expr.SYMBOL, "Plus")
  def MINUS = new MExpr(Expr.SYMBOL, "Subtract")
  def MINUSSIGN = new MExpr(Expr.SYMBOL, "Minus") //No conversion rule.
  def MULT = new MExpr(Expr.SYMBOL, "Times")
  def DIV = new MExpr(Expr.SYMBOL, "Divide")
  def EXP = new MExpr(Expr.SYMBOL, "Power")
  def APPLY = new MExpr(Expr.SYMBOL, "Apply")
  def EQUALS = new MExpr(Expr.SYMBOL, "Equal")
  def UNEQUAL = new MExpr(Expr.SYMBOL, "Unequal")
  def LESS = new MExpr(Expr.SYMBOL, "Less")
  def LESS_EQUALS = new MExpr(Expr.SYMBOL, "LessEqual")
  def GREATER = new MExpr(Expr.SYMBOL, "Greater")
  def GREATER_EQUALS = new MExpr(Expr.SYMBOL, "GreaterEqual")
  def INEQUALITY = new MExpr(Expr.SYMBOL, "Inequality")
  def FORALL = new MExpr(Expr.SYMBOL, "ForAll")
  def EXISTS = new MExpr(Expr.SYMBOL, "Exists")
  def AND = new MExpr(Expr.SYMBOL, "And")
  def OR = new MExpr(Expr.SYMBOL, "Or")
  def IMPL = new MExpr(Expr.SYMBOL, "Implies")
  def BIIMPL = new MExpr(Expr.SYMBOL, "Equivalent")
  //def INVERSE_FUNCTION = new MExpr(Expr.SYMBOL, "InverseFunction")
  def INTEGRATE = new MExpr(Expr.SYMBOL, "Integrate")
  //def RULE = new MExpr(Expr.SYMBOL, "Rule")
  def LIST = new MExpr(Expr.SYMBOL, "List") //?
  def DERIVATIVE = new MExpr(Expr.SYMBOL, "Derivative")
  def D = new MExpr(Expr.SYMBOL, "D")
  def RULE = new MExpr(Expr.SYMBOL, "Rule")

  def REDUCE = new MExpr(Expr.SYMBOL,  "Reduce")
  def RESOLVE = new MExpr(Expr.SYMBOL,  "Resolve")
  def REALS = new MExpr(Expr.SYMBOL, "Reals")
  def SOLVE = new MExpr(Expr.SYMBOL,  "Solve")
  def DSOLVE = new MExpr(Expr.SYMBOL,  "DSolve")
  def FULLSIMPLIFY = new MExpr(Expr.SYMBOL,  "FullSimplify")
  def POLYNOMIALQUOTIENTREMAINDER = new MExpr(Expr.SYMBOL,  "PolynomialQuotientRemainder")

  def CHECK = new MExpr(Expr.SYMBOL, "Check")
  def EXCEPTION = new MExpr(Expr.SYMBOL, "$Exception")
  def ABORTED = new MExpr(Expr.SYMBOL, "$Aborted")
}
