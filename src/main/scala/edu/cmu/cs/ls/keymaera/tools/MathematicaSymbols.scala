package edu.cmu.cs.ls.keymaera.tools

import com.wolfram.jlink._

/**
 * This is a symbol table used to check for matches using .equals()
 * This is mostly copied from the original KeYmaera implementation by
 * Jan-David.
 */
private object MathematicaSymbols {
  type MExpr = com.wolfram.jlink.Expr

  val keywords = Seq("False", "True", "Not", "Rational", "Plus", "Subtract", "Minus",
      "Times", "Divide", "Power", "Equal", "Unequal", "Less", "LessEqual",
      "Greater", "GreaterEqual", "Inequality", "ForAll", "Exists", "And",
      "Or", "Implies", "Equivalent", "InverseFunction", "Integrate", "Rule",
      "List")
      
  val FALSE = new MExpr(Expr.SYMBOL, "False")
  val TRUE = new MExpr(Expr.SYMBOL, "True")
  val NOT = new MExpr(Expr.SYMBOL, "Not")
  val RATIONAL = new MExpr(Expr.SYMBOL, "Rational") //No special case; works with numberQ
  val PLUS = new MExpr(Expr.SYMBOL, "Plus")
  val MINUS = new MExpr(Expr.SYMBOL, "Subtract")
  val MINUSSIGN = new MExpr(Expr.SYMBOL, "Minus") //No conversion rule.
  val MULT = new MExpr(Expr.SYMBOL, "Times")
  val DIV = new MExpr(Expr.SYMBOL, "Divide")
  val EXP = new MExpr(Expr.SYMBOL, "Power")
  val EQUALS = new MExpr(Expr.SYMBOL, "Equal")
  val UNEQUAL = new MExpr(Expr.SYMBOL, "Unequal")
  val LESS = new MExpr(Expr.SYMBOL, "Less")
  val LESS_EQUALS = new MExpr(Expr.SYMBOL, "LessEqual")
  val GREATER = new MExpr(Expr.SYMBOL, "Greater")
  val GREATER_EQUALS = new MExpr(Expr.SYMBOL, "GreaterEqual")
  val INEQUALITY = new MExpr(Expr.SYMBOL, "Inequality")
  val FORALL = new MExpr(Expr.SYMBOL, "ForAll")
  val EXISTS = new MExpr(Expr.SYMBOL, "Exists")
  val AND = new MExpr(Expr.SYMBOL, "And")
  val OR = new MExpr(Expr.SYMBOL, "Or")
  val IMPL = new MExpr(Expr.SYMBOL, "Implies")
  val BIIMPL = new MExpr(Expr.SYMBOL, "Equivalent")
  //val INVERSE_FUNCTION = new MExpr(Expr.SYMBOL, "InverseFunction")
  val INTEGRATE = new MExpr(Expr.SYMBOL, "Integrate")
  //val RULE = new MExpr(Expr.SYMBOL, "Rule")
  val LIST = new MExpr(Expr.SYMBOL, "List") //?
  val DERIVATIVE = new MExpr(Expr.SYMBOL, "Derivative")
}
