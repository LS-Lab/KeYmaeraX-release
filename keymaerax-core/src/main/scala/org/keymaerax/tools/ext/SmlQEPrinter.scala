/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools.ext

import org.keymaerax.core._

/** Prints SML QE problems with Real64 rounding. */
object SmlQEReal64Printer extends (Formula => String) {
  def apply(f: Formula): String = new SmlQEPrinter(_.toString + ".0", _.toString)
    .print(f)(StaticSemantics.freeVars(f).toSet.toList.zipWithIndex.toMap)
}

/** Prints SML QE problems with RatReal, avoiding rounding. */
object SmlQENoRoundingPrinter extends (Formula => String) {
  def apply(f: Formula): String = {
    new SmlQEPrinter(
      intPrinter = "(Int2Real " + (_: BigInt).toString + ")",
      realPrinter = (n: BigDecimal) => {
        val num = n.bigDecimal.unscaledValue()
        val denom = BigDecimal(1).bigDecimal.movePointRight(n.scale).toBigIntegerExact
        "(Rat2Real " + num + " " + denom + ")"
      },
    ).print(f)(StaticSemantics.freeVars(f).toSet.toList.zipWithIndex.toMap)
  }
}

/** Prints expressions to SML QE data structure. */
class SmlQEPrinter(intPrinter: BigInt => String, realPrinter: BigDecimal => String) {

  /** Prints formula `f`, encoding variables using DeBruijn-indices as supplied by `vIdx`. */
  def print(f: Formula)(implicit vIdxs: Map[Variable, Int]): String = f match {
    case True => "TrueF"
    case False => "FalseF"
    case Equal(l, Number(n)) if n == 0 => s"Atom(Eq(${print(l)}))"
    case NotEqual(l, Number(n)) if n == 0 => s"Atom(Neq(${print(l)}))"
    case Less(l, Number(n)) if n == 0 => s"Atom(Less(${print(l)}))"
    case LessEqual(l, Number(n)) if n == 0 => s"Atom(Leq(${print(l)}))"
    case Equal(l, r) => s"Atom(Eq(minus (${print(l)}) (${print(r)})))"
    case NotEqual(l, r) => s"Atom(Neq(minus (${print(l)}) (${print(r)})))"
    case Less(l, r) => s"Atom(Less(minus (${print(l)}) (${print(r)})))"
    case LessEqual(l, r) => s"Atom(Leq(minus (${print(l)}) (${print(r)})))"
    case Greater(l, r) => print(Not(LessEqual(l, r)))
    case GreaterEqual(l, r) => print(Not(Less(l, r)))
    case Not(p) => s"Neg(${print(p)})"
    case And(p, q) => s"And(${print(p)},${print(q)})"
    case Or(p, q) => s"Or(${print(p)},${print(q)})"
    case Imply(p, q) => print(Or(Not(p), q))
    case Equiv(p, q) => print(Or(And(p, q), And(Not(p), Not(q))))
    case Forall(x :: Nil, p) =>
      s"AllQ (${print(p)(Map((vIdxs.map({ case (k, v) => k -> (v + 1) }).toList :+ (x -> 0)): _*))})"
    case Exists(x :: Nil, p) =>
      s"ExQ (${print(p)(Map((vIdxs.map({ case (k, v) => k -> (v + 1) }).toList :+ (x -> 0)): _*))})"
  }

  /** Prints term `t`, encoding variables using DeBruijn-indices as supplied by `vIdx`. */
  def print(t: Term)(implicit vIdx: Map[Variable, Int]): String = t match {
    case Number(n) => s"Const ${printNum(n)}"
    case v: Variable => s"Var ${vIdx(v)}"
    case Neg(t) => print(Minus(Number(0), t))
    case Plus(Number(l), Number(r)) => s"Const (real_plus ${printNum(l)} ${printNum(r)})"
    case Plus(l, r) => s"add (${print(l)}) (${print(r)})"
    case Minus(Number(l), Number(r)) => s"Const (real_minus ${printNum(l)} ${printNum(r)})"
    case Minus(l, r) => s"minus (${print(l)}) (${print(r)})"
    case Times(Number(l), Number(r)) => s"Const (real_mult ${printNum(l)} ${printNum(r)})"
    case Times(l, r) => s"mult (${print(l)}) (${print(r)})"
    case Power(l, Number(n)) => s"pow (${print(l)}) $n"
    case Divide(Number(l), Number(r)) => s"Const (real_div ${printNum(l)} ${printNum(r)})"
    case Divide(l, r: Number) => print(Times(l, Divide(Number(1), r)))
  }

  /** Prints number `n`. */
  def printNum(n: BigDecimal): String = n.toBigIntExact match {
    case Some(i) => intPrinter(i).replace("-", "~")
    case None => realPrinter(n).replace("-", "~")
  }
}
