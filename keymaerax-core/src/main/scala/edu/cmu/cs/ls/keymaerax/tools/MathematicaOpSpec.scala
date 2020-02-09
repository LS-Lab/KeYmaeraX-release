/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.core.{Function, NamedSymbol, Real, Tuple}

/** Mathematica operator notation. */
trait MathematicaOpSpec {
  /** The operator symbol */
  def op: Expr

  /**
    * Whether e is `thing` or starts with head `thing`.
    * @return True if `e` and `thing` are ==-related; false otherwise.
    */
  def hasHead(e: Expr, thing: Expr): Boolean = e == thing || e.head == thing
}

/** Math literals. */
case class LiteralMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Indicates whether Mathematica expression `e` fits this operator. */
  def applies(e: Expr): Boolean = hasHead(e, op)
}

/** Unary Math operators. */
case class UnaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(e: Expr): Expr = new Expr(op, Array[Expr](e))
  /** Indicates whether Mathematica expression `e` fits this operator. */
  def applies(e: Expr): Boolean = hasHead(e, op)
}

/** Binary Math operators. */
case class BinaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(l: Expr, r: Expr): Expr = new Expr(op, Array[Expr](l, r))
  /** Indicates whether Mathematica expression `e` fits this operator. */
  def applies(e: Expr): Boolean = hasHead(e, op)
}

/** Nary Math operators. */
case class NaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(args: Expr*): Expr = new Expr(op, args.toArray)
  /** Indicates whether Mathematica expression `e` fits this operator. */
  def applies(e: Expr): Boolean = hasHead(e, op)
}

/** Quantifier Math operators. */
case class QuantifiedMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with quantified variables `vars` and formula `q`. */
  def apply(vars: Array[Expr], q: Expr): Expr = new Expr(op, Array[Expr](MathematicaOpSpec.list(vars:_*), q))
  /** Indicates whether Mathematica expression `e` fits this operator. */
  def applies(e: Expr): Boolean = hasHead(e, op)
}

/** [[NamedSymbol]] operators, with `k2m` converter {{{(name, args) => Expr}}}. */
case class NameMathOpSpec(k2m: (NamedSymbol, Array[Expr]) => Expr, applies: Expr => Boolean) {
  def apply(ns: NamedSymbol, args: Array[Expr]): Expr = k2m(ns, args)
}

/** Function Math operators, with `k2m` converter {{{args => Expr}}}. */
case class InterpretedMathOpSpec(op: Expr, fn: Function) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with head `op` and arguments `args`. */
  def apply(args: Array[Expr]): Expr = new Expr(op, args)
  /** Indicates whether Mathematica expression `e` fits this operator. */
  def applies(e: Expr): Boolean = hasHead(e, op)
}

/** Mathematica operator specifications with conversions. */
object MathematicaOpSpec {

  /** Keywords, not to convert as functions or variables.  */
  private val keywords: Seq[String] = Seq(
    // terms
    "Minus", "Plus", "Subtract", "Times", "Divide", "Rational", "Power",
    // comparisons
    "Equal", "Unequal", "Less", "LessEqual", "Greater", "GreaterEqual", "Inequality",
    // formulas
    "False", "True", "Not", "And", "Or", "Implies", "Equivalent", "ForAll", "Exists",
    // rest
    "InverseFunction", "Integrate", "Rule", "List", "Reduce", "Reals")

  /** Indicates whether the expression `e` is a keyword. */
  def isNonKeywordSymbol(e: Expr): Boolean =
    (e.head().symbolQ() && !keywords.contains(e.head().toString)) || (e.symbolQ() && !keywords.contains(e.toString))

  //<editor-fold desc="Basic data structures">

  /** Creates a Mathematica symbol `s`. */
  def symbol(s: String): Expr = new Expr(Expr.SYMBOL, s)

  /** Creates a Mathematica Int. */
  def int(n: Int): Expr = new Expr(n)

  /** Creates a Mathematica Long. */
  def long(n: Long): Expr = new Expr(n)

  /** Creates a Mathematica Double. */
  def double(n: Double): Expr = new Expr(n)

  /** Creates a Mathematica big integer. */
  def bigInt(n: BigInt): Expr = new Expr(n.bigInteger)

  /** Creates a Mathematica String. */
  def string(s: String): Expr = new Expr(s)

  val list = NaryMathOpSpec(Expr.SYM_LIST)

  /** Mathematica function application f(args). */
  def apply(f: Expr): (Expr*) => Expr = (args: Seq[Expr]) => new Expr(f, args.toArray)

  //</editor-fold>

  //<editor-fold desc="Terms">

  val neg: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Minus"))

  val plus: NaryMathOpSpec = NaryMathOpSpec(symbol("Plus"))

  val minus: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Subtract"))

  val times: NaryMathOpSpec = NaryMathOpSpec(symbol("Times"))

  val divide: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Divide"))

  val rational: BinaryMathOpSpec = BinaryMathOpSpec(Expr.SYM_RATIONAL)

  val power: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Power"))

  val func: NameMathOpSpec = NameMathOpSpec(
    (name: NamedSymbol, args: Array[Expr]) => {
      require(args.length <= 2, "Functions expected to have at most 2 arguments (nothing, single argument, or converted pair)")
      new Expr(MathematicaNameConversion.toMathematica(name), args)
    },
    e => e.head.symbolQ() && e.args().length <= 2
  )

  val abs: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Abs"), Function("abs", None, Real, Real, interpreted=true))

  val min: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Min"), Function("min", None, Tuple(Real, Real), Real, interpreted=true))

  val max: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Max"), Function("max", None, Tuple(Real, Real), Real, interpreted=true))

  val variable: NameMathOpSpec = NameMathOpSpec(
    (name: NamedSymbol, args: Array[Expr]) => {
      require(args.isEmpty, "Unexpected arguments")
      MathematicaNameConversion.toMathematica(name)
    },
    _.symbolQ()
  )

  val pair: BinaryMathOpSpec = new BinaryMathOpSpec(Expr.SYM_LIST) {
    //@note inherited apply converts nested pairs into nested lists of length 2 each
    override def applies(e: Expr): Boolean = e.listQ
  }

  //</editor-fold>

  //<editor-fold desc="Comparison formulas">

  val equal: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Equal"))

  val unequal: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Unequal"))

  val inequality: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Inequality"))

  val greater: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Greater"))

  val greaterEqual: BinaryMathOpSpec = BinaryMathOpSpec(symbol("GreaterEqual"))

  val less: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Less"))

  val lessEqual: BinaryMathOpSpec = BinaryMathOpSpec(symbol("LessEqual"))

  //</editor-fold>

  //<editor-fold desc="Formulas">

  val ltrue: LiteralMathOpSpec = LiteralMathOpSpec(Expr.SYM_TRUE)

  val lfalse: LiteralMathOpSpec = LiteralMathOpSpec(Expr.SYM_FALSE)

  val not: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Not"))

  val and: NaryMathOpSpec = NaryMathOpSpec(symbol("And"))

  val or: NaryMathOpSpec = NaryMathOpSpec(symbol("Or"))

  val implies: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Implies"))

  val equivalent: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Equivalent"))

  val forall: QuantifiedMathOpSpec = QuantifiedMathOpSpec(symbol("ForAll"))

  val exists: QuantifiedMathOpSpec = QuantifiedMathOpSpec(symbol("Exists"))

  //</editor-fold>

  //<editor-fold desc="Arithmetic">

  val rule = BinaryMathOpSpec(symbol("Rule"))

  val reduce = NaryMathOpSpec(symbol("Reduce"))

  val resolve = NaryMathOpSpec(symbol("Resolve"))

  val reals = LiteralMathOpSpec(symbol("Reals"))

  //</editor-fold>

  //<editor-fold desc="Diagnostics">

  val aborted = LiteralMathOpSpec(symbol("$Aborted"))

  val abort = LiteralMathOpSpec(new Expr(symbol("Abort"), Array.empty[Expr]))

  val failed = LiteralMathOpSpec(symbol("$Failed"))

  val exception = LiteralMathOpSpec(symbol("$Exception"))

  val versionNumber = LiteralMathOpSpec(symbol("$VersionNumber"))

  val releaseNumber = LiteralMathOpSpec(symbol("$ReleaseNumber"))

  val licenseExpirationDate = LiteralMathOpSpec(symbol("$LicenseExpirationDate"))

  val check = NaryMathOpSpec(symbol("Check"))

  //</editor-fold>
}