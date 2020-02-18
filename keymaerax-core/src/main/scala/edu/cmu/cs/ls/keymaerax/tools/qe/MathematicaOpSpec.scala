/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.core.{Function, NamedSymbol, Real, Tuple}

/** Mathematica operator notation. */
trait MathematicaOpSpec {
  /** The operator symbol */
  def op: Expr

  /** Indicates whether this operator can be applied to Mathematica expression `e`. */
  def applies(e: Expr): Boolean
}

/** Math literals. */
case class LiteralMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e == op
}

/** Unary Math operators. */
case class UnaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(e: Expr): Expr = new Expr(op, Array[Expr](e))
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Binary Math operators. */
case class BinaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(l: Expr, r: Expr): Expr = new Expr(op, Array[Expr](l, r))
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Nary Math operators. */
case class NaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(args: Expr*): Expr = new Expr(op, args.toArray)
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Quantifier Math operators. */
case class QuantifiedMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with quantified variables `vars` and formula `q`. */
  def apply(vars: Array[Expr], q: Expr): Expr = new Expr(op, Array[Expr](MathematicaOpSpec.list(vars:_*), q))
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** [[NamedSymbol]] operators, with `k2m` converter {{{(name, args) => Expr}}}. */
case class NameMathOpSpec(k2m: (NamedSymbol, Array[Expr]) => Expr, applies: Expr => Boolean) {
  def apply(ns: NamedSymbol, args: Array[Expr]): Expr = k2m(ns, args)
}

/** Interpreted functions. */
case class InterpretedMathOpSpec(op: Expr, fn: Function) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with head `op` and arguments `args`. */
  def apply(args: Array[Expr]): Expr = new Expr(op, args)
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Mathematica operator specifications with conversions. */
object MathematicaOpSpec {

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
  def apply(f: Expr): Seq[Expr] => Expr = (args: Seq[Expr]) => new Expr(f, args.toArray)

  //</editor-fold>

  //<editor-fold desc="Terms">

  val neg: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Minus"))

  val plus: NaryMathOpSpec = NaryMathOpSpec(symbol("Plus"))

  val minus: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Subtract"))

  val times: NaryMathOpSpec = NaryMathOpSpec(symbol("Times"))

  val divide: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Divide"))

  val rational: BinaryMathOpSpec = BinaryMathOpSpec(Expr.SYM_RATIONAL)

  val power: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Power"))

  // implicit function application name[args]
  val func: NameMathOpSpec = NameMathOpSpec(
    (name: NamedSymbol, args: Array[Expr]) => {
      require(args.length <= 2, "Functions expected to have at most 2 arguments (nothing, single argument, or converted pair)")
      new Expr(MathematicaNameConversion.toMathematica(name), args)
    },
    e => MathematicaNameConversion.isConvertibleName(e.head) && e.args().length <= 2
  )
  // explicit function application Apply[name, args]
  val mapply: NaryMathOpSpec = new NaryMathOpSpec(symbol("Apply")) {
    override def applies(e: Expr): Boolean = super.applies(e) && MathematicaNameConversion.isConvertibleName(e.args.head)
  }

  val abs: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Abs"), Function("abs", None, Real, Real, interpreted=true))

  val min: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Min"), Function("min", None, Tuple(Real, Real), Real, interpreted=true))

  val max: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Max"), Function("max", None, Tuple(Real, Real), Real, interpreted=true))

  val variable: NameMathOpSpec = NameMathOpSpec(
    (name: NamedSymbol, args: Array[Expr]) => {
      require(args.isEmpty, "Unexpected arguments")
      MathematicaNameConversion.toMathematica(name)
    },
    MathematicaNameConversion.isConvertibleName
  )

  val pair: BinaryMathOpSpec = new BinaryMathOpSpec(Expr.SYM_LIST) {
    //@note inherited apply gets pairs as lists of length 2 each
    override def applies(e: Expr): Boolean = e.listQ && e.args().length == 2
  }

  //</editor-fold>

  //<editor-fold desc="Comparison formulas">

  val equal: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Equal"))

  // x!=y
  val unequal: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Unequal"))

  // x<y<=z
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

  val timeConstrained = BinaryMathOpSpec(symbol("TimeConstrained"))

  val memoryConstrained = BinaryMathOpSpec(symbol("MemoryConstrained"))

  //</editor-fold>
}
