/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.core.{Function, NamedSymbol}
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.tools.qe.ExprFactory.makeExpr

/** Mathematica operator notation. */
trait MathematicaOpSpec {
  /** The operator symbol */
  def op: Expr

  /** Indicates whether this operator can be applied to Mathematica expression `e`. */
  def applies(e: Expr): Boolean
}

/** Creates [[Expr]] objects. */
object ExprFactory {
  def makeExpr(head: Expr, args: Array[Expr]): Expr = new Expr(head, args)
}

/** Math literals. */
case class LiteralMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e == op
}

/** Unary Math operators. */
case class UnaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(e: Expr): Expr = makeExpr(op, Array[Expr](e))
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Binary Math operators. */
case class BinaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(l: Expr, r: Expr): Expr = makeExpr(op, Array[Expr](l, r))
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Nary Math operators. */
case class NaryMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with argument `e`. */
  def apply(args: Expr*): Expr = makeExpr(op, args.toArray)
  /** @inheritdoc */
  override def applies(e: Expr): Boolean = e.head == op
}

/** Quantifier Math operators. */
case class QuantifiedMathOpSpec(op: Expr) extends MathematicaOpSpec {
  /** Creates a Mathematica expression with quantified variables `vars` and formula `q`. */
  def apply(vars: Array[Expr], q: Expr): Expr = makeExpr(op, Array[Expr](MathematicaOpSpec.list(vars:_*), q))
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
  def apply(args: Array[Expr]): Expr = makeExpr(op, args)
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

  /** Creates a Mathematica Boolean. */
  def bool(b: Boolean): Expr = if (b) Expr.SYM_TRUE else Expr.SYM_FALSE

  def list: NaryMathOpSpec = NaryMathOpSpec(Expr.SYM_LIST)

  /** Mathematica function application f(args). */
  def apply(f: Expr): Seq[Expr] => Expr = (args: Seq[Expr]) => makeExpr(f, args.toArray)

  /** Mathematica compound expression `;`. */
  def compoundExpr(f: Expr*): Expr = MathematicaOpSpec(symbol("CompoundExpression"))(f)

  //</editor-fold>

  //<editor-fold desc="Terms">

  def neg: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Minus"))

  def plus: NaryMathOpSpec = NaryMathOpSpec(symbol("Plus"))

  def minus: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Subtract"))

  def times: NaryMathOpSpec = NaryMathOpSpec(symbol("Times"))

  def divide: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Divide"))

  def rational: BinaryMathOpSpec = BinaryMathOpSpec(Expr.SYM_RATIONAL)

  def power: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Power"))

  // implicit function application name[args]
  def func: NameMathOpSpec = NameMathOpSpec(
    (name: NamedSymbol, args: Array[Expr]) => {
      require(args.length <= 2, "Functions expected to have at most 2 arguments (nothing, single argument, or converted pair)")
      makeExpr(MathematicaNameConversion.toMathematica(name), args)
    },
    e => MathematicaNameConversion.isConvertibleName(e.head) && e.args().length <= 2
  )
  // explicit function application Apply[name, args]
  def mapply: NaryMathOpSpec = new NaryMathOpSpec(symbol("Apply")) {
    override def applies(e: Expr): Boolean = super.applies(e) && MathematicaNameConversion.isConvertibleName(e.args.head)
  }

  def abs: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Abs"), InterpretedSymbols.absF)

  def min: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Min"), InterpretedSymbols.minF)

  def max: InterpretedMathOpSpec = InterpretedMathOpSpec(symbol("Max"), InterpretedSymbols.maxF)

  def variable: NameMathOpSpec = NameMathOpSpec(
    (name: NamedSymbol, args: Array[Expr]) => {
      require(args.isEmpty, "Unexpected arguments")
      MathematicaNameConversion.toMathematica(name)
    },
    MathematicaNameConversion.isConvertibleName
  )

  def pair: BinaryMathOpSpec = new BinaryMathOpSpec(Expr.SYM_LIST) {
    //@note inherited apply gets pairs as lists of length 2 each
    override def applies(e: Expr): Boolean = e.listQ && e.args().length == 2
  }

  //</editor-fold>

  //<editor-fold desc="Comparison formulas">

  def equal: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Equal"))

  // x!=y
  def unequal: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Unequal"))

  // x<y<=z
  def inequality: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Inequality"))

  def greater: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Greater"))

  def greaterEqual: BinaryMathOpSpec = BinaryMathOpSpec(symbol("GreaterEqual"))

  def less: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Less"))

  def lessEqual: BinaryMathOpSpec = BinaryMathOpSpec(symbol("LessEqual"))

  //</editor-fold>

  //<editor-fold desc="Formulas">

  def ltrue: LiteralMathOpSpec = LiteralMathOpSpec(Expr.SYM_TRUE)

  def lfalse: LiteralMathOpSpec = LiteralMathOpSpec(Expr.SYM_FALSE)

  def not: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Not"))

  def and: NaryMathOpSpec = NaryMathOpSpec(symbol("And"))

  def or: NaryMathOpSpec = NaryMathOpSpec(symbol("Or"))

  def implies: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Implies"))

  def equivalent: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Equivalent"))

  def forall: QuantifiedMathOpSpec = QuantifiedMathOpSpec(symbol("ForAll"))

  def exists: QuantifiedMathOpSpec = QuantifiedMathOpSpec(symbol("Exists"))

  //</editor-fold>

  //<editor-fold desc="Arithmetic">

  def rule: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Rule"))

  def reduce: NaryMathOpSpec = NaryMathOpSpec(symbol("Reduce"))

  def resolve: NaryMathOpSpec = NaryMathOpSpec(symbol("Resolve"))

  def reals: LiteralMathOpSpec = LiteralMathOpSpec(symbol("Reals"))

  //</editor-fold>

  //<editor-fold desc="Diagnostics">

  def aborted: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$Aborted"))

  def abort: LiteralMathOpSpec = LiteralMathOpSpec(makeExpr(symbol("Abort"), Array.empty[Expr]))

  def failed: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$Failed"))

  def exception: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$Exception"))

  def versionNumber: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$VersionNumber"))

  def releaseNumber: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$ReleaseNumber"))

  def licenseExpirationDate: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$LicenseExpirationDate"))

  def check: NaryMathOpSpec = NaryMathOpSpec(symbol("Check"))

  def timeConstrained: BinaryMathOpSpec = BinaryMathOpSpec(symbol("TimeConstrained"))

  def memoryConstrained: BinaryMathOpSpec = BinaryMathOpSpec(symbol("MemoryConstrained"))

  //</editor-fold>
}
