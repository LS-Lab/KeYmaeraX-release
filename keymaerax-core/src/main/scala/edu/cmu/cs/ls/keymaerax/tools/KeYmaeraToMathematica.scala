/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable._
import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

import scala.reflect.ClassTag

/**
 * Converts KeYmaeara X [[edu.cmu.cs.ls.keymaerax.core.Expression expression data structures]]
 * to Mathematica Expr objects.
 * @author Nathan Fulton
 */
object KeYmaeraToMathematica extends BaseK2MConverter[KExpr] {

  def m2k: M2KConverter[KExpr] = MathematicaToKeYmaera

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  //@todo Code Review contract: convert back is identity, ask converse converter
  //@solution: introduced traits/base traits that implement contract checking. here: convert without contract checking
  def convert(e: KExpr): MExpr = e match {
    case t: Term =>
      require(disjointNames(StaticSemantics.symbols(t)), "Disjoint names required for Mathematica conversion")
      convertTerm(t)
    case f: Formula =>
      require(disjointNames(StaticSemantics.symbols(f)), "Disjoint names required for Mathematica conversion")
      convertFormula(f)
    case fn: Function =>
      //@todo Code Review: prefixed name must be disjoint from other names in the containing term/formula -> Mathematica namespace `constFn`
      MathematicaNameConversion.toMathematica(
        new Function(MathematicaNameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
  }

  private def disjointNames(symbols: Set[NamedSymbol]): Boolean = {
    val names = symbols.map(x=>(x.name,x.index)).toList
    names.distinct.length == names.length
  }

  /**
   * Converts a KeYmaera terms to a Mathematica expression.
   */
  protected def convertTerm(t : Term): MExpr = {
    /** Convert tuples to list of sorts */
    def flattenSort(s: Sort): List[Sort] = s match {
      case Tuple(ls, rs) => flattenSort(ls) ++ flattenSort(rs)
      case _ => s :: Nil
    }

    require(t.sort == Real || t.sort == Unit || flattenSort(t.sort).forall(_ == Real), "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      //@todo Code Review: clean up FuncOf conversion into two cases here
      case FuncOf(fn, child) => convertFnApply(fn, child)
      case Neg(c) => new MExpr(MathematicaSymbols.MINUSSIGN, Array[MExpr](convertTerm(c)))
      case plus: Plus =>
        new MExpr(MathematicaSymbols.PLUS, flattenLeftBinary(plus, Plus.unapply).map(convertTerm).toArray)
      case Minus(l, r) =>
        new MExpr(MathematicaSymbols.MINUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case times: Times =>
        new MExpr(MathematicaSymbols.MULT, flattenLeftBinary(times, Times.unapply).map(convertTerm).toArray)
      case Divide(l: Number, r: Number) =>
        //@note for sake of roundtrip identity: set correct Rational type ID by reflection (no public JLink constructor!)
        val rational = new MExpr(MathematicaSymbols.RATIONAL, Array[MExpr](convertTerm(l), convertTerm(r)))
        val tf = rational.getClass.getDeclaredField("type")
        tf.setAccessible(true)
        tf.set(rational, com.wolfram.jlink.Expr.RATIONAL)
        rational
      case Divide(l, r) =>
        new MExpr(MathematicaSymbols.DIV, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Power(l, r) =>
        new MExpr(MathematicaSymbols.EXP, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Number(n) if n.isValidInt || n.isValidLong => new MExpr(n.longValue())
      case Number(n) => new MExpr(n.underlying())
      case Pair(l, r) =>
        //@note converts nested pairs into nested lists
        new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(l), convertTerm(r)))

      case t: Variable => MathematicaNameConversion.toMathematica(t)
    }
  }

  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  protected def convertFormula(f : Formula): MExpr = f match {
    case and: And   => new MExpr(MathematicaSymbols.AND, flattenLeftBinary(and, And.unapply).map(convertFormula).toArray)
    case Equiv(l,r) => new MExpr(MathematicaSymbols.BIIMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Imply(l,r) => new MExpr(MathematicaSymbols.IMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case or: Or    => new MExpr(MathematicaSymbols.OR, flattenLeftBinary(or, Or.unapply).map(convertFormula).toArray)
    case Equal(l,r) => new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case NotEqual(l,r) => new MExpr(MathematicaSymbols.UNEQUAL, Array[MExpr](convertTerm(l), convertTerm(r)))
    case LessEqual(l,r) => new MExpr(MathematicaSymbols.LESS_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Less(l,r)   => new MExpr(MathematicaSymbols.LESS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case GreaterEqual(l,r) => new MExpr(MathematicaSymbols.GREATER_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Greater(l,r) => new MExpr(MathematicaSymbols.GREATER, Array[MExpr](convertTerm(l), convertTerm(r)))
    case False => MathematicaSymbols.FALSE
    case True => MathematicaSymbols.TRUE
    case Not(phi) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertFormula(phi)))
    case Exists(vs, phi) => convertQuantified(vs, phi, Exists.unapply, MathematicaSymbols.EXISTS)
    case Forall(vs, phi) => convertQuantified(vs, phi, Forall.unapply, MathematicaSymbols.FORALL)
    case _ => throw new ProverException("Don't know how to convert " + f + " of class " + f.getClass)
  }

  protected def convertFnApply(fn: Function, child: Term): MExpr = child match {
    //@todo Code Review: avoid duplicate code, see fromKeYmaera
    case Nothing => MathematicaNameConversion.toMathematica(new Function(MathematicaNameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
    case p: Pair =>
      //@note Pair arguments turn into list arguments Apply[f, {{x,y}}] == f[{x,y}]
      //@note Pairs will be transformed into nested lists, which makes f[{x, {y,z}] different from f[{{x,y},z}] and would require list arguments (instead of argument lists) when using the functions in Mathematica. Unproblematic for QE, since converted in the same fashion every time
      val args = Array[MExpr](MathematicaNameConversion.toMathematica(fn), convertTerm(child))
      new MExpr(MathematicaSymbols.APPLY, args)
    case _ =>
      //@note single-argument f[x]
      new MExpr(MathematicaNameConversion.toMathematica(fn), Array[MExpr](convertTerm(child)))
  }

  //@todo Code Review: Forall+Exists could be 1 conversion
  //@solution: added parameters for unapplier (ua) and head symbol
  /** Convert block of quantifiers into a single quantifier block, using unapply (ua) and matching head (FORALL/EXISTS) */
  protected def convertQuantified[T <: Quantified](vs: Seq[NamedSymbol], f: Formula,
                                                   ua: T => Option[(Seq[Variable], Formula)], head: MExpr): MExpr = {
    require(head == MathematicaSymbols.EXISTS || head == MathematicaSymbols.FORALL,
      "Expected either existential or universal quantifier as MExpr head")

    /** Recursively collect quantified variables, return variables+quantified formula */
    def collectVars(vsSoFar: Seq[NamedSymbol], candidate: T): (Seq[NamedSymbol], Formula) = {
      ua(candidate) match {
        case Some((nextVs, nextf: T)) => collectVars(vsSoFar ++ nextVs, nextf)
        case Some((nextVs, nextf)) => (vsSoFar ++ nextVs, nextf)
        case _ => (vsSoFar, candidate)
      }
    }

    val (vars, formula) = f match {
      case q: T => collectVars(vs, q)
      case _ => (vs, f)
    }
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(MathematicaNameConversion.toMathematica).toArray)
    new MExpr(head, Array[MExpr](variables, convertFormula(formula)))
  }

  /** Flattens left-associative binary term operators (keeps explicit right-associativity) */
  private def flattenLeftBinary[T <: Expression, U <: T](t: U, ua: U => Option[(T, T)])(implicit mf: ClassTag[U]): Seq[T] = ua(t) match {
    //@note Some((l: T, r)) does not match correctly
    case Some((l, r)) if mf.runtimeClass.isAssignableFrom(l.getClass) => flattenLeftBinary(l.asInstanceOf[U], ua) :+ r
    case Some((l, r)) => l :: r :: Nil
    case None => t :: Nil
  }

  protected def keyExn(e: KExpr): Exception =
    new ConversionException("conversion not defined for KeYmaera expr: " + PrettyPrinter.printer(e))
}

