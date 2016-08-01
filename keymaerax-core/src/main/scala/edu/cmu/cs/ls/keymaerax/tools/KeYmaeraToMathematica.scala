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
import edu.cmu.cs.ls.keymaerax.tools.MathematicaNameConversion._

/**
  * Converts KeYmaeara X [[edu.cmu.cs.ls.keymaerax.core.Expression expression data structures]]
  * to Mathematica Expr objects.
  * @author Stefan Mitsch
  * @author Nathan Fulton
 */
object KeYmaeraToMathematica extends KeYmaeraToMathematica
class KeYmaeraToMathematica extends BaseK2MConverter[KExpr] {

  def m2k: M2KConverter[KExpr] = MathematicaToKeYmaera

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  //@todo Code Review contract: convert back is identity, ask converse converter
  //@solution: introduced traits/base traits that implement contract checking. here: convert without contract checking
  def convert(e: KExpr): MExpr = {
    insist(StaticSemantics.symbols(e).forall({case fn@Function(_, _, _, _, true) => interpretedSymbols.contains(fn) case _ => true}),
      "Interpreted functions must have expected domain and sort")
    insist(disjointNames(StaticSemantics.symbols(e)), "Disjoint names required for Mathematica conversion")

    e match {
      case t: Term => convertTerm(t)
      case f: Formula => convertFormula(f)
      case fn: Function =>
        //@todo Code Review: prefixed name must be disjoint from other names in the containing term/formula -> Mathematica namespace `constFn`
        //@solution uninterpreted function symbols are removed with tactics -> we disallow them here, constFn removed entirely.
        // can remove this case during next code review (if we remove: can also remove overridden CEXK2MConverter.convert). Non-soundness critical CEX and Simulation tools can override
        throw new ConversionException("Uninterpreted function symbols are disallowed")
    }
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
      //@solution: inlined and simplified the FuncOf cases, moved uniform name conversion into MathematicaNameConversion
      //@solution: distinguish between interpreted and uninterpreted function symbols
      case FuncOf(fn@Function(_, _, _, _, true), child) => convertFunction(interpretedSymbols(fn), child)
      //@note Uninterpreted functions are mapped to namespace kyx` to avoid clashes with any interpreted names
      case FuncOf(fn@Function(_, _, _, _, false), child) => convertFunction(toMathematica(fn), child)
      case Neg(c) => new MExpr(MathematicaSymbols.MINUSSIGN, Array[MExpr](convertTerm(c)))
      case Plus(l, r) => new MExpr(MathematicaSymbols.PLUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Minus(l, r) => new MExpr(MathematicaSymbols.MINUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Times(l, r) => new MExpr(MathematicaSymbols.MULT, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Divide(l, r) => new MExpr(MathematicaSymbols.DIV, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Power(l, r) => new MExpr(MathematicaSymbols.EXP, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Number(n) if n.isValidInt || n.isValidLong => new MExpr(n.longValue())
      case Number(n) => new MExpr(n.underlying())
      case Pair(l, r) =>
        //@note converts nested pairs into nested lists
        new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(l), convertTerm(r)))

      case t: Variable => toMathematica(t)
    }
  }

  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  protected def convertFormula(f : Formula): MExpr = f match {
    case And(l, r)  => new MExpr(MathematicaSymbols.AND, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equiv(l,r) => new MExpr(MathematicaSymbols.BIIMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Imply(l,r) => new MExpr(MathematicaSymbols.IMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Or(l, r)   => new MExpr(MathematicaSymbols.OR, Array[MExpr](convertFormula(l), convertFormula(r)))
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
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(toMathematica).toArray)
    new MExpr(head, Array[MExpr](variables, convertFormula(formula)))
  }

  /** Convert a function. */
  private def convertFunction(head: MExpr, child: Term): MExpr = child match {
    case _: Pair =>
      assert(convertTerm(child).listQ(), "Converted pair expected to be a list, but was " + convertTerm(child))
      new MExpr(head, convertTerm(child).args())
    case _ => new MExpr(head, Array[MExpr](convertTerm(child)))
  }
}
