/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._
import scala.math.BigDecimal

/**
 * Converts KeYmaeara X [[edu.cmu.cs.ls.keymaerax.core.Expression expression data structures]]
 * to Mathematica Expr objects.
 * @author Nathan Fulton
 */
object KeYmaeraToMathematica {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  //@todo contract: convert back is identity
  def fromKeYmaera(e : KExpr): MExpr = e match {
    case t : Term => require(disjointNames(StaticSemantics.symbols(t)), "Disjoint names required for Mathematica conversion");
      convertTerm(t)
    case t : Formula => require(disjointNames(StaticSemantics.symbols(t)), "Disjoint names required for Mathematica conversion");
      convertFormula(t)
  }

  private def disjointNames(symbols: Set[NamedSymbol]): Boolean = {
    val names = symbols.map(x=>(x.name,x.index)).toList
    names.distinct.length == names.length
  }

  /**
   * Converts a KeYmaera terms to a Mathematica expression.
   */
  private def convertTerm(t : Term) : MExpr = {
    /** Convert tuples to list of sorts */
    def flattenSort(s: Sort): List[Sort] = s match {
      case Tuple(ls, rs) => ls :: rs :: Nil
      case _ => s :: Nil
    }

    require(t.sort == Real || t.sort == Unit || flattenSort(t.sort).forall(_ == Real), "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      case FuncOf(fn, child) => convertFnApply(fn, child)
      case Neg(c) => new MExpr(MathematicaSymbols.MINUSSIGN, Array[MExpr](convertTerm(c)))
      case Plus(l, r) =>
        new MExpr(MathematicaSymbols.PLUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Minus(l, r) =>
        new MExpr(MathematicaSymbols.MINUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Times(l, r) =>
        new MExpr(MathematicaSymbols.MULT, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Divide(l, r) =>
        new MExpr(MathematicaSymbols.DIV, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Power(l, r) =>
        new MExpr(MathematicaSymbols.EXP, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Differential(c) =>
        new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convertTerm(c)))
      case DifferentialSymbol(c) =>
        new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convertTerm(c)))
      case Number(n) => new MExpr(n.underlying())
      case Pair(l, r) =>     //@todo handle nested pairs (flatten to a list?)
        new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(l), convertTerm(r)))

      case t: Variable => MathematicaNameConversion.toMathematica(t)
    }
  }

  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  private def convertFormula(f : Formula) : MExpr = f match {
    case And(l,r)   => new MExpr(MathematicaSymbols.AND, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equiv(l,r) => new MExpr(MathematicaSymbols.BIIMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Imply(l,r) => new MExpr(MathematicaSymbols.IMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Or(l,r)    => new MExpr(MathematicaSymbols.OR, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equal(l,r) => new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case NotEqual(l,r) => new MExpr(MathematicaSymbols.UNEQUAL, Array[MExpr](convertTerm(l), convertTerm(r)))
    case LessEqual(l,r) => new MExpr(MathematicaSymbols.LESS_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Less(l,r)   => new MExpr(MathematicaSymbols.LESS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case GreaterEqual(l,r) => new MExpr(MathematicaSymbols.GREATER_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Greater(l,r) => new MExpr(MathematicaSymbols.GREATER, Array[MExpr](convertTerm(l), convertTerm(r)))
    case False => MathematicaSymbols.FALSE
    case True => MathematicaSymbols.TRUE
    case Not(phi) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertFormula(phi)))
    case Exists(vs, phi) => convertExists(vs,phi)
    case Forall(vs, phi) => convertForall(vs,phi)
  }

  private def convertFnApply(fn: Function, child: Term): MExpr = child match {
    case Nothing => MathematicaNameConversion.toMathematica(new Function(MathematicaNameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
    case _ =>
      //@todo Code Review: figure out how nested lists affect binary functions
      val args = Array[MExpr](MathematicaNameConversion.toMathematica(fn), new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(child))))
      new MExpr(MathematicaSymbols.APPLY, args)
  }

  /** Convert block of exists quantifiers into a single exists quantifier block */
  private def convertExists(vs:Seq[NamedSymbol],f:Formula) = {
    val (vars, formula) = collectVarsExists(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(MathematicaNameConversion.toMathematica).toArray)
    new MExpr(MathematicaSymbols.EXISTS, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsExists(vsSoFar:Seq[NamedSymbol],candidate:Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextf) =>  collectVarsExists(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }

  /** Convert block of forall quantifiers into a single forall quantifier block */
  private def convertForall(vs:Seq[NamedSymbol],f:Formula) = {
    val (vars, formula) = collectVarsForall(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(MathematicaNameConversion.toMathematica).toArray)
    new MExpr(MathematicaSymbols.FORALL, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsForall(vsSoFar:Seq[NamedSymbol],candidate:Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextf) =>  collectVarsForall(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }

  private def keyExn(e: KExpr) : Exception =
    new ConversionException("conversion not defined for KeYmaera expr: " + PrettyPrinter.printer(e))
}

