/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Created by smitsch on 3/23/15.
 * @author Stefan Mitsch
 * @todo implement using Context._ or using FormulaAugmentor. The additional functions could stay here or move, but should have a position upgrade?
 */
@deprecated("Use FormulaAugmentor instead?")
object FormulaConverter {
  import scala.language.implicitConversions
  implicit def FormulaToFormulaConverter(f: Formula): FormulaConverter = new FormulaConverter(f)
}
@deprecated("Use FormulaAugmentor instead?")
class FormulaConverter(val fml: Formula) {

  /**
   * Indicates whether or not the expr at position pos is a formula.
   * @param pos The position in this converter's formula.
   * @return True, if the expr at pos is a formula; false otherwise.
   */
  def isFormulaAt(pos: PosInExpr): Boolean = {
    if (pos.pos.isEmpty) true
    else {
      var fAtPos: Option[Formula] = None
      ExpressionTraversal.traverse(TraverseToPosition(pos, new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          fAtPos = if (p == pos) Some(e) else None
          Left(Some(ExpressionTraversal.stop))
        }
      }), fml)
      fAtPos match {
        case Some(_) => true
        case None => false
      }
    }
  }

  /** Subexpression at indicated position */
  def apply(pos: PosInExpr): Expression = extractContext(pos)._2
  /** Subexpression at indicated position */
  def at(pos: PosInExpr): Option[Expression] =
    try {Some(extractContext(pos)._2)} catch {
      case e: NoSuchElementException   => println("ill-positioned " + pos + " in " + fml + " since " + e); None
      case e: IllegalArgumentException => println("ill-positioned " + pos + " in " + fml + " since " + e); None}
  def at(p: Position): Option[Expression] = at(p.inExpr)

  /**
   * Returns the subformula of fml at position pos.
   * @param pos The position pointing to the subformula.
   * @return The subformula.
   * @todo duplicate compared to FormulaConverter.subFormulaAt and PositionTactic.formulaAtPosition and TacticLibrary.getFormula
   */
  def subFormulaAt(pos: PosInExpr): Option[Formula] = {
    if (pos.pos.isEmpty) Some(fml)
    else {
      var fAtPos: Option[Formula] = None
      ExpressionTraversal.traverse(TraverseToPosition(pos, new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          fAtPos = if (p == pos) Some(e) else None
          Left(Some(ExpressionTraversal.stop))
        }
      }), fml)
      fAtPos
    }
  }

  /**
   * Indicates whether or not the expr at position pos is a term.
   * @param pos The position in this converter's formula.
   * @return True, if the expr at pos is a term; false otherwise.
   */
  def isTermAt(pos: PosInExpr): Boolean = {
    if (pos.pos.isEmpty) false
    else {
      var tAtPos: Option[Term] = None
      ExpressionTraversal.traverse(TraverseToPosition(pos, new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          tAtPos = if (p == pos) Some(e) else None
          Left(Some(ExpressionTraversal.stop))
        }
      }), fml)
      tAtPos match {
        case Some(_) => true
        case None => false
      }
    }
  }

  /**
   * Returns the expression at position pos in fml.
   */
  def subAt(pos: PosInExpr): Expression = if (isFormulaAt(pos)) subFormulaAt(pos).get else if (isTermAt(pos)) termAt(pos)
  else throw new IllegalArgumentException("Position " + pos + " of " + fml + " cannot be located as either a subterm or a subformula")

    /**
   * Returns the term at position pos in fml.
   * @param pos The position pointing to the term.
   * @return The term.
   */
  def termAt(pos: PosInExpr): Term = {
    if (pos.pos.isEmpty) throw new IllegalArgumentException(s"Formula $fml is not a term")
    else {
      var tAtPos: Option[Term] = None
      ExpressionTraversal.traverse(TraverseToPosition(pos, new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          tAtPos = if (p == pos) Some(e) else None
          Left(Some(ExpressionTraversal.stop))
        }
      }), fml)
      tAtPos match {
        case Some(t) => t
        case None => throw new IllegalArgumentException(s"Formula $fml at position $pos is not a term")
      }
    }
  }

  /**
   * Replaces the term at position where with the term repl.
   * @param where Where to replace.
   * @param repl The replacement.
   * @return This converter's formula with repl at position where.
   */
  @deprecated("Incorrect, use Augmentors.FormulaAugmentor.replaceAt instead")
  def replaceAt(where: PosInExpr, repl: Term): Formula = replaceAt(termAt(where), where, repl)

  /**
   * Replaces the term what at position where with the term repl. Checks that what is indeed present at position where.
   * @param what What to replace.
   * @param where Where to replace.
   * @param repl The replacement.
   * @return This converter's formula with repl at position where.
   */
  def replaceAt(what: Term, where: PosInExpr, repl: Term): Formula = {
    ExpressionTraversal.traverse(TraverseToPosition(where, new ExpressionTraversalFunction {
      override def preT(pos: PosInExpr, t: Term): Either[Option[StopTraversal], Term] =
        if (t == what) Right(repl)
        else Left(Some(ExpressionTraversal.stop))
    }), fml) match {
      case Some(f) => f
      case None => throw new IllegalArgumentException(s"Did not find $what at position $where in $fml")
    }
  }

  /**
   * Replaces the formula at position where with the formula repl.
   * @param where Where to replace.
   * @param repl The replacement.
   * @return This converter's formula with repl at position where.
   */
  @deprecated("Incorrect, use Augmentors.FormulaAugmentor.replaceAt instead")
  def replaceAt(where: PosInExpr, repl: Formula): Formula = subFormulaAt(where) match {
    case Some(f) => replaceAt(f, where, repl)
    case None => fml
  }

  /**
   * Replaces the formula what at position where with the formula repl. Checks that what is indeed present at position
   * where.
   * @param what What to replace.
   * @param where Where to replace.
   * @param repl The replacement.
   * @return This converter's formula with repl at position where.
   */
  def replaceAt(what: Formula, where: PosInExpr, repl: Formula): Formula = {
    ExpressionTraversal.traverse(TraverseToPosition(where, new ExpressionTraversalFunction {
      override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
        if (f == what) Right(repl)
        else Left(Some(ExpressionTraversal.stop))
    }), fml) match {
      case Some(f) => f
      case None => throw new IllegalArgumentException(s"Did not find $what at position $where")
    }
  }

  /**
   * Split formula at a position into sub-expression at that position and the context in which it occurs.
   * @param pos The position pointing to the expression.
   * @return A tuple (p(.), e) of context p(.) and sub-expression e, where p(e) is equivalent to fml.
   * @todo bug:
   *       Assertion failed extractContext(PosInExpr(1.1)) of (x)'=x'
led to ((x)'=x')@Equal yet eInCtx=None
   *  Assertion failed extractContext(PosInExpr(1.1)) of [{x'=5*y,y'=-5*x&true}](x*x+y*y>=8)'
led to ([{x'=5*y,y'=-5*x&true}](x*x+y*y>=8)')@Box yet eInCtx=None
   */
  def extractContext(pos: PosInExpr): (Context[Formula], Expression) = {
    var eInCtx: Option[Expression] = None
    ExpressionTraversal.traverse(TraverseToPosition(pos, new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
        if (p == pos) {
          eInCtx = Some(e)
          Right(DotFormula)
        } else {
          Left(None)
        }
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
        if (p == pos) {
          eInCtx = Some(e)
          Right(DotTerm)
        } else {
          Left(None)
        }
    }), fml) match {
      case Some(f) => (new Context(f), eInCtx.getOrElse(throw new ProverAssertionError("extractContext(" + pos +") of " + fml.prettyString + "\nled to " + f + " yet eInCtx=" + eInCtx)))
      case None => throw new IllegalArgumentException("Position not defined")
    }
  } ensuring(r => r._1(r._2) == fml, "context splitting of " + fml + " at " + pos + " is successful")

  /**
   * Transforms the formula into its structural form (all variables and functions substituted with CDot).
   * @return The dottified formula.
   */
  def dottify: Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {

    override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
//      case Forall(vars, phi) => Right(Forall(vars.map(_ => DotTerm), new FormulaConverter(phi).dottify))
//      case Exists(vars, phi) => Right(Exists(vars.map(_ => DotTerm), new FormulaConverter(phi).dottify))
      case _ => Left(None)
    }

    override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
      case _: Variable => Right(DotTerm)
      case _: FuncOf => Right(DotTerm)
      case _ => Left(None)
    }
  }, fml) match {
    case Some(dottified) => dottified
  }

  /**
   * Renames according to names.
   * @param names Maps from old names to new names.
   * @return The renamed formula
   */
  def renameAll(names: Map[NamedSymbol, NamedSymbol]): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v: Variable if names.contains(v) => names(v) match {
          case rv: Variable => Right(rv)
        }
        case _ => Left(None)
      }
    }, fml) match {
      case Some(f) => f
    }
  }

  /**
   * Renames all names according to the example.
   * @param example The example with original names.
   * @param renamedExample The examples with renamed names.
   * @return The renamed formula.
   */
  def renameAllByExample(example: Formula, renamedExample: Formula): Formula = {
    val fmlSymbols = StaticSemantics.symbols(fml)
    val renamedSymbols = StaticSemantics.symbols(example) -- StaticSemantics.symbols(renamedExample)
    val names = renamedSymbols.map(mapName(_, example, renamedExample)).toMap
    if (fmlSymbols.intersect(renamedSymbols).isEmpty) fml
    else renameAll(names)
  }

  /**
   * Returns the name mapping from fml to other.
   * @param other The other formula.
   * @return The name mapping.
   */
  def nameMapping(other: Formula): Map[NamedSymbol, NamedSymbol] = {
    val fmlSymbols = StaticSemantics.symbols(fml)
    val otherSymbols = StaticSemantics.symbols(other)
    (fmlSymbols -- otherSymbols).map(mapName(_, fml, other)).toMap
  }

  private def mapName(orig: NamedSymbol, example: Formula, renamedExample: Formula): (NamedSymbol, NamedSymbol) = {
    var renamedPos: Option[PosInExpr] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v: Variable if v == orig => renamedPos = Some(p); Left(Some(ExpressionTraversal.stop))
        case _ => Left(None)
      }
    }, example)
    renamedPos match {
      case Some(p) => (orig, new FormulaConverter(renamedExample).termAt(p) match { case n: NamedSymbol => n })
      case None => (orig, orig)
    }
  }
}