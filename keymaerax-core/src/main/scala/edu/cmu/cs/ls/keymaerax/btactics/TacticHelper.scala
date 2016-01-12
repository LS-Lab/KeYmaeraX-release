/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr

object TacticHelper {

  def freshIndexInFormula(name: String, f: Formula) =
    if (symbols(f).exists(_.name == name)) {
      val vars = symbols(f).map(n => (n.name, n.index)).filter(_._1 == name)
      require(vars.nonEmpty)
      val maxIdx: Option[Int] = vars.map(_._2).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) =>
        acc match {
          case Some(a) => i match {
            case Some(b) => if (a < b) Some(b) else Some(a)
            case None => Some(a)
          }
          case None => i
        })
      maxIdx match {
        case None => Some(0)
        case Some(a) => Some(a + 1)
      }
    } else None

  def symbols(f: Formula): Set[NamedSymbol] = {
    var symbols = Set[NamedSymbol]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case v: Variable => symbols += v; Left(None)
        case FuncOf(fn: Function, _) => symbols += fn; Left(None)
        case _ => Left(None)
      }
    }, f)
    symbols
  }

  def names(s: Sequent) = s.ante.flatMap(symbols) ++ s.succ.flatMap(symbols)

  def freshIndexInSequent(name: String, s: Sequent) =
    if (names(s).exists(_.name == name))
      (s.ante.map(freshIndexInFormula(name, _)) ++ s.succ.map(freshIndexInFormula(name, _))).max
    else None

  def freshNamedSymbol[T <: NamedSymbol](t: T, f: Formula): T =
    if (symbols(f).exists(_.name == t.name)) t match {
      case Variable(vName, _, vSort) => Variable(vName, freshIndexInFormula(vName, f), vSort).asInstanceOf[T]
      case Function(fName, _, fDomain, fSort) => Function(fName, freshIndexInFormula(fName, f), fDomain, fSort).asInstanceOf[T]
    } else t

  def freshNamedSymbol[T <: NamedSymbol](t: T, s: Sequent): T =
    if (names(s).exists(_.name == t.name)) t match {
      case Variable(vName, _, vSort) => Variable(vName, freshIndexInSequent(vName, s), vSort).asInstanceOf[T]
      case Function(fName, _, fDomain, fSort) => Function(fName, freshIndexInSequent(fName, s), fDomain, fSort).asInstanceOf[T]
    } else t

}