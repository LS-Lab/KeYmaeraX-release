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
      case BaseVariable(vName, _, vSort) => Variable(vName, freshIndexInFormula(vName, f), vSort).asInstanceOf[T]
      case Function(fName, _, fDomain, fSort, false) => Function(fName, freshIndexInFormula(fName, f), fDomain, fSort).asInstanceOf[T]
    } else t

  def freshNamedSymbol[T <: NamedSymbol](t: T, s: Sequent): T =
    if (names(s).exists(_.name == t.name)) t match {
      case BaseVariable(vName, _, vSort) => Variable(vName, freshIndexInSequent(vName, s), vSort).asInstanceOf[T]
      case Function(fName, _, fDomain, fSort, false) => Function(fName, freshIndexInSequent(fName, s), fDomain, fSort).asInstanceOf[T]
    } else t

  /** Returns a list of formulas that invariants should treat as invariants. */
  def propertiesOfConstants(s: Sequent, pos: SeqPos) : List[Formula] = {
    val constants : Set[Variable] = invariantSymbols(s, pos)
    s.ante.filter(f => (StaticSemantics.freeVars(f) -- constants).isEmpty).toList
  } //@todo tests and then use this function to determine which formulas should be added to a loop invariant.

  /** Returns the set of variables we should consider as constant in invariant proofs for the modality located at pos. */
  private def invariantSymbols(s: Sequent, pos: SeqPos) : Set[Variable] = {
    val (program: Program, formula: Formula) = s(pos) match {
      case Box(p,f) => (p,f)
      case Diamond(p,f) => (p,f)
      case _ => assert(false, "s(pos) should hve form [a]p or <a>p.")
    }

    val freeInGamma = s.ante.map(StaticSemantics.freeVars).reduce(_ ++ _)
    val freeInModality = StaticSemantics.freeVars(s(pos))
    val boundInProgram = StaticSemantics.boundVars(program)

    //@todo not sure about that last term.
    freeInModality.intersect(freeInGamma).intersect(SetLattice.topVarsDiffVars -- boundInProgram).symbols
  }
}