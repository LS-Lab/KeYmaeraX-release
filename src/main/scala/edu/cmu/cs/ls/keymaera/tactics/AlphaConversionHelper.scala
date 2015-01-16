package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import Substitution.freeVariables

/**
 * Performs alpha conversion on formulas and terms. Used in tactics to setup axiom instances and substitution
 * definitions for uniform substitution.
 *
 * Created by smitsch on 1/15/15.
 * @author Stefan Mitsch
 */
object AlphaConversionHelper {
  /**
   * Replace the old term (usually a variable) o by a new named term (variable or CDot) n in formula f, but only if the
   * old term is contained in the set of free names.
   * @param f The formula.
   * @param o The old term.
   * @param n The new named term (i.e., a variable or CDot).
   * @param free The optional set of free names. If None, all names are considered free. Defaults to the free names
   *             in f.
   */
  def replace(f: Formula)(o: Term, n: NamedSymbol with Term, free: Option[Set[NamedSymbol]] = Some(freeVariables(f))): Formula = {
    import Substitution.freeVariables
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Forall(v, fo) => Right(Forall(v.map((name: NamedSymbol) => if (name == o) n else name),
            replace(fo)(o, n, Some(freeVariables(fo)))))
          case Exists(v, fo) => Right(Exists(v.map((name: NamedSymbol) => if (name == o) n else name),
            replace(fo)(o, n, Some(freeVariables(fo)))))
          case BoxModality(Assign(x: Variable, t), pred) => free match {
            case Some(freeVars) => Right(BoxModality(Assign(x, replace(t)(o, n, free)),
              replace(pred)(o, n, Some(freeVars - x))))
            case None => Right(BoxModality(Assign(n, t), replace(pred)(o, n, None)))
          }
          case BoxModality(NFContEvolve(v, xprime@Derivative(d, x: Variable), t, h), pred) => free match {
            case Some(freeVars) => Right(BoxModality(NFContEvolve(v, xprime, replace(t)(o, n, Some(freeVars - x)),
              replace(h)(o, n, Some(freeVars - x))), replace(pred)(o, n, Some(freeVars - x))))
            case None => Right(BoxModality(NFContEvolve(v, Derivative(d, n), replace(t)(o, n, None),
              replace(h)(o, n, None)), replace(pred)(o, n, None)))
          }
          // TODO systems of ODEs
          case DiamondModality(Assign(x: Variable, t), pred) => free match {
            case Some(freeVars) => Right(DiamondModality(Assign(x, replace(t)(o, n, Some(freeVars - x))),
              replace(pred)(o, n, Some(freeVars - x))))
            case None => Right(DiamondModality(Assign(n, t), replace(pred)(o, n, None)))
          }
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case v: Variable if v == o => free match {
            case Some(freeVars) => if (freeVars.contains(v)) Right(n) else Left(None)
            case None => Right(n)
          }
          case _ => Left(None)
        }

      }, f) match {
      case Some(g) => g
      case None => throw new IllegalStateException("Replacing one variable by another should not fail")
    }
  }

  /**
   * Replace the old term o (usually a variable) by a new named term (variable or CDot) n in term t, but only if the
   * old term is contained in the set of free names.
   * @param t The term.
   * @param o The old term.
   * @param n The new named term (i.e., a variable or CDot).
   * @param free The optional set of free names. If None, all names are considered free.
   */
  def replace(t: Term)(o: Term, n: Term, free: Option[Set[NamedSymbol]]): Term =
      ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v: Variable if v == o => free match {
          case Some(freeVars) => if (freeVars.contains(v)) Right(n) else Left(None)
          case _ => Right(n)
        }
        case _ => Left(None)
      }
    }, t) match {
    case Some(g) => g
    case None => throw new IllegalStateException("Replacing one variable by another should not fail")
  }
}
