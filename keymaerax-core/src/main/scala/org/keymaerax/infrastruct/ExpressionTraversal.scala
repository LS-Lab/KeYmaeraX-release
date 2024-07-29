/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.infrastruct

import org.keymaerax.core._
import org.keymaerax.infrastruct.PosInExpr.HereP

import scala.annotation.nowarn

/**
 * Generic traversal functionality for expressions for pre/post/infix traversal.
 * @author
 *   Nathan Fulton
 * @author
 *   Ran Ji
 * @author
 *   Stefan Mitsch
 * @author
 *   Jan-David Quesel
 */
object ExpressionTraversal {
  def fail(x: Expression) = throw UnknownOperatorException("Unimplemented case in Expr traversal", x)

  trait StopTraversal
  val stop = new StopTraversal {}

  /**
   * TODO: Maybe we need to relax this interface to just the cases: Formula -> Formula, Term -> Term, Program ->
   * Program, ModalOp -> ModalOp in order to make it implementable
   */
  trait ExpressionTraversalFunction {
    def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = Left(None)
    def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = Left(None)
    def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = Left(None)
    def inF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = Left(None)
    def inP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = Left(None)
    def inT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = Left(None)
    def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = Left(None)
    def postP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = Left(None)
    def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = Left(None)
  }

  /** blacklist is a set of symbols that most not be bound */
  object TraverseToPosition {
    def apply(t: PosInExpr, cont: ExpressionTraversalFunction): ExpressionTraversalFunction =
      new TraverseToPosition(t, cont, Set.empty)
    def apply(t: PosInExpr, cont: ExpressionTraversalFunction, blacklist: Set[Variable]): ExpressionTraversalFunction =
      new TraverseToPosition(t, cont, blacklist)
  }

  class TraverseToPosition(t: PosInExpr, cont: ExpressionTraversalFunction, blacklist: Set[Variable])
      extends ExpressionTraversalFunction {
    override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
      if (p == t) traverse(p, cont, e) match {
        case Some(x: Formula) => Right(x)
        case _ => Left(Some(stop))
      }
      else e match {
        case Forall(v, _) if blacklist.map(v.contains).foldLeft(false)(_ || _) => Left(Some(stop))
        case Exists(v, _) if blacklist.map(v.contains).foldLeft(false)(_ || _) => Left(Some(stop))
        case Box(a, _) if blacklist.map(StaticSemantics(a).bv.contains).foldLeft(false)(_ || _) => Left(Some(stop))
        case Diamond(a, _) if blacklist.map(StaticSemantics(a).bv.contains).foldLeft(false)(_ || _) => Left(Some(stop))
        case _ =>
          if (p.isPrefixOf(t))
            // proceed
            Left(None)
          else
            // return id to ignore this branch
            Right(e)
      }
    override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] =
      if (p == t) traverse(p, cont, e) match {
        case Some(x: Program) => Right(x)
        case _ => Left(Some(stop))
      }
      else if (p.isPrefixOf(t))
        // proceed
        Left(None)
      else
        // return id to ignore this branch
        Right(e)
    override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
      if (p == t) traverse(p, cont, e) match {
        case Some(x: Term) => Right(x)
        case _ => Left(Some(stop))
      }
      else if (p.isPrefixOf(t))
        // proceed
        Left(None)
      else
        // return id to ignore this branch
        Right(e)
  }

  @nowarn("msg=match may not be exhaustive")
  final def pre[A <: Expression](f: ExpressionTraversalFunction, p: PosInExpr, e: A): Either[Option[StopTraversal], A] =
    e match {
      case x: Formula => f.preF(p, x) match {
          case Left(Some(_)) => Left(Some(stop))
          case Left(None) => Left(None)
          case Right(a) => Right(a.asInstanceOf[A])
        }
      case x: Program => f.preP(p, x) match {
          case Left(Some(_)) => Left(Some(stop))
          case Left(None) => Left(None)
          case Right(a) => Right(a.asInstanceOf[A])
        }
      case x: Term => f.preT(p, x) match {
          case Left(Some(_)) => Left(Some(stop))
          case Left(None) => Left(None)
          case Right(a) => Right(a.asInstanceOf[A])
        }
    }

  @nowarn("msg=match may not be exhaustive")
  final def in[A <: Expression](f: ExpressionTraversalFunction, p: PosInExpr, e: A): Either[Option[StopTraversal], A] =
    e match {
      case x: Formula => f.inF(p, x) match {
          case Left(Some(_)) => Left(Some(stop))
          case Left(None) => Left(None)
          case Right(a) => Right(a.asInstanceOf[A])
        }
      case x: Program => f.inP(p, x) match {
          case Left(Some(_)) => Left(Some(stop))
          case Left(None) => Left(None)
          case Right(a) => Right(a.asInstanceOf[A])
        }
      case x: Term => f.inT(p, x) match {
          case Left(Some(_)) => Left(Some(stop))
          case Left(None) => Left(None)
          case Right(a) => Right(a.asInstanceOf[A])
        }
    }

  @nowarn("msg=match may not be exhaustive")
  final def post[A <: Expression](
      f: ExpressionTraversalFunction,
      p: PosInExpr,
      e: A,
  ): Either[Option[StopTraversal], A] = e match {
    case x: Formula => f.postF(p, x) match {
        case Left(Some(_)) => Left(Some(stop))
        case Left(None) => Left(None)
        case Right(a) => Right(a.asInstanceOf[A])
      }
    case x: Program => f.postP(p, x) match {
        case Left(Some(_)) => Left(Some(stop))
        case Left(None) => Left(None)
        case Right(a) => Right(a.asInstanceOf[A])
      }
    case x: Term => f.postT(p, x) match {
        case Left(Some(_)) => Left(Some(stop))
        case Left(None) => Left(None)
        case Right(a) => Right(a.asInstanceOf[A])
      }
  }

  def matchZero[A <: Expression](p: PosInExpr, f: ExpressionTraversalFunction, a: A): Option[A] = post(f, p, a) match {
    case Left(Some(_)) => None
    case Left(None) => Some(a)
    case Right(x) => Some(x)
  }

  def matchOne[A <: Expression, B <: Expression](
      p: PosInExpr,
      c: A => B,
      f: ExpressionTraversalFunction,
      a: A,
  ): Option[B] = traverse(p ++ 0, f, a) match {
    case Some(na) => val res = c(na); matchZero(p, f, res)
    case None => None
  }

  def matchTwo[A <: Expression, B <: Expression, C <: Expression](
      p: PosInExpr,
      c: (A, B) => C,
      f: ExpressionTraversalFunction,
      a: A,
      b: B,
  ): Option[C] = traverse(p ++ 0, f, a) match {
    case Some(na) => in(f, p, c(na, b)) match {
        case Left(Some(_)) => None
        case Left(None) => traverse(p ++ 1, f, b) match {
            case Some(nb) => matchZero(p, f, c(na, nb))
            case None => None
          }
        case Right(n) => Some(n)
      }
    case None => None
  }

  def traverse[A <: Expression](f: ExpressionTraversalFunction, e: A): Option[A] = traverse(HereP, f, e)
  @nowarn("msg=match may not be exhaustive")
  def traverseExpr[E <: Expression](f: ExpressionTraversalFunction, expr: E): Option[E] = expr match {
    case e: Term => traverse(HereP, f, e).map(_.asInstanceOf[E])
    case e: Formula => traverse(HereP, f, e).map(_.asInstanceOf[E])
    case e: Program => traverse(HereP, f, e).map(_.asInstanceOf[E])
  }

  def traverse[A <: Expression](p: PosInExpr, f: ExpressionTraversalFunction, e: A): Option[A] = {
    pre(f, p, e) match {
      case Left(Some(_)) => None
      case Left(None) => (e match {
          // Formulas
          case True => matchZero(p, f, e)
          case False => matchZero(p, f, e)
          case DotFormula => matchZero(p, f, e)
          case _: UnitPredicational => matchZero(p, f, e)
          case PredOf(a, b) => matchOne(p, PredOf.apply(a, _: Term), f, b)
          case PredicationalOf(a, b) => matchOne(p, PredicationalOf.apply(a, _: Formula), f, b)
          case Equal(a, b) => matchTwo(p, Equal.apply(_: Term, _: Term), f, a, b)
          case NotEqual(a, b) => matchTwo(p, NotEqual.apply(_: Term, _: Term), f, a, b)
          case Less(a, b) => matchTwo(p, Less.apply(_: Term, _: Term), f, a, b)
          case LessEqual(a, b) => matchTwo(p, LessEqual.apply(_: Term, _: Term), f, a, b)
          case GreaterEqual(a, b) => matchTwo(p, GreaterEqual.apply(_: Term, _: Term), f, a, b)
          case Greater(a, b) => matchTwo(p, Greater.apply(_: Term, _: Term), f, a, b)
          case Not(a) => matchOne(p, Not.apply, f, a)
          case And(a, b) => matchTwo(p, And.apply, f, a, b)
          case Or(a, b) => matchTwo(p, Or.apply, f, a, b)
          case Imply(a, b) => matchTwo(p, Imply.apply, f, a, b)
          case Equiv(a, b) => matchTwo(p, Equiv.apply, f, a, b)
          case Box(a, b) => matchTwo(p, Box.apply, f, a, b)
          case Diamond(a, b) => matchTwo(p, Diamond.apply, f, a, b)
          case Forall(v, a) => matchOne(p, Forall(v, _: Formula), f, a)
          case Exists(v, a) => matchOne(p, Exists(v, _: Formula), f, a)
          case DifferentialFormula(a) => matchOne(p, DifferentialFormula.apply, f, a)

          // Terms
          case Number(_) => matchZero(p, f, e)
          case _: BaseVariable => matchZero(p, f, e)
          case _: DotTerm => matchZero(p, f, e)
          case Nothing => matchZero(p, f, e)
          case _: UnitFunctional => matchZero(p, f, e)
          case FuncOf(a, b) => matchOne(p, FuncOf.apply(a, _: Term), f, b)
          case Differential(a) => matchOne(p, Differential.apply(_: Term), f, a)
          case DifferentialSymbol(a) => matchOne(p, DifferentialSymbol.apply(_: Variable), f, a)
          case Neg(a) => matchOne(p, Neg.apply(_: Term), f, a)
          case Plus(a, b) => matchTwo(p, Plus.apply(_: Term, _: Term), f, a, b)
          case Minus(a, b) => matchTwo(p, Minus.apply(_: Term, _: Term), f, a, b)
          case Times(a, b) => matchTwo(p, Times.apply(_: Term, _: Term), f, a, b)
          case Divide(a, b) => matchTwo(p, Divide.apply(_: Term, _: Term), f, a, b)
          case Power(a, b) => matchTwo(p, Power.apply(_: Term, _: Term), f, a, b)
          case Pair(a, b) => matchTwo(p, Pair.apply(_: Term, _: Term), f, a, b)

          // Programs
          case ProgramConst(_, _) => matchZero(p, f, e)
          case SystemConst(_, _) => matchZero(p, f, e)
          case DifferentialProgramConst(_, _) => matchZero(p, f, e)
          case Assign(a, b) => matchTwo(p, Assign.apply, f, a, b)
          case AssignAny(a) => matchOne(p, AssignAny.apply, f, a)
          case Test(a) => matchOne(p, Test.apply, f, a)
          case Compose(a, b) => matchTwo(p, Compose.apply, f, a, b)
          case Choice(a, b) => matchTwo(p, Choice.apply, f, a, b)
          case Loop(a) => matchOne(p, Loop.apply, f, a)
          case Dual(a) => matchOne(p, Dual.apply, f, a)
          case AtomicODE(x, t) => matchTwo(p, AtomicODE.apply, f, x, t)
          case DifferentialProduct(a, b) => matchTwo(p, DifferentialProduct.apply, f, a, b)
          case ODESystem(a, h) => matchTwo(p, ODESystem(_: DifferentialProgram, _: Formula), f, a, h)

          case _ => fail(e)
        }) match {
          case Some(y) => Some(y.asInstanceOf[A])
          case None => None
        }
      case Right(n) => Some(n)
    }
  }
}
