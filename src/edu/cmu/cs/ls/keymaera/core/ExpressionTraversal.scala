package edu.cmu.cs.ls.keymaera.core

/**
 * Created by jdq on 3/17/14.
 */
object ExpressionTraversal {
  val fail = (x: Expr) => throw new IllegalStateException("Unimplemented case in Expr traversal: " + x)

  trait PosInExpr
  trait StopTraversal

  trait ExpressionTraversalFunction {
    def pre(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]
    def pre(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term]
    def pre(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game]
    def pre(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program]

    def in(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]
    def in(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term]
    def in(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game]
    def in(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program]

    def post(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]
    def post(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term]
    def post(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game]
    def post(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program]
  }

  def matchOne[A <: Expr](p: PosInExpr, c: A => Formula, f: ExpressionTraversalFunction, a: A): Option[Formula] = traverse(f, a) match {
    case Some(na: A) => val res = c(na); f.post(p, res) match {
      case Left(Some(_)) => None
      case Left(None) => Some(res)
      case Right(x) => Some(x)
    }
    case None => None
  }

  def matchTwo[A <: Expr, B <: Expr, C <: Formula](p: PosInExpr, c: (A, B) => C, f: ExpressionTraversalFunction, a: A, b: B): Option[Formula] = traverse(f, a) match {
    case Some(na: A) => f.in(p, c(na, b)) match {
      case Left(Some(_)) => None
      case Left(None) => traverse(f, b) match {
        case Some(nb: B) => val res = c(na, nb); f.post(p, res) match {
          case Left(Some(_)) => None
          case Left(None) => Some(res)
          case Right(x) => Some(x)
        }
        case None => None
      }
      case Right(n) => Some(n)
    }
    case None => None
  }

  def matchThree[A <: Expr, B <: Expr, C <: Expr, D <: Formula](p: PosInExpr, const: (A, B, C) => D, f: ExpressionTraversalFunction, a: A, b: B, c: C): Option[Formula] = traverse(f, a) match {
    case Some(na: A) => f.in(p, const(na, b, c)) match {
      case Left(Some(_)) => None
      case Left(None) => traverse(f, b) match {
        case Some(nb: B) => f.in(p, const(na, nb, c)) match {
          case Left(Some(_)) => None
          case Left(None) => traverse(f, c) match {
            case Some(nc: C) => val res = const(na, nb, nc); f.post(p, res) match {
              case Left(Some(_)) => None
              case Left(None) => Some(res)
              case Right(x) => Some(x)
            }
            case None => None
          }
        }
        case None => None
      }
      case Right(n) => Some(n)
    }
    case None => None
  }
  def traverse(f: ExpressionTraversalFunction, e: Expr): Option[Expr] = {
    e match {
      case x: Formula => traverse(f, x)
      case x: Term => traverse(f, x)
      case x: Game => traverse(f, x)
      case x: Program => traverse(f, x)
    }
  }

  def traverse(f: ExpressionTraversalFunction, e: Formula): Option[Formula] = {
    val p = new PosInExpr {}
    f.pre(p, e) match {
      case Left(Some(_)) => None
      case Left(None) => e match {
          case Not(a) => matchOne(p, Not.apply, f, a)
          case And(a, b) => matchTwo(p, And.apply, f, a, b)
          case Or(a, b) => matchTwo(p, Or.apply, f, a, b)
          case Imply(a, b) => matchTwo(p, Imply.apply, f, a, b)
          case Equiv(a, b) => matchTwo(p, Equiv.apply, f, a, b)
          case IfThen(a, b) => matchTwo(p, IfThen.apply, f, a, b)
          case IfThenElse(a, b, c) => matchThree(p, IfThenElse.apply, f, a, b, c)
          case _ => fail(e)
        }
      case Right(n) => Some(n)
    }
  }
  def traverse(f: ExpressionTraversalFunction, e: Term): Option[Term] = {
    e match {
      case _ => fail(e)
    }
  }
  def traverse(f: ExpressionTraversalFunction, e: Game): Option[Game] = {
    e match {
      case _ => fail(e)
    }
  }

  def traverse(f: ExpressionTraversalFunction, e: Program): Option[Program] = {
    e match {
      case _ => fail(e)
    }
  }
}
