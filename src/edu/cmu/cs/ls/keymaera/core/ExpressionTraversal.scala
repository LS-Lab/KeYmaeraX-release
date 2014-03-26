package edu.cmu.cs.ls.keymaera.core

/**
 * Created by jdq on 3/17/14.
 */
object ExpressionTraversal {
  val fail = (x: Expr) => throw new IllegalStateException("Unimplemented case in Expr traversal: " + x)

  trait PosInExpr
  trait StopTraversal

  /**
   * TODO: Maybe we need to relax this interface to just the cases: Formula -> Formula, Term -> Term, Program -> Program, Game -> Game in order to make it implementable
   */
  trait ExpressionTraversalFunction {
    def pre[A <: Expr](p: PosInExpr, e: A): Either[Option[StopTraversal], A]
    def in[A <: Expr](p: PosInExpr, e: A): Either[Option[StopTraversal], A]
    def post[A <: Expr](p: PosInExpr, e: A): Either[Option[StopTraversal], A]
  }

  def matchZero[A <: Expr](p: PosInExpr, f: ExpressionTraversalFunction, a: A): Option[A] = f.post(p, a) match {
      case Left(Some(_)) => None
      case Left(None) => Some(a)
      case Right(x) => Some(x)
    }

  def matchOne[A <: Expr, B <: Expr](p: PosInExpr, c: A => B, f: ExpressionTraversalFunction, a: A): Option[B] = traverse(p, f, a) match {
    case Some(na: A) => val res = c(na); matchZero(p, f, res)
    case None => None
  }

  def matchTwo[A <: Expr, B <: Expr, C <: Expr](p: PosInExpr, c: (A, B) => C, f: ExpressionTraversalFunction, a: A, b: B): Option[C] = traverse(p, f, a) match {
    case Some(na: A) => f.in(p, c(na, b)) match {
      case Left(Some(_)) => None
      case Left(None) => traverse(p, f, b) match {
        case Some(nb: B) => val res = c(na, nb); matchZero(p, f, res)
        case None => None
      }
      case Right(n) => Some(n)
    }
    case None => None
  }

  def matchThree[A <: Expr, B <: Expr, C <: Expr, D <: Expr](p: PosInExpr, const: (A, B, C) => D, f: ExpressionTraversalFunction, a: A, b: B, c: C): Option[D] = traverse(p, f, a) match {
    case Some(na: A) => f.in(p, const(na, b, c)) match {
      case Left(Some(_)) => None
      case Left(None) => traverse(p, f, b) match {
        case Some(nb: B) => f.in(p, const(na, nb, c)) match {
          case Left(Some(_)) => None
          case Left(None) => traverse(p, f, c) match {
            case Some(nc: C) => val res = const(na, nb, nc); matchZero(p, f, res)
            case None => None
          }
        }
        case None => None
      }
      case Right(n) => Some(n)
    }
    case None => None
  }

  def traverse(p: PosInExpr, f: ExpressionTraversalFunction, e: Expr): Option[Expr] = {
    e match {
      case x: Formula => traverse(p, f, x)
      case x: Term => traverse(p, f, x)
      case x: Game => traverse(p, f, x)
      case x: Program => traverse(p, f, x)
    }
  }

  def traverse(p: PosInExpr, f: ExpressionTraversalFunction, e: Formula): Option[Formula] = {
    f.pre(p, e) match {
      case Left(Some(_)) => None
      case Left(None) => e match {
        case PredicateConstant(n, i) => matchZero(p, f, e)
        case ApplyPredicate(a, b) => matchTwo(p, ApplyPredicate.apply, f, a, b)
        case Equals(d, a, b) => matchTwo(p, Equals.apply(d, _: Term, _: Term), f, a, b)
        case NotEquals(d, a, b) => matchTwo(p, NotEquals.apply(d, _: Term, _: Term), f, a, b)
        case LessThan(d, a, b) => matchTwo(p, LessThan.apply(d, _: Term, _: Term), f, a, b)
        case LessEquals(d, a, b) => matchTwo(p, LessEquals.apply(d, _: Term, _: Term), f, a, b)
        case GreaterEquals(d, a, b) => matchTwo(p, GreaterEquals.apply(d, _: Term, _: Term), f, a, b)
        case GreaterThan(d, a, b) => matchTwo(p, GreaterThan.apply(d, _: Term, _: Term), f, a, b)
        case Not(a) => matchOne(p, Not.apply, f, a)
        case And(a, b) => matchTwo(p, And.apply, f, a, b)
        case Or(a, b) => matchTwo(p, Or.apply, f, a, b)
        case Imply(a, b) => matchTwo(p, Imply.apply, f, a, b)
        case Equiv(a, b) => matchTwo(p, Equiv.apply, f, a, b)
        case Modality(a, b) => matchTwo(p, Modality.apply, f, a, b)
        case Forall(v, a) => matchOne(p, Forall(v, _: Formula), f, a)
        case Exists(v, a) => matchOne(p, Exists(v, _: Formula), f, a)
        case _ => fail(e)
      }
      case Right(n) => Some(n)
    }
  }
  def traverse(p: PosInExpr, f: ExpressionTraversalFunction, e: Term): Option[Term] = {
    f.pre(p, e) match {
      case Left(Some(_)) => None
      case Left(None) =>  e match {
        case x: Variable => matchZero(p, f, e)
        case Apply(a, b) => matchTwo(p, Apply.apply, f, a, b)
        case Derivative(d, a) => matchOne(p, Derivative.apply(d, _: Term), f, a)
        case Neg(d, a) => matchOne(p, Neg.apply(d, _: Term), f, a)
        case Add(d, a, b) => matchTwo(p, Add.apply(d, _: Term, _: Term), f, a, b)
        case Subtract(d, a, b) => matchTwo(p, Subtract.apply(d, _: Term, _: Term), f, a, b)
        case Multiply(d, a, b) => matchTwo(p, Multiply.apply(d, _: Term, _: Term), f, a, b)
        case Divide(d, a, b) => matchTwo(p, Divide.apply(d, _: Term, _: Term), f, a, b)
        case Exp(d, a, b) => matchTwo(p, Exp.apply(d, _: Term, _: Term), f, a, b)
        case IfThenElseTerm(a, b, c) => matchThree(p, IfThenElseTerm.apply, f, a, b, c)
        case Pair(d, a, b) => matchTwo(p, Pair.apply(d, _: Term, _: Term), f, a, b)
        case _ => fail(e)
      }
      case Right(n) => Some(n)
    }
  }
  def traverse(p: PosInExpr, f: ExpressionTraversalFunction, e: Game): Option[Game] = {
    f.pre(p, e) match {
      case Left(Some(_)) => None
      case Left(None) =>  e match {
        case x: BoxModality => matchOne(p, BoxModality(_: Program), f, x.child)
        case x: DiamondModality => matchOne(p, DiamondModality(_: Program), f, x.child)
        case _ => fail(e)
      }
      case Right(n) => Some(n)
    }
  }

  def traverse(p: PosInExpr, f: ExpressionTraversalFunction, e: Program): Option[Program] = {
    f.pre(p, e) match {
      case Left(Some(_)) => None
      case Left(None) =>  e match {
        case Assign(a, b) => matchTwo(p, Assign.apply, f, a, b)
        case NDetAssign(a) => matchOne(p, NDetAssign.apply, f, a)
        case Test(a) => matchOne(p, Test.apply, f, a)
        case ContEvolve(a) => matchOne(p, ContEvolve.apply, f, a)
        case IfThen(a, b) => matchTwo(p, IfThen.apply, f, a, b)
        case IfThenElse(a, b, c) => matchThree(p, IfThenElse.apply, f, a, b, c)
        case Sequence(a, b) => matchTwo(p, Sequence.apply, f, a, b)
        case Choice(a, b) => matchTwo(p, Choice.apply, f, a, b)
        case Parallel(a, b) => matchTwo(p, Parallel.apply, f, a, b)
        case Loop(a) => matchOne(p, Loop.apply, f, a)
        case _ => fail(e)
      }
      case Right(n) => Some(n)
    }
  }
}
