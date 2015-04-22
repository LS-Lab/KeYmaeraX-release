package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

/**
 * Created by jdq on 3/17/14.
 * @author Nathan Fulton
 * @author Ran Ji
 * @author Stefan Mitsch
 * @author Jan-David Quesel
 *
 */
object ExpressionTraversal {
  type N[A] = A => Nothing
  type NN[A] = N[N[A]]

  trait UnionType[T] {
    type and[S] = UnionType[T with N[S]]
    type andProvideAType = N[T]
    type andProvideEvidence[X] = NN[X] <:< N[T]
  }

  // for convenience
  type union[T] = { type and[S] = UnionType[N[T]]#and[S] }

  type FTPG[T] = union[Term]#and[Formula]#and[Program]#andProvideEvidence[T]

  def fail(x: Expression) = throw new UnknownOperatorException("Unimplemented case in Expr traversal", x.asInstanceOf[Expression])
  def failFTPG[T, A : FTPG](x: A) = throw new UnknownOperatorException("Unimplemented case in Expr traversal", x.asInstanceOf[Expression])

  trait StopTraversal
  val stop = new StopTraversal {}

  /**
   * TODO: Maybe we need to relax this interface to just the cases: Formula -> Formula, Term -> Term, Program -> Program, ModalOp -> ModalOp in order to make it implementable
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

  /**
   * blacklist is a set of symbols that most not be bound
   */
  object TraverseToPosition {
    def apply(t: PosInExpr, cont: ExpressionTraversalFunction): ExpressionTraversalFunction = new TraverseToPosition(t, cont, Set.empty)
    def apply(t: PosInExpr, cont: ExpressionTraversalFunction, blacklist: Set[NamedSymbol]): ExpressionTraversalFunction = new TraverseToPosition(t, cont, blacklist)
  }

  class TraverseToPosition(t: PosInExpr, cont: ExpressionTraversalFunction, blacklist: Set[NamedSymbol]) extends ExpressionTraversalFunction {
    override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
      if(p == t) traverse(p, cont, e) match {
          case Some(x: Formula) => Right(x)
          case _ => Left(Some(stop))
        }
      else e match {
        case Forall(v, phi) if blacklist.map(v.contains).foldLeft(false)(_||_) => Left(Some(stop))
        case Exists(v, phi) if blacklist.map(v.contains).foldLeft(false)(_||_) => Left(Some(stop))
        case Box(a, c) if blacklist.map(StaticSemantics(a).bv.contains).foldLeft(false)(_||_) => Left(Some(stop))
        case Diamond(a, c) if blacklist.map(StaticSemantics(a).bv.contains).foldLeft(false)(_||_) =>  Left(Some(stop))
        case _ =>
          if (p.isPrefixOf(t))
          // proceed
            Left(None)
          else
          // return id to ignore this branch
            Right(e)
      }
    override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = if(p == t)
      traverse(p, cont, e) match { case Some(x: Program) => Right(x) case _ => Left(Some(stop))}
    else if(p.isPrefixOf(t))
    // proceed
      Left(None)
    else
    // return id to ignore this branch
      Right(e)
    override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if(p == t)
      traverse(p, cont, e) match { case Some(x: Term) => Right(x) case _ => Left(Some(stop))}
    else if(p.isPrefixOf(t))
    // proceed
      Left(None)
    else
    // return id to ignore this branch
      Right(e)
  }

  final def pre[A : FTPG](f: ExpressionTraversalFunction, p: PosInExpr, e: A): Either[Option[StopTraversal], A] = e match {
    case x: Formula => f.preF(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
    case x: Program => f.preP(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
    case x: Term => f.preT(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
  }

  final def in[A : FTPG](f: ExpressionTraversalFunction, p: PosInExpr, e: A): Either[Option[StopTraversal], A] = e match {
    case x: Formula => f.inF(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
    case x: Program => f.inP(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
    case x: Term => f.inT(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
  }

  final def post[A : FTPG](f: ExpressionTraversalFunction, p: PosInExpr, e: A): Either[Option[StopTraversal], A] = e match {
    case x: Formula => f.postF(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
    case x: Program => f.postP(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
    case x: Term => f.postT(p, x) match {
      case a@Left(Some(_)) => Left(Some(stop))
      case Left(None) => Left(None)
      case Right(a) => Right(a.asInstanceOf[A])
    }
  }

  def matchZero[A : FTPG](p: PosInExpr, f: ExpressionTraversalFunction, a: A): Option[A] = post(f, p, a) match {
    case Left(Some(_)) => None
    case Left(None) => Some(a)
    case Right(x) => Some(x)
  }

  def matchOne[A : FTPG, B : FTPG](p: PosInExpr, c: A => B, f: ExpressionTraversalFunction, a: A): Option[B] = traverse(p.first, f, a) match {
    case Some(na) => val res = c(na); matchZero(p, f, res)
    case None => None
  }

  def matchTwo[A : FTPG, B : FTPG, C : FTPG](p: PosInExpr, c: (A, B) => C, f: ExpressionTraversalFunction, a: A, b: B): Option[C] = traverse(p.first, f, a) match {
    case Some(na) => in(f, p, c(na, b)) match {
      case Left(Some(_)) => None
      case Left(None) => traverse(p.second, f, b) match {
        case Some(nb) => matchZero(p, f, c(na, nb))
        case None => None
      }
      case Right(n) => Some(n)
    }
    case None => None
  }

  def matchThree[A : FTPG, B : FTPG, C : FTPG, D : FTPG](p: PosInExpr, const: (A, B, C) => D, f: ExpressionTraversalFunction, a: A, b: B, c: C): Option[D] = traverse(p.first, f, a) match {
    case Some(na) => in(f, p, const(na, b, c)) match {
      case Left(Some(_)) => None
      case Left(None) => traverse(p.second, f, b) match {
        case Some(nb) => in(f, p, const(na, nb, c)) match {
          case Left(Some(_)) => None
          case Left(None) => traverse(p.third, f, c) match {
            case Some(nc) => val res = const(na, nb, nc); matchZero(p, f, res)
            case None => None
          }
        }
        case None => None
      }
      case Right(n) => Some(n)
    }
    case None => None
  }
  def traverse[A : FTPG](f: ExpressionTraversalFunction, e: A): Option[A] = traverse(HereP, f, e)

  def traverse[A : FTPG](p: PosInExpr, f: ExpressionTraversalFunction, e: A): Option[A] = {
    pre(f, p, e) match {
      case Left(Some(_)) => None
      case Left(None) => (e match {
        // Formulas
        case True => matchZero(p, f, e)
        case False => matchZero(p, f, e)
        case PredOf(a, b) => matchOne(p, PredOf.apply(a, _: Term), f, b)
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
        case _: Variable => matchZero(p, f, e)
        case FuncOf(a, b) => matchOne(p, FuncOf.apply(a, _: Term), f, b)
        case Differential(a) => matchOne(p, Differential.apply(_: Term), f, a)
        case DifferentialSymbol(a) => matchOne(p, DifferentialSymbol.apply(_: Variable), f, a)
        case Plus(a, b) => matchTwo(p, Plus.apply(_: Term, _: Term), f, a, b)
        case Minus(a, b) => matchTwo(p, Minus.apply(_: Term, _: Term), f, a, b)
        case Times(a, b) => matchTwo(p, Times.apply(_: Term, _: Term), f, a, b)
        case Divide(a, b) => matchTwo(p, Divide.apply(_: Term, _: Term), f, a, b)
        case Power(a, b) => matchTwo(p, Power.apply(_: Term, _: Term), f, a, b)

        // Programs
        case ProgramConst(_) => matchZero(p, f, e)
        case DifferentialProgramConst(_) => matchZero(p, f, e)
        case DotTerm => matchZero(p, f, e)
        case Nothing => matchZero(p, f, e)
        case Anything => matchZero(p, f, e)
        case Assign(a, b) => matchTwo(p, Assign.apply, f, a, b)
        case AssignAny(a) => matchOne(p, AssignAny.apply, f, a)
        case Test(a) => matchOne(p, Test.apply, f, a)
        case Compose(a, b) => matchTwo(p, Compose.apply, f, a, b)
        case Choice(a, b) => matchTwo(p, Choice.apply, f, a, b)
        case Loop(a) => matchOne(p, Loop.apply, f, a)
        case AtomicODE(x, t) => matchTwo(p, AtomicODE.apply, f, x, t)
        case DifferentialProduct(a, b) => matchTwo(p, DifferentialProduct.apply, f, a, b)
        case ODESystem(a, h) => matchTwo(p, ODESystem(_: DifferentialProgram, _: Formula), f, a, h)

        case _ => failFTPG(e)
      }) match {
        case Some(y) => Some(y.asInstanceOf[A])
        case None => None
      }
      case Right(n) => Some(n)
    }
  }
}
