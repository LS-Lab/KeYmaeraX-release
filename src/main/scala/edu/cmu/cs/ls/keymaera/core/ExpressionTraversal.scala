package edu.cmu.cs.ls.keymaera.core

/**
 * Created by jdq on 3/17/14.
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

  type FTPG[T] = union[Term]#and[Formula]#and[Program]#and[Game]#andProvideEvidence[T]

  def fail(x: Expr) = throw new IllegalStateException("Unimplemented case in Expr traversal: " + x)
  def failFTPG[T, A : FTPG](x: A) = throw new IllegalStateException("Unimplemented case in Expr traversal: " + x)

  trait StopTraversal
  val stop = new StopTraversal {}

  /**
   * TODO: Maybe we need to relax this interface to just the cases: Formula -> Formula, Term -> Term, Program -> Program, Game -> Game in order to make it implementable
   */
  trait ExpressionTraversalFunction {
    def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = Left(None)
    def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = Left(None)
    def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = Left(None)
    def preG(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game] = Left(None)
    def inF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = Left(None)
    def inP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = Left(None)
    def inT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = Left(None)
    def inG(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game] = Left(None)
    def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = Left(None)
    def postP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = Left(None)
    def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = Left(None)
    def postG(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game] = Left(None)
  }

  /**
   * blacklist is a set of symbols that most not be bound
   */
  object TraverseToPosition {
    def apply(t: PosInExpr, cont: ExpressionTraversalFunction): ExpressionTraversalFunction = new TraverseToPosition(t, cont, Set.empty)
    def apply(t: PosInExpr, cont: ExpressionTraversalFunction, blacklist: Set[NamedSymbol]): ExpressionTraversalFunction = new TraverseToPosition(t, cont, blacklist)
  }

  class TraverseToPosition(t: PosInExpr, cont: ExpressionTraversalFunction, blacklist: Set[NamedSymbol]) extends ExpressionTraversalFunction {
    override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
      case Forall(v, phi) if(blacklist.map(v.contains).foldLeft(false)(_||_)) => Left(Some(stop))
      case Exists(v, phi) if(blacklist.map(v.contains).foldLeft(false)(_||_)) => Left(Some(stop))
      case BoxModality(a, c) if(blacklist.map(a.writes.contains).foldLeft(false)(_||_)) => Left(Some(stop))
      case DiamondModality(a, c) if(blacklist.map(a.writes.contains).foldLeft(false)(_||_)) =>  Left(Some(stop))
      case _ => {
        if (p == t)
          traverse(p, cont, e) match {
            case Some(x: Formula) => Right(x)
            case _ => Left(Some(stop))
          }
        else if (p.isPrefixOf(t))
        // proceed
          Left(None)
        else
        // return id to ignore this branch
          Right(e)
      }
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
    override def preG(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game] = if(p == t)
      traverse(p, cont, e) match { case Some(x: Game) => Right(x) case _ => Left(Some(stop))}
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
    case x: Game => f.preG(p, x) match {
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
    case x: Game => f.inG(p, x) match {
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
    case x: Game => f.postG(p, x) match {
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
        case Some(nb) => val res = c(na, nb); matchZero(p, f, res)
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
        case PredicateConstant(_, _) => matchZero(p, f, e)
        case ApplyPredicate(a, b) => matchOne(p, ApplyPredicate.apply(a, _: Term), f, b)
        case Equals(d, a, b) => matchTwo(p, Equals.apply(d, _: Term, _: Term), f, a, b)
        case NotEquals(d, a, b) => matchTwo(p, NotEquals.apply(d, _: Term, _: Term), f, a, b)
        case ProgramEquals(a, b) => matchTwo(p, ProgramEquals.apply, f, a, b)
        case ProgramNotEquals(a, b) => matchTwo(p, ProgramNotEquals.apply, f, a, b)
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

        // Terms
        case Number(_, _) => matchZero(p, f, e)
        case _: Variable => matchZero(p, f, e)
        case Apply(a, b) => matchOne(p, Apply.apply(a, _: Term), f, b)
        case Derivative(d, a) => matchOne(p, Derivative.apply(d, _: Term), f, a)
        case Neg(d, a) => matchOne(p, Neg.apply(d, _: Term), f, a)
        case Add(d, a, b) => matchTwo(p, Add.apply(d, _: Term, _: Term), f, a, b)
        case Subtract(d, a, b) => matchTwo(p, Subtract.apply(d, _: Term, _: Term), f, a, b)
        case Multiply(d, a, b) => matchTwo(p, Multiply.apply(d, _: Term, _: Term), f, a, b)
        case Divide(d, a, b) => matchTwo(p, Divide.apply(d, _: Term, _: Term), f, a, b)
        case Exp(d, a, b) => matchTwo(p, Exp.apply(d, _: Term, _: Term), f, a, b)
        case IfThenElseTerm(a, b, c) => matchThree(p, IfThenElseTerm.apply, f, a, b, c)
        case Pair(d, a, b) => matchTwo(p, Pair.apply(d, _: Term, _: Term), f, a, b)

        // Games
        case x: BoxModality => matchOne(p, BoxModality(_: Program), f, x.child.asInstanceOf[Program])
        case x: DiamondModality => matchOne(p, DiamondModality(_: Program), f, x.child.asInstanceOf[Program])

        // Programs
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

        case _ => failFTPG(e)
      }) match {
        case Some(y) => Some(y.asInstanceOf[A])
        case None => None
      }
      case Right(n) => Some(n)
    }
  }

}
