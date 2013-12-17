/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
//package edu.cmu.cs.ls.keymaera.core


import scala.annotation.elidable
import scala.annotation.elidable._

import scala.math
import scala.math._

/**
 * External functions imported in core but not used in proof check mode
 */
trait Annotable


/**
 * Prover Core
 */
object Core {

/**
 * Sorts
 *=======
 * Class hierarchy defining builtin and user defined sorts. Because user defined
 * sorts are only known at runtime, we use instances of the below classes to
 * identify the sorts on which the dynamic logic expressions operate. (See
 * TypeSafety.scala for a description how typechecking works)
 */
  sealed abstract class Sort
  abstract class S[T <: Sort] extends Sort

  /* sort of booleans: true, false */
  class BoolT                                                    extends S[BoolT]
  val Bool = new BoolT

  /* sort of reals: 0, 1, 2.73 */
  class RealT                                                    extends S[RealT]
  val Real = new RealT
 
 /* sort of games */
  class GameT                                                    extends S[GameT]
  val Game = new GameT

  /* sort of hybrid probrams */
  class ProgramT                                                 extends S[ProgramT]
  val Program = new ProgramT

  /* user defined sort */
  class UserT(name : String)                                     extends S[UserT]
  /* user defined enum sort. values is the list of named constants of this enum */
  class EnumT(name : String, values : list[String])              extends S[EnumT]

  /* used to define pairs of sorts. That is the pair sort is of type L x R */
  class PairT[L <: Sort, R <: Sort](val left : L, val right : R) extends S[PairT[L,R]] {
    def equals(that : Anyref) = that match {
      PairT(l, r) => left == l && right == r
      _ => false
    }
  }

  val RealXReal       = new PairT(Real, Real)
  val BoolXBool       = new PairT(Bool, Bool)
  val GameXBool       = new PairT(Game, Bool)
  val GameXGame       = new PairT(Game, Game)
  val ProgramXProgram = new PairT(Program, Program)

  /* subtype of a given type; for example TimeT = Subtype("the time that passes", Real) */
  class Subtype[T <: Sort](name : String, sort : T)              extends S[T]

/**
 * Context
 *=========
 * trait used to collect and maintain context information while traversing sequents and expressions.
 */
  trait Context {
    /* invoked when the sequent or expression is traversed to the subexpression of a unary term */
    def next  : Context
    /* invoked when the sequent or expression is traversed to the left subexpression of a binary term */
    def left  : Context
    /* invoked when the sequent or expression is traversed to the right subexpression of a binary term */
    def right : Context
  }

  /**
   * Default Context
   *-----------------
   * A context that remains the same irrespective of the position in the expression. Can be used to 
   * traverse the entire tree in a position agnostic manner.
   */
  object DefaultContext extends Context {
    def next  = this
    def left  = this
    def right = this
  }

/**
 * Expression infrastructure
 *===========================
 * (see TypeSafety.scala for an explaination how the Expression builtin typechecking
 * mechanism works. Each expression may replicate itself with apply and adheres to the
 * generic recursion structure via the function reduce.
 */
  sealed abstract class Expression[+T <: Sort](val sort : T) extends Annotable {

    /* create a clone of this expression with the given subexpressions */
    def apply(subexpressions : Expression[Sort]*) : Expression[Sort]

    /* returns the sequence of subexpressions of an expression */
    def subexpressions() : Seq[Expression[Sort]]

    /**
     * Reduce
     *--------
     * recurse upward through the expression data structure while
     * building up the context through ctx.next, ctx.left and ctx.right
     * until at the end of a given path up evaluates to false. From there
     * on, traverse down mapping the expression and the already reduced
     * subexpressions to an element of type A.
     *
     * For example
     *   size = reduce[Int]((_,_) => true, (_, _, summands : Int*) => 1 + sum(summands))(DefaultContext)
     * computes the size of the expression.
     */
    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A

    /**
     * Map
     *-----
     * recursively traverse the expression (collecting the path context) and create a transformed expression on the way back down
     */
    def map(up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, Expression[Sort]*) => Expression[Sort])
           (ctx : Context) : Expression[Sort] = reduce[Expression[Sort]](up, down)(ctx)

    def identity_map(expression : Expression[Sort], ctx : Context, subexpressions : Expression[Sort]*) : Expression[Sort] = 
          if (expression.subexpressions() == subexpressions) expression else expression.apply(subexpressions)
  }

  /* atom / leaf expression */
  trait Atom[T <: Sort] extends Expression[T] {
    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A = 
          down(this, ctx)

    def subexpressions() : Seq[Expression[Sort]] = Nil
  }

  /* unary expression */
  trait Unary[D <: Sort, T <: Sort] extends Expression[T] {
    val subsort : D
    val next    : Expression[D]

    applicable
    @elidable(ASSERTION) def applicable = require(subsort == next.sort, "Sort Mismatch in Unary Expression")

    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A =
          if (up(this, ctx)) down(this, ctx, next.reduce(up, down)(ctx.next)) else down(this, ctx)

    def subexpressions() : Seq[Expression[Sort]] = Seq(next)
  }

  /* binary expression (n-ary is encoded as binary of binary of ... */
  trait Binary[L <: Sort, R <: Sort, T <: Sort] extends Expression[T] {
    val subsort : Pair[L, R]
    val left  : Expression[L]
    val right : Expression[R]

    applicable
    @elidable(ASSERTION) def applicable =
          require(subsort.left == left.sort, subsort.right == right.sort, "Sort Mismatch in Binary Expression")

    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A =
          if (up(this, ctx)) down(this, ctx, left.reduce(up, down)(ctx.left), right.reduce(up, down)(ctx.right))
          else down(this, pos)

    def subexpressions() : Seq[Expression[Sort]] = Seq(left, right)
  }

  /*********************************************************************************
   * Differential Logic
   *********************************************************************************
   */

  /**
   * Variables and Functions
   *=========================
   */
  object NameCounter {
    private var next_id : Int = 0

    applicable
    @elidable(ASSERTION) def applicable = require(next_id < Int.MaxValue, "Error: too many variable objects; counter overflow")

    def next() : Int = {
      this.synchronized {
        next_id = next_id + 1;
        return next_id;
      }
    }
  }

  abstract class NamedSymbol[+T <: Sort](val name : String, val sort : T) {

    private val id : Int = NameCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.type_object == x.type_object

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  class Variable[T <: Sort] (val name : String, sort : T)     extends NamedSymbol[T](name, sort)

  class FunctionVar[D <: Sort, T <: Sort] (val name : String, val domain : D, sort : T)
                                                              extends NamedSymbol[T](name, sort)

  /**
   * Constant, Variable and Function Expressions
   *=============================================
   */

  /* The * in nondet. assignments */
  class Random[T <: Sort](val sort : T) extends Expression(sort) with Atom[T] {
    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Nil => new Random(sort)
      _       => throw new IllegalArgumentException("Random is an Atom and hence has no subexpressions.")
    }
  }

  /* Constant of scala type A cast into sort T */
  class Constant[T <: Sort, A](val sort : T, val value : A) extends Expression(sort) with Atom[T] {
    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Nil => new Constant(sort, value)
      _       => throw new IllegalArgumentException("Constant is an Atom and hence has no subexpressions.")
    }
  }

  /* convenience wrappers for boolean / real constants */
  val TrueEx  = new Constant[_, Boolean](Bool, true)
  val FalseEx = new Constant[_, Boolean](Bool, false)

  class Number[T <: S[RealT]](sort : T, value : Int)        extends Constant(sort, value)
  class Number[T <: S[RealT]](sort : T, value : Double)     extends Constant(sort, value)
  class Number[T <: S[RealT]](sort : T, value : BigDecimal) extends Constant(sort, value)

  /* value of variable */
  class Value[T <: Sort](val variable : Variable[T]) extends Expression(variable.sort) with Atom[T] {
    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Nil => new Value(variable)
      _       => throw new IllegalArgumentException("Value is an Atom and hence has no subexpressions.")
    }
  }

  /* function application */
  class Apply[D <: Sort, T <: Sort](val function : FunctionVar[D, T], val parameter : Expression(function.domain))
             extends Expression(function.sort) extends Unary[D, T] { 
    val subsort = function.domain

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Seq[Expression[Sort]] => if (f.length == 1) new Apply(function, f(0))
      else
           throw new IllegalArgumentException("Apply requires an argument of type Expression(function.domain).")
      _ => throw new IllegalArgumentException("Apply requires an argument of type Expression(function.domain).")
    }
  }

  /* combine subexpressions into a vector */
  class Vector[T <: PairT](val subsort : T, val left : Expression(subsort.left), val right : Expression(subsort.right))
              extends Expression(subsort) with Binary {
    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Seq[Expression[Sort]] => if (f.length == 2) new Vector(subsort, f(0), f(1))
      else
           throw new IllegalArgumentException("Vector requires two arguments of type Expression(subsort.left) 
                                               and Expression(subsort.right), respectively.")
      _ => throw new IllegalArgumentException("Vector requires two arguments of type Expression(subsort.left) 
                                               and Expression(subsort.right), respectively.")
    }
  }

  /* extract elements from a vector expression */
  class Left [T <: PairT](val subsort : T, val next : Expression(subsort)) extends Expression(subsort.left)  with Unary {
    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Seq[Expression[Sort]] => if (f.length == 1) new Left(subsort, f(0))
      else
           throw new IllegalArgumentException("Left requires an argument of type Expression(subsort).")
      _ => throw new IllegalArgumentException("Left requires an argument of type Expression(subsort).")
    }
  }

  class Right[T <: PairT](val subsort : T, val next : Expression(subsort)) extends Expression(subsort.right) with Unary {
    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
      f : Seq[Expression[Sort]] => if (f.length == 1) new Right(subsort, f(0)) 
      else
           throw new IllegalArgumentException("Right requires an argument of type Expression(subsort).")
      _ => throw new IllegalArgumentException("Right requires an argument of type Expression(subsort).")
    }
  }

  /**
   * Formulas (aka Terms)
   *======================
   */
  abstract class UnaryFormula  extends Expression(Bool) With Unary  {val subsort = Bool}      /* Bool -> Bool */

  sealed abstract class TermSymbol

  abstract class UnaryTermSymbol  extends TermSymbol
  object Not        extends UnaryTermSymbol  /* !\Phi */
  object Globally   extends UnaryTermSymbol  /* []\Phi e.g., in [\alpha] []\Phi */
  object Finally    extends UnaryTermSymbol  /* <>\Phi e.g., in [\alpha] <>\Phi */

  class UnaryFormula (val termSymbol : UnaryTermSymbol, val next : Expression(Bool))
    extends Expression(Bool) With Unary {
      val subsort = Bool

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new UnaryFormula(termSymbol, f(0))
        else
             throw new IllegalArgumentException("UnaryFormula " + termSymbol + " requires one argument of type Expression(Bool)")
        _ => throw new IllegalArgumentException("UnaryFormula " + termSymbol + " requires one argument of type Expression(Bool)")
      }
  }

  object UnaryFormula {
    def !  (next : Expression(Bool)) = new UnaryFormula(Not     , next)
    def <> (next : Expression(Bool)) = new UnaryFormula(Globally, next)
    def [] (next : Expression(Bool)) = new UnaryFormula(Finally , next)
  }

  abstract class BinaryTermSymbol extends TermSymbol
  object And        extends BinaryTermSymbol /* \Phi /\ \Psi */
  object Or         extends BinaryTermSymbol /* \Phi \/ \Psi */
  object Implies    extends BinaryTermSymbol /* \Phi  => \Psi */
  object Equivalent extends BinaryTermSymbol /* \Phi <=> \Psi */
  object Antedecent extends BinaryTermSymbol /* , left  of |- */
  object Succedent  extends BinaryTermSymbol /* , right of |- */

  class BinaryFormula (val termSymbol : BinaryTermSymbol, val left : Expression(Bool), val right : Expression(Bool)) 
    extends Expression(Bool) With Binary {
      val subsort = BoolXBool

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2) new BinaryFormula(termSymbol, f(0), f(1))
        else
             throw new IllegalArgumentException("BinaryFormula " + termSymbol+ " requires two arguments of type Expression(Bool)")
        _ => throw new IllegalArgumentException("BinaryFormula " + termSymbol+ " requires two arguments of type Expression(Bool)")
      }
  }

  object BinaryFormula {
    def &   (left : Expression(Bool), right : Expression(Bool)) = new BinaryFormula(And,        left, right)
    def |   (left : Expression(Bool), right : Expression(Bool)) = new BinaryFormula(Or,         left, right)
    def =>  (left : Expression(Bool), right : Expression(Bool)) = new BinaryFormula(Implies,    left, right)
    def <=> (left : Expression(Bool), right : Expression(Bool)) = new BinaryFormula(Equivalent, left, right)
  }

  /**
   * Comparisson and Equality
   *==========================
   */

  class Equals[T <: Sort](val elemSort : T, val left : Expression[T], val right : Expression[T])
    extends Expression(Bool) with Binary {
      val subsort = new Pair(elemSort, elemSort)

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2 && f(0).sort == elemSort && f(1).sort == elemSort)
            new Equals(elemSort, f(0), f(1))
        else
             throw new IllegalArgumentException("Equals requires two arguments of type Expression(elemSort)")
        _ => throw new IllegalArgumentException("Equals requires two arguments of type Expression(elemSort)")
      }
  }

  class NotEquals[T <: Sort](val elemSort : T, val left : Expression[T], val right : Expression[T])
    extends Expression(Bool) with Binary {
      val subsort = new Pair(elemSort, elemSort)

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2 && f(0).sort == elemSort && f(1).sort == elemSort)
            new NotEquals(elemSort, f(0), f(1))
        else
             throw new IllegalArgumentException("Equals requires two arguments of type Expression(elemSort)")
        _ => throw new IllegalArgumentException("Equals requires two arguments of type Expression(elemSort)")
      }
  }

  abstract class CompareSymbol extends TermSymbol
  object GreaterThan   extends CompareSymbol /* > */
  object LessThan      extends CompareSymbol /* < */
  object GreaterEquals extends CompareSymbol /* >= */
  object LessEquals    extends CompareSymbol /* <= */

  class Compare[T <: S[RealT]](val cSymbol : CompareSymbol, 
                               val elemSort : T, val left : Expression(elemSort), val right : Expression(elemSort))
    extends Expression(Bool) with Binary {
      val subsort = new Pair(elemSort, elemSort)

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2 && f(0).sort == elemSort && f(1).sort == elemSort)
            new Compare(cSymbol, elemSort, f(0), f(1))
        else
             throw new IllegalArgumentException("Equals requires two arguments of type Expression(elemSort)")
        _ => throw new IllegalArgumentException("Equals requires two arguments of type Expression(elemSort)")
      }
  }

  object Compare {
    def > [T <: S[RealT]](elemSort : T, left : Expression(elemSort), right : Expression(elemSort)) =
          new Compare(GreaterThan, elemSort, left, right)
    def < [T <: S[RealT]](elemSort : T, left : Expression(elemSort), right : Expression(elemSort)) =
          new Compare(LessThan, elemSort, left, right)
    def >=[T <: S[RealT]](elemSort : T, left : Expression(elemSort), right : Expression(elemSort)) =
          new Compare(GreaterEquals, elemSort, left, right)
    def <=[T <: S[RealT]](elemSort : T, left : Expression(elemSort), right : Expression(elemSort)) =
          new Compare(LessEquals, elemSort, left, right)
  }

  /**
   * Games
   *=======
   */

  /* Modality */
  class Modality (val game : Expression(Game), val term : Expression(Bool)) extends Expression(Bool) with Binary {
    val subsort = GameXBool
    val left    = game
    val right   = term

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2) new Modality(f(0), f(1))
        else
             throw new IllegalArgumentException("Modality requires two arguments of type Expression(Game) and Expression(Bool)")
        _ => throw new IllegalArgumentException("Modality requires two arguments of type Expression(Game) and Expression(Bool)")
      }
  }

  /* Games */
  class BoxModality     (val program : Expression(Program)) extends Expression(Game) with Unary {
    val subsort = Program
    val next = program

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new BoxModality(f(0))
        else
             throw new IllegalArgumentException("BoxModality requires one arguments of type Expression(Program).")
        _ => throw new IllegalArgumentException("BoxModality requires one argument of type Expression(Program).")
      }
  }

  class DiamondModality (val program : Expression(Program)) extends Expression(Game) with Unary {
    val subsort = Program
    val next = program

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new BoxModality(f(0))
        else
             throw new IllegalArgumentException("BoxModality requires one argument of type Expression(Program).")
        _ => throw new IllegalArgumentException("BoxModality requires one argument of type Expression(Program).")
      }
  }

  abstract class UnaryGameSymbol extends TermSymbol
  object BoxStar     extends UnaryGameSymbol
  object DiamondStar extends UnaryGameSymbol

  class UnaryGame(val gameSymbol : UnaryGameSymbol, val next : Expression(Game)) extends Expression(Game) with Unary {
    val subobject = Game

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new UnaryGame(gameSymbol, f(0))
        else
             throw new IllegalArgumentException("UnaryGame requires one argument of type Expression(Game).")
        _ => throw new IllegalArgumentException("UnaryGame requires one argument of type Expression(Game).")
      }
  }

  abstract class BinaryGameSymbol extends TermSymbol
  object SequenceGame extends BinaryGameSymbol
  object DisjunctGame extends BinaryGameSymbol
  object ConjunctGame extends BinaryGameSymbol

  class BinaryGame(val gameSymbol : BinaryGameSymbol, val left : Expression(Game), val right : Expression(Game)) 
    extends Expression(Game) with Binary {
      val subobject = Game

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
          f : Seq[Expression[Sort]] => if (f.length == 2) new BinaryGame(gameSymbol, f(0), f(1))
          else
               throw new IllegalArgumentException("BinaryGame requires two arguments of type Expression(Game).")
          _ => throw new IllegalArgumentException("BinaryGame requires two arguments of type Expression(Game).")
        }
  }

  /**
   * Programs
   *==========
   */

  abstract class ProgramSymbol extends TermSymbol
  object SequenceProgram extends ProgramSymbol
  object Choice          extends ProgramSymbol
  object ParallelProgram extends ProgramSymbol

  class BinaryProgram(val prog : ProgramSymbol, val left : Expression(Program), val right : Expression(Program)) 
    extends Expression(Program) with Binary {
      val subsort = ProgramXProgram

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2) new BinaryProgram(prog, f(0), f(1))
        else
             throw new IllegalArgumentException("BinaryProgram requires two arguments of type Expression(Program).")
        _ => throw new IllegalArgumentException("BinaryProgram requires two arguments of type Expression(Program).")
      }
  }


  class Loop(val program : Expression(Program)) extends Expression(Program) with Unary {
    val subsort = Program
    val next = program

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new Loop(f(0))
        else
             throw new IllegalArgumentException("Loop requires one argument of type Expression(Program).")
        _ => throw new IllegalArgumentException("Loop requires one argument of type Expression(Program).")
      }
  }

  class Assign[T <: Sort](val variable : Variable[T], val next : Expression(variable.sort)) extends Expression(Program) with Unary {
    val subsort = variable.sort

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new Assign(variable, f(0))
        else
             throw new IllegalArgumentException("Assign to variable requires one argument of type Expression(variable.sort).")
        _ => throw new IllegalArgumentException("Assign to variable requires one argument of type Expression(variable.sort).")
    }
  }

  class Assign[D <: Sort, T <: Sort](val function : FunctionVar[D, T],
                                     val parameter : Expression(function.domain), val right : Expression(function.sort)
    extends Expression(Program) with Binary {
      val subsort = variable.sort

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
          f : Seq[Expression[Sort]] => if (f.length == 2) new Assign(function, f(0), f(1))
          else
               throw new IllegalArgumentException("Assign to function requires two arguments matching domain and co-domain.")
          _ => throw new IllegalArgumentException("Assign to function requires two arguments matching domain and co-domain.")
      }
  }

  class StateCheck(val next : Expression(Bool)) extends Expression(Program) With Unary {
    val subterm = Bool

    def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new StateCheck(f(0))
        else
             throw new IllegalArgumentException("StateCheck requires one argument of type Expression(Bool).")
        _ => throw new IllegalArgumentException("StateCheck requires one argument of type Expression(Bool).")
      }
  }


  class ContinuousEvolution(val differentialEquation : Expression(Bool), val evolutionConstraint : Expression(Bool)) 
    extends Expression(Program) With Binary {
      val subterm = BoolXBool
      val left    = differentialEquation
      val right   = evolutionConstraint

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
          f : Seq[Expression[Sort]] => if (f.length == 2) new ContinuousEvolution(f(0), f(1))
          else
               throw new IllegalArgumentException("ContinuousEvolution requires two argument of type Expression(Bool).")
          _ => throw new IllegalArgumentException("ContinuousEvolution requires two argument of type Expression(Bool).")
      }
  }


  /**
   * Quantifiers
   */

  abstract class QuantifierSymbol extends TermSymbol
  object Forall extends QuantifierSymbol
  object Exists extends QuantifierSymbol

  class Quantifier[T <: Sort](val quantSymbol : QuantifierSymbol, val nameSymbol : NamedSymbol[T], val next : Expression(Bool)) 
    extends Expression(Bool) with Unary {
      val subsort = Bool

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 1) new Quantifier(quantSymbol, nameSymbol, f(0))
        else
             throw new IllegalArgumentException("Quantifier requires an argument of type Expression(Bool).")
        _ => throw new IllegalArgumentException("Quantifier requires an argument of type Expression(Bool).")
      }
  }

  /**
   * Sequent
   *=========
   */
  class Sequent    (val variables : List[NamedSymbol[Sort]], val left : Expression(Bool), val right : Expression(Bool))
    extends Expression(Bool) with Binary {
      val subsort = BoolXBool

      def apply(subexpressions : Expression[Sort]*) = subexpressions match {
        f : Seq[Expression[Sort]] => if (f.length == 2) new Sequent(variables, f(0), f(1))
        else
             throw new IllegalArgumentException("Sequent construction requires two arguments of type Expression(Bool).")
        _ => throw new IllegalArgumentException("Sequent construction requires two arguments of type Expression(Bool).")
      }
  }


  /*********************************************************************************
   * Proof Tree
   *********************************************************************************
   */

  /**
   * Rule
   *======
   */

  sealed abstract class Rule extends (Sequent => List[Sequent])

  /**
   * Proof Tree
   *============
   */

  sealed class ProofNode protected (val sequent : Sequent, val parent : ProofNode) {

    case class ProofStep(rule : Rule, subgoals : List[ProofNode])

    @volatile private var alternatives : List[ProofStep] = Nil

    /* must not be invoked when there is no alternative */
    def getStep : ProofStep = alternatives match {
      List(h, t) => h
      Nil        => throw new IllegalArgumentException("getStep can only be invoked when there is at least one alternative.")
    }

    private def prepend(r : Rule, s : List[ProofNode]) {
      this.synchronized {
        alternatives = ProofStep(r, s) :: alternatives;
      }
    }

    def prune(n : Int) {
      this.synchronized {
        if (n < alternatives.length)
          alternatives = alternatives.take(n-1) ++ alternatives.drop(n)
        else
          throw new IllegalArgumentException("Pruning an alternative from a proof tree requires this alternative to exists.")
      }
    }

    def apply(rule : Rule) : ProofNode = {
      val result = rule.apply(sequent).map(new ProofNode(_, this))
      prepend(rule, result)
      return this
    }
  }

  class RootNode(sequent : Sequent) extends ProofNode(sequent, null)

  /*********************************************************************************
   * Proof Rules
   *********************************************************************************
   */






  /**
   *================================================================================
   */

  def main(args : Array[String]) {
  }

} /* Core */
