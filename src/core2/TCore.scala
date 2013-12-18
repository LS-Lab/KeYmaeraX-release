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

/* sort of reals: 0, 1, 2.73 */
class RealT                                                    extends S[RealT]

/* sort of games */
class GameT                                                    extends S[GameT]

/* sort of hybrid probrams */
class ProgramT                                                 extends S[ProgramT]

/* user defined sort */
class UserT(name : String)                                     extends S[UserT]
/* user defined enum sort. values is the list of named constants of this enum */
class EnumT(name : String, values : List[String])              extends S[EnumT]

/* used to define pairs of sorts. That is the pair sort is of type L x R */
class PairT[L <: Sort, R <: Sort](val left : L, val right : R) extends S[PairT[L,R]] {
  override def equals(other : Any) = other match {
    case that : PairT[L, R] => left == that.left && right == that.right
    case _ => false
  }
}

/* subtype of a given type; for example TimeT = Subtype("the time that passes", Real) */
class Subtype[T <: Sort](name : String, sort : T)              extends S[T]

object PredefinedSorts {
  val Bool    = new BoolT
  val Real    = new RealT
  val Game    = new GameT
  val Program = new ProgramT

  val RealXReal       = new PairT(Real, Real)
  val BoolXBool       = new PairT(Bool, Bool)
  val GameXBool       = new PairT(Game, Bool)
  val GameXGame       = new PairT(Game, Game)
  val ProgramXProgram = new PairT(Program, Program)
}

import PredefinedSorts._

class Core {

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
  }

  /* atom / leaf expression */
  abstract class Atom[T <: Sort](sort : T) extends Expression(sort) {
    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A = 
          down(this, ctx)
  }

  /* unary expression */
  abstract class Unary[D <: Sort, T <: Sort](sort : T, val nSort : D, val next : Expression[D]) extends Expression(sort) {
    @elidable(ASSERTION) def applicable = require(nSort == next.sort, "Sort Mismatch in Unary Expression: " + nSort + " " + next.sort)
    applicable

    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A =
          if (up(this, ctx)) down(this, ctx, next.reduce(up, down)(ctx.next)) else down(this, ctx)

    def subexpressions() : Seq[Expression[Sort]] = Seq(next)
  }

  /* binary expression (n-ary is encoded as binary of binary of ... */
  abstract class Binary[L <: Sort, R <: Sort, T <: Sort]
                       (sort : T, val nSort : PairT[L, R], val left : Expression[L], val right : Expression[R]) extends Expression(sort) {

    @elidable(ASSERTION) def applicable =
          require(nSort.left == left.sort && nSort.right == right.sort, "Sort Mismatch in Binary Expression")
    applicable

    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A =
          if (up(this, ctx)) down(this, ctx, left.reduce(up, down)(ctx.left), right.reduce(up, down)(ctx.right))
          else down(this, ctx)

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

    @elidable(ASSERTION) def applicable = require(next_id < Int.MaxValue, "Error: too many variable objects; counter overflow")

    def next() : Int = {
      this.synchronized {
        applicable
        next_id = next_id + 1;
        return next_id;
      }
    }
  }

  abstract class NamedSymbol[+T <: Sort](val name : String, val sort : T) {

    private val id : Int = NameCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.sort == x.sort

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  class Variable[T <: Sort] (name : String, sort : T) extends NamedSymbol[T](name, sort)

  class FunctionVar[D <: Sort, T <: Sort] (name : String, val domain : D, sort : T)
                                                      extends NamedSymbol[T](name, sort)

  /**
   * Constant, Variable and Function Expressions
   *=============================================
   */

  /* The * in nondet. assignments */
  class Random[T <: Sort](sort : T) extends Atom(sort)

  /* Constant of scala type A cast into sort T */
  class Constant[T <: Sort, A](sort : T, val value : A) extends Atom(sort)

  /* convenience wrappers for boolean / real constants */
  val TrueEx  = new Constant(Bool, true)
  val FalseEx = new Constant(Bool, false)

  class Number[T <: S[RealT]](sort : T, value : BigDecimal) extends Constant(sort, value)

  /* value of variable */
  class Value[T <: Sort](val variable : Variable[T]) extends Atom(variable.sort)

  /* function application */
  class Apply[D <: Sort, T <: Sort](val function : FunctionVar[D, T], next : Expression[D])
             extends Unary(function.sort, function.domain, next)

  /* combine subexpressions into a vector */
  class Vector[L <: Sort, R <: Sort](nSort : PairT[L, R], left : Expression[L], right : Expression[R]) extends Binary(nSort, nSort, left, right)

  /* extract elements from a vector expression */
  class Left [L <: Sort, R <: Sort](nSort : PairT[L, R], next : Expression[PairT[L, R]]) extends Unary(nSort.left, nSort, next)
  class Right[L <: Sort, R <: Sort](nSort : PairT[L, R], next : Expression[PairT[L, R]]) extends Unary(nSort.right, nSort, next)

  /**
   * Formulas (aka Terms)
   *======================
   */
  /* Bool -> Bool */
  abstract class UnaryFormula(next : Expression[BoolT]) extends Unary(Bool, Bool, next)
  /* Bool x Bool -> Bool */
  abstract class BinaryFormula(left : Expression[BoolT], right : Expression[BoolT]) extends Binary(Bool, BoolXBool, left, right)

  class Not        (next : Expression[BoolT]) extends UnaryFormula(next)
  class And        (left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)
  class Or         (left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)
  class Implies    (left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)
  class Equivalent (left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)

  abstract class BinaryRelation[T <: Sort](val eSort : T, left : Expression[T], right : Expression[T])
    extends Binary(Bool, new PairT(eSort, eSort), left, right)

  /* equality */
  class Equals[T <: Sort]   (eSort : T, left : Expression[T], right : Expression[T]) extends BinaryRelation(eSort, left, right)
  class NotEquals[T <: Sort](eSort : T, left : Expression[T], right : Expression[T]) extends BinaryRelation(eSort, left, right)

  /* comparisson */
  class GreaterThan  [R <: S[RealT]](eSort : R, left : Expression[R], right : Expression[R]) extends BinaryRelation(eSort, left, right)
  class LessThan     [R <: S[RealT]](eSort : R, left : Expression[R], right : Expression[R]) extends BinaryRelation(eSort, left, right)
  class GreaterEquals[R <: S[RealT]](eSort : R, left : Expression[R], right : Expression[R]) extends BinaryRelation(eSort, left, right)
  class LessEquals   [R <: S[RealT]](eSort : R, left : Expression[R], right : Expression[R]) extends BinaryRelation(eSort, left, right)

  /* temporal */
  class Globally (next : Expression[BoolT]) extends UnaryFormula(next) /* []\Phi e.g., in [\alpha] []\Phi */
  class Finally  (next : Expression[BoolT]) extends UnaryFormula(next) /* <>\Phi e.g., in [\alpha] <>\Phi */

  /**
   * Real Expressions
   *==================
   */

  abstract class UnaryReal [R <: S[RealT]](sort : R, next : Expression[R]) extends Unary(sort, sort, next)
  abstract class BinaryReal[R <: S[RealT]](sort : R, left : Expression[R], right : Expression[R]) extends Binary(sort, new PairT(sort, sort), left, right) 

  class Neg     [R <: S[RealT]](sort : R, next : Expression[R]) extends UnaryReal(sort, next)
  class Add     [R <: S[RealT]](sort : R, left : Expression[R], right : Expression[R]) extends BinaryReal(sort, left, right)
  class Subtract[R <: S[RealT]](sort : R, left : Expression[R], right : Expression[R]) extends BinaryReal(sort, left, right)
  class Multiply[R <: S[RealT]](sort : R, left : Expression[R], right : Expression[R]) extends BinaryReal(sort, left, right)
  class Divide  [R <: S[RealT]](sort : R, left : Expression[R], right : Expression[R]) extends BinaryReal(sort, left, right)

  class Derivate[R <: S[RealT]](sort : R, next : Expression[R]) extends UnaryReal(sort, next)

  /**
   * Games
   *=======
   */

  /* Modality */
  class Modality (left : Expression[GameT], right : Expression[BoolT]) extends Binary(Bool, GameXBool, left, right)

  abstract class UnaryGame  (next : Expression[GameT]) extends Unary(Game, Game, next)
  abstract class BinaryGame (left : Expression[GameT], right : Expression[GameT]) extends Binary(Game, GameXGame, left, right)

  /* Games */
  class BoxModality     (next : Expression[ProgramT]) extends Unary(Game, Program, next)
  class DiamondModality (next : Expression[ProgramT]) extends Unary(Game, Program, next)

  class BoxStar         (next : Expression[GameT])    extends UnaryGame(next)
  class DiamondStar     (next : Expression[GameT])    extends UnaryGame(next)
  class SequenceGame    (left : Expression[GameT], right : Expression[GameT]) extends BinaryGame(left, right)
  class DisjunctGame    (left : Expression[GameT], right : Expression[GameT]) extends BinaryGame(left, right)
  class ConjunctGame    (left : Expression[GameT], right : Expression[GameT]) extends BinaryGame(left, right)

  /**
   * Programs
   *==========
   */

  abstract class UnaryProgram  (next : Expression[ProgramT]) extends Unary(Program, Program, next) 
  abstract class BinaryProgram (left : Expression[ProgramT], right : Expression[ProgramT]) extends Binary(Program, ProgramXProgram, left, right)

  class Sequence(left : Expression[ProgramT], right : Expression[ProgramT]) extends BinaryProgram(left, right)
  class Choice  (left : Expression[ProgramT], right : Expression[ProgramT]) extends BinaryProgram(left, right)
  class Parallel(left : Expression[ProgramT], right : Expression[ProgramT]) extends BinaryProgram(left, right)
  class Loop    (next : Expression[ProgramT])                               extends UnaryProgram(next)

  class Assign[T <: Sort](val variable : Variable[T], next : Expression[T]) extends Unary(Program, variable.sort, next)

  class AssignFn[D <: Sort, T <: Sort](val function : FunctionVar[D, T], left : Expression[D], right : Expression[T])
    extends Binary(Program, new PairT(function.domain, function.sort), left, right)

  class StateCheck(next : Expression[BoolT]) extends Unary(Program, Bool, next)

  /* left = differential algebraic formula; right = evolution domain constraint */
  class ContinuousEvolution(left : Expression[BoolT], right : Expression[BoolT]) extends Binary(Program, BoolXBool, left, right)

  /**
   * Quantifiers
   *=============
   */

  abstract class Quantifier[T <: Sort](val variable : NamedSymbol[T], next : Expression[BoolT]) extends UnaryFormula(next)

  class Forall[T <: Sort](variable : NamedSymbol[T], next : Expression[BoolT]) extends Quantifier(variable, next)
  class Exists[T <: Sort](variable : NamedSymbol[T], next : Expression[BoolT]) extends Quantifier(variable, next)

  /**
   * Sequent
   *=========
   */

  class Antedecent(left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)
  class Succedent (left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)
  class Sequent   (val context : List[NamedSymbol[Sort]], left : Expression[BoolT], right : Expression[BoolT]) extends BinaryFormula(left, right)


/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

  def identity_map() = true

  object Helpers {

    def Not(e : Expression[BoolT]) = new Not(e)

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
      case List(h, t) => h
      case Nil        => throw new IllegalArgumentException("getStep can only be invoked when there is at least one alternative.")
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

  class RootNode(sequent : Sequent) extends ProofNode(sequent, null) {

  }

  /*********************************************************************************
   * Proof Rules
   *********************************************************************************
   */

} /* Core */

/**
 *==================================================================================
 *==================================================================================
 */



object TCore {

  def main(args : Array[String]) {

    println("=========== STARTING ===========")

    val core = new Core()

    import core._
    import core.Helpers._

    val Time  = new Subtype("The time that is.", Real)
    val Speed = new Subtype("Really fast.", Real)

    val ex1 = Not(TrueEx)

    /* True |= q => (p => q) */
    val p = new Variable("p", Bool)
    val q = new Variable("q", Bool)
    val seq = new Sequent(List(p, q), TrueEx, new Implies(new Value(q), new Implies(new Value(p), new Value(q))))


    println (Not(TrueEx))
//    println (new Neg(Time, new Random(Speed)))

  }

}
