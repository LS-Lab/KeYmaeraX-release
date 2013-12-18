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
  class EnumT(name : String, values : List[String])              extends S[EnumT]

  /* used to define pairs of sorts. That is the pair sort is of type L x R */
  class PairT[L <: Sort, R <: Sort](val left : L, val right : R) extends S[PairT[L,R]] {
    override def equals(other : Any) = other match {
      case that : PairT[L, R] => left == that.left && right == that.right
      case _ => false
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
  trait Atom[T <: Sort] extends Expression[T] {
    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A = 
          down(this, ctx)
  }

  /* unary expression */
  trait Unary[D <: Sort, T <: Sort] extends Expression[T] {
    val nSort : D
    val next    : Expression[D]

    applicable
    @elidable(ASSERTION) def applicable = require(nSort == next.sort, "Sort Mismatch in Unary Expression")

    def reduce[A](up : (Expression[Sort], Context) => Boolean, down : (Expression[Sort], Context, A*) => A)(ctx : Context) : A =
          if (up(this, ctx)) down(this, ctx, next.reduce(up, down)(ctx.next)) else down(this, ctx)

    def subexpressions() : Seq[Expression[Sort]] = Seq(next)
  }

  /* binary expression (n-ary is encoded as binary of binary of ... */
  trait Binary[L <: Sort, R <: Sort, T <: Sort] extends Expression[T] {
    val nSort : PairT[L, R]
    val left  : Expression[L]
    val right : Expression[R]

    applicable
    @elidable(ASSERTION) def applicable =
          require(nSort.left == left.sort && nSort.right == right.sort, "Sort Mismatch in Binary Expression")

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
  class Random[T <: Sort](sort : T) extends Expression(sort) with Atom[T]

  /* Constant of scala type A cast into sort T */
  class Constant[T <: Sort, A](sort : T, val value : A) extends Expression(sort) with Atom[T]

  /* convenience wrappers for boolean / real constants */
  val TrueEx  = new Constant(Bool, true)
  val FalseEx = new Constant(Bool, false)

  class Number[T <: S[RealT]](sort : T, value : BigDecimal) extends Constant(sort, value)

  /* value of variable */
  class Value[T <: Sort](val variable : Variable[T]) extends Expression(variable.sort) with Atom[T]

  /* function application */
  class Apply[D <: Sort, T <: Sort](val function : FunctionVar[D, T], val next : Expression[D])
             extends Expression(function.sort) with Unary[D,T] { val nSort = function.domain }

  /* combine subexpressions into a vector */
  class Vector[L <: Sort, R <: Sort](val nSort : PairT[L, R], val left : Expression[L], val right : Expression[R])
    extends Expression(nSort) with Binary[L, R, PairT[L, R]]

  /* extract elements from a vector expression */
  class Left [L <: Sort, R <: Sort](val nSort : PairT[L, R], val next : Expression[PairT[L, R]]) 
    extends Expression(nSort.left)  with Unary[PairT[L, R], L]
  class Right[L <: Sort, R <: Sort](val nSort : PairT[L, R], val next : Expression[PairT[L, R]]) 
    extends Expression(nSort.right) with Unary[PairT[L, R], R]

  /**
   * Formulas (aka Terms)
   *======================
   */
  /* Bool -> Bool */
  abstract class UnaryFormula  extends Expression(Bool) with Unary [BoolT, BoolT]       { val nSort = Bool }
  /* Bool x Bool -> Bool */
  abstract class BinaryFormula extends Expression(Bool) with Binary[BoolT, BoolT, BoolT]{ val nSort = BoolXBool }

  class Not        (val next : Expression[BoolT]) extends UnaryFormula
  class And        (val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula
  class Or         (val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula
  class Implies    (val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula
  class Equivalent (val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula

  abstract class BinaryRelation[T <: Sort](val eSort : T) 
    extends Expression(Bool) with Binary[T, T, BoolT] { val nSort = new PairT(eSort, eSort) }

  /* equality */
  class Equals[T <: Sort]   (eSort : T, val left : Expression[T], val right : Expression[T]) extends BinaryRelation(eSort)
  class NotEquals[T <: Sort](eSort : T, val left : Expression[T], val right : Expression[T]) extends BinaryRelation(eSort)

  /* comparisson */
  class GreaterThan  [R <: S[RealT]](eSort : R, val left : Expression[R], val right : Expression[R]) extends BinaryRelation(eSort)
  class LessThan     [R <: S[RealT]](eSort : R, val left : Expression[R], val right : Expression[R]) extends BinaryRelation(eSort)
  class GreaterEquals[R <: S[RealT]](eSort : R, val left : Expression[R], val right : Expression[R]) extends BinaryRelation(eSort)
  class LessEquals   [R <: S[RealT]](eSort : R, val left : Expression[R], val right : Expression[R]) extends BinaryRelation(eSort)

  /* temporal */
  class Globally (val next : Expression[BoolT]) extends UnaryFormula /* []\Phi e.g., in [\alpha] []\Phi */
  class Finally  (val next : Expression[BoolT]) extends UnaryFormula /* <>\Phi e.g., in [\alpha] <>\Phi */

  /**
   * Games
   *=======
   */

  /* Modality */
  class Modality (val left : Expression[GameT], val right : Expression[BoolT]) 
    extends Expression(Bool) with Binary[GameT, BoolT, BoolT] { val nSort = GameXBool }

  abstract class UnaryGame  extends Expression(Game) with Unary[GameT, GameT]         {val nSort = Game }
  abstract class BinaryGame extends Expression(Game) with Binary[GameT, GameT, GameT] {val nSort = GameXGame }

  /* Games */
  class BoxModality     (val next : Expression[ProgramT]) extends Expression(Game) with Unary[ProgramT, GameT]{ val nSort = Program }
  class DiamondModality (val next : Expression[ProgramT]) extends Expression(Game) with Unary[ProgramT, GameT]{ val nSort = Program }

  class BoxStar         (val next : Expression[GameT])    extends UnaryGame
  class DiamondStar     (val next : Expression[GameT])    extends UnaryGame
  class SequenceGame    (val left : Expression[GameT], val right : Expression[GameT]) extends BinaryGame
  class DisjunctGame    (val left : Expression[GameT], val right : Expression[GameT]) extends BinaryGame
  class ConjunctGame    (val left : Expression[GameT], val right : Expression[GameT]) extends BinaryGame

  /**
   * Programs
   *==========
   */

  abstract class UnaryProgram  extends Expression(Program) with Unary [ProgramT, ProgramT]           {val nSort = Program }
  abstract class BinaryProgram extends Expression(Program) with Binary[ProgramT, ProgramT, ProgramT] {val nSort = ProgramXProgram }

  class Sequence(val left : Expression[ProgramT], val right : Expression[ProgramT]) extends BinaryProgram
  class Choice  (val left : Expression[ProgramT], val right : Expression[ProgramT]) extends BinaryProgram
  class Parallel(val left : Expression[ProgramT], val right : Expression[ProgramT]) extends BinaryProgram
  class Loop    (val next : Expression[ProgramT])                                   extends UnaryProgram

  class Assign[T <: Sort](val variable : Variable[T], val next : Expression[T]) 
    extends Expression(Program) with Unary[T, ProgramT] {val nSort = variable.sort }

  class AssignFn[D <: Sort, T <: Sort](val function : FunctionVar[D, T], val left : Expression[D], val right : Expression[T])
    extends Expression(Program) with Binary[D, T, ProgramT] { val nSort = new PairT(function.domain, function.sort) }

  class StateCheck(val next : Expression[BoolT]) extends Expression(Program) with Unary[BoolT, ProgramT] { val nSort = Bool }

  /* left = differential algebraic formula; right = evolution domain constraint */
  class ContinuousEvolution(val left : Expression[BoolT], val right : Expression[BoolT])
    extends Expression(Program) with Binary[BoolT, BoolT, ProgramT] { val nSort = BoolXBool }

  /**
   * Quantifiers
   *=============
   */

  abstract class Quantifier[T <: Sort](val variable : NamedSymbol[T], val next : Expression[BoolT]) extends UnaryFormula

  class Forall[T <: Sort](variable : NamedSymbol[T], next : Expression[BoolT]) extends Quantifier(variable, next)
  class Exists[T <: Sort](variable : NamedSymbol[T], next : Expression[BoolT]) extends Quantifier(variable, next)

  /**
   * Sequent
   *=========
   */

  class Antedecent(val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula
  class Succedent (val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula
  class Sequent   (val context : List[NamedSymbol[Sort]], val left : Expression[BoolT], val right : Expression[BoolT]) extends BinaryFormula


/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

  object Expression {

    def identity_map() = true

    def !   (next : Expression[BoolT]) = new Not(next)
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
