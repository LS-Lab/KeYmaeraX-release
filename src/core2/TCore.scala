/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
//package edu.cmu.cs.ls.keymaera.core


import scala.annotation.elidable
import scala.annotation.elidable._

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

  }

  val RealXReal = new PairT(Real, Real)
  val BoolXBool = new PairT(Bool, Bool)

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

  abstract class NamedSymbol[T <: Sort](val name : String, val sort : T) {

    private val id : Int = NameCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.type_object == x.type_object

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  class Variable[T <: Sort] (name : String, sort : T)     extends NamedSymbol[T](name, type_object)

  class FunctionVar[D <: Sort, T <: Sort] (name : String, val domain : D, sort : T)
                                                          extends NamedSymbol[T](name, type_object)

  /*--------------------------------------------------------------------------------*/

  /* HERE !!! */

  /*--------------------------------------------------------------------------------*/

  class RealVar      (name : String) extends Variable   (name, Real)
  class RealFnUnary  (name : String) extends FunctionVar(name, Real, Real)
  class RealFnBinary (name : String) extends FunctionVar(name, RealXReal, Real)

  class BoolVar         (name : String) extends Variable   (name, Bool)
  class PredicateUnary  (name : String) extends FunctionVar(name, Bool, Bool)
  class PredicateBinary (name : String) extends FunctionVar(name, BoolXBool, Bool)

  /**
   * Constant, Variable and Function Expressions
   */

  /* Constant of scala type A cast into sort T */
  class Constant[T <: Sort, A](val sort : T, val value : A) extends Expression(sort) with Atom[T]

  /* convenience wrappers for boolean / real constants */
  val TrueEx  = new Constant[_, Boolean](Bool, true)
  val FalseEx = new Constant[_, Boolean](Bool, false)

  class Number(value : Int)    extends Constant(Real, value)
  class Number(value : Double) extends Constant(Real, value)

  /* value of variable */
  class Value[T <: Sort](val variable : Variable[T]) extends Expression(variable.sort) with Atom[T]

  /* convenience wrappers for real / boolean values */
  class RealValue(variable : RealVar) extends Value(Real, variable)
  class BoolValue(variable : BoolVar) extends Value(Bool, variable)

  /* function application */
  class Apply[D <: Sort, T <: Sort](val function : FunctionVar[D, T], val parameter : Expression(function.domain))
             extends Expression(function.sort) extends Unary[D, T] { val subsort = function.domain }

  class Vector[T <: PairT](val subsort : T, val left : Expression(subsort.left), val right : Expression(subsort.right))
              extends Expression(subsort) with Binary

  abstract class BinaryReal[T <: S[RealT]](val function : FunctionVar[PairT[T, T],T],
                                           val left : Expression(function.domain.left), val right : Expression(function.domain.right))
                 extends Apply(function, new Vector(function.domain, left, right)) with Binary { val subsort = function.domain }

  class Plus[T <: S[RealT]](val subsort : T, val left : Expression(subsort), val right : Expression(subsort))
                 extends BinaryReal(new FunctionVar("+", 




/*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*/


  /* vector functions */


  class Left [T <: PairT](val subsort : T, val next : Expression(subsort)) extends Expression(subsort.left)  with Unary
  class Right[T <: PairT](val subsort : T, val next : Expression(subsort)) extends Expression(subsort.right) with Unary


/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
*/





  /* Formula */
  abstract class Formula      extends Expression[BoolT.type](BoolT)
  abstract class UnaryGenericFormula [T <: Sort]           (val expr : Expression[T])
                              extends Formula with Unary[T, BoolT.type]
  abstract class BinaryGenericFormula[L <: Sort, R <: Sort](val left : Expression[L], val right : Expression[R])
                              extends Formula with Binary[L, R, BoolT.type]
  abstract class UnaryFormula(val expr : Formula)
                              extends Formula with Unary[BoolT.type, BoolT.type]
  abstract class BinaryFormula(val left : Formula, val right : Formula)
                              extends Formula with Binary[BoolT.type, BoolT.type, BoolT.type]

  /* Real */
  abstract class Real         extends Expression[RealT.type](RealT)
  abstract class UnaryReal    [T <: Sort]           (val expr : Expression[T])
                              extends Real with Unary[T, RealT.type]
  abstract class BinaryReal   [L <: Sort, R <: Sort](val left : Expression[L], val right : Expression[R])
                              extends Real with Binary[L, R, RealT.type]

  /* Game */
  abstract class Game         extends Expression[GameT.type](GameT)
  /* Program */
  abstract class Program      extends Expression[ProgramT.type](ProgramT)





/**
 * Differential Logic
 */
  class Value[T <: Sort](val variable : Variable[T]) extends Expression[T](variable.type_object) with Atom[T] {
    def apply(e : Expression[Sort]*) = new Value(variable)
  }

  class Implies    (left : Formula, right : Formula) extends BinaryFormula(left, right) {
    def apply(e : Expression[Sort]*) = e match {
      case x : Seq[Formula] => if (x.length == 2) new Implies(x(0), x(1)) else /* XXX */ 
      case _ => /* XXX */

  }

  class And        (left : Formula, right : Formula) extends BinaryFormula(left, right) {
    def apply (e : Expression[Sort]*) = new And(e(0).asInstanceOf[Formula], e(1).asInstanceOf[Formula])
  }

  class Antedecent (left : Formula, right : Formula) extends BinaryFormula(left, right) {
    def apply (e : Expression[Sort]*) = new Antedecent(e(0).asInstanceOf[Formula], e(1).asInstanceOf[Formula])
  }

  class Succedent  (left : Formula, right : Formula) extends BinaryFormula(left, right) {
    def apply (e : Expression[Sort]*) = new Succedent(e(0).asInstanceOf[Formula], e(1).asInstanceOf[Formula])
  }

  class Sequent    (variables : List[Variable[Sort]], left : Formula, right : Formula) extends BinaryFormula(left, right) {

    def apply (e : Expression[Sort]*) = new Sequent(variables, e(0).asInstanceOf[Formula], e(1).asInstanceOf[Formula])

    def rename_doubles() = {
      /* if variable with same user name is in variables;
       * add with new variable object with new user name and remove old one
       * replace value objects etc. in left and right to point to new variable object wherever they contained the old one
       */
    }

    def merge(s : Sequent) = {
/*      val s2 = new Sequent (this.variables :: s.variables, And(this.left, s.left), And(this.right, s.right));
      return s2.rename_doubles()
      */
    }
  }


/**
 * Proof Tree
 */

  type Rule = ((Sequent) => List[Sequent])

  class ProofTree(val sequent : Sequent, val parent : Option[ProofTree]) {

    @volatile private var rule     : Rule = null
    @volatile private var subgoals : List[ProofTree] = Nil

    def getRule     : Rule             = rule
    def getSubgoals : List[ProofTree] = subgoals

    private def prepend(r : Rule, s : List[ProofTree]) {
      this.synchronized {
        subgoals = s
        rule     = r
      }
    }

    /**
     * throws timeout / rule application failed / ...
     */ 
    def apply(rule : Rule) = {
//      var subgoals = rule(sequent).map...
//      prepend(rule, subgoals)
    }

    def prune() = {
      rule = null
      subgoals = Nil
    }

  }


/**
 *================================================================================
 */

  def main(args : Array[String]) {
  }

}
