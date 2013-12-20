/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
//package edu.cmu.cs.ls.keymaera.core

/**
 * Abbreviations
 *===============
 *
 * The following abbreviations are relevant for the core:
 *
 * C = codomain sort
 * D = domain sort
 * L = left child sort
 * R = right child sort
 *
 * sort   : C = Sort object for codomain C
 * domain : D = Sort object for domain D
 */

/**
 * Todos
 *=======
 * 1) First class * Expression: * also in if(*) \alpha else \beta vs. nondet. assignment forms (:= *)
 * 2) Assignment Expressions:   := as assign(Expr, Expr) (e.g., assign(apply(f, param), term) but also (x)' := 42
 *                                    assign(x, term) resp. assign(f, param, term)
 *                                    quant. assign vs. vector assign with "large" vector
 *                                    quant. assign as function update f = g with [x := y]
 * 3) [HELP ME] differential equations in some normal form (I don't remember the details)
 */

/**
 * Points to Discuss
 *===================
 * 1) Currently we support efficicent type based mapping but no constructor patterns
 *    (i.e., case e : Add[_] instead of case Add(sort, left, right). Members are still
 *    accessible (e.g., through e.sort). Alternatively we could add apply / unapply
 *    methods which degrade performance and increase codesize or turn some classes into
 *    case classes, which increases their memory footprint mainly due to successive
 *    overwrite.
 * 2) Modality tracks variables that are bound in game / program: simplifies building
 *    up context but may require modality to change more often
 */

import scala.annotation.elidable
import scala.annotation.elidable._
import scala.language.existentials

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
class TupleT[L <: Sort, R <: Sort](val left : L, val right : R) extends S[TupleT[L,R]] {
  override def equals(other : Any) = other match {
    case that : TupleT[L, R] => left == that.left && right == that.right
    case _ => false
  }
}

/* subtype of a given type; for example TimeT = Subtype("the time that passes", Real) */
class Subtype[C <: Sort](name : String, sort : C)              extends S[C]

object PredefinedSorts {
  val Bool    = new BoolT
  val Real    = new RealT
  val Game    = new GameT
  val Program = new ProgramT

  val RealXReal       = new TupleT(Real, Real)
  val BoolXBool       = new TupleT(Bool, Bool)
  val GameXBool       = new TupleT(Game, Bool)
  val GameXGame       = new TupleT(Game, Game)
  val ProgramXProgram = new TupleT(Program, Program)
}

import PredefinedSorts._

/**
 * Context
 *=========
 * trait used to collect and maintain context information while traversing sequents and expressions.
 */
trait Context[E] {
  /* invoked when the sequent or expression is traversed to the subexpression of a unary term */
  def child(expr : E) : Context[E]
  /* invoked when the sequent or expression is traversed to the left subexpression of a binary term */
  def left (expr : E) : Context[E]
  /* invoked when the sequent or expression is traversed to the right subexpression of a binary term */
  def right(expr : E) : Context[E]
}

class Core {

  /**
   * Expression infrastructure
   *===========================
   * (see TypeSafety.scala for an explaination how the Expression builtin typechecking
   * mechanism works. Each expression may replicate itself with apply and adheres to the
   * generic recursion structure via the function reduce.
   */
  sealed abstract class Expr[+C <: Sort](val sort : C) extends Annotable {

    /**
     * Reduce
     *--------
     * recurse upward through the expression data structure while
     * building up the context through ctx.child, ctx.left and ctx.right
     * until at the end of a given path up evaluates to false. From there
     * on, traverse down mapping the expression and the already reduced
     * subexpressions to an element of type A.
     *
     * For example
     *   size = reduce[Int]((_,_) => true, (_, _, summands : Int*) => 1 + sum(summands))(DefaultContext)
     * computes the size of the expression.
     */
    def reduce[A](continue : (Expr[Sort], Context[Expr[Sort]]) => Boolean,
                  down : (Expr[Sort], Context[Expr[Sort]], List[A]) => A, ctx : Context[Expr[Sort]]) : A

  }

  /* atom / leaf expression */
  abstract class Atom[C <: Sort](sort : C) extends Expr(sort) {

    def reduce[A](continue : (Expr[Sort], Context[Expr[Sort]]) => Boolean,
                  down : (Expr[Sort], Context[Expr[Sort]], List[A]) => A, ctx : Context[Expr[Sort]]) : A =
      down(this, ctx, Nil)

  }

  /* unary expression */
  abstract class Unary[D <: Sort, C <: Sort](sort : C, val domain : D, val child : Expr[D]) extends Expr(sort) {

    applicable

    @elidable(ASSERTION) def applicable = require(domain == child.sort, "Sort Mismatch in Unary Expr: " + domain + " " + child.sort)


    def reduce[A](continue : (Expr[Sort], Context[Expr[Sort]]) => Boolean, 
                  down : (Expr[Sort], Context[Expr[Sort]], List[A]) => A, ctx : Context[Expr[Sort]]) : A =
      if (continue(this, ctx)) down(this, ctx, List(child.reduce(continue, down, ctx.child(this)))) else down(this, ctx, Nil)

  }

  /* binary expression (n-ary is encoded as binary of binary of ... */
  abstract class Binary[L <: Sort, R <: Sort, C <: Sort](sort : C, val domain : TupleT[L, R], val left : Expr[L], val right : Expr[R]) extends Expr(sort) {

    applicable

    @elidable(ASSERTION) def applicable = 
          require(domain.left == left.sort && domain.right == right.sort, "Sort Mismatch in Binary Expr")

    def reduce[A](continue : (Expr[Sort], Context[Expr[Sort]]) => Boolean, 
                  down : (Expr[Sort], Context[Expr[Sort]], List[A]) => A, ctx : Context[Expr[Sort]]) : A =
      if (continue(this, ctx)) down(this, ctx, List(left.reduce (continue, down, ctx.left (this)),
                                                    right.reduce(continue, down, ctx.right(this)))) else down(this, ctx, Nil)
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

  abstract class NamedSymbol[+C <: Sort](val name : String, val sort : C) {

    private val id : Int = NameCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.sort == x.sort

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  class Variable[C <: Sort] (name : String, sort : C) extends NamedSymbol[C](name, sort)

  class FunctionVar[+D <: Sort, C <: Sort] (name : String, val domain : D, sort : C) extends NamedSymbol[C](name, sort)

  /**
   * Constant, Variable and Function Expressions
   *=============================================
   */

  /* The * in nondet. assignments */
  // class Random[C <: Sort](sort : C) extends Atom(sort) /* SOONISH BUT NOT NOW */

  /* Constant of scala type A cast into sort C */
  class Constant[C <: Sort, A](sort : C, val value : A) extends Atom(sort)

  /* convenience wrappers for boolean / real constants */
  val TrueEx  = new Constant(Bool, true)
  val FalseEx = new Constant(Bool, false)

  class Number[C <: S[RealT]](sort : C, value : BigDecimal) extends Constant(sort, value)

  /* value of variable */
  class Value[C <: Sort](val variable : Variable[C]) extends Atom(variable.sort)

  /* function application */
  class Apply[D <: Sort, C <: Sort](val function : FunctionVar[D, C], child : Expr[D])
             extends Unary(function.sort, function.domain, child)

  /* combine subexpressions into a vector */
  class Pair[L <: Sort, R <: Sort](domain : TupleT[L, R], left : Expr[L], right : Expr[R]) extends Binary(domain, domain, left, right)

  /* extract elements from a vector expression */
  class Left [L <: Sort, R <: Sort](domain : TupleT[L, R], child : Expr[TupleT[L, R]]) extends Unary(domain.left, domain, child)
  class Right[L <: Sort, R <: Sort](domain : TupleT[L, R], child : Expr[TupleT[L, R]]) extends Unary(domain.right, domain, child)

  /**
   * Formulas (aka Terms)
   *======================
   */
  /* Bool -> Bool */
  abstract class UnaryFormula(child : Expr[BoolT]) extends Unary(Bool, Bool, child)
  /* Bool x Bool -> Bool */
  abstract class BinaryFormula(left : Expr[BoolT], right : Expr[BoolT]) extends Binary(Bool, BoolXBool, left, right)

  class Not   (child : Expr[BoolT]) extends UnaryFormula(child)
  class And   (left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)
  class Or    (left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)
  class Imply (left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)
  class Equiv (left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)

  abstract class BinaryRelation[C <: Sort](domain : C, left : Expr[C], right : Expr[C])
    extends Binary(Bool, new TupleT(domain, domain), left, right)

  /* equality */
  class Equals[C <: Sort]   (domain : C, left : Expr[C], right : Expr[C]) extends BinaryRelation(domain, left, right)
  class NotEquals[C <: Sort](domain : C, left : Expr[C], right : Expr[C]) extends BinaryRelation(domain, left, right)

  /* comparisson */
  class GreaterThan  [R <: S[RealT]](domain : R, left : Expr[R], right : Expr[R]) extends BinaryRelation(domain, left, right)
  class LessThan     [R <: S[RealT]](domain : R, left : Expr[R], right : Expr[R]) extends BinaryRelation(domain, left, right)
  class GreaterEquals[R <: S[RealT]](domain : R, left : Expr[R], right : Expr[R]) extends BinaryRelation(domain, left, right)
  class LessEquals   [R <: S[RealT]](domain : R, left : Expr[R], right : Expr[R]) extends BinaryRelation(domain, left, right)

  /* temporal */
  class Globally (child : Expr[BoolT]) extends UnaryFormula(child) /* []\Phi e.g., in [\alpha] []\Phi */
  class Finally  (child : Expr[BoolT]) extends UnaryFormula(child) /* <>\Phi e.g., in [\alpha] <>\Phi */

  /**
   * Real Expressions
   *==================
   */

  abstract class UnaryReal [R <: S[RealT]](sort : R, child : Expr[R]) extends Unary[R, R](sort, sort, child)
  abstract class BinaryReal[R <: S[RealT]](sort : R, left  : Expr[R], right : Expr[R]) extends Binary(sort, new TupleT(sort, sort), left, right) 

  class Neg     [R <: S[RealT]](sort : R, child : Expr[R]) extends UnaryReal(sort, child)
  class Add     [R <: S[RealT]](sort : R, left  : Expr[R], right : Expr[R]) extends BinaryReal(sort, left, right)
  class Subtract[R <: S[RealT]](sort : R, left  : Expr[R], right : Expr[R]) extends BinaryReal(sort, left, right)
  class Multiply[R <: S[RealT]](sort : R, left  : Expr[R], right : Expr[R]) extends BinaryReal(sort, left, right)
  class Divide  [R <: S[RealT]](sort : R, left  : Expr[R], right : Expr[R]) extends BinaryReal(sort, left, right)
  class Exp     [R <: S[RealT]](sort : R, left  : Expr[R], right : Expr[R]) extends BinaryReal(sort, left, right) /* x^y (for "nice" y only) */

  class Derivative[R <: S[RealT]](sort : R, child : Expr[R]) extends UnaryReal(sort, child)
  class FormulaDerivative        (child : Expr[BoolT])       extends UnaryFormula(child)

  /**
   * Games
   *=======
   */

  /* Modality */
  class Modality (val variables : List[NamedSymbol[Sort]], left : Expr[GameT], right : Expr[BoolT]) extends Binary(Bool, GameXBool, left, right)

  abstract class UnaryGame  (child : Expr[GameT]) extends Unary(Game, Game, child)
  abstract class BinaryGame (left : Expr[GameT], right : Expr[GameT]) extends Binary(Game, GameXGame, left, right)

  /* Games */
  class BoxModality     (child : Expr[ProgramT]) extends Unary(Game, Program, child)
  class DiamondModality (child : Expr[ProgramT]) extends Unary(Game, Program, child)

  class BoxStar         (child : Expr[GameT])    extends UnaryGame(child)
  class DiamondStar     (child : Expr[GameT])    extends UnaryGame(child)
  class SequenceGame    (left  : Expr[GameT], right : Expr[GameT]) extends BinaryGame(left, right)
  class DisjunctGame    (left  : Expr[GameT], right : Expr[GameT]) extends BinaryGame(left, right)
  class ConjunctGame    (left  : Expr[GameT], right : Expr[GameT]) extends BinaryGame(left, right)

  /**
   * Programs
   *==========
   */

  abstract class UnaryProgram  (child : Expr[ProgramT]) extends Unary(Program, Program, child) 
  abstract class BinaryProgram (left  : Expr[ProgramT], right : Expr[ProgramT]) extends Binary(Program, ProgramXProgram, left, right)

  class Sequence(left  : Expr[ProgramT], right : Expr[ProgramT]) extends BinaryProgram(left, right)
  class Choice  (left  : Expr[ProgramT], right : Expr[ProgramT]) extends BinaryProgram(left, right)
  class Parallel(left  : Expr[ProgramT], right : Expr[ProgramT]) extends BinaryProgram(left, right)
  class Loop    (child : Expr[ProgramT])                         extends UnaryProgram(child)

/* TODO:
 *
 * - Assign(func, parameter, value) vs. Assign(Apply(func, parameter), value)
 * - need QAssign
 * - nondeterministic assign vs. Assign(Var, Random)
 *
  class Assign[C <: Sort](val variable : Variable[C], child : Expr[C]) extends Unary(Program, variable.sort, child)

  class AssignFn[D <: Sort, C <: Sort](val function : FunctionVar[D, C], left : Expr[D], right : Expr[C])
    extends Binary(Program, new TupleT(function.domain, function.sort), left, right)

  class QAssign ...
  class QAssignFn ...
 */


  class Test(child : Expr[BoolT]) extends Unary(Program, Bool, child)

  /* left = differential algebraic formula; right = evolution domain constraint */
  class ContEvolve(left : Expr[BoolT], right : Expr[BoolT]) extends Binary(Program, BoolXBool, left, right)

  /**
   * Quantifiers
   *=============
   */

  abstract class Quantifier[C <: Sort](val variable : NamedSymbol[C], child : Expr[BoolT]) extends UnaryFormula(child)

  class Forall[C <: Sort](variable : NamedSymbol[C], child : Expr[BoolT]) extends Quantifier(variable, child)
  class Exists[C <: Sort](variable : NamedSymbol[C], child : Expr[BoolT]) extends Quantifier(variable, child)

  /**
   * Sequent
   *=========
   */

  class Antedecent(left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)
  class Succedent (left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)
  class Sequent   (val context : List[NamedSymbol[Sort]], left : Expr[BoolT], right : Expr[BoolT]) extends BinaryFormula(left, right)


/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/


  /*********************************************************************************
   * Expression Traversal and Helper Functions
   *********************************************************************************
   */

  /**
   * Default Context
   *-----------------
   * A context that remains the same irrespective of the position in the expression. Can be used to 
   * traverse the entire tree in a position agnostic manner.
   */
  object DefaultContext extends Context[Expr[Sort]] {
    def child(expr : Expr[Sort]) = this
    def left (expr : Expr[Sort]) = this
    def right(expr : Expr[Sort]) = this
  }

  /**
   * Fold
   *======
   */

  /* shortcut to traverse the entire tree */
  def all(expr : Expr[Sort], ctx : Context[Expr[Sort]]) : Boolean = true

  /* fold with context */
  def fold[A](down : (Expr[Sort], Context[Expr[Sort]], List[A]) => A, ctx : Context[Expr[Sort]])(expr : Expr[Sort]) : A = 
        expr.reduce[A](all, down, ctx)

  /* fold ignoring context */
  def fold[A](down : (Expr[Sort], List[A]) => A)(expr : Expr[Sort]) : A =
        fold[A]((e : Expr[Sort], c : Context[Expr[Sort]], red : List[A]) => down(e, red), DefaultContext)(expr)

  /**
   * Map
   *-----
   * recursively traverse the expression (collecting the path context) and create a transformed expression on the way back down
   */
  def map(continue : (Expr[Sort], Context[Expr[Sort]]) => Boolean,
          down : (Expr[Sort], Context[Expr[Sort]], List[Expr[Sort]]) => Expr[Sort],
          ctx : Context[Expr[Sort]])(expr : Expr[Sort]) : Expr[Sort] =
        expr.reduce[Expr[Sort]](continue, down, ctx)

  def cast[A <: Sort](child : Expr[Sort]) : Expr[A] =
    child match {
      case c : Expr[A] => c
      case _ => throw new IllegalArgumentException("Clone unary with invalid child argument") 
    }

  def cloneUnary[D <: Sort, C <: Sort](u : Unary[D, C], child : Expr[Sort]) = {
    u match {
      case e : Apply[l, r]       => new Apply             (e.function, cast[l](child))
      case e : Left [l, r]       => new Left              (e.domain, cast[TupleT[l,r]](child))
      case e : Right[l, r]       => new Right             (e.domain, cast[TupleT[l,r]](child))
      case e : Not               => new Not               (cast[BoolT](child))
      case e : Globally          => new Globally          (cast[BoolT](child))
      case e : Finally           => new Finally           (cast[BoolT](child))
      case e : Neg[l]            => new Neg               (e.sort, cast[l](child))
      case e : Derivative[l]     => new Derivative        (e.sort, cast[l](child))
      case e : FormulaDerivative => new FormulaDerivative (cast[BoolT](child))
      case e : BoxModality       => new BoxModality       (cast[ProgramT](child))
      case e : DiamondModality   => new DiamondModality   (cast[ProgramT](child))
      case e : BoxStar           => new BoxStar           (cast[GameT](child))
      case e : DiamondStar       => new DiamondStar       (cast[GameT](child))
      case e : Loop              => new Loop              (cast[ProgramT](child))
      /* Assign */
      /* QAssign */
      /* NDetAssignFn */
      case e : Test              => new Test              (cast[BoolT](child))
      case e : Forall[l]         => new Forall            (e.variable, cast[BoolT](child))
      case e : Exists[l]         => new Exists            (e.variable, cast[BoolT](child))
    }
  }

  def cloneBinary[L <: Sort, R <: Sort, C <: Sort](b : Binary[L, R, C], left : Expr[Sort], right : Expr[Sort]) =
    b
    // if (left.isInstanceOf[b.left.type] && right.isInstanceOf[b.right.type]) {
    //   val l = left.asInstanceOf[b.left.type]
    //   val r = right.asInstanceOf[b.right.type]
    //   b match {
    //     case e : Pair[_, _]       => new Pair         (e.domain, l, r)
    //     case e : And              => new And          (l, r)
    //     case e : Or               => new Or           (l, r)
    //     case e : Imply            => new Imply        (l, r)
    //     case e : Equiv            => new Equiv        (l, r)
    //     case e : Equals[_]        => new Equals       (e.domain.left, l, r)
    //     case e : NotEquals[_]     => new NotEquals    (e.domain.left, l, r)
    //     case e : GreaterThan[_]   => new GreaterThan  (e.domain.left, l, r)
    //     case e : LessThan[_]      => new LessThan     (e.domain.left, l, r)
    //     case e : GreaterEquals[_] => new GreaterEquals(e.domain.left, l, r)
    //     case e : LessEquals[_]    => new LessEquals   (e.domain.left, l, r)
    //     case e : Add[_]           => new Add          (e.sort, l, r)
    //     case e : Subtract[_]      => new Subtract     (e.sort, l, r)
    //     case e : Multiply[_]      => new Multiply     (e.sort, l, r)
    //     case e : Divide [_]       => new Divide       (e.sort, l, r)
    //     case e : Modality         => new Modality     (e.variables, l, r)
    //     case e : SequenceGame     => new SequenceGame (l, r)
    //     case e : DisjunctGame     => new DisjunctGame (l, r)
    //     case e : ConjunctGame     => new ConjunctGame (l, r)
    //     case e : Sequence         => new Sequence     (l, r)
    //     case e : Choice           => new Choice       (l, r)
    //     case e : Parallel         => new Parallel     (l, r)
    //     /* AssignFn */
    //     /* QAssignFn */
    //     case e : ContEvolve       => new ContEvolve   (l, r)
    //     case e : Antedecent       => new Antedecent   (l, r)
    //     case e : Succedent        => new Succedent    (l, r)
    //     case e : Sequent          => new Sequent      (e.context, l, r)
    //   }
    // } else throw new IllegalArgumentException("Clone binary with invalid child argument")

  /* create identical mapping; clone expression if a member has changed */
  def identity_map(expr : Expr[Sort], ctx : Context[Expr[Sort]], reduced : List[Expr[Sort]]) = expr match {
    case e : Atom[_]         => e
    case e : Unary[_, _]     => assert(reduced == Nil || reduced.length == 1)
                                if (reduced == Nil || reduced(0) == e.child) e
                                else cloneUnary(e, reduced(0))
    case e : Binary[_, _, _] => assert(reduced == Nil || reduced.length == 2)
                                if (reduced == Nil || (reduced(0) == e.left && reduced(1) == e.right)) e /* beware the indices ist List(L, R) */
                                else cloneBinary(e, reduced(0), reduced(1))
  }








  object Helpers {

    def Not(e : Expr[BoolT]) = new Not(e)

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
    val seq = new Sequent(List(p, q), TrueEx, new Imply(new Value(q), new Imply(new Value(p), new Value(q))))

    def size(expr : Expr[Sort]) = 
      fold[Int]((e : Expr[Sort], l :  List[Int]) => l.fold[Int](1)((x : Int, y : Int) => x + y))(expr)

    println (Not(TrueEx) + " has size " + size(map(all, identity_map, DefaultContext)(Not(TrueEx))))
    println (seq + " has size " + size(seq))
//    println (new Neg(Time, new Random(Speed)))

  }

}
