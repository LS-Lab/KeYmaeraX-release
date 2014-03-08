/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
package edu.cmu.cs.ls.keymaera.core

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

class Core {

  /**
   * Expression infrastructure
   *===========================
   * (see TypeSafety.scala for an explaination how the Expression builtin typechecking
   * mechanism works. Each expression may replicate itself with apply and adheres to the
   * generic recursion structure via the function reduce.
   */
  sealed abstract class Expr(val sort : Sort) extends Annotable

  /* atom / leaf expression */
  abstract class Atom(sort : Sort) extends Expr(sort)

  /* unary expression */
  abstract class Unary(sort : Sort, val domain : Sort, val child : Expr) extends Expr(sort) {

    applicable

    @elidable(ASSERTION) def applicable = require(domain == child.sort, "Sort Mismatch in Unary Expr: " + domain + " " + child.sort)

  }

  /* binary expression (n-ary is encoded as binary of binary of ... */
  abstract class Binary(sort : Sort, val domain : Sort, val left : Expr, val right : Expr) extends Expr(sort) {

    applicable

    @elidable(ASSERTION) def applicable = 
          require(domain.left == left.sort && domain.right == right.sort, "Sort Mismatch in Binary Expr")

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

  abstract class NamedSymbol(val name : String, val sort : Sort) {

    private val id : Int = NameCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.sort == x.sort

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  class Variable(name : String, sort : Sort) extends NamedSymbol(name, sort)

  class FunctionVar (name : String, val domain : Sort, sort : Sort) extends NamedSymbol(name, sort)

  /**
   * Constant, Variable and Function Expressions
   *=============================================
   */

  /* The * in nondet. assignments */
  // class Random[C <: Sort](sort : C) extends Atom(sort) /* SOONISH BUT NOT NOW */

  /* Constant of scala type A cast into sort C */
  class Constant(sort : Sort, val value : Sort) extends Atom(sort)

  /* convenience wrappers for boolean / real constants */
  val TrueEx  = new Constant(Bool, true)
  val FalseEx = new Constant(Bool, false)

  class Number(sort : Sort, value : BigDecimal) extends Constant(sort, value)

  /* value of variable */
  class Value(val variable : Variable) extends Atom(variable.sort)

  /* function application */
  class Apply(val function : FunctionVar, child : Expr)
             extends Unary(function.sort, function.domain, child)

  /* combine subexpressions into a vector */
  class Pair(domain : TupleT, left : Expr, right : Expr) extends Binary(domain, domain, left, right)

  /* extract elements from a vector expression */
  class Left (domain : TupleT, child : Expr) extends Unary(domain.left, domain, child)
  class Right(domain : TupleT, child : Expr) extends Unary(domain.right, domain, child)

  /**
   * Formulas (aka Terms)
   *======================
   */
  /* Bool -> Bool */
  abstract class UnaryFormula(child : Expr) extends Unary(Bool, Bool, child)
  /* Bool x Bool -> Bool */
  abstract class BinaryFormula(left : Expr, right : Expr) extends Binary(Bool, BoolXBool, left, right)

  class Not   (child : Expr) extends UnaryFormula(child)
  class And   (left : Expr, right : Expr) extends BinaryFormula(left, right)
  class Or    (left : Expr, right : Expr) extends BinaryFormula(left, right)
  class Imply (left : Expr, right : Expr) extends BinaryFormula(left, right)
  class Equiv (left : Expr, right : Expr) extends BinaryFormula(left, right)

  abstract class BinaryRelation(domain : Sort, left : Expr, right : Expr)
    extends Binary(Bool, new TupleT(domain, domain), left, right)

  /* equality */
  class Equals   (domain : Sort, left : Expr, right : Expr) extends BinaryRelation(domain, left, right)
  class NotEquals(domain : Sort, left : Expr, right : Expr) extends BinaryRelation(domain, left, right)

  /* comparisson */
  class GreaterThan  (domain : Sort, left : Expr, right : Expr) extends BinaryRelation(domain, left, right)
  class LessThan     (domain : Sort, left : Expr, right : Expr) extends BinaryRelation(domain, left, right)
  class GreaterEquals(domain : Sort, left : Expr, right : Expr) extends BinaryRelation(domain, left, right)
  class LessEquals   (domain : Sort, left : Expr, right : Expr) extends BinaryRelation(domain, left, right)

  /* temporal */
  class Globally (child : Expr) extends UnaryFormula(child) /* []\Phi e.g., in [\alpha] []\Phi */
  class Finally  (child : Expr) extends UnaryFormula(child) /* <>\Phi e.g., in [\alpha] <>\Phi */

  /**
   * Real Expressions
   *==================
   */

  class Neg     (sort : Sort, child : Expr) extends Unary(sort, sort, child)
  class Add     (sort : Sort, left  : Expr, right : Expr) extends Binary(sort, sort, left, right)
  class Subtract(sort : Sort, left  : Expr, right : Expr) extends Binary(sort, sort, left, right)
  class Multiply(sort : Sort, left  : Expr, right : Expr) extends Binary(sort, sort, left, right)
  class Divide  (sort : Sort, left  : Expr, right : Expr) extends Binary(sort, sort, left, right)
  class Exp     (sort : Sort, left  : Expr, right : Expr) extends Binary(sort, sort, left, right) /* x^y (for "nice" y only) */

  class Derivative(sort : Sort, child : Expr) extends Unary(sort, sort, child)
  class FormulaDerivative        (child : Expr)       extends UnaryFormula(child)

  /**
   * Games
   *=======
   */

  /* Modality */
  class Modality (left : Expr, right : Expr) extends Binary(Bool, GameXBool, left, right) {
    def variables: List[NamedSymbol]
  }

  abstract class UnaryGame  (child : Expr) extends Unary(Game, Game, child)
  abstract class BinaryGame (left : Expr, right : Expr) extends Binary(Game, GameXGame, left, right)

  /* Games */
  class BoxModality     (child : Expr) extends Unary(Game, Program, child)
  class DiamondModality (child : Expr) extends Unary(Game, Program, child)

  class BoxStar         (child : Expr)    extends UnaryGame(child)
  class DiamondStar     (child : Expr)    extends UnaryGame(child)
  class SequenceGame    (left  : Expr, right : Expr) extends BinaryGame(left, right)
  class DisjunctGame    (left  : Expr, right : Expr) extends BinaryGame(left, right)
  class ConjunctGame    (left  : Expr, right : Expr) extends BinaryGame(left, right)

  /**
   * Programs
   *==========
   */

  abstract class UnaryProgram  (child : Expr) extends Unary(Program, Program, child) 
  abstract class BinaryProgram (left  : Expr, right : Expr) extends Binary(Program, ProgramXProgram, left, right)

  class Sequence(left  : Expr, right : Expr) extends BinaryProgram(left, right)
  class Choice  (left  : Expr, right : Expr) extends BinaryProgram(left, right)
  class Parallel(left  : Expr, right : Expr) extends BinaryProgram(left, right)
  class Loop    (child : Expr)               extends UnaryProgram(child)

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


  class Test(child : Expr) extends Unary(Program, Bool, child)

  /* child = differential algebraic formula */
  class ContEvolve(child : Expr) extends Unary(Program, Bool, child)

  /* TODO: normal form ODE data structures */
  class NFContEvolve(xvector: Expr, thetavector: Expr, evolutionDomain: Expr)

  /**
   * Quantifiers
   *=============
   */

  abstract class Quantifier(val variable : NamedSymbol, child : Expr) extends UnaryFormula(child)

  class Forall(variable : NamedSymbol, child : Expr) extends Quantifier(variable, child)
  class Exists(variable : NamedSymbol, child : Expr) extends Quantifier(variable, child)

  class Sequent(val pref: Seq[(String, Sort)], val ante: IndexedSeq[Formula], val succ: IndexedSeq[Formula])

  object Sequent {
    def apply(pref: Seq[(String, Sort)], ante: IndexedSeq[Formula], succ: IndexedSeq[Formula]) : Sequent = new Sequent(pref, ante, succ)
  }



} /* Core */

/**
 *==================================================================================
 *==================================================================================
 */
