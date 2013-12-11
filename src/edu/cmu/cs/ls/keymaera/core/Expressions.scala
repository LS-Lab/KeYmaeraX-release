/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
 package edu.cmu.cs.ls.keymaera.core


import scala.annotation.elidable
import scala.annotation.elidable._

/**
 * Sorts
 * =====
 *
 * The rational behind the below type hierarchy Sort is to let scala
 * discarge ill typed terms whenever this is possible. That is, scala
 * will automatically check type safety for builtin sorts. However,
 * because Sorts can be user defined. We have to support the creation
 * of new Sorts, which prevents compile time checks for these sorts.
 * We therefore equipped terms over user defined sorts with runtime
 * checks to assert type safety.
 */
sealed abstract class Sort

trait Quantifiable

/**
 * Builtin sorts
 */
sealed abstract class BuiltInSort extends Sort

object Bool extends BuiltInSort with Quantifiable
object Real extends BuiltInSort with Quantifiable
object Unit extends BuiltInSort with Quantifiable

object GameSort    extends BuiltInSort
object ProgramSort extends BuiltInSort
//object FormulaSort extends BuiltInSort

/**
 * User defined sorts
 */
sealed class UserDefinedSort(name : String) extends Sort with Quantifiable
sealed class UserDefinedEnum(name : String, elements : List[String]) extends UserDefinedSort(name)

/* ??? We could perhaps just create "Constant" objects for every element of an enum */

sealed case class Pair(val l: Sort, val r: Sort) extends Sort

/**
 * Trait for adding annotations
 * ============================
 * 
 * They are no longer required in the proof checker. Hence this trait may be empty.
 */
trait Annotable

/**
 * Term
 * ====
 *
 * Data structure for representing terms in (quantified) differential dynamic logic
 *
 * Type checking works automatically for builtin terms. For user defined types and
 * for pairs, the trait TypeCheck asserts 
 */
sealed abstract class Expr[+T <: Sort] extends Annotable

trait UnaryExpr[T <: Sort, A <: Sort] extends Expr[T] {
  val child: Expr[A]
  def construct(e: Expr[A]): Expr[T]
}

object UnaryExpr {
  def unapply[A](e: Expr[T]) : Option[Expr[A]] = e match {
    case e: UnaryExpr[T, A] => Some(e.child)
    case _ => None
  }
}

trait BinaryExpr[T <: Sort, A <: Sort] extends Expr[T] {
  val left: Expr[A]
  val right: Expr[A]
  def constuct(l: Expr[A], r: Expr[A])
}

object BinaryExpr {
  def unapply[A](e: Expr[T]) : Option[(Expr[A], Expr[A])] = e match {
    case e: BinaryExpr[T, A] => Some((e.left, e.right))
    case _ => None
  }
}

case object True  extends Expr[Bool.type]
case object False extends Expr[Bool.type]

case class Equals   [T <: Sort](left : Expr[T], right : Expr[T]) extends Expr[Bool.type] with BinaryExpr[Bool.type,T] {
  def construct(a: Expr[T], b: Expr[T]) = new Equals[T](a,b) 
}

case class NotEquals[T <: Sort](left : Expr[T], right : Expr[T]) extends Expr[Bool.type]
                                                                    with BinaryExpr[Bool.type,T] {
  def construct(a: Expr[T], b: Expr[T]) = new NotEquals[T](a,b) 
}

case class GreaterThan (left : Expr[Real.type], right : Expr[Real.type]) extends Expr[Bool.type] with BinaryExpr[Bool.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new GreaterThan(a,b) 
}
case class GreaterEquals (left : Expr[Real.type], right : Expr[Real.type]) extends Expr[Bool.type] with BinaryExpr[Bool.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new GreaterEquals(a,b) 
}
case class LessEquals (left : Expr[Real.type], right : Expr[Real.type]) extends Expr[Bool.type] with BinaryExpr[Bool.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new LessEquals(a,b) 
}
case class LessThan (left : Expr[Real.type], right : Expr[Real.type]) extends Expr[Bool.type] with BinaryExpr[Bool.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new LessThan(a,b) 
}

case class Not         (child : Expr[Bool.type]) extends Expr[Bool.type] with UnaryExpr[Bool.type, Bool.type] {
  def construct(e: Expr[Bool.type]) = new Not(e)
}

case class And         (left : Expr[Bool.type], right : Expr[Bool.type]) extends Expr[Bool.type]
                                                            with BinaryExpr[Bool.type,Bool.type]  {
  def construct(a: Expr[Bool.type], b: Expr[Bool.type]) = new And(a,b) 
}
case class Or         (left : Expr[Bool.type], right : Expr[Bool.type]) extends Expr[Bool.type]
                                                            with BinaryExpr[Bool.type,Bool.type] {
  def construct(a: Expr[Bool.type], b: Expr[Bool.type]) = new Or(a,b) 
}
case class Implies         (left : Expr[Bool.type], right : Expr[Bool.type]) extends Expr[Bool.type]
                                                            with BinaryExpr[Bool.type, Bool.type] {
  def construct(a: Expr[Bool.type], b: Expr[Bool.type]) = new Implies(a,b) 
}
case class Equivalent         (left : Expr[Bool.type], right : Expr[Bool.type]) extends Expr[Bool.type]
                                                            with BinaryExpr[Bool.type,Bool.type] {
  def construct(a: Expr[Bool.type], b: Expr[Bool.type]) = new Equivalent(a,b) 
}

/**
 * Temporal Expr[Bool.type](Bool)s
 */
case class Globally  (child : Expr[Bool.type]) extends Expr[Bool.type] with UnaryExpr[Bool.type, Bool.type] { /* []\Phi e.g., in [\alpha] []\Phi */
  def construct(e: Expr[Bool.type]) = new Globally(e)
}
case class Finally  (child : Expr[Bool.type]) extends Expr[Bool.type] with UnaryExpr[Bool.type, Bool.type] { /* <>\Phi e.g., in [\alpha] <>\Phi */
  def construct(e: Expr[Bool.type]) = new Finally(e)
}

/**
 * Modality
 */
case class Modality[A <: Sort]        (val game : Expr[GameSort.type], val term : Expr[A]) extends Expr[A] /* G   \Phi */
// TODO: this is a binary expression with two _different_ types as parameters

/**
 * Games
 * =====
 */
case class BoxModality     (child : Expr[ProgramSort.type]) extends Expr[GameSort.type] with UnaryExpr[GameSort.type, ProgramSort.type] /* \[ \alpha \] */ {
  def construct(e: Expr[ProgramSort.type]) = new BoxModality(e)
}
case class DiamondModality (child : Expr[ProgramSort.type]) extends Expr[GameSort.type] with UnaryExpr[GameSort.type, ProgramSort.type] /* \< \alpha \> */
case class SequenceGame    (val left : Expr[GameSort.type], val right : Expr[GameSort.type]) extends Expr[GameSort.type]
case class DisjunctGame    (val left : Expr[GameSort.type], val right : Expr[GameSort.type]) extends Expr[GameSort.type]
case class ConjunctGame    (val left : Expr[GameSort.type], val right : Expr[GameSort.type]) extends Expr[GameSort.type]
case class BoxStarGame     (val game : Expr[GameSort.type]) extends Expr[GameSort.type]
case class DiamondStarGame (val game : Expr[GameSort.type]) extends Expr[GameSort.type]

/**
 * Programs
 * ========
 */

/* !!! quantified assign / quantified evolve missing */

case class SequenceProgram (val left : Expr[ProgramSort.type], val right : Expr[ProgramSort.type]) extends Expr[ProgramSort.type]
case class ChoiceProgram   (val left : Expr[ProgramSort.type], val right : Expr[ProgramSort.type]) extends Expr[ProgramSort.type]
case class ParallelProgram   (val left : Expr[ProgramSort.type], val right : Expr[ProgramSort.type]) extends Expr[ProgramSort.type]
case class Loop            (val program : Expr[ProgramSort.type]) extends Expr[ProgramSort.type]
case class Assign[T <: Sort]          (val n: Name[T], val t : Expr[T]) extends Expr[ProgramSort.type]
case class QuantifiedAssign[T <: Sort, A <: Sort]          (val n: Name[A], val f: Function[T, A], val t : Expr[T]) extends Expr[ProgramSort.type]
case class NonDeterminsticAssign[T <: Sort] (val n: Name[T]) extends Expr[ProgramSort.type]
case class QuantifiedNonDeterministicAssign[T <: Sort, A <: Sort]   (val n: Name[A], val f: Function[T, A]) extends Expr[ProgramSort.type]
case class StateCheck      (val term : Expr[Bool.type])        extends Expr[ProgramSort.type]

/* !!! identifier handling missing */
/* !!! binders missing */

sealed abstract class Binder[T <: Sort](val variableName : String) extends Expr[T]

case class Forall[T <: Sort](override val variableName : String) extends Binder[T](variableName)
case class Exists[T <: Sort](override val variableName : String) extends Binder[T](variableName)

sealed class Bind[C <: Sort, T <: Sort](val binder : Binder[C], val term : Expr[T]) extends Expr[T]
sealed class Name[C <: Sort](val name : String) extends Expr[C]

sealed class Function[R <: Sort](val name: String) 

sealed class Application[C <: Sort](val f: Function[C], val args: Expr[_]) extends Expr[C]

sealed class Vector[A <: Sort, B <: Sort](val a: Expr[A], val b: Expr[B]) extends Expr[Pair[A,B]]

sealed class Left[A <: Sort, B <: Sort] (val v: Vector[A,B]) extends Application[A](new Function[A]("left"), v)

sealed class Right[A <: Sort, B <: Sort](val v: Vector[A,B]) extends Application[B](new Function[B]("right"), v)

case class Neg(child: Expr[Real.type]) extends Expr[Real.type] with UnaryExpr[Real.type, Real.type] {
  def construct(a: Expr[Real.type]) = new Neg(a,b)
}

case class Add(left: Expr[Real.type], right: Expr[Real.type]) extends Expr[Real.type] with BinaryExpr[Real.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new Add(a,b)
}

case class Sub(left: Expr[Real.type], right: Expr[Real.type]) extends Expr[Real.type] with BinaryExpr[Real.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new Sub(a,b)
}

case class Mult(left: Expr[Real.type], right: Expr[Real.type]) extends Expr[Real.type] with BinaryExpr[Real.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new Mult(a,b)
}

case class Div(left: Expr[Real.type], right: Expr[Real.type]) extends Expr[Real.type] with BinaryExpr[Real.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new Div(a,b)
}

case class Exp(left: Expr[Real.type], right: Expr[Real.type]) extends Expr[Real.type] with BinaryExpr[Real.type, Real.type] {
  def construct(a: Expr[Real.type], b: Expr[Real.type]) = new Div(a,b)
}
