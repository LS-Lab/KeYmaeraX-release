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

sealed class Pair[L <: Sort, R <: Sort] extends Sort

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
sealed abstract class Term[T <: Sort](val typeObject : T) extends Annotable

//abstract class Term[Bool.type](Bool)     extends Term[Bool.type](Bool)
//abstract class Term[Real.type]    extends Term[Real.type](Real)
//abstract class Term[GameSort.type]    extends Term[GameSort.type](GameSort)
//abstract class Term[ProgramSort.type] extends Term[ProgramSort.type](ProgramSort)

abstract class BinaryFormula[C <: Sort](val l : Term[C], val r : Term[C]) extends Term[Bool.type](Bool)

/* !!! Not really nice because only defined on formulas */
trait Commutative[T <: Sort] extends BinaryFormula[T]
trait Associative[T <: Sort] extends BinaryFormula[T]

trait TypeCheck[T <: Sort]   extends BinaryFormula[T] {
  applicable
  @elidable(ASSERTION) def applicable = {
    require(l.typeObject == r.typeObject, "Sort Mismatch in Term[Bool.type](Bool)")
  }
}

case object True  extends Term[Bool.type](Bool)
case object False extends Term[Bool.type](Bool)

case class Equals   [T <: Sort](left : Term[T], right : Term[T]) extends BinaryFormula[T](left, right)
                                                                    with Commutative  [T]
                                                                    with Associative  [T]
                                                                    with TypeCheck    [T]

case class NotEquals[T <: Sort](left : Term[T], right : Term[T]) extends BinaryFormula[T](left, right)
                                                                    with Commutative  [T]
                                                                    with TypeCheck    [T]

case class GreaterThan (left : Term[Real.type], right : Term[Real.type]) extends BinaryFormula[Real.type](left, right)
case class GreaterEqual(left : Term[Real.type], right : Term[Real.type]) extends BinaryFormula[Real.type](left, right)
case class LessThan    (left : Term[Real.type], right : Term[Real.type]) extends BinaryFormula[Real.type](left, right)
case class LessEqual   (left : Term[Real.type], right : Term[Real.type]) extends BinaryFormula[Real.type](left, right)

case class Not         (term : Term[Bool.type]) extends Term[Bool.type](term.typeObject)

case class And         (left : Term[Bool.type], right : Term[Bool.type]) extends BinaryFormula[Bool.type](left, right)
                                                            with Commutative  [Bool.type]
                                                            with Associative  [Bool.type]
case class Or          (left : Term[Bool.type], right : Term[Bool.type]) extends BinaryFormula[Bool.type](left, right)
                                                            with Commutative  [Bool.type]
                                                            with Associative  [Bool.type]
case class Implies     (left : Term[Bool.type], right : Term[Bool.type]) extends BinaryFormula[Bool.type](left, right)
                                                            with Associative  [Bool.type]
case class Equivalent  (left : Term[Bool.type], right : Term[Bool.type]) extends BinaryFormula[Bool.type](left, right)
                                                            with Commutative  [Bool.type]
                                                            with Associative  [Bool.type]

/**
 * Temporal Term[Bool.type](Bool)s
 */
case class Globally  (term : Term[Bool.type]) extends Term[Bool.type](Bool) /* []\Phi e.g., in [\alpha] []\Phi */
case class Finally   (term : Term[Bool.type]) extends Term[Bool.type](Bool) /* <>\Phi e.g., in [\alpha] <>\Phi */

/**
 * Modality
 */
case class Modality        (val game : Term[GameSort.type], val term : Term[Bool.type]) extends Term[Bool.type](Bool) /* G   \Phi */

/**
 * Games
 * =====
 */
case class BoxModality     (val program : Term[ProgramSort.type]) extends Term[GameSort.type](GameSort) /* \[ \alpha \] */
case class DiamondModality (val program : Term[ProgramSort.type]) extends Term[GameSort.type](GameSort) /* \< \alpha \> */
case class SequenceGame    (val left : Term[GameSort.type], val right : Term[GameSort.type]) extends Term[GameSort.type](GameSort)
case class DisjunctGame    (val left : Term[GameSort.type], val right : Term[GameSort.type]) extends Term[GameSort.type](GameSort)
case class ConjunctGame    (val left : Term[GameSort.type], val right : Term[GameSort.type]) extends Term[GameSort.type](GameSort)
case class BoxStarGame     (val game : Term[GameSort.type]) extends Term[GameSort.type](GameSort)
case class DiamondStarGame (val game : Term[GameSort.type]) extends Term[GameSort.type](GameSort)

/**
 * Programs
 * ========
 */

/* !!! quantified assign / quantified evolve missing */

case class SequenceProgram (val left : Term[ProgramSort.type], val right : Term[ProgramSort.type]) extends Term[ProgramSort.type](ProgramSort)
case class ChoiceProgram   (val left : Term[ProgramSort.type], val right : Term[ProgramSort.type]) extends Term[ProgramSort.type](ProgramSort)
case class StateCheck      (val term : Term[Bool.type])        extends Term[ProgramSort.type](ProgramSort)
case class Loop            (val program : Term[ProgramSort.type]) extends Term[ProgramSort.type](ProgramSort)

/* !!! identifier handling missing */
/* !!! binders missing */

sealed abstract class Binder[T <: Sort](typeObject : T)(val variableName : String) extends Term[T](typeObject)

case class Forall[T <: Sort](override val typeObject : T)(override val variableName : String) extends Binder[T](typeObject)(variableName)
case class Exists[T <: Sort](override val typeObject : T)(override val variableName : String) extends Binder[T](typeObject)(variableName)

sealed class Bind[C <: Sort, T <: Sort](val binder : Binder[C], val term : Term[T]) extends Term[T](term.typeObject)
sealed class Name[C <: Sort](typeObject : C)(val name : String) extends Term[C](typeObject)

//sealed case class Term[Bool.type](Bool)Name(val name : String) extends Term[Bool.type](Bool)
//sealed case class ProgramName(val name : String) extends Term[ProgramSort.type]
//sealed case class GameName(val name : String) extends Term[GameSort.type]


