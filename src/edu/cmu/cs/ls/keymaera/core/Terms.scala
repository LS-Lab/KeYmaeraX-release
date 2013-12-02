/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
 package edu.cmu.cs.ls.keymaera


import scala.annotation.elidable
import scala.annotation.elidable._

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
 * Data structure for representing terms in (quantified) dynamic differential logic
 *
 * Type checking works automatically for builtin terms. For user defined types and
 * for pairs, the trait TypeCheck asserts 
 */
sealed abstract class Term[A, T <: Sort](val typeObject : T) extends Annotable

abstract class Formula     extends Term[Bool.type](Bool)
abstract class RealTerm    extends Term[Real.type](Real)
abstract class GameTerm    extends Term[Game.type](Game)
abstract class ProgramTerm extends Term[Program.type](Program)

abstract class BinaryFormula[C <: Sort](val left : Term[C], val right : Term[C]) extends Formula

/* !!! Not really nice because only defined on formulas */
trait Commutative[T <: Sort] extends BinaryFormula[T]
trait Associative[T <: Sort] extends BinaryFormula[T]

trait TypeCheck[T <: Sort]   extends BinaryFormula[T] {
  applicable
  @elidable(ASSERTION) def applicable = {
    require(left.typeObject == right.typeObject, "Sort Mismatch in Formula")
  }
}

case object True  extends Formula
case object False extends Formula

case class Equals   [T <: Sort](left : Term[T], right : Term[T]) extends BinaryFormula[T](left, right)
                                                                    with Commutative  [T]
                                                                    with Associative  [T]
                                                                    with TypeCheck    [T]

case class NotEquals[T <: Sort](left : Term[T], right : Term[T]) extends BinaryFormula[T](left, right)
                                                                    with Commutative  [T]
                                                                    with TypeCheck    [T]

case class GreaterThan (left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)
case class GreaterEqual(left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)
case class LessThan    (left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)
case class LessEqual   (left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)

case class Not         (term : Formula) extends Formula

case class And         (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                            with Commutative  [Bool.type]
                                                            with Associative  [Bool.type]
case class Or          (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                            with Commutative  [Bool.type]
                                                            with Associative  [Bool.type]
case class Implies     (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                            with Associative  [Bool.type]
case class Equivalent  (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                            with Commutative  [Bool.type]
                                                            with Associative  [Bool.type]

/**
 * Temporal Formulas
 */
case class Globally  (term : Formula) extends Formula /* []\Phi e.g., in [\alpha] []\Phi */
case class Finally   (term : Formula) extends Formula /* <>\Phi e.g., in [\alpha] <>\Phi */

/**
 * Modality
 */
case class Modality        (val game : GameTerm, val term : Formula) extends Formula /* G   \Phi */

/**
 * Games
 * =====
 */
case class BoxModality     (val program : ProgramTerm) extends GameTerm /* \[ \alpha \] */
case class DiamondModality (val program : ProgramTerm) extends GameTerm /* \< \alpha \> */
case class SequenceGame    (val left : GameTerm, val right : GameTerm) extends GameTerm
case class DisjunctGame    (val left : GameTerm, val right : GameTerm) extends GameTerm
case class ConjunctGame    (val left : GameTerm, val right : GameTerm) extends GameTerm
case class BoxStarGame     (val game : GameTerm) extends GameTerm
case class DiamondStarGame (val game : GameTerm) extends GameTerm

/**
 * Programs
 * ========
 */

/* !!! quantified assign / quantified evolve missing */

case class SequenceProgram (val left : ProgramTerm, val right : ProgramTerm) extends ProgramTerm
case class ChoiceProgram   (val left : ProgramTerm, val right : ProgramTerm) extends ProgramTerm
case class StateCheck      (val term : Formula)        extends ProgramTerm
case class Loop            (val program : ProgramTerm) extends ProgramTerm

/* !!! identifier handling missing */
/* !!! binders missing */

sealed abstract class Binder[T <: Sort](typeObject : T)(val variableName : String) extends Term[T](typeObject)

case class Forall[T <: Sort](typeObject : T)(variableName : String) extends Binder[T](typeObject)(variableName)
case class Exists[T <: Sort](typeObject : T)(variableName : String) extends Binder[T](typeObject)(variableName)

sealed class Bind[C <: Sort, T <: Sort](val binder : Binder[C], val term : Term[T]) extends Term[T](term.typeObject)
sealed class Name[C <: Sort](val name : String) : Term[C](binder.typeObject)

