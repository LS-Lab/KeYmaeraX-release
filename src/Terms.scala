/**
 * @author Marcus Völp
 */

/**
 * Term
 * ====
 *
 * Data structure for representing terms in (quantified) dynamic differential logic
 *
 * Type checking works automatically for builtin terms.
 */

sealed abstract class Term[T <: Sort](val typeObject : T)

abstract class Formula     extends Term[Bool.type](Bool)
abstract class RealTerm    extends Term[Real.type](Real)
abstract class GameTerm    extends Term[Game.type](Game)
abstract class ProgramTerm extends Term[Program.type](Program)

abstract class BinaryFormula[C <: Sort](val left : Term[C], val right : Term[C]) extends Formula {
  assert(left.typeObject == right.typeObject)
}

/* !!! Not really nice */
trait Commutative[T <: Sort] extends BinaryFormula[T]
trait Associative[T <: Sort] extends BinaryFormula[T]

object True  extends Formula
object False extends Formula

class Equals   [T <: Sort](left : Term[T], right : Term[T]) extends BinaryFormula[T](left, right)
                                                               with Commutative  [T]
                                                               with Associative  [T]

class NotEquals[T <: Sort](left : Term[T], right : Term[T]) extends BinaryFormula[T](left, right)
                                                               with Commutative[T]

class GreaterThan (left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)
class GreaterEqual(left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)
class LessThan    (left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)
class LessEqual   (left : RealTerm, right : RealTerm) extends BinaryFormula[Real.type](left, right)

class Not         (term : Formula) extends Formula

class And         (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                       with Commutative  [Bool.type]
                                                       with Associative  [Bool.type]
class Or          (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                       with Commutative  [Bool.type]
                                                       with Associative  [Bool.type]
class Implies     (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                       with Associative  [Bool.type]
class Equivalent  (left : Formula, right : Formula) extends BinaryFormula[Bool.type](left, right)
                                                       with Commutative  [Bool.type]
                                                       with Associative  [Bool.type]

/**
 * Modality
 */
case class Modality          (val game : GameTerm, val term : Formula) extends Formula /* G   \Phi */

/*
class ThroughoutModality(val game : GameTerm, val term : Formula) extends Formula /* G []\Phi */
class SometimesModality (val game : GameTerm, val term : Formula) extends Formula /* G <>\Phi */

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

/* !!! annotations */

