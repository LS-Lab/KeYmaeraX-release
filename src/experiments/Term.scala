import scala.annotation.elidable
import scala.annotation.elidable._

abstract sealed class Term;


/** Sorts like reals or the sort C of cars. */
sealed abstract class Sort(parent: Sort) extends Term{
  /** Check whether s is a super-sort */
  def <=(s: Sort): Boolean = (this == s) || (this < s)
  /** Check whether s is a sub-sort */
  def >=(s:Sort): Boolean = s <= this
  /** Check whether s is a proper super-sort */
  def <(s: Sort): Boolean = (parent != null && parent <= s)
  /** Check whether s is a proper sub-sort */
  def >(s: Sort): Boolean = (s < this)
}
case object Real extends Sort(AnySort)
case object Rational extends Sort(Real)
case object Integer extends Sort(Rational)
case object Natural extends Sort(Integer)
// everything with boolean sort can be used as formula
case object Boolean extends Sort(Natural)
case object AnySort extends Sort(null)

case object ProgramSort extends Sort(AnySort)

/** Object sort called nm. */
case class St(nm: String, parent: Sort) extends Sort(parent) {
  applicable
  @elidable(ASSERTION) def applicable = {
    require(nm != null, "Name of the sort must not be null")
    require(this < AnySort, "User defined sorts have to be sub-sorts of AnySort")
  }
}

case class Function(n: String, s: Sort, ss: Sort*)
case class Apply(op: Function, args: Term*) extends Term;

case class Predicate(n: String)
case class ApplyPred(op: Predicate, args: Formula*) extends Formula
class BooleanOp(n: String)

case class Formula(

abstract class ModalityType;
object Box extends ModalityType;
object Diamond extends ModalityType;

abstract class Game extends Term;
abstract class GameCombinator extends Game;
class SeqGame extends GameCombinator;
class CupGame extends GameCombinator;
class CapGame extends GameCombinator;
class BoxLoop extends GameCombinator;
class DiaLoop extends GameCombinator;

class Modality(t: ModalityType) extends Game;

abstract class Program extends Term;

abstract class ProgramCombinator extends Program;
object Seq extends ProgramCombinator;
object Cup extends ProgramCombinator;
object Loop extends ProgramCombinator;

abstract class AtomicProgramOp extends Program;
object Assignment extends AtomicProgramOp;
object Test extends AtomicProgramOp;


abstract class QuantifierType;
object Forall extends QuantifierType;
object Exists extends QuantifierType;

class Quantifier(t: QuantifierType) extends Term;

// vim: set ts=4 sw=4 et:
