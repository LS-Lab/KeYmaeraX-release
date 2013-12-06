
/**
 * External functions imported in core but not used in proof check mode
 */
trait Annotable


/**
 * Prover Core
 */
object Core {

/**
 * Helper classes used within the core
 */

/* List */
  sealed abstract class CList[+T] {
    val length : Int
  }

  case class Nil() extends CList {
    val length = 0
  }

  case class Cons[T, U >: T](head : U, tail : CList[T]) extends CList[U] {
    val length = 1 + tail.length
  }

/**
 * Types
 */

  sealed abstract class Sort

  trait Quantifiable

  abstract class BuiltinSort extends Sort

  object Bool    extends BuiltinSort with Quantifiable
  object Real    extends BuiltinSort with Quantifiable
  object Game    extends BuiltinSort
  object Program extends BuiltinSort
  case class  User(name : String)                          extends Sort
  case class  Enum(name : String, elements : CList[String]) extends Sort
  case class  Pair[L <: Sort, R <: Sort](val left : L, val right : R) extends Sort


/**
 * Term infrastructure
 */

  sealed abstract class Term[+T <: Sort](val type_object : T) extends Annotable {
    def reduce[A](f : (Term[Sort]) => A, red : (Term[Sort], A, A => A)) : A = {
      f(this)
    }
  }

  trait Unary[D <: Sort, C <: Sort] extends Term[C] {
    val term : Term[D]

    def reduce[A](f : (Term[Sort]) => A, red : (Term[Sort], A, A => A)) : A = {
      red(this, f(this), term.reduce(f, red))
    }
  }

  trait Binary[L <: Sort, R <: Sort, T <: Sort] extends Term[T] {
    val left  : Term[L]
    val right : Term[R]

    def reduce[A](f : (Term[Sort]) => A, red : (Term[Sort], A, A => A)) : A = {
      red(this, f(this), red(this, left.reduce(f, red), right.reduce(f, red)))
    }
  }

  /* Formula */
  abstract class FormulaTerm  extends Term[Bool.type](Bool)

  abstract class UnaryFormula [T <: Sort]           (val term : Term[T])
                              extends FormulaTerm with Unary[T, Bool.type]
  abstract class BinaryFormula[L <: Sort, R <: Sort](val left : Term[L], val right : Term[R])
                              extends FormulaTerm with Binary[L, R, Bool.type]

  abstract class UnaryBoolFormula(val term : FormulaTerm)
                              extends FormulaTerm with Unary[Bool.type, Bool.type]
  abstract class BinaryBoolFormula(val left : FormulaTerm, val right : FormulaTerm)
                              extends FormulaTerm with Binary[Bool.type, Bool.type, Bool.type]

  /* Real */
  abstract class RealTerm     extends Term[Real.type](Real)

  abstract class UnaryReal    [T <: Sort]           (val term : Term[T])
                              extends RealTerm with Unary[T, Real.type]

  abstract class BinaryReal   [L <: Sort, R <: Sort](val left : Term[L], val right : Term[R])
                              extends RealTerm with Binary[L, R, Real.type]

  /* Game */
  abstract class GameTerm     extends Term[Game.type](Game)
  /* Program */
  abstract class ProgramTerm  extends Term[Program.type](Program)


/**
 * Differential Logic
 */

  abstract class Variable[T <: Sort](val name : String, val type_object : T)

  case class PredicateVariable                      (name : String) extends Variable[Bool.type](name, Bool)
  case class RealVariable                           (name : String) extends Variable[Real.type](name, Real)
  case class FunctionVariable[D <: Sort, C <: Sort] (name : String, val domain_type : D, type_object : C) 
                                                extends Variable[C](name, type_object)

  case class Value[T <: Sort](val variable : Variable[T]) extends Term[T](variable.type_object)

  case class Implies    (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class Antedecent (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class Succedent  (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class Sequent    (variables : CList[Variable[Sort]], left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)


/**
 *
 */

/**
 *================================================================================
 */

  def main(args : Array[String]) {
  }

}
