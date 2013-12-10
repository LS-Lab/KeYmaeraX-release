
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
  
sealed abstract class CList[+T]

object CList {

  object Nil extends CList 
  case class CCons[T, U >: T](val head : U, val tail : CList[T]) extends CList[U] 

  def nil[T] : CList[T] = Nil
  def cons[T, U >: T](head : U, tail : CList[T]) : CList[U] = new CCons(head, tail)

  def reduce[T, U >: T, A](consf : (U, A) => A, nilf : A)(l : CList[T]) : A = {
    l match {
        case Nil              => nilf
        case CCons(head, tail) => consf(head, reduce(consf, nilf)(tail))
    }
  }

  def append[T](back : CList[T])(front : CList[T]) : CList[T] = reduce[T, T, CList[T]](cons, back)(front)
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
    def reduce[L <: Sort, R <: Sort, T <: Sort]
  }

  trait Unary[D <: Sort, C <: Sort] extends Term[C] {
    val term : Term[D]
  }

  trait Binary[L <: Sort, R <: Sort, T <: Sort] extends Term[T] {
    val left  : Term[L]
    val right : Term[R]
  }

  trait Reducible extends Term {
    def reduce[A](leafFun : (Term[Sort]) => A, unaryFun : (Term[Sort], A) => A, binaryFun : (Term[Sort], A, A) => A) : A = {
      this match {
        case Unary  (term)        => unaryFun(this, term.reduce(leafFunterm)
        case Binary (left, right) => binaryFun(
      }
    }
  }




    def reduce[A](leafFun : (Term[Sort]) => A, unaryFun : (Term[Sort], A => A), binaryFun : (Term[Sort], A, A) => A) : A = {
      return unaryFun(this, reduce(leafFun, unaryFun, binaryFun))
    }
  }



    def reduce[A](leafFun : (Term[Sort]) => A, unaryFun : (Term[Sort], A => A), binaryFun : (Term[Sort], A, A) => A) : A = {
      return binaryFun(this, reduce(leafFun, unaryFun, binaryFun), reduce(leafFun, unaryFun, binaryFun))
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

  abstract class Variable[+T <: Sort] private {

    val name : String
    private val id : Int
    val type_object : T

    def this(name : String, type_object : T) = this(name, VariableCounter.get_next(), type_object)

    object VariableCounter {
      private var next_id : Int = 0

      def get_next() : Int = {
        return ++next_id;
      }
    }

    def deepName() = return name + "_" + id;
    def getId() = return id;

    def varEquals(x : Variable[Sort]) = {
      return this.name == x.name && this.type_object == x.type_object
    }
  }

  case class RealVariable                           (name : String) extends Variable[Real.type](name, id, Real)
  case class FunctionVariable[D <: Sort, C <: Sort] (name : String, val domain_type : D, type_object : C)
                                                     extends Variable[C](name, id, type_object)
  case class PredicateVariable[D <: Sort]           (name : String, domtain_type : D)
                                                     extends FunctionVariable[D, Bool.type](name, domain_type, Bool)


  case class Value[T <: Sort](val variable : Variable[T]) extends Term[T](variable.type_object)

  case class Implies    (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class And        (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class Antedecent (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class Succedent  (left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right)

  case class Sequent    (variables : CList[Variable[Sort]], left : FormulaTerm, right : FormulaTerm)
                    extends BinaryBoolFormula(left, right) {

    def rename_doubles() = {
      /* if variable with same user name is in variables;
       * add with new variable object with new user name and remove old one
       * replace value objects etc. in left and right to point to new variable object wherever they contained the old one
       */
    }

    def merge(s : Sequent) = {
      val s2 = new Sequent (this.variables :: s.variables, And(this.left, s.left), And(this.right, s.right));
      return s2.rename_doubles()
    }
  }


/**
 * Proof Tree
 */

  class ProofTree(val sequence : Sequent, val parent : Option[ProofTree]) {

    @volatile private var rule     : Rule = Null
    @volatile private var subgoals : CList[ProofTree] = Nil

    def getRule     : Rule             = rule
    def getSubgoals : CList[ProofTree] = subgoals

    private def prepend(r : Rule, s : CList[ProofTree]) {
      this.synchronized {
        subgoals = s
        result   = r
      }
    }

    /**
     * throws timeout / rule application failed / ...
     */ 
    def apply(rule : Rule) = {
      var subgoals = map((s : Sequent) => new ProofTree(s, this), rule(sequence))
      prepend(rule, subgoals)
    }

    def prune() = {
      rule = Null
      subgoals = Nil
    }

  }


/**
 *================================================================================
 */

  def main(args : Array[String]) {
  }

}
