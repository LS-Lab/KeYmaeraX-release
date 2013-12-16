
/**
 * External functions imported in core but not used in proof check mode
 */
trait Annotable


/**
 * Prover Core
 */
object Core {

/**
 * Types
 */
  sealed abstract class Sort

  trait Quantifiable

  abstract class BuiltinSort extends Sort

  object BoolT                                                        extends BuiltinSort with Quantifiable
  object RealT                                                        extends BuiltinSort with Quantifiable
  object GameT                                                        extends BuiltinSort
  object ProgramT                                                     extends BuiltinSort
  case class UserT(name : String)                                     extends Sort
  case class EnumT(name : String, elements : List[String])           extends Sort
  case class PairT[L <: Sort, R <: Sort](val left : L, val right : R) extends Sort

/**
 * Path definition
 */
  abstract class Position {
    def goLeft  : Position
    def goRight : Position
  }

/**
 * Expression infrastructure
 */
  sealed abstract class Expression[+T <: Sort](val type_object : T) extends Annotable {

    /* Generic expression traveral
     *=============================

     */
    def reduce[A](traverse  : (Expression[Sort], Position) => Boolean,
                  transform : (Expression[Sort], Position, A*) => A)
                 (pos       : Position) : A

    def map(traverse  : (Expression[Sort], Position) => Boolean,
            transform : (Expression[Sort], Position, Expression[Sort]*) => Expression[Sort])
           (pos       : Position) : Expression[Sort] = reduce[Expression[Sort]](traverse, transform)(pos)

    def apply(expressions : Expression[Sort]*) : Expression[Sort]

    def default_map(pos : Position, red : Expression[Sort]*) : Expression[Sort]
  }

  trait Atom[T <: Sort] extends Expression[T] {
    def reduce[A](traverse  : (Expression[Sort], Position) => Boolean,
                  transform : (Expression[Sort], Position, A*) => A)
                 (pos       : Position) : A =
          transform(this, pos)

    def default_map(pos : Position, red : Expression[Sort]*) : Expression[Sort] = this
  }

  trait Unary[D <: Sort, T <: Sort] extends Expression[T] {
    val expr : Expression[D]

    def reduce[A](traverse  : (Expression[Sort], Position) => Boolean,
                  transform : (Expression[Sort], Position, A*) => A)
                 (pos       : Position) : A =
      if (traverse(this, pos)) transform(this, pos, expr.reduce(traverse, transform)(pos.goLeft)) else transform(this, pos)

    def default_map(pos : Position, red : Expression[Sort]*) : Expression[Sort] = 
      if (red(0) == expr) this else apply(red(0))

  }

  trait Binary[L <: Sort, R <: Sort, T <: Sort] extends Expression[T] {
    val left  : Expression[L]
    val right : Expression[R]

    def reduce[A](traverse  : (Expression[Sort], Position) => Boolean,
                  transform : (Expression[Sort], Position, A*) => A)
                 (pos       : Position) : A =
      if (traverse(this, pos)) transform(this, pos, left.reduce(traverse, transform)(pos.goLeft),
                                                    right.reduce(traverse, transform)(pos.goRight))
      else transform(this, pos)

    def default_map(pos : Position, red : Expression[Sort]*) : Expression[Sort] = 
      if (red(0) == left && red(1) == right) this else apply(red(0), red(1))
  }


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
 * Variables
 */

  object VariableCounter {
    private var next_id : Int = 0

    def next() : Int = {
      this.synchronized {
        next_id = next_id + 1;
        return next_id;
      }
    }
  }

  class Variable[+T <: Sort](val name : String, val type_object : T) {

    private val id : Int = VariableCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.type_object == x.type_object

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  class RealVar                           (name : String) extends Variable[RealT.type](name, RealT)
  class FunctionVar[D <: Sort, T <: Sort] (name : String, val domain_type : D, type_object : T)
                                                          extends Variable[T](name, type_object)
  class PredicateVar[D <: Sort]           (name : String, domain_type : D)
                                                          extends FunctionVar[D, BoolT.type](name, domain_type, BoolT)
  class RealFunction[D <: Sort]           (name : String, domain_type : D)
                                                          extends FunctionVar[D, RealT.type](name, domain_type, RealT)


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
