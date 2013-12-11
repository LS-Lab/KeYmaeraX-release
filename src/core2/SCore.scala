
/**
 * Core of prover: instantiate for different tasks
 */
class Core {

  sealed abstract class Sort

  object BoolT                                         extends Sort
  object RealT                                         extends Sort
  object ProgramT                                      extends Sort
  object GameT                                         extends Sort
  class  UserT(name : String)                          extends Sort
  class  EnumT(name : String, elements : List[String]) extends Sort
  class  Pair(left : Sort, right : Sort)               extends Sort

  trait Position {
    def goLeft  : Position
    def goRight : Position
  }

  sealed abstract class Expression {

    def reduce[A](up : (Expression, Position) => Boolean, down : (Expression, Position, A*) => A)(pos : Position) : A
    def map(up : (Expression, Position) => Boolean, down : (Expression, Position, Expression*) => Expression)(pos : Position) : Expression = 
          reduce[Expression](up, down)(pos)

    def apply(subexpr : Expression*) : Expression
    def default(pos : Position, red : Expression*) : Expression
  }

  trait Atom extends Expression {
    def reduce[A](up : (Expression, Position) => Boolean, down : (Expression, Position, A*) => A)(pos : Position) : A = down(this, pos)
    def default(pos : Position, red : Expression*) : Expression = this
  }

  trait Unary extends Expression {
    val subexpr : Expression

    def reduce[A](up : (Expression, Position) => Boolean, down : (Expression, Position, A*) => A)(pos : Position) : A =
          if (up(this, pos)) down(this, pos, subexpr.reduce(up, down)(pos.goLeft)) else down(this, pos)

    def default(pos : Position, red : Expression*) : Expression =
          if (red.length == 1 && red(0) == subexpr) this else apply(red(0))
  }

  trait Binary extends Expression {
    val left  : Expression
    val right : Expression

    def reduce[A](up : (Expression, Position) => Boolean, down : (Expression, Position, A*) => A)(pos : Position) : A =
          if (up(this, pos)) down(this, pos, left.reduce(up, down)(pos.goLeft), right.reduce(up, down)(pos.goRight)) else down(this, pos)

    def default(pos : Position, red : Expression*) : Expression =
          if (red.length == 2 && red(0) == left && red(1) == right) this else apply(red(0), red(1))
  }

  abstract class Formula           extends Expression
  abstract class RealExpression    extends Expression
  abstract class Game              extends Expression
  abstract class Program           extends Expression
  abstract class SequentExpression extends Expression

  /**
   * Variable Objects (for Signature)
   */
  object VCount {
    private var id : Int = 0

    def next() : Int = {
      this.synchronized {
        id = id + 1;
        return id;
      }
    }
  }

  class Variable(val name : String, val sort : Sort) {
    private val id : Int = VCount.next()

    def getId() : Int = id;

    def flatEquals(v : Variable) = this.name == v.name && this.sort == v.sort
    def deepEquals(v : Variable) = this.flatEquals(v) && this.id == v.id
  }

  class Function(name : String, val argSort : Sort, sort : Sort) extends Variable(name, sort)

/*********************************************************************************/

// Q: stick with sort objects / pair or switch to string? 
// Todo: need to implement all the apply methods

  /**
   * Differential Logic Expressions
   */

  /* the value of a variable */
  class Value        (val name : String) extends Expression with Atom {
    def apply(subexpr : Expression*) = null
  }

  /* function application */
  class Application  (val functionName : String, val subexpr : Expression) extends Expression with Unary {
    def apply(subexpr : Expression*) = null
  }

  /* vector */
  class Vector       (val left : Expression, val right : Expression) extends Expression with Binary {
    def apply(subexpr : Expression*) = null
  }

  /* projection */
  class ProjectLeft  (val subexpr : Expression) extends Expression with Unary {
    def apply(subexpr : Expression*) = null
  }

  class ProjectRight (val subexpr : Expression) extends Expression with Unary {
    def apply(subexpr : Expression*) = null
  }

  /* casts */
  class ToReal       (val subexpr : Expression) extends RealExpression with Unary {
    def apply(subexpr : Expression*) = null
  }

  class ToBool       (val subexpr : Expression) extends Formula with Unary {
    def apply(subexpr : Expression*) = null
  }

  /* terms */
  class Equals       (val left : Expression, val right : Expression) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class NotEquals    (val left : Expression, val right : Expression) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }

  class GreaterThan  (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class GreaterEqual (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class LessThan     (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class LessEqual    (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }

  class Not          (val subexpr : Formula) extends Formula with Unary {
    def apply(subexpr : Expression*) = null
  }

  class And          (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class Or           (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class Implies      (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }
  class Equivalent   (val left : Formula, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }

  /* temporal */
  class Globally     (val subexpr : Formula) extends Formula with Unary { /* []\Phi e.g., in [\alpha] []\Phi */
    def apply(subexpr : Expression*) = null
  }
  class Finally      (val subexpr : Formula) extends Formula with Unary { /* <>\Phi e.g., in [\alpha] <>\Phi */
    def apply(subexpr : Expression*) = null
  }

  /* modality */
  class Modality     (val left : Game, val right : Formula) extends Formula with Binary {
    def apply(subexpr : Expression*) = null
  }

  /* games */
  class BoxModality     (val subexpr : Program) extends Game with Unary {
    def apply(subexpr : Expression*) = null
  }
  class DiamondModality (val subexpr : Program) extends Game with Unary {
    def apply(subexpr : Expression*) = null
  }
  class SequenceGame    (val left : Game, val right : Game) extends Game with Binary {
    def apply(subexpr : Expression*) = null
  }
  class DisjunctGame    (val left : Game, val right : Game) extends Game with Binary {
    def apply(subexpr : Expression*) = null
  }
  class ConjunctGame    (val left : Game, val right : Game) extends Game with Binary {
    def apply(subexpr : Expression*) = null
  }
  class BoxStarGame     (val subexpr : Game) extends Game with Unary {
    def apply(subexpr : Expression*) = null
  }
  class DiamondStarGame (val subexpr : Game) extends Game with Unary {
    def apply(subexpr : Expression*) = null
  }

  /* programs */
  class SequenceProgram (val left : Program, val right : Program) extends Program with Binary {
    def apply(subexpr : Expression*) = null
  }
  class ChoiceProgram   (val left : Program, val right : Program) extends Program with Binary {
    def apply(subexpr : Expression*) = null
  }
  class ParallelProgram (val left : Program, val right : Program) extends Program with Binary {
    def apply(subexpr : Expression*) = null
  }
  class Loop            (val subexpr : Program) extends Program with Unary {
    def apply(subexpr : Expression*) = null
  }
  class StateCheck      (val subexpr : Formula) extends Program with Unary {
    def apply(subexpr : Expression*) = null
  }

  class Assign          (val name : String, val subexpr : Expression) extends Program with Unary {
    def apply(subexpr : Expression*) = null
  }
  class NonDeterministicAssign (val name : String) extends Program with Atom {
    def apply(subexpr : Expression*) = null
  }

  /* quantifiers */
  abstract class Binder (val name : String, val sort : Sort, val subexpr : Formula) extends Formula with Unary

  class Forall (name : String, sort : Sort, subexpr : Formula) extends Binder(name, sort, subexpr) {
    def apply(subexpr : Expression*) = null
  }
  class Exists (name : String, sort : Sort, subexpr : Formula) extends Binder(name, sort, subexpr) {
    def apply(subexpr : Expression*) = null
  }

// Q: sequent as expression ? Lets us reuse the same position / path-to-root copy mechanism
  /* sequent */
  class Antedecent(val left : Formula, val right : SequentExpression) extends SequentExpression with Binary {
    def apply(subexpr : Expression*) = null
  }
  class Succedent (val left : Formula, val right : SequentExpression) extends SequentExpression with Binary {
    def apply(subexpr : Expression*) = null
  }
  class Sequent   (val sorts : List[Sort], val signature : List[Variable], 
                   val left : SequentExpression, val right : SequentExpression) extends SequentExpression with Binary {
    def apply(subexpr : Expression*) = null
  }

/*********************************************************************************/

/**
 * Rule
 */

  sealed abstract class Rule extends (Sequent => List[Sequent])

/**
 * Proof Tree
 */

  sealed class ProofNode protected (val sequent : Sequent, val parent : ProofNode) {

    case class ProofStep(rule : Rule, subgoals : List[ProofNode])

    @volatile private var alternatives : List[ProofStep] = Nil

    /* must not be invoked when there is no alternative */
// Todo: add assertion
    def getStep : ProofStep = alternatives.head

    private def prepend(r : Rule, s : List[ProofNode]) {
      this.synchronized {
        alternatives = ProofStep(r, s) :: alternatives;
      }
    }

    def prune(n : Int) {
      this.synchronized {
// Todo: use own implementation 
// Todo: assert n < length if necessary
        alternatives = alternatives.take(n-1) ++ alternatives.drop(n)
      }
    }

    def apply(rule : Rule) : ProofNode = {
      val result = rule.apply(sequent).map(new ProofNode(_, this))
      prepend(rule, result)
      return this
    }
  }

  class RootNode(sequent : Sequent) extends ProofNode(sequent, null)

/**
 * Differential Logic Rules
 */



} /* Core */
