/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 */
package edu.cmu.cs.ls.keymaera.core

/**
 * Todos
 *=======
 */

/**
 * Points to Discuss
 *===================
 * 1) Generic traversal and rewriting function necessary
 * 2) First class * Expression: * also in if(*) \alpha else \beta vs. nondet. assignment forms (:= *)
 */

import scala.annotation.elidable
import scala.annotation.elidable._

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
 */
sealed abstract class Sort

object Unit extends Sort

/* sort of booleans: true, false */
object Bool extends Sort

/* sort of reals: 0, 1, 2.73 */
object Real extends Sort

/* sort of games */
object GameSort extends Sort

/* sort of hybrid probrams */
object ProgramSort extends Sort

/* user defined sort */
case class UserSort(name : String) extends Sort
/* user defined enum sort. values is the list of named constants of this enum */
case class EnumT(name : String, values : List[String]) extends Sort

/* used to define pairs of sorts. That is the pair sort is of type L x R */
sealed trait TupleT extends Sort {
  val left: Sort
  val right: Sort
}
object TupleT {
  // Currying of sorts such that left is never a TupleT
  def apply(left: Sort, right: Sort): TupleT = left match {
    case TupleTImpl(l, r) => TupleT(l, TupleT(r, right))
    case _ => new TupleTImpl(left, right)
  }
  def unapply(e: Sort): Option[(Sort, Sort)] = e match {
    case TupleTImpl(l, r) => Some((l,r))
    case _ => None
  }
  private case class TupleTImpl(val left : Sort, val right : Sort) extends TupleT {
    override def equals(other : Any) = other match {
      case that : TupleT => left == that.left && right == that.right
      case _ => false
    }
  }
}


/* subtype of a given type; for example TimeT = Subtype("the time that passes", Real) */
case class Subtype(name : String, sort : Sort) extends Sort

object PredefinedSorts {
  val RealXReal       = TupleT(Real, Real)
  val BoolXBool       = TupleT(Bool, Bool)
  val GameXBool       = TupleT(GameSort, Bool)
  val BoolXProgram    = TupleT(Bool, ProgramSort)
  val GameXGame       = TupleT(GameSort, GameSort)
  val ProgramXProgram = TupleT(ProgramSort, ProgramSort)
  val BoolXProgramXProgram    = TupleT(Bool, ProgramXProgram)
}

import PredefinedSorts._

/**
 * Expression infrastructure
 *===========================
 */
sealed abstract class Expr(val sort : Sort) extends Annotable

/* atom / leaf expression */
sealed trait Atom extends Expr

/* unary expression */
abstract class Unary(sort : Sort, val domain : Sort, val child : Expr) extends Expr(sort) {

  applicable

  @elidable(ASSERTION) def applicable = require(domain == child.sort, "Sort Mismatch in Unary Expr: " + domain + " " + child.sort)

}

/* binary expression (n-ary is encoded as binary of binary of ... */
abstract class Binary(sort : Sort, val domain : TupleT, val left : Expr, val right : Expr) extends Expr(sort) {

  applicable

  @elidable(ASSERTION) def applicable =
        require(domain.left == left.sort && domain.right == right.sort, "Sort Mismatch in Binary Expr")

}

abstract class Ternary(sort: Sort, val domain: TupleT, val fst: Expr, val snd: Expr, val thd: Expr) extends Expr(sort) {
  applicable

  @elidable(ASSERTION) def applicable = require(domain.left == fst.sort
    && (domain.right match { case TupleT(a,b) => snd.sort == a && thd.sort == b case _ => false}),
    "Sort Mismatch in Binary Expr")
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

abstract class NamedSymbol(val name : String, val index: Option[Int], val domain: Sort, sort : Sort) extends Expr(sort) {

  //private val id : Int = NameCounter.next()

  //def deepName = name + "_" + index + "_" + id;

  override def equals(e : Any) = e match {
    case x: NamedSymbol => this.name == x.name && this.sort == x.sort && this.index == x.index && this.domain == x. domain
    case _ => false
  }

  //def deepEquals(x : NamedSymbol) =
  //  flatEquals(x) && this.id == x.id
}

object Variable {
  def apply(name : String, index: Option[Int] = None, sort : Sort): Variable = new Variable(name, index, sort)
  def unapply(e: Any): Option[(String, Option[Int], Sort)] = e match {
    case x: Variable => Some((x.name, x.index, x.sort))
    case _ => None
  }
}
final class Variable(name : String, index: Option[Int] = None, sort : Sort) extends NamedSymbol(name, index, Unit, sort) with Atom with Term

object PredicateConstant {
  def apply(name : String, index: Option[Int] = None): PredicateConstant = new PredicateConstant(name, index)
  def unapply(e: Any): Option[(String, Option[Int])] = e match {
    case x: PredicateConstant => Some((x.name, x.index))
    case _ => None
  }
}
final class PredicateConstant(name : String, index: Option[Int] = None) extends NamedSymbol(name, index, Unit, Bool) with Formula

object ProgramConstant {
  def apply(name : String, index: Option[Int] = None): ProgramConstant = new ProgramConstant(name, index)
  def unapply(e: Any): Option[(String, Option[Int])] = e match {
    case x: ProgramConstant => Some((x.name, x.index))
    case _ => None
  }
}
class ProgramConstant(name : String, index: Option[Int] = None) extends NamedSymbol(name, index, Unit, ProgramSort) with AtomicProgram {
  def reads = Nil
  def writes = Nil
}

object Function {
  def apply(name : String, index: Option[Int] = None, domain: Sort, sort : Sort): Function = new Function(name, index, domain, sort)
  def unapply(e: Any): Option[(String, Option[Int], Sort, Sort)] = e match {
    case x: Function => Some((x.name, x.index, x.domain, x.sort))
    case _ => None
  }
}
final class Function (name : String, index: Option[Int] = None, domain : Sort, sort : Sort) extends NamedSymbol(name, index, domain, sort)

/**
 * Constant, Variable and Function Expressions
 *=============================================
 */

/* The * in nondet. assignments */
// class Random(sort : Sort) extends Atom(sort) /* SOONISH BUT NOT NOW */

object True extends Expr(Bool) with Formula with Term with Atom
object False extends Expr(Bool) with Formula with Term with Atom

/**
 * - Make sure that there are no constants for negative numbers
 * - Strip all the trailing zeros
 */
object Number {
  def apply(value: BigDecimal) : Term = Number(Real, value)
  def apply(sort: Sort, number: BigDecimal) : Term = {
    var n = number.underlying.stripTrailingZeros.toPlainString
    // bugfix for 0.0 and so on (will be fixed in BigDecimal in Java 8
    // http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6480539
    while(n.contains(".") && (n.endsWith("0") || n.endsWith("."))) {
      n = n.substring(0, n.length() - 1)
    }
    require(BigDecimal(n).underlying.compareTo(number.underlying()) == 0,
      "Stripping trailing zeros should not change the value of a number " + number + " != " + n)
    val value = BigDecimal(n)
    if(value < 0)
      new Neg(sort, new NumberObj(sort, value.abs))
    else
      new NumberObj(sort, value)
  }

  def unapply(e: Any): Option[(Sort, BigDecimal)] = e match {
    case x: NumberObj => Some((x.sort,x.value.asInstanceOf[BigDecimal]))
    case _ => None
  }
  private final class NumberObj(sort : Sort, val value : BigDecimal) extends Expr(sort) with Atom with Term {
    override def equals(e: Any): Boolean = e match {
      case Number(a, b) => a == sort && b == value
      case _ => false
    }
  }
}

/* function application */
object Apply {
  def apply(function: Function, child: Term): Apply = new Apply(function, child)
  def unapply(e: Any): Option[(Function, Term)] = e match {
    case x: Apply => x.child match {
      case t: Term => Some((x.function, t))
      case _ => None
    }
    case _ => None
  }
}
final class Apply(val function : Function, child : Term)
           extends Unary(function.sort, function.domain, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case Apply(f, t) => f == function && t == child
    case _ => false
  }
}

/*
 * Predicate application
 *
 * Note that this is necessary to ensure that predicates actually implement
 * the trait Formula
 */
object ApplyPredicate {
  def apply(function: Function, child: Term): ApplyPredicate = new ApplyPredicate(function, child)
  def unapply(e: Any): Option[(Function, Term)] = e match {
    case x: ApplyPredicate => x.child match {
      case t: Term => Some((x.function, t))
      case _ => None
    }
    case _ => None
  }
}
final class ApplyPredicate(val function : Function, child : Term)
  extends Unary(Bool, function.domain, child) with Formula {
  applicable

  @elidable(ASSERTION) override def applicable = super.applicable; require(function.sort == Bool,
    "Sort mismatch in if then else condition: "  + function.sort + " is not Bool")

  override def equals(e: Any): Boolean = e match {
    case ApplyPredicate(f, t) => f == function && t == child
    case _ => false
  }
}

/* combine subexpressions into a vector */
object Pair {
  def apply(domain : TupleT, left : Term, right : Term) = new Pair(domain, left, right)
  def unapply(e: Any): Option[(TupleT, Term, Term)] = e match {
    case x: Pair => (x.left, x.right) match {
      case (a: Term, b: Term) => Some((x.domain, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class Pair(domain : TupleT, left : Term, right : Term) extends Binary(domain, domain, left, right) with Term {
  override def equals(e: Any): Boolean = e match {
    case Pair(a, b, c) => domain == a && left == b && right == c
    case _ => false
  }
}

/* extract elements from a vector expression */
final class Left (domain : TupleT, child : Pair) extends Unary(domain.left, domain, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case x: Left => domain == x.domain && child  == x.child
    case _ => false
  }
}
final class Right(domain : TupleT, child : Pair) extends Unary(domain.right, domain, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case x: Right => domain == x.domain && child  == x.child
    case _ => false
  }

}


/**
 * Formulas
 *======================
 */

sealed trait Formula extends Expr
/* Bool -> Bool */
abstract class UnaryFormula(child : Formula) extends Unary(Bool, Bool, child) with Formula
/* Bool x Bool -> Bool */
abstract class BinaryFormula(left : Formula, right : Formula) extends Binary(Bool, BoolXBool, left, right) with Formula

object Not {
  def apply(child: Formula): Formula = new Not(child)
  def unapply(e: Any): Option[Formula] = e match {
    case x: Not => Some(x.child.asInstanceOf[Formula])
    case _ => None
  }
}
final class Not   (child : Formula) extends UnaryFormula(child) {
  override def equals(e: Any): Boolean = e match {
    case Not(a) => a == child
    case _ => false
  }
}
object And {
  def apply(left: Formula, right: Formula): Formula = new And(left, right)
  def unapply(e: Any): Option[(Formula,Formula)] = e match {
    case x: And => Some((x.left.asInstanceOf[Formula],x.right.asInstanceOf[Formula]))
    case _ => None
  }
}
final class And   (left : Formula, right : Formula) extends BinaryFormula(left, right) {
  override def equals(e: Any): Boolean = e match {
    case And(a, b) => left == a && right == b
    case _ => false
  }
}
object Or {
  def apply(left: Formula, right: Formula): Formula = new Or(left, right)
  def unapply(e: Any): Option[(Formula,Formula)] = e match {
    case x: Or => Some((x.left.asInstanceOf[Formula],x.right.asInstanceOf[Formula]))
    case _ => None
  }
}
final class Or    (left : Formula, right : Formula) extends BinaryFormula(left, right) {
  override def equals(e: Any): Boolean = e match {
    case Or(a, b) => left == a && right == b
    case _ => false
  }
}
object Imply {
  def apply(left: Formula, right: Formula): Formula = new Imply(left, right)
  def unapply(e: Any): Option[(Formula,Formula)] = e match {
    case x: Imply => Some((x.left.asInstanceOf[Formula],x.right.asInstanceOf[Formula]))
    case _ => None
  }
}
final class Imply (left : Formula, right : Formula) extends BinaryFormula(left, right) {
  override def equals(e: Any): Boolean = e match {
    case Imply(a, b) => left == a && right == b
    case _ => false
  }
}
object Equiv {
  def apply(left: Formula, right: Formula): Equiv = new Equiv(left, right)
  def unapply(e: Any): Option[(Formula,Formula)] = e match {
    case x: Equiv => Some((x.left.asInstanceOf[Formula],x.right.asInstanceOf[Formula]))
    case _ => None
  }
}
final class Equiv (left : Formula, right : Formula) extends BinaryFormula(left, right) {
  override def equals(e: Any): Boolean = e match {
    case Equiv(a, b) => left == a && right == b
    case _ => false
  }
}

abstract class BinaryRelation(domain : Sort, left : Expr, right : Expr)
  extends Binary(Bool, TupleT(domain, domain), left, right) with Formula

/* equality */
object Equals {
  def apply(domain : Sort = Real, left : Expr, right : Expr): Equals = new Equals(domain, left, right)
  def unapply(e: Any): Option[(Sort, Expr, Expr)] = e match {
    case x: Equals => x.domain match {
      case TupleT(a, b) if (a == b) => Some((x.domain, x.left, x.right))
      case _ => None
    }
    case _ => None
  }
}
final class Equals   (domain : Sort = Real, left : Expr, right : Expr) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case Equals(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
}

object NotEquals {
  def apply(domain : Sort = Real, left : Expr, right : Expr): NotEquals = new NotEquals(domain, left, right)
  def unapply(e: Any): Option[(Sort, Expr, Expr)] = e match {
    case x: NotEquals => x.domain match {
      case TupleT(a, b) if (a == b) => Some((x.domain, x.left, x.right))
      case _ => None
    }
    case _ => None
  }
}
final class NotEquals(domain : Sort = Real, left : Expr, right : Expr) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case NotEquals(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
}

/* comparison */
object GreaterThan {
  def apply(domain : Sort = Real, left : Term, right : Term): GreaterThan = new GreaterThan(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: GreaterThan => (x.domain, x.left, x.right) match {
      case (TupleT(s, t), a: Term, b: Term) if s == t => Some((s, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class GreaterThan  (domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case GreaterThan(d, a, b)  => d == domain && left == a && right == b
    case _ => false
  }
}

object GreaterEquals {
  def apply(domain : Sort = Real, left : Term, right : Term): GreaterEquals = new GreaterEquals(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: GreaterEquals => (x.domain, x.left, x.right) match {
      case (TupleT(s, t), a: Term, b: Term) if s == t => Some((s, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class GreaterEquals(domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case GreaterEquals(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
}

object LessEquals {
  def apply(domain : Sort = Real, left : Term, right : Term): LessEquals = new LessEquals(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: LessEquals => (x.domain, x.left, x.right) match {
      case (TupleT(s, t), a: Term, b: Term) if s == t => Some((s, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class LessEquals   (domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case LessEquals(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
}

object LessThan {
  def apply(domain : Sort = Real, left : Term, right : Term): LessThan = new LessThan(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: LessThan => (x.domain, x.left, x.right) match {
      case (TupleT(s, t), a: Term, b: Term) if s == t => Some((s, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class LessThan     (domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case LessThan(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
}

/* temporal */
final class Globally (child : Formula) extends UnaryFormula(child) { /* []\Phi e.g., in [\alpha] []\Phi */
  override def equals(e: Any): Boolean = e match {
    case x: Globally => child == x.child
    case _ => false
  }
}
final class Finally  (child : Formula) extends UnaryFormula(child) {/* <>\Phi e.g., in [\alpha] <>\Phi */
  override def equals(e: Any): Boolean = e match {
    case x: Finally => child == x.child
    case _ => false
  }
}

final class FormulaDerivative(child : Formula)    extends UnaryFormula(child) {
  override def equals(e: Any): Boolean = e match {
    case x: FormulaDerivative => child == x.child
    case _ => false
  }
}

/**
 * Terms
 *==================
 */

sealed trait Term extends Expr
object Neg {
  def apply(sort: Sort, child: Term): Neg = new Neg(sort, child)
  def unapply(e: Any): Option[(Sort, Term)] = e match {
    case x: Neg => x.child match {
      case c: Term => Some((x.sort, c))
      case _ => None
    }
    case _ => None
  }
}
final class Neg     (sort : Sort, child : Term) extends Unary(sort, sort, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case Neg(a, b) => a == sort && b == child
    case _ => false
  }
}

object Add {
  def apply(sort: Sort, left: Term, right: Term): Add = new Add(sort, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: Add => (x.left, x.right) match {
      case (l: Term, r: Term) => Some((x.sort, l, r))
      case _ => None
    }
    case _ => None
  }
}
final class Add     (sort : Sort, left  : Term, right : Term) extends Binary(sort, TupleT(sort, sort), left, right) with Term {
  override def equals(e: Any): Boolean = e match {
    case Add(a, b, c) => a == sort && b == left && c == right
    case _ => false
  }
}

object Subtract {
  def apply(sort: Sort, left: Term, right: Term): Subtract = new Subtract(sort, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: Subtract => (x.left, x.right) match {
      case (l: Term, r: Term) => Some((x.sort, l, r))
      case _ => None
    }
    case _ => None
  }
}
final class Subtract(sort : Sort, left  : Term, right : Term) extends Binary(sort, TupleT(sort, sort), left, right) with Term {
  override def equals(e: Any): Boolean = e match {
    case Subtract(a, b, c) => a == sort && b == left && c == right
    case _ => false
  }
}

object Multiply {
  def apply(sort: Sort, left: Term, right: Term): Multiply = new Multiply(sort, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: Multiply => (x.left, x.right) match {
      case (l: Term, r: Term) => Some((x.sort, l, r))
      case _ => None
    }
    case _ => None
  }
}
final class Multiply(sort : Sort, left  : Term, right : Term) extends Binary(sort, TupleT(sort, sort), left, right) with Term {
  override def equals(e: Any): Boolean = e match {
    case Multiply(a, b, c) => a == sort && b == left && c == right
    case _ => false
  }
}

object Divide {
  def apply(sort: Sort, left: Term, right: Term): Divide = new Divide(sort, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: Divide => (x.left, x.right) match {
      case (l: Term, r: Term) => Some((x.sort, l, r))
      case _ => None
    }
    case _ => None
  }
}
final class Divide  (sort : Sort, left  : Term, right : Term) extends Binary(sort, TupleT(sort, sort), left, right) with Term {
  override def equals(e: Any): Boolean = e match {
    case Divide(a, b, c) => a == sort && b == left && c == right
    case _ => false
  }
}

object Exp {
  def apply(sort: Sort, left: Term, right: Term): Exp = new Exp(sort, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: Exp => (x.left, x.right) match {
      case (l: Term, r: Term) => Some((x.sort, l, r))
      case _ => None
    }
    case _ => None
  }
}
final class Exp     (sort : Sort, left  : Term, right : Term) extends Binary(sort, TupleT(sort, sort), left, right) with Term {
  override def equals(e: Any): Boolean = e match {
    case Exp(a, b, c) => a == sort && b == left && c == right
    case _ => false
  }
}

object Derivative {
  def apply(sort: Sort, child: Term): Derivative = new Derivative(sort, child)
  def unapply(e: Any): Option[(Sort, Term)] = e match {
    case x: Derivative => x.child match {
      case c: Term => Some((x.sort, c))
      case _ => None
    }
    case _ => None
  }
}
final class Derivative(sort : Sort, child : Term) extends Unary(sort, sort, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case Derivative(a, b) => a == sort && b == child
    case _ => false
  }
}

final class IfThenElseTerm(cond: Formula, then: Term, elseT: Term)
  extends Ternary(then.sort, TupleT(Bool, TupleT(then.sort, elseT.sort)), cond, then, elseT) with Term {
  applicable

  @elidable(ASSERTION) override def applicable = super.applicable; require(then.sort == elseT.sort, "Sort mismatch" +
    "in if-then-else statement: " + then.sort + " != " + elseT.sort)

  override def equals(e: Any): Boolean = e match {
    case x: IfThenElseTerm => fst == x.fst && snd == x.snd && thd == x.thd
    case _ => false
  }
}
/**
 * Games
 *=======
 */

sealed trait Game extends Expr {
  def reads: Seq[NamedSymbol]
  def writes: Seq[NamedSymbol]
}
/* Modality */
object Modality {
  def unapply(e: Any): Option[(Game, Formula)] = e match {
    case x: Modality => (x.left, x.right) match {
      case (a: Game, b: Formula) => Some((a,b))
      case _ => None
    }
    case _ => None
  }
}
final class Modality (left : Game, right : Formula) extends Binary(Bool, GameXBool, left, right) with Formula {
  def reads: Seq[NamedSymbol] = ???
  def writes: Seq[NamedSymbol] = left.writes

  override def equals(e: Any): Boolean = e match {
    case Modality(a, b) => a == left && b == right
    case _ => false
  }
}

abstract class UnaryGame  (child : Game) extends Unary(GameSort, GameSort, child) with Game
abstract class BinaryGame (left : Game, right : Game) extends Binary(GameSort, GameXGame, left, right) with Game

/* Games */
object BoxModality {
  def apply(child: Program, f: Formula): Modality = new Modality(new BoxModality(child), f)
  def unapply(e: Any): Option[(Program, Formula)] = e match {
    case Modality(x: BoxModality, f) => x.child match {
      case p: Program => Some((p, f))
      case _ => None
    }
    case _ => None
  }
}
final class BoxModality     (child : Program) extends Unary(GameSort, ProgramSort, child) with Game {
  def reads = child.reads
  def writes = child.writes

  override def equals(e: Any): Boolean = e match {
    case x: BoxModality => x.child == child
    case _ => false
  }
}
object DiamondModality {
  def apply(child: Program, f: Formula): Modality = new Modality(new DiamondModality(child), f)
  def unapply(e: Expr): Option[(Program, Formula)] = e match {
    case Modality(x: DiamondModality, f) => x.child match {
      case p: Program => Some((p, f))
      case _ => None
    }
    case _ => None
  }
}
final class DiamondModality (child : Program) extends Unary(GameSort, ProgramSort, child) with Game {
  def reads = child.reads
  def writes = child.writes

  override def equals(e: Any): Boolean = e match {
    case x: DiamondModality => x.child == child
    case _ => false
  }
}

final class BoxStar         (child : Game)    extends UnaryGame(child){
  def reads = child.reads
  def writes = child.writes

  override def equals(e: Any): Boolean = e match {
    case x: BoxStar => x.child == child
    case _ => false
  }
}
final class DiamondStar     (child : Game)    extends UnaryGame(child) {
  def reads = child.reads
  def writes = child.writes

  override def equals(e: Any): Boolean = e match {
    case x: DiamondStar => x.child == child
    case _ => false
  }
}
final class SequenceGame    (left  : Game, right : Game) extends BinaryGame(left, right) {
  def reads = left.reads ++ right.reads
  def writes = left.writes ++ left.writes

  override def equals(e: Any): Boolean = e match {
    case x: SequenceGame => x.left == left && x.right == right
    case _ => false
  }
}
final class DisjunctGame    (left  : Game, right : Game) extends BinaryGame(left, right) {
  def reads = left.reads ++ right.reads
  def writes = left.writes ++ left.writes

  override def equals(e: Any): Boolean = e match {
    case x: DisjunctGame => x.left == left && x.right == right
    case _ => false
  }
}
final class ConjunctGame    (left  : Game, right : Game) extends BinaryGame(left, right) {
  def reads = left.reads ++ right.reads
  def writes = left.writes ++ left.writes

  override def equals(e: Any): Boolean = e match {
    case x: ConjunctGame => x.left == left && x.right == right
    case _ => false
  }
}

/**
 * Programs
 *==========
 */

sealed trait Program extends Expr {
  def reads: Seq[NamedSymbol]
  def writes: Seq[NamedSymbol]
}

abstract class UnaryProgram  (child : Program) extends Unary(ProgramSort, ProgramSort, child) with Program
abstract class BinaryProgram (left  : Program, right : Program) extends Binary(ProgramSort, ProgramXProgram, left, right) with Program

object Sequence {
  def apply(left: Program, right: Program) = new Sequence(left, right)
  def unapply(e: Any): Option[(Program, Program)] = e match {
    case x: Sequence => (x.left, x.right) match {
      case (a: Program, b: Program) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class Sequence(left  : Program, right : Program) extends BinaryProgram(left, right) {
  def reads = left.reads ++ right.reads
  def writes = left.writes ++ left.writes

  override def equals(e: Any): Boolean = e match {
    case x: Sequence => x.left == left && x.right == right
    case _ => false
  }
}

object Choice {
  def apply(left: Program, right: Program) = new Choice(left, right)
  def unapply(e: Any): Option[(Program, Program)] = e match {
    case x: Choice => (x.left, x.right) match {
      case (a: Program, b: Program) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class Choice  (left  : Program, right : Program) extends BinaryProgram(left, right) {
  def reads = left.reads ++ right.reads
  def writes = left.writes ++ left.writes

  override def equals(e: Any): Boolean = e match {
    case x: Choice => x.left == left && x.right == right
    case _ => false
  }
}

object Parallel {
  def apply(left: Program, right: Program) = new Parallel(left, right)
  def unapply(e: Any): Option[(Program, Program)] = e match {
    case x: Parallel => (x.left, x.right) match {
      case (a: Program, b: Program) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class Parallel(left  : Program, right : Program) extends BinaryProgram(left, right) {
  def reads = left.reads ++ right.reads
  def writes = left.writes ++ left.writes

  override def equals(e: Any): Boolean = e match {
    case x: Parallel => x.left == left && x.right == right
    case _ => false
  }
}


object Loop {
  def apply(child: Program) = new Loop(child)
  def unapply(e: Any): Option[Program] = e match {
    case x: Loop => x.child match {
      case a: Program => Some(a)
      case _ => None
    }
    case _ => None
  }
}
final class Loop    (child : Program)               extends UnaryProgram(child) {
  def reads = child.reads
  def writes = child.writes

  override def equals(e: Any): Boolean = e match {
    case x: Loop => x.child == child
    case _ => false
  }
}

object IfThen {
  def apply(cond: Formula, then: Program) = new IfThen(cond, then)
  def unapply(e: Any): Option[(Formula, Program)] = e match {
    case x: IfThen => (x.left, x.right) match {
      case (a: Formula, b: Program) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class IfThen(cond: Formula, then: Program) extends Binary(ProgramSort, BoolXProgram, cond, then) with Program {
  def reads = ???
  def writes = then.writes

  override def equals(e: Any): Boolean = e match {
    case x: IfThen => x.left == left && x.right == right
    case _ => false
  }
}

object IfThenElse {
  def apply(cond: Formula, then: Program, elseP: Program) = new IfThenElse(cond, then, elseP)
  def unapply(e: Any): Option[(Formula, Program, Program)] = e match {
    case x: IfThenElse => (x.fst, x.snd, x.thd) match {
      case (a: Formula, b: Program, c: Program) => Some((a, b, c))
      case _ => None
    }
    case _ => None
  }
}
final class IfThenElse(cond: Formula, then: Program, elseP: Program)
  extends Ternary(ProgramSort, BoolXProgramXProgram, cond, then, elseP) with Program {
  def reads = ???
  def writes = then.writes ++ elseP.writes

  override def equals(e: Any): Boolean = e match {
    case x: IfThenElse => x.fst == fst && x.snd == snd && x.thd == thd
    case _ => false
  }
}

/* TODO:
*
* - need QAssign
* - nondeterministic assign vs. Assign(Var, Random)
*/

sealed trait AtomicProgram extends Program

/**
 * Term -> Term in order to allow for the following cases:
 * x := 5
 * f(i) := 5
 * (x,y) := (5,5)
 */
object Assign {
  def apply(left: Term, right: Term): Assign = new Assign(left, right)
  def unapply(e: Any): Option[(Term, Term)] = e match {
    case x: Assign => (x.left, x.right) match {
      case (a: Term, b: Term) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class Assign(left: Term, right: Term) extends Binary(ProgramSort, TupleT(left.sort, left.sort), left, right) with AtomicProgram {
  def reads = ???
  def writes = VSearch.modified(left)

  override def equals(e: Any): Boolean = e match {
    case x: Assign => x.left == left && x.right == right
    case _ => false
  }
}


object NDetAssign {
  def apply(child: Term): NDetAssign = new NDetAssign(child)
  def unapply(e: Any): Option[Term] = e match {
    case x: NDetAssign => x.child match {
      case a: Term => Some(a)
      case _ => None
    }
    case _ => None
  }
}
final class NDetAssign(child: Term) extends Unary(ProgramSort, child.sort, child) with AtomicProgram {
  def reads = Nil
  def writes = VSearch.modified(child)

  override def equals(e: Any): Boolean = e match {
    case x: NDetAssign => x.child == child
    case _ => false
  }
}

object Test {
  def apply(child: Formula): Test = new Test(child)
  def unapply(e: Any): Option[Formula] = e match {
    case x: Test => x.child match {
      case a: Formula => Some(a)
      case _ => None
    }
    case _ => None
  }
}
final class Test(child : Formula) extends Unary(ProgramSort, Bool, child) with AtomicProgram {
  def reads = ???
  def writes = Nil

   override def equals(e: Any): Boolean = e match {
    case x: Test => x.child == child
    case _ => false
  }
}

/* child = differential algebraic formula */
object ContEvolve {
  def apply(child: Formula): ContEvolve = new ContEvolve(child)
  def unapply(e: Any): Option[Formula] = e match {
    case x: ContEvolve => x.child match {
      case a: Formula => Some(a)
      case _ => None
    }
    case _ => None
  }
}
final class ContEvolve(child : Formula) extends Unary(ProgramSort, Bool, child) with AtomicProgram {
  def reads = ???
  def writes = VSearch.primed(child)

  override def equals(e: Any): Boolean = e match {
    case x: ContEvolve => x.child == child
    case _ => false
  }
}

/** Normal form ODE data structures
 * \exists R a,b,c. (\D{x} = \theta & F)
 */
object NFContEvolve {
  def apply(vars: Seq[NamedSymbol], x: Term, theta: Term, f: Formula): NFContEvolve = new NFContEvolve(vars, x, theta, f)
  def unapply(e: Any): Option[(Seq[NamedSymbol], Term, Term, Formula)] = e match {
    case x: NFContEvolve => Some((x.vars, x.x, x.theta, x.f))
    case _ => None
  }
}
final class NFContEvolve(val vars: Seq[NamedSymbol], val x: Term, val theta: Term, val f: Formula) extends Expr(ProgramSort) with AtomicProgram {
  def reads = ???
  def writes = VSearch.primed(x)

  override def equals(e: Any): Boolean = e match {
    case o: NFContEvolve => o.vars == vars && o.x == x && o.theta == theta && o.f == f
    case _ => false
  }
}

/**
 * Quantifiers
 *=============
 */

abstract class Quantifier(val variables : Seq[NamedSymbol], child : Formula) extends UnaryFormula(child)

object Forall {
  def apply(variables : Seq[NamedSymbol], child : Formula): Forall = new Forall(variables, child)
  def unapply(e: Any): Option[(Seq[NamedSymbol], Formula)] = e match {
    case x: Forall => x.child match {
      case f: Formula => Some((x.variables, f))
      case _ => None
    }
    case _ => None
  }
}
final class Forall(variables : Seq[NamedSymbol], child : Formula) extends Quantifier(variables, child) {

  override def equals(e: Any): Boolean = e match {
    case x: Forall => x.variables == variables && x.child == child
    case _ => false
  }
}

object Exists {
  def apply(variables : Seq[NamedSymbol], child : Formula): Exists = new Exists(variables, child)
  def unapply(e: Any): Option[(Seq[NamedSymbol], Formula)] = e match {
    case x: Exists => x.child match {
      case f: Formula => Some((x.variables, f))
      case _ => None
    }
    case _ => None
  }
}
final class Exists(variables : Seq[NamedSymbol], child : Formula) extends Quantifier(variables, child) {
  override def equals(e: Any): Boolean = e match {
    case x: Exists => x.variables == variables && x.child == child
    case _ => false
  }
}

/**
 * Sequent notation
 */

final class Sequent(val pref: Seq[NamedSymbol], val ante: IndexedSeq[Formula], val succ: IndexedSeq[Formula])

object Sequent {
  def apply(pref: Seq[NamedSymbol], ante: IndexedSeq[Formula], succ: IndexedSeq[Formula]) : Sequent = new Sequent(pref, ante, succ)
}

/**
 *==================================================================================
 * Helpers
 *==================================================================================
 */

private object VSearch {
  def modified(e: Term): Seq[NamedSymbol] = e match {
    case Pair(dom, a, b) => modified(a) ++ modified(b)
    case Apply(f, args) => Seq(f)
    case x:Variable => Seq(x)
    case Neg(_, a) => modified(a)
    case Add(_, a, b) => modified(a) ++ modified(b)
    case Subtract(_, a, b) => modified(a) ++ modified(b)
    case Multiply(_, a, b) => modified(a) ++ modified(b)
    case Divide(_, a, b) => modified(a) ++ modified(b)
    case Exp(_, a, b) => modified(a) ++ modified(b)
    case _ => throw new IllegalArgumentException("Unexpected form" + e)
  }

  def primed(f: Formula): Seq[NamedSymbol] = f match {
    case Not(a) => primed(a)
    case And(a, b) => primed(a) ++ primed(b)
    case Or(a, b) => primed(a) ++ primed(b)
    case Imply(a, b) => primed(a) ++ primed(b)
    case Equiv(a, b) => primed(a) ++ primed(b)
    case ApplyPredicate(_, arg) => primed(arg)
    case _ => ???
  }

  def primed(t: Term): Seq[NamedSymbol] = t match {
    case Pair(_, a, b) => primed(a) ++ primed(b)
    case Derivative(_, x) => modified(x)
    case Neg(_, a) => primed(a)
    case Add(_, a, b) => primed(a) ++ primed(b)
    case Subtract(_, a, b) => primed(a) ++ primed(b)
    case Multiply(_, a, b) => primed(a) ++ primed(b)
    case Divide(_, a, b) => primed(a) ++ primed(b)
    case Exp(_, a, b) => primed(a) ++ primed(b)
    case Apply(f, args) => primed(args)
    case _ => ???
  }
}

