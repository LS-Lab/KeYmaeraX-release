/**
 * @author Marcus Völp
 * @author Jan-David Quesel
 * @author aplatzer
 * @author smitsch
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.elidable
import scala.annotation.elidable._

import scala.math._

import edu.cmu.cs.ls.keymaera.parser._
import scala.collection.immutable

//the pretty printer.

/**
 * External functions imported in core but not used in proof check mode
 * @TODO ???
 */
trait Annotable

/**
 * Prover Core
 */

object HashFn {
  /**
   * Next free prime is 281
   * @param prime
   * @param a
   * @return
   */
  def hash(prime: Int, a: Any*): Int = a.length match {
    case 0 => prime
    case 1 => prime + a.head.hashCode
    case _ => (prime * hash(prime, a.tail)) + hash(prime, a.head)
  }
}

import HashFn.hash

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

/* sort of modal operators */
object ModalOpSort extends Sort

/* sort of games */
//object GameSort extends Sort

/* sort of hybrid programs */
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
    override def hashCode: Int = hash(3, left, right)
  }
}


/* subtype of a given type; for example TimeT = Subtype("the time that passes", Real) */
//case class Subtype(name : String, sort : Sort) extends Sort

/**
 * Expression infrastructure
 *===========================
 */
sealed abstract class Expr(val sort : Sort) extends Annotable {
  override def toString = super.toString() + " (" + prettyString() + ")"
  def prettyString() = new KeYmaeraPrettyPrinter().stringify(this)
}

/* atom / leaf expression */
sealed trait Atom extends Expr

/* unary expression */
abstract class Unary(sort : Sort, val domain : Sort, val child : Expr) extends Expr(sort) {

  applicable

  @elidable(ASSERTION) def applicable = require(domain == child.sort, "Sort Mismatch in Unary Expr. Required " + domain + " but found " + child.sort)

}

/* binary expression (n-ary is encoded as binary of binary of ... */
abstract class Binary(sort : Sort, val domain : TupleT, val left : Expr, val right : Expr) extends Expr(sort) {

  applicable

  @elidable(ASSERTION) def applicable =
        require(domain.left == left.sort && domain.right == right.sort, "Sort Mismatch in Binary Expr " + domain.left + "(" + domain + ") != " + left.sort + "(" + left + ")" )

}

abstract class Ternary(sort: Sort, val domain: TupleT, val fst: Expr, val snd: Expr, val thd: Expr) extends Expr(sort) {
  applicable

  @elidable(ASSERTION) def applicable = require(domain.left == fst.sort
    && (domain.right match { case TupleT(a,b) => snd.sort == a && thd.sort == b case _ => false}),
    "Sort Mismatch in Binary Expr")
}

/**
 * Variables and Functions
 *=========================
 */
abstract class NamedSymbol(val name : String, val index: Option[Int], val domain: Sort, sort : Sort) extends Expr(sort) {
  override def equals(e : Any): Boolean = {
    e match {
      case x: NamedSymbol =>
       this.getClass == x.getClass && this.name == x.name && this.sort == x.sort && this.index == x.index && this.domain == x. domain
      case _ => false
    }
  }
  override def hashCode: Int = hash(5, getClass, name, index, domain)
}

/*********************************************************************************
 * Differential Dynamic Logic
 *********************************************************************************
 */

object Anything extends NamedSymbol("\\anything", None, Unit, Real) with Atom with Term
object Nothing extends NamedSymbol("\\nothing", None, Unit, Unit) with Atom with Term
object CDot extends NamedSymbol("\\cdot", None, Unit, Real) with Atom with Term

object DifferentialSymbol {
  def apply(symbol : NamedSymbol): DifferentialSymbol = new DifferentialSymbol(symbol)

  def unapply(e: Any): Option[NamedSymbol] = e match {
    case x : DifferentialSymbol => Some(x.ns)
    case _ => None
  }
}
final class DifferentialSymbol(val ns : NamedSymbol) extends NamedSymbol(ns.name, ns.index, ns.domain, ns.sort) with Atom with Term

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
//@TODO replace with just predicate functions, alias functions that happen to be of type ()=>bool
final class PredicateConstant(name : String, index: Option[Int] = None) extends NamedSymbol(name, index, Unit, Bool) with Formula

object ProgramConstant {
  def apply(name : String, index: Option[Int] = None): ProgramConstant = new ProgramConstant(name, index)
  def unapply(e: Any): Option[(String, Option[Int])] = e match {
    case x: ProgramConstant => Some((x.name, x.index))
    case _ => None
  }
}
class ProgramConstant(name : String, index: Option[Int] = None) extends NamedSymbol(name, index, Unit, ProgramSort) with AtomicProgram

object DifferentialProgramConstant {
  def apply(name : String, index: Option[Int] = None): DifferentialProgramConstant = new DifferentialProgramConstant(name, index)
  def unapply(e: Any): Option[(String, Option[Int])] = e match {
    case x: DifferentialProgramConstant => Some((x.name, x.index))
    case _ => None
  }
}
class DifferentialProgramConstant(name : String, index: Option[Int] = None) extends NamedSymbol(name, index, Unit, ProgramSort) with AtomicProgram with DifferentialProgram

object Function {
  def apply(name : String, index: Option[Int] = None, domain: Sort, sort : Sort): Function = new Function(name, index, domain, sort)
  def unapply(e: Any): Option[(String, Option[Int], Sort, Sort)] = e match {
    case x: Function => Some((x.name, x.index, x.domain, x.sort))
    case _ => None
  }
}
final class Function (name : String, index: Option[Int] = None, domain : Sort, sort : Sort) extends NamedSymbol(name, index, domain, sort) {
  /**
   * A function is marked as external by using the external input during
   * function delcaration. External functions are passed as bare names to QE
   * backends.
   */
  var external : Boolean = false
  def markExternal() = {
    external = true
    this
  }
}

/**
 * Constant, Variable and Function Expressions
 *=============================================
 */

/* The * in nondet. assignments */
// class Random(sort : Sort) extends Atom(sort) /* SOONISH BUT NOT NOW */

object True extends Expr(Bool) with Formula with Term with Atom {
  def unapply(e: Any): Boolean = e.isInstanceOf[True.type]
//  def unapply(e: Any): Option[Any] = {
//    if(e.isInstanceOf[True.type]) Some("") else None
//  }
}
object False extends Expr(Bool) with Formula with Term with Atom {
  def unapply(e: Any): Boolean = e.isInstanceOf[False.type]
}

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
  object NumberObj {
    def apply(sort : Sort, value : BigDecimal) : NumberObj = new NumberObj(sort,value)
    def unapply(e : NumberObj) : Option[(Sort,BigDecimal)] = e match {
      case NumberObj(s, v) => Some((s,v))
      case _ => None
    }
  }
  final class NumberObj(sort : Sort, val value : BigDecimal) extends Expr(sort) with Atom with Term {
    override def equals(e: Any): Boolean = e match {
      case Number(a, b) => a == sort && b == value
      case _ => false
    }
    override def hashCode: Int = hash(7, sort, value)
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
  override def hashCode: Int = hash(11, function, child)
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
  override def hashCode: Int = hash(13, function, child)
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
  override def hashCode: Int = hash(17, domain, left, right)
}

/* extract elements from a vector expression */
final class Left (domain : TupleT, child : Pair) extends Unary(domain.left, domain, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case x: Left => domain == x.domain && child  == x.child
    case _ => false
  }
  override def hashCode: Int = hash(19, domain, child)
}
final class Right(domain : TupleT, child : Pair) extends Unary(domain.right, domain, child) with Term {
  override def equals(e: Any): Boolean = e match {
    case x: Right => domain == x.domain && child  == x.child
    case _ => false
  }
  override def hashCode: Int = hash(23, domain, child)
}


/**
 * Formulas
 *======================
 */

sealed trait Formula extends Expr
/* Bool -> Bool */
abstract class UnaryFormula(child : Formula) extends Unary(Bool, Bool, child) with Formula
/* Bool x Bool -> Bool */
abstract class BinaryFormula(left : Formula, right : Formula) extends Binary(Bool, TupleT(Bool, Bool), left, right) with Formula

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
  override def hashCode: Int = hash(29, domain, child)
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
  override def hashCode: Int = hash(31, left, right)
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
  override def hashCode: Int = hash(37, left, right)
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
  override def hashCode: Int = hash(41, left, right)
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
  override def hashCode: Int = hash(43, left, right)
}

abstract class BinaryRelation(domain : Sort, left : Expr, right : Expr)
  extends Binary(Bool, TupleT(domain, domain), left, right) with Formula

/* equality */
object Equals {
  def apply(domain : Sort = Real, left : Term, right : Term): Equals = new Equals(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: Equals => (x.domain, x.left, x.right) match {
      case (TupleT(a, b), c: Term, d: Term) if (a == b) => Some((a, c, d))
      case _ => None
    }
    case _ => None
  }
}
final class Equals   (domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case Equals(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
  override def hashCode: Int = hash(47, domain, left, right)
}

object ProgramEquals {
  def apply(left : Program, right : Program): ProgramEquals = new ProgramEquals(left, right)
  def unapply(e: Any): Option[(Program, Program)] = e match {
    case x: ProgramEquals => (x.left, x.right) match {
      case (c: Program, d: Program) => Some((c, d))
      case _ => None
    }
    case _ => None
  }
}
final class ProgramEquals   (left : Program, right : Program) extends BinaryRelation(ProgramSort, left, right) {
  override def equals(e: Any): Boolean = e match {
    case ProgramEquals(a, b) => left == a && right == b
    case _ => false
  }
  override def hashCode: Int = hash(239, domain, left, right)
}

object NotEquals {
  def apply(domain : Sort = Real, left : Term, right : Term): NotEquals = new NotEquals(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: NotEquals => (x.domain, x.left, x.right) match {
      case (TupleT(a, b), c: Term, d: Term) if (a == b) => Some((a, c, d))
      case _ => None
    }
    case _ => None
  }
}
final class NotEquals(domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case NotEquals(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
  override def hashCode: Int = hash(53, domain, left, right)
}

object ProgramNotEquals {
  def apply(left : Program, right : Program): ProgramNotEquals = new ProgramNotEquals(left, right)
  def unapply(e: Any): Option[(Program, Program)] = e match {
    case x: ProgramNotEquals => (x.left, x.right) match {
      case (c: Program, d: Program) => Some((c, d))
      case _ => None
    }
    case _ => None
  }
}
final class ProgramNotEquals   (left : Program, right : Program) extends BinaryRelation(ProgramSort, left, right) {
  override def equals(e: Any): Boolean = e match {
    case ProgramNotEquals(a, b) => left == a && right == b
    case _ => false
  }
  override def hashCode: Int = hash(241, domain, left, right)
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
  override def hashCode: Int = hash(59, domain, left, right)
}

object GreaterEqual {
  def apply(domain : Sort = Real, left : Term, right : Term): GreaterEqual = new GreaterEqual(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: GreaterEqual => (x.domain, x.left, x.right) match {
      case (TupleT(s, t), a: Term, b: Term) if s == t => Some((s, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class GreaterEqual(domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case GreaterEqual(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
  override def hashCode: Int = hash(61, domain, left, right)
}

object LessEqual {
  def apply(domain : Sort = Real, left : Term, right : Term): LessEqual = new LessEqual(domain, left, right)
  def unapply(e: Any): Option[(Sort, Term, Term)] = e match {
    case x: LessEqual => (x.domain, x.left, x.right) match {
      case (TupleT(s, t), a: Term, b: Term) if s == t => Some((s, a, b))
      case _ => None
    }
    case _ => None
  }
}
final class LessEqual   (domain : Sort = Real, left : Term, right : Term) extends BinaryRelation(domain, left, right) {
  override def equals(e: Any): Boolean = e match {
    case LessEqual(d, a, b) => d == domain && left == a && right == b
    case _ => false
  }
  override def hashCode: Int = hash(67, domain, left, right)
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
  override def hashCode: Int = hash(71, domain, left, right)
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
  override def hashCode: Int = hash(73, child)
}

object FormulaDerivative {
  def apply(child: Formula): Formula = new FormulaDerivative(child)
  def unapply(e: Any): Option[Formula] = e match {
    case x: FormulaDerivative => Some(x.child.asInstanceOf[Formula])
    case _ => None
  }
}
final class FormulaDerivative(child : Formula)    extends UnaryFormula(child) {
  override def equals(e: Any): Boolean = e match {
    case FormulaDerivative(a) => child == a
    case _ => false
  }
  override def hashCode: Int = hash(79, child)
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
  override def hashCode: Int = hash(83, sort, child)
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
  override def hashCode: Int = hash(89, sort, left, right)
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
  override def hashCode: Int = hash(97, sort, left, right)
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
  override def hashCode: Int = hash(101, sort, left, right)
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
  override def hashCode: Int = hash(103, sort, left, right)
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
  override def hashCode: Int = hash(107, sort, left, right)
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
  override def hashCode: Int = hash(109, sort, child)
}

object IfThenElseTerm {
  def apply(cond: Formula, thenT: Term, elseT: Term): Term = new IfThenElseTerm(cond, thenT, elseT)
  def unapply(e: Any): Option[(Formula, Term, Term)] = e match {
    case x: IfThenElseTerm => (x.fst, x.snd, x.thd) match {
      case (a: Formula, b: Term, c: Term) => Some((a, b, c))
      case _ => None
    }
    case _ => None
  }
}
final class IfThenElseTerm(cond: Formula, thenT: Term, elseT: Term)
  extends Ternary(thenT.sort, TupleT(Bool, TupleT(thenT.sort, elseT.sort)), cond, thenT, elseT) with Term {
  applicable

  @elidable(ASSERTION) override def applicable = super.applicable; require(thenT.sort == elseT.sort, "Sort mismatch" +
    "in if-then-else statement: " + thenT.sort + " != " + elseT.sort)

  override def equals(e: Any): Boolean = e match {
    case x: IfThenElseTerm => fst == x.fst && snd == x.snd && thd == x.thd
    case _ => false
  }
  override def hashCode: Int = hash(113, cond, thenT, elseT)
}
/**
 * Games
 *=======
 */

sealed trait ModalOp extends Expr

/* Modality */
object Modality {
  def apply(g: ModalOp, f: Formula): Formula = new Modality(g, f)
  def unapply(e: Any): Option[(ModalOp, Formula)] = e match {
    case x: Modality => (x.left, x.right) match {
      case (a: ModalOp, b: Formula) => Some((a,b))
      case _ => None
    }
    case _ => None
  }
}
final class Modality (left : ModalOp, right : Formula) extends Binary(Bool, TupleT(ModalOpSort, Bool), left, right) with Formula {
  override def equals(e: Any): Boolean = e match {
    case Modality(a, b) => a == left && b == right
    case _ => false
  }
  override def hashCode: Int = hash(127, left, right)
}

//abstract class UnaryGame  (child : Game) extends Unary(GameSort, GameSort, child) with Game
//abstract class BinaryGame (left : Game, right : Game) extends Binary(GameSort, TupleT(GameSort, GameSort), left, right) with Game

/* Modalities */
object BoxModality {
  def apply(child: Program): ModalOp = new BoxModality(child)
  def apply(child: Program, f: Formula): Modality = new Modality(new BoxModality(child), f)
  def unapply(e: Any): Option[(Program, Formula)] = e match {
    case Modality(x: BoxModality, f) => x.child match {
      case p: Program => Some((p, f))
      case _ => None
    }
    case _ => None
  }
}
final class BoxModality     (child : Program) extends Unary(ModalOpSort, ProgramSort, child) with ModalOp {
  override def equals(e: Any): Boolean = e match {
    case x: BoxModality => x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(131, child)
}
object DiamondModality {
  def apply(child: Program): ModalOp = new DiamondModality(child)
  def apply(child: Program, f: Formula): Modality = new Modality(new DiamondModality(child), f)
  def unapply(e: Expr): Option[(Program, Formula)] = e match {
    case Modality(x: DiamondModality, f) => x.child match {
      case p: Program => Some((p, f))
      case _ => None
    }
    case _ => None
  }
}
final class DiamondModality (child : Program) extends Unary(ModalOpSort, ProgramSort, child) with ModalOp {
  override def equals(e: Any): Boolean = e match {
    case x: DiamondModality => x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(137, child)
}


/**
 * Programs
 *==========
 */

sealed trait Program extends Expr

abstract class UnaryProgram  (child : Program) extends Unary(ProgramSort, ProgramSort, child) with Program
abstract class BinaryProgram (left  : Program, right : Program) extends Binary(ProgramSort, TupleT(ProgramSort, ProgramSort), left, right) with Program

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
  override def equals(e: Any): Boolean = e match {
    case x: Sequence => x.left == left && x.right == right
    case _ => false
  }
  override def hashCode: Int = hash(167, left, right)
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
  override def equals(e: Any): Boolean = e match {
    case x: Choice => x.left == left && x.right == right
    case _ => false
  }
  override def hashCode: Int = hash(173, left, right)
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
  override def equals(e: Any): Boolean = e match {
    case x: Parallel => x.left == left && x.right == right
    case _ => false
  }
  override def hashCode: Int = hash(179, left, right)
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
  override def equals(e: Any): Boolean = e match {
    case x: Loop => x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(181, child)
}

object IfThen {
  def apply(cond: Formula, thenT: Program): Program = new IfThen(cond, thenT)
  def unapply(e: Any): Option[(Formula, Program)] = e match {
    case x: IfThen => (x.left, x.right) match {
      case (a: Formula, b: Program) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class IfThen(cond: Formula, thenP: Program) extends Binary(ProgramSort, TupleT(Bool, ProgramSort), cond, thenP) with Program {
  override def equals(e: Any): Boolean = e match {
    case x: IfThen => x.left == left && x.right == right
    case _ => false
  }
  override def hashCode: Int = hash(191, cond, thenP)
}

object IfThenElse {
  def apply(cond: Formula, thenP: Program, elseP: Program): Program = new IfThenElse(cond, thenP, elseP)
  def unapply(e: Any): Option[(Formula, Program, Program)] = e match {
    case x: IfThenElse => (x.fst, x.snd, x.thd) match {
      case (a: Formula, b: Program, c: Program) => Some((a, b, c))
      case _ => None
    }
    case _ => None
  }
}
final class IfThenElse(cond: Formula, thenP: Program, elseP: Program)
  extends Ternary(ProgramSort, TupleT(Bool, TupleT(ProgramSort, ProgramSort)), cond, thenP, elseP) with Program {

  override def equals(e: Any): Boolean = e match {
    case x: IfThenElse => x.fst == fst && x.snd == snd && x.thd == thd
    case _ => false
  }
  override def hashCode: Int = hash(193, cond, thenP, elseP)
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
  override def equals(e: Any): Boolean = e match {
    case x: Assign => x.left == left && x.right == right
    case _ => false
  }
  override def hashCode: Int = hash(197, left, right)
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
  override def equals(e: Any): Boolean = e match {
    case x: NDetAssign => x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(199, child)
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
  override def equals(e: Any): Boolean = e match {
    case x: Test => x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(211, child)
}

/* child = differential algebraic formula */
@deprecated(message="Use AtomicODE, ODEProduct, ODESystem etc. instead", since="")
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
final class ContEvolve(child : Formula) extends Unary(ProgramSort, Bool, child) with AtomicProgram with DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case x: ContEvolve => x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(223, child)
}

object CheckedContEvolveFragment {
  def apply(child: DifferentialProgram): CheckedContEvolveFragment = {
    assert(!child.isInstanceOf[CheckedContEvolveFragment])
    new CheckedContEvolveFragment(child)
  }
  def unapply(e:Any) : Option[DifferentialProgram] = e match {
    case x: CheckedContEvolveFragment => {
      assert(x.child.isInstanceOf[DifferentialProgram]) //the lone constructor should enforce this.
      Some(x.child.asInstanceOf[DifferentialProgram])
    }
    case _ => None
  }
}
final class CheckedContEvolveFragment(child:DifferentialProgram) extends Unary(ProgramSort, ProgramSort, child) with AtomicProgram with DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case x: CheckedContEvolveFragment => x.child.equals(child)
    case _ => false
  }
  override def hashCode: Int = hash(224, child)
}


sealed trait DifferentialProgram extends Program {
  def normalize() = this
}

object AtomicODE {
  def apply(x: Derivative, theta: Term): AtomicODE = new AtomicODE(x, theta)
  def unapply(e: Any): Option[(Derivative, Term)] = e match {
    case x: AtomicODE => Some((x.x, x.theta))
    case _ => None
  }
}
//@TODO Change types to "val x: DifferentialSymbol" for now?
final class AtomicODE(val x: Derivative, val theta: Term) extends Expr(ProgramSort) with AtomicProgram with DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case o: AtomicODE => o.x == x && o.theta == theta
    case _ => false
  }
  override def hashCode: Int = hash(271, x, theta)
}

object EmptyODE {
  def apply() = new EmptyODE()
  def unapply(x:Any): Option[_] = { None }
}
//@TODO Turn into object since singleton
final class EmptyODE extends Expr(ProgramSort) with AtomicProgram with DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case _: EmptyODE => true
    case ODEProduct(_: EmptyODE, _: EmptyODE) => true
    case _ => false
  }
  override def hashCode: Int = hash(269)
}

object ODEProduct {
  def apply(left: DifferentialProgram, right: DifferentialProgram) = new ODEProduct(left, right)
  def apply(left: DifferentialProgram) = new ODEProduct(left, EmptyODE())
  def unapply(e: Any): Option[(DifferentialProgram, DifferentialProgram)] = e match {
    case x: ODEProduct => (x.left, x.right) match {
      case (a: DifferentialProgram, b: DifferentialProgram) => Some((a, b))
      case _ => None
    }
    case _ => None
  }
}
final class ODEProduct(left: DifferentialProgram, right: DifferentialProgram)
    extends BinaryProgram(left, right) with DifferentialProgram {
  def flatten(): List[DifferentialProgram] = {
    val leftList = left match {
      case left: ODEProduct => left.flatten()
      case _ => left :: Nil
    }
    val rightList = right match {
      case right: ODEProduct => right.flatten()
      case _ => right :: Nil
    }
    leftList ++ rightList
  }

  override def normalize() = {
    //Note: this has to be a type-level comparison or else equals diverges.
    val pl = flatten().filter(!_.isInstanceOf[EmptyODE])
    if (pl.isEmpty) EmptyODE()
    else pl.foldRight[DifferentialProgram](EmptyODE())((prg, prod) => ODEProduct(prg, prod))
  }

  //@todo SYMMETRY!
  override def equals(e: Any): Boolean = equalsContEvolve(e)

  //Alternative implementations:
  private def equalsContEvolve(e:Any) = {
    e match {
      case e: ODEProduct =>
        //Note: this has to be a type-level comparison or else equals diverges (also: cannot use normalize here for the same reason)
        def fn(x: DifferentialProgram) = !x.isInstanceOf[EmptyODE]
        this.flatten().filter(fn).equals(e.flatten().filter(fn))
      case _: EmptyODE => left.isInstanceOf[EmptyODE] && right.isInstanceOf[EmptyODE]
      case _ => false
    }
  }

  private def saferEquals(e:Any):Boolean = e match {
    case e : ODEProduct => {
      this.left.equals(e.left) && this.right.equals(e.right)
    }
    case _ => (this.left.equals(e) && this.right.equals(EmptyODE())) || (this.left.equals(EmptyODE()) && this.right.equals(e))
  }

  override def hashCode: Int = hash(257, left, right)
}

/**
 * Normal form differential equation data structures for explicit ODE
 * NFContEvolve(Seq(a,b,c), child, F) is \exists R a,b,c. (\D{x_1} = \theta_1, ..., \D{x_n)=\theta_n & F) where a,b,c are disturbances.
 * See page 10 of the DAL paper.
 * @param disturbance list of disturbance quantifiers
 * @param child the ordinary differential equation (in cons list representation)
 * @param constraint evolution domain constraint.
 */
object ODESystem {
  def apply(disturbance: Seq[NamedSymbol], child: DifferentialProgram, constraint: Formula) = new ODESystem(disturbance, child, constraint)
  def apply(child: DifferentialProgram, constraint: Formula) = new ODESystem(Nil, child, constraint)

  def unapply(e: Any): Option[(Seq[NamedSymbol], DifferentialProgram, Formula)] = e match {
    case s: ODESystem => Some(s.disturbance, s.child, s.constraint)
    case _ => None
  }
}
final class ODESystem(val disturbance: Seq[NamedSymbol], val child: DifferentialProgram, val constraint: Formula) extends Expr(ProgramSort) with DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case ODESystem(d, c, cnstr) => disturbance == d && child == c && constraint == constr
    case _ => false
  }
  override def hashCode: Int = hash(277, child, f)
}

//@TODO What is this?
object IncompleteSystem {
  def apply(system: DifferentialProgram) = new IncompleteSystem(system)
  def apply() = new IncompleteSystem(new EmptyODE)
  def unapply(e: Any): Option[DifferentialProgram] = e match {
      case s: IncompleteSystem => Some(s.system)
      case _                   => None
  }
}
final class IncompleteSystem(val system: DifferentialProgram) extends Expr(ProgramSort) with DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case IncompleteSystem(s) => system == s
    case _ => false
  }
  override def hashCode: Int = hash(263, system)
}

/**
 * Quantifiers
 *=============
 */

abstract class Quantifier(val variables : Seq[NamedSymbol], child : Formula) extends UnaryFormula(child) {
  require(!variables.isEmpty, "no empty quantifiers " + this)
}

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

final class Forall(variables : immutable.Seq[NamedSymbol], child : Formula) extends Quantifier(variables, child) {
  require(!variables.isEmpty, "Quantifiers should bind at least one variable")
  override def equals(e: Any): Boolean = e match {
    case x: Forall => x.variables == variables && x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(229, variables, child)
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
final class Exists(variables : immutable.Seq[NamedSymbol], child : Formula) extends Quantifier(variables, child) {
  require(!variables.isEmpty, "Quantifiers should bind at least one variable")

  override def equals(e: Any): Boolean = e match {
    case x: Exists => x.variables == variables && x.child == child
    case _ => false
  }
  override def hashCode: Int = hash(233, variables, child)
}

