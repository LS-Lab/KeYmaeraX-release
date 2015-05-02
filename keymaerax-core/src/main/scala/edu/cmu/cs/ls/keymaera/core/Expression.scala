/**
 * Differential Dynamic Logic expression data structures.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter // external

import scala.math._

/*******************************
  * Kinds of expressions
  */
sealed abstract class Kind
object TermKind extends Kind { override def toString = "Term" }
object FormulaKind extends Kind { override def toString = "Formula" }
object ProgramKind extends Kind { override def toString = "Program" }
object FunctionKind extends Kind { override def toString = "Function" }

/*******************************
 * Sorts
 */
sealed abstract class Sort
/**  Unit type of Nothing */
object Unit extends Sort
/** Sort of booleans: true, false */
object Bool extends Sort
/** Sort of real numbers: 0, 1, 2.5 */
object Real extends Sort
/** Sort of state transformations (i.e. programs) */
object Trafo extends Sort
/** Tuple sort for pairs */
case class Tuple(left: Sort, right: Sort) extends Sort
/** User-defined object sort */
case class ObjectSort(name : String) extends Sort


/**
 * Expressions of differential dynamic logic.
 * @author aplatzer
 */
sealed trait Expression {
  def kind : Kind
  def sort : Sort
  override def toString : String = "(" + prettyString() + ")@" + super.toString
  def prettyString() : String = new KeYmaeraPrettyPrinter().stringify(this)
}

sealed trait Atomic extends Expression
sealed trait Composite extends Expression

sealed trait ApplicationOf extends Expression

/**
 * A named symbol such as a variable or function symbol or predicate symbol.
 * User-level symbols should not use underscores, which are reserved for the core.
 */
sealed trait NamedSymbol extends Expression with Ordered[NamedSymbol] {
  require(!name.isEmpty && !name.substring(0, name.length-1).contains("_"),
    "non-empty names without underscores (except at end for internal names)")
  require(!name.contains("'"), "names cannot mention primes, not even the names of differential symbols")

  def name: String
  def index: Option[Int]

  def compare(other: NamedSymbol): Int = {
    val cmp = name.compare(other.name)
    if (cmp != 0) cmp else index.getOrElse(-1) - other.index.getOrElse(-1)
  } ensuring(r => r!=0 || this==other, "no different categories of symbols with same name " + this + " compared to " + other)

  override def toString: String = index match {
    case None => name
    case Some(idx) => name + "_" + idx
  }
}

/********************************************
 * Terms of differential dynamic logic.
 * @author aplatzer
 */
sealed trait Term extends Expression {
  final def kind: Kind = TermKind
}

/** atomic terms */
sealed trait AtomicTerm extends Term with Atomic

/**  real terms */
private[core] trait RTerm extends Term {
  final def sort: Sort = Real
}

sealed case class Variable(name: String, index: Option[Int] = None, sort: Sort)
  extends NamedSymbol with AtomicTerm

sealed case class DifferentialSymbol(x: Variable)
  extends NamedSymbol with AtomicTerm with RTerm {
  require(x.sort == Real, "differential symbols expect real sort")
  def name: String = x.name
  def index: Option[Int] = x.index
  override def toString: String =  super.toString + "'"
}

case class Number(value: BigDecimal) extends AtomicTerm with RTerm

/** Function symbol or predicate symbol or predicational symbol */
sealed case class Function(name: String, index: Option[Int] = None, domain: Sort, sort: Sort)
  extends Expression with NamedSymbol {
  def kind: Kind = FunctionKind
}

/** Reserved function symbol \\cdot for substitutions are unlike ordinary function symbols */
object DotTerm extends NamedSymbol with AtomicTerm with RTerm {
  def name: String = "\\cdot"
  def index: Option[Int] = None
}

/** The empty argument of Unit sort */
object Nothing extends NamedSymbol with AtomicTerm {
  def sort: Sort = Unit
  def name: String = "\\nothing"
  def index: Option[Int] = None
}

/** The list of all variables as arguments \bar{x} */
object Anything extends NamedSymbol with AtomicTerm with RTerm {
  def name: String = "\\anything"
  def index: Option[Int] = None
}

/** Function symbol applied to argument child */
case class FuncOf(func: Function, child: Term) extends AtomicTerm with ApplicationOf {
  def sort: Sort = func.sort
  require(child.sort == func.domain, "expected argument sort")
}

/** Composite terms */
sealed trait CompositeTerm extends Term with Composite

/** Unary Composite Real Terms, i.e. real terms composed of one real term. */
private[core] trait RUnaryCompositeTerm extends RTerm with Composite {
  require(child.sort == Real, "expected argument sort real")
  def child: Term
}

/** Composite Real Terms, i.e. real terms composed of two real terms. */
private[core] trait RCompositeTerm extends RTerm with Composite {
  require(left.sort == Real && right.sort == Real, "expected argument sorts real")
  def left: Term
  def right: Term
}

/** Unary negation */
case class Neg(child: Term) extends RUnaryCompositeTerm
case class Plus(left: Term, right: Term) extends RCompositeTerm
/** Binary subtraction */
case class Minus(left: Term, right: Term) extends RCompositeTerm
case class Times(left: Term, right: Term) extends RCompositeTerm
case class Divide(left: Term, right: Term) extends RCompositeTerm
//@note axiom("^' derive power") needs right to be a Term not just a Number
case class Power(left: Term, right: Term) extends RCompositeTerm

case class Differential(child: Term) extends RUnaryCompositeTerm

/** Pairs are to enable binary Function and FuncOf and PredOf */
case class Pair(left: Term, right: Term) extends CompositeTerm {
  def sort: Sort = Tuple(left.sort, right.sort)
}

/********************************************
 * Formulas of differential dynamic logic.
 * @author aplatzer
 */
sealed trait Formula extends Expression {
  final def kind: Kind = FormulaKind
  final def sort: Sort = Bool
}

/** Atomic formulas */
sealed trait AtomicFormula extends Formula with Atomic

/** Formulas composed of real terms. */
private[core] trait RAtomicFormula extends AtomicFormula {
  require(left.sort == Real && right.sort == Real, "expected argument sorts real")
  def left: Term
  def right: Term
}

object True extends AtomicFormula
object False extends AtomicFormula

case class Equal(left: Term, right: Term) extends AtomicFormula {
  require(left.sort == right.sort, "expected identical argument sorts")
}
case class NotEqual(left: Term, right: Term) extends AtomicFormula {
  require(left.sort == right.sort, "expected identical argument sorts")
}

case class GreaterEqual(left: Term, right: Term) extends RAtomicFormula
case class Greater(left: Term, right: Term) extends RAtomicFormula
case class LessEqual(left: Term, right: Term) extends RAtomicFormula
case class Less(left: Term, right: Term) extends RAtomicFormula

/** Reserved predicational symbol _ for substitutions are unlike ordinary predicational symbols */
object DotFormula extends NamedSymbol with AtomicFormula {
  def name: String = "\\_"
  def index: Option[Int] = None
}

/** Predicate symbol applied to argument child */
case class PredOf(pred: Function, child: Term) extends AtomicFormula with ApplicationOf {
  require(child.sort == pred.domain, "expected argument sort")
}
/** Predicational symbol applied to argument formula child */
case class PredicationalOf(pred: Function, child: Formula) extends AtomicFormula with ApplicationOf {
  require(pred.sort == Bool, "expected argument sort")
}

/** Composite formulas */
sealed trait CompositeFormula extends Formula with Composite

case class Not(child: Formula) extends CompositeFormula
case class And(left: Formula, right:Formula) extends CompositeFormula
case class Or(left: Formula, right:Formula) extends CompositeFormula
case class Imply(left: Formula, right:Formula) extends CompositeFormula
case class Equiv(left: Formula, right:Formula) extends CompositeFormula

trait Quantified extends CompositeFormula {
  def vars: immutable.Seq[Variable]
  def child: Formula
}
case class Forall(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula with Quantified {
  require(vars.nonEmpty, "quantifiers bind at least one variable")
  require(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
  require(vars.forall(x => x.sort == vars.head.sort), "all vars have the same sort")
}
case class Exists(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula with Quantified {
  require(vars.nonEmpty, "quantifiers bind at least one variable")
  require(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
  require(vars.forall(x => x.sort == vars.head.sort), "all vars have the same sort")
}

trait Modal extends CompositeFormula {
  def program: Program
  def child: Formula
}
case class Box(program: Program, child: Formula) extends CompositeFormula with Modal
case class Diamond(program: Program, child: Formula) extends CompositeFormula with Modal

/** Differential formula are differentials of formulas in analogy to differential terms */
case class DifferentialFormula(child: Formula) extends CompositeFormula

/********************************************
  * Hybrid programs of differential dynamic logic.
  * @author aplatzer
  */
sealed trait Program extends Expression {
  final def kind: Kind = ProgramKind
  final def sort: Sort = Trafo
}

/** Atomic programs */
sealed trait AtomicProgram extends Program with Atomic

sealed case class ProgramConst(name: String) extends NamedSymbol with AtomicProgram {
  def index: Option[Int] = None
}

case class Assign(x: Variable, e: Term) extends AtomicProgram {
  require(e.sort == x.sort, "assignment of compatible sort")
}
case class DiffAssign(xp: DifferentialSymbol, e: Term) extends AtomicProgram {
  require(e.sort == Real, "differential assignment of real sort")
}
/** Nondeterministic assignment */
case class AssignAny(x: Variable) extends AtomicProgram
case class Test(cond: Formula) extends AtomicProgram

/** composite programs */
sealed trait CompositeProgram extends Program with Composite

case class Choice(left: Program, right: Program) extends CompositeProgram
case class Compose(left: Program, right: Program) extends CompositeProgram
case class Loop(child: Program) extends CompositeProgram
//case class Dual(child: Program) extends CompositeProgram

/** differential programs */
sealed trait DifferentialProgram extends Program
sealed trait AtomicDifferentialProgram extends DifferentialProgram with AtomicProgram
case class ODESystem(ode: DifferentialProgram, constraint: Formula)
  extends Program with DifferentialProgram
sealed case class DifferentialProgramConst(name: String) extends NamedSymbol with AtomicDifferentialProgram {
  def index: Option[Int] = None
}
case class AtomicODE(xp: DifferentialSymbol, e: Term) extends AtomicDifferentialProgram {
  require(e.sort == Real, "expected argument sort real")
}

/**
 * Parallel product of differential programs.
 * This data structure automatically reassociates to list form
 * DifferentialProduct(AtomicDifferentialProgram, DifferentialProduct(AtomicDifferentialProgram, ....))
 * @note This is a case class except for an override of the apply function.
 */
final class DifferentialProduct private(val left: DifferentialProgram, val right: DifferentialProgram)
  extends DifferentialProgram {

  override def equals(e: Any): Boolean = e match {
    case a: DifferentialProduct => left == a.left && right == a.right
    case _ => false
  }

  override def hashCode: Int = 3 * left.hashCode() + right.hashCode()

  override def toString = getClass.getSimpleName + "(" + left + ", " + right + ")"
}

object DifferentialProduct {
  /**
   * Construct an ODEProduct in reassociated normal form, i.e. as a list such that left will never be an ODEProduct in
   * the data structures.
   * @note This is important to not get stuck after using axiom "DE differential effect (system)".
   */
  def apply(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct =
    reassociate(left, right)

  def unapply(e: Any): Option[(DifferentialProgram, DifferentialProgram)] = e match {
    case a: DifferentialProduct => Some(a.left, a.right)
    case _ => None
  }

  //@tailrec
  private def reassociate(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct = (left match {
    // reassociate
    case DifferentialProduct(ll, lr) =>
      assert(ll.isInstanceOf[AtomicDifferentialProgram], "reassociation has succeeded on the left")
      reassociate(ll, reassociate(lr, right))
    // properly associated cases
    case l: AtomicODE => new DifferentialProduct(l, right)
    case l: DifferentialProgramConst => new DifferentialProduct(l, right)
  }) ensuring(r => listify(r) == listify(left) ++ listify(right),
    "reassociating DifferentialProduct does not change the list of atomic ODEs")

  private def listify(ode: DifferentialProgram): immutable.List[DifferentialProgram] = ode match {
    case p: DifferentialProduct => listify(p.left) ++ listify(p.right)
    case a: AtomicDifferentialProgram => a :: Nil
  }
}