/**
 * Differential Dynamic Logic expression data structures.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter

import scala.collection.immutable
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.SortedSet
import scala.collection.immutable.Set

import scala.annotation.{tailrec, elidable}
import scala.annotation.elidable._

import scala.math._

//import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter  // external

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
/**
 * Unit type of Nothing
 */
object Unit extends Sort
/**
 * Sort of booleans: true, false
 */
object Bool extends Sort
/**
 * Sort of real numbers: 0, 1, 2.5
 */
object Real extends Sort
/**
 * Sort of state transformations (i.e. programs)
 */
object Trafo extends Sort
/**
 * Tuple sort for pairs
 */
case class Tuple(left: Sort, right: Sort) extends Sort
/**
 * User-defined object sort
 */
case class ObjectSort(name : String) extends Sort


/**
 * Expressions of differential dynamic logic.
 * @author aplatzer
 */
sealed trait Expression {
  def kind : Kind
  def sort : Sort
  override def toString = "(" + prettyString() + ")@" + super.toString
  def prettyString() : String = new KeYmaeraPrettyPrinter().stringify(this)
}

sealed trait Atomic extends Expression
sealed trait Composite extends Expression

sealed trait NamedSymbol extends Expression {
  def name: String
  def index: Option[Int]
  override def toString = name
}

/********************************************
 * Terms of differential dynamic logic.
 * @author aplatzer
 */
sealed trait Term extends Expression {
  final def kind = TermKind
}

// atomic terms
sealed trait AtomicTerm extends Term with Atomic

/**
 * real terms
 */
private[core] trait RTerm extends Term {
  final def sort = Real
}

sealed case class Variable(name: String, index: Option[Int] = None, sort: Sort)
  extends NamedSymbol with AtomicTerm
sealed case class DifferentialSymbol(e: Variable)
  extends NamedSymbol with AtomicTerm with RTerm {
  require(e.sort == Real)
  def name = e.name  //@todo eisegesis
  def index = e.index  //@todo eisegesis
}

case class Number(value: BigDecimal) extends AtomicTerm with RTerm

sealed case class Function(name: String, index: Option[Int] = None, domain: Sort, sort: Sort)
  extends Expression with NamedSymbol {
  def kind = FunctionKind
}

object DotTerm extends NamedSymbol with AtomicTerm with RTerm {
  def name = ("\\cdot")
  def index = None
}

object Nothing extends NamedSymbol with AtomicTerm {
  def sort = Unit
  def name = ("\\nothing")
  def index = None
}
object Anything extends NamedSymbol with AtomicTerm with RTerm {
  def name = ("\\anything")
  def index = None
}

case class FuncOf(func: Function, child: Term) extends AtomicTerm {
  def sort = func.sort
  require(child.sort == func.domain)
}

// composite terms
sealed trait CompositeTerm extends Term with Composite

/**
 * Unary Composite Real Terms, i.e. real terms composed of one real term.
 */
private[core] abstract class RUnaryCompositeTerm(child: Term) extends RTerm with Composite {
  require(child.sort == Real)
}

/**
 * Composite Real Terms, i.e. real terms composed of two real terms.
 */
private[core] abstract class RCompositeTerm(left: Term, right: Term) extends RTerm with Composite {
  require(left.sort == Real && right.sort == Real)
}

case class Neg(child: Term) extends RUnaryCompositeTerm(child)
case class Plus(left: Term, right: Term) extends RCompositeTerm(left, right)
case class Minus(left: Term, right: Term) extends RCompositeTerm(left, right)
case class Times(left: Term, right: Term) extends RCompositeTerm(left, right)
case class Divide(left: Term, right: Term) extends RCompositeTerm(left, right)
//@note axiom("^' derive power") needs right to be a Term not just a Number
case class Power(left: Term, right: Term) extends RCompositeTerm(left, right)

case class Differential(child: Term) extends RUnaryCompositeTerm(child)

case class Pair(left: Term, right: Term) extends CompositeTerm {
  def sort = Tuple(left.sort, right.sort)
}

/********************************************
 * Formulas of differential dynamic logic.
 * @author aplatzer
 */

sealed trait Formula extends Expression {
  final def kind = FormulaKind
  final def sort = Bool
}

// atomic formulas
sealed trait AtomicFormula extends Formula with Atomic

/**
 * Composite Real Terms, i.e. real terms composed of two real terms.
 */
private[core] abstract class RAtomicFormula(left: Term, right: Term) extends AtomicFormula {
  require(left.sort == Real && right.sort == Real)
}

object True extends AtomicFormula
object False extends AtomicFormula

case class Equal(left: Term, right: Term) extends AtomicFormula {
  require(left.sort == right.sort)
}
case class NotEqual(left: Term, right: Term) extends AtomicFormula {
  require(left.sort == right.sort)
}

case class GreaterEqual(left: Term, right: Term) extends RAtomicFormula(left, right)
case class Greater(left: Term, right: Term) extends RAtomicFormula(left, right)
case class LessEqual(left: Term, right: Term) extends RAtomicFormula(left, right)
case class Less(left: Term, right: Term) extends RAtomicFormula(left, right)

object DotFormula extends NamedSymbol with AtomicFormula {
  def name = "\\_"
  def index = None
}

case class PredOf(pred: Function, child: Term) extends AtomicFormula {
  require(child.sort == pred.domain)
}
case class PredicationalOf(pred: Function, child: Formula) extends AtomicFormula {
  require(pred.sort == Bool)
}

// composite formulas
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
  //@todo require all vars have the same sort?
}
case class Exists(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula with Quantified {
  require(vars.nonEmpty, "quantifiers bind at least one variable")
  require(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
  //@todo require all vars have the same sort?
}

trait Modal extends CompositeFormula {
  def program: Program
  def child: Formula
}

case class Box(program: Program, child: Formula) extends CompositeFormula with Modal
case class Diamond(program: Program, child: Formula) extends CompositeFormula with Modal

case class DifferentialFormula(child: Formula) extends CompositeFormula

/********************************************
  * Hybrid programs of differential dynamic logic.
  * @author aplatzer
  */

sealed trait Program extends Expression {
  final def kind = ProgramKind
  final def sort = Trafo
}

// atomic programs
sealed trait AtomicProgram extends Program with Atomic

sealed case class ProgramConst(name: String) extends NamedSymbol with AtomicProgram {
  def index = None
}

case class Assign(target: Variable, e: Term) extends AtomicProgram {
  require(e.sort == target.sort)
}
case class DiffAssign(target: DifferentialSymbol, e: Term) extends AtomicProgram {
  require(e.sort == Real)
}
case class AssignAny(target: Variable) extends AtomicProgram
case class Test(cond: Formula) extends AtomicProgram

// composite programs
sealed trait CompositeProgram extends Program with Composite
case class Choice(left: Program, right: Program) extends CompositeProgram
case class Compose(left: Program, right: Program) extends CompositeProgram
case class Loop(child: Program) extends CompositeProgram
//case class Dual(child: Program) extends CompositeProgram

// differential programs
sealed trait DifferentialProgram extends Program/*???*/
sealed trait AtomicDifferentialProgram extends DifferentialProgram with AtomicProgram
case class ODESystem(ode: DifferentialProgram, constraint: Formula) extends DifferentialProgram
sealed case class DifferentialProgramConst(name: String) extends NamedSymbol with AtomicDifferentialProgram {
  def index = None
}
case class AtomicODE(xp: DifferentialSymbol, e: Term) extends AtomicDifferentialProgram {
  require(e.sort == Real)
}
final class DifferentialProduct(val left: DifferentialProgram, val right: DifferentialProgram)
  extends DifferentialProgram {
  override def equals(e: Any): Boolean = e match {
    case x: DifferentialProduct => x.left == left && x.right == right
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
    case x: DifferentialProduct => Some(x.left, x.right)
    case _ => None
  }

  //@tailrec
  private def reassociate(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct = (left match {
    // properly associated cases
    case l: AtomicODE => new DifferentialProduct(l, right)
    case l: DifferentialProgramConst => new DifferentialProduct(l, right)
    // reassociate
    case DifferentialProduct(ll, lr) => reassociate(ll, reassociate(lr, right))
  }) ensuring(r => listify(r) == listify(left) ++ listify(right),
    "reassociating DifferentialProduct does not change the list of atomic ODEs")

  private def listify(ode: DifferentialProgram): List[DifferentialProgram] = ode match {
    case p: DifferentialProduct => listify(p.left) ++ listify(p.right)
    case a: AtomicDifferentialProgram => a :: Nil
  }
}