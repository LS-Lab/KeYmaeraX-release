/**
 * Differential Dynamic Logic expression data structures.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraPrettyPrinter // external

import scala.math._

/**
  * Kinds of expressions (term, formula, program).
  */
sealed abstract class Kind
/** All terms are of kind TermKind */
object TermKind extends Kind { override def toString = "Term" }
/** All formulas are of kind FormulaKind */
object FormulaKind extends Kind { override def toString = "Formula" }
/** All programs are of kind ProgramKind */
object ProgramKind extends Kind { override def toString = "Program" }
/** Function/predicate symbols that are not themselves terms or formulas are of kind FunctionKind */
object FunctionKind extends Kind { override def toString = "Function" }

/**
 * Sorts
 */
sealed abstract class Sort
/** Unit type of [[edu.cmu.cs.ls.keymaerax.core.Nothing Nothing]] */
object Unit extends Sort
/** Sort of booleans: [[edu.cmu.cs.ls.keymaerax.core.True True]], [[edu.cmu.cs.ls.keymaerax.core.False False]]. */
object Bool extends Sort
/** Sort of real numbers: 0, 1, 2.5 */
object Real extends Sort
/** Sort of state transformations (i.e. programs) */
object Trafo extends Sort
/** Tuple sort for [[edu.cmu.cs.ls.keymaerax.core.Pair Pair]]. */
case class Tuple(left: Sort, right: Sort) extends Sort
/** User-defined object sort */
case class ObjectSort(name : String) extends Sort


/**
 * Expressions of differential dynamic logic.
 * Expressions are categorized according to the syntactic categories of the grammar of differential dynamic logic:
 *
 * 1. terms are of type [[edu.cmu.cs.ls.keymaerax.core.Term]] of kind [[edu.cmu.cs.ls.keymaerax.core.TermKind]]
 *
 * 2. formulas are of type [[edu.cmu.cs.ls.keymaerax.core.Formula]] of kind [[edu.cmu.cs.ls.keymaerax.core.FormulaKind]]
 *
 * 3. hybrid programs are of type [[edu.cmu.cs.ls.keymaerax.core.Program]] of kind [[edu.cmu.cs.ls.keymaerax.core.ProgramKind]]
 *
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 2.1]]
 * @author aplatzer
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser#parseBareExpression()]]
 */
sealed trait Expression {
  def kind : Kind
  def sort : Sort
  override def toString : String = "(" + prettyString() + ")@" + super.toString
  def prettyString() : String = new KeYmaeraPrettyPrinter().stringify(this)
}

/** Atomic expressions */
sealed trait Atomic extends Expression
/** Composite expressions that are composed of subexpressions */
sealed trait Composite extends Expression

/** Function/predicate/predicational application */
sealed trait ApplicationOf extends Expression {
  def func : Function
  def child : Expression
}

/**
 * A named symbol such as a variable or function symbol or predicate symbol.
 * @note User-level symbols should not use underscores, which are reserved for the core.
 */
sealed trait NamedSymbol extends Expression with Ordered[NamedSymbol] {
  require(!name.isEmpty && !name.substring(0, name.length-1).contains("_"),
    "non-empty names without underscores (except at end for internal names): " + name)
  require(!name.contains("'"), "names cannot mention primes, not even the names of differential symbols: " + name)

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

/*********************************************************************************
  * Terms of differential dynamic logic
  *********************************************************************************
  */

/**
 * Terms of differential dynamic logic.
 * @author aplatzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser#parseBareTerm()]]
 */
sealed trait Term extends Expression {
  final def kind: Kind = TermKind
}

/** Atomic terms */
sealed trait AtomicTerm extends Term with Atomic

/** Real terms */
private[core] trait RTerm extends Term {
  final def sort: Sort = Real
}

/** Variable called name with an index of a fixed sort */
sealed case class Variable(name: String, index: Option[Int] = None, sort: Sort = Real)
  extends NamedSymbol with AtomicTerm

/** Differential symbol x' for variable x */
sealed case class DifferentialSymbol(x: Variable)
  extends NamedSymbol with AtomicTerm with RTerm {
  require(x.sort == Real, "differential symbols expect real sort")
  def name: String = x.name
  def index: Option[Int] = x.index
  override def toString: String =  super.toString + "'"
}

/** Number literal */
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
  require(child.sort == func.domain, "expected argument sort to match domain sort")
}

/** Composite terms */
sealed trait CompositeTerm extends Term with Composite

/** Unary Composite Terms, i.e. terms composed of one real term. */
trait UnaryCompositeTerm extends CompositeTerm {
  def child: Term
}

/** Unary Composite Real Terms, i.e. real terms composed of one real term. */
private[core] trait RUnaryCompositeTerm extends UnaryCompositeTerm with RTerm {
  require(child.sort == Real, "expected argument sort real")
}

/** Binary Composite Terms, i.e. terms composed of two terms. */
trait BinaryCompositeTerm extends CompositeTerm {
  def left: Term
  def right: Term
}

/** Binary Composite Real Terms, i.e. real terms composed of two real terms. */
private[core] trait RBinaryCompositeTerm extends BinaryCompositeTerm with RTerm {
  require(left.sort == Real && right.sort == Real, "expected argument sorts real")
  def left: Term
  def right: Term
}

/** - unary negation: minus */
case class Neg(child: Term) extends RUnaryCompositeTerm
/** + binary addition */
case class Plus(left: Term, right: Term) extends RBinaryCompositeTerm
/** - binary subtraction */
case class Minus(left: Term, right: Term) extends RBinaryCompositeTerm
/** * binary multiplication*/
case class Times(left: Term, right: Term) extends RBinaryCompositeTerm
/** / real division */
case class Divide(left: Term, right: Term) extends RBinaryCompositeTerm
/** real exponentiation or power: left^right^ */
//@note axiom("^' derive power") needs right to be a Term not just a Number
case class Power(left: Term, right: Term) extends RBinaryCompositeTerm

/** ' differential of a term */
case class Differential(child: Term) extends RUnaryCompositeTerm

/** Pairs (left,right) for binary Function and FuncOf and PredOf */
case class Pair(left: Term, right: Term) extends BinaryCompositeTerm {
  def sort: Sort = Tuple(left.sort, right.sort)
}

/*********************************************************************************
  * Formulas of differential dynamic logic
  *********************************************************************************
  */

/**
 * Formulas of differential dynamic logic.
 * @author aplatzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser#parseBareFormula()]]
 */
sealed trait Formula extends Expression {
  final def kind: Kind = FormulaKind
  final def sort: Sort = Bool
}

/** Atomic formulas */
sealed trait AtomicFormula extends Formula with Atomic

/** Atomic comparison formula composed of two terms. */
trait ComparisonFormula extends AtomicFormula {
  def left: Term
  def right: Term
}

/** Real comparison formula composed of two real terms. */
private[core] trait RComparisonFormula extends ComparisonFormula {
  require(left.sort == Real && right.sort == Real, "expected argument sorts real")
}

/** Verum formula true */
object True extends AtomicFormula
/** Falsum formula false */
object False extends AtomicFormula

/** ``=`` equality left = right */
case class Equal(left: Term, right: Term) extends ComparisonFormula {
  require(left.sort == right.sort, "expected identical argument sorts")
}
/** != disequality left != right */
case class NotEqual(left: Term, right: Term) extends ComparisonFormula {
  require(left.sort == right.sort, "expected identical argument sorts")
}

/** >= greater or equal comparison left >= right */
case class GreaterEqual(left: Term, right: Term) extends RComparisonFormula
/** > greater than comparison left > right */
case class Greater(left: Term, right: Term) extends RComparisonFormula
/** < less or equal comparison left <= right */
case class LessEqual(left: Term, right: Term) extends RComparisonFormula
/** <= less than comparison left < right */
case class Less(left: Term, right: Term) extends RComparisonFormula

/** Reserved predicational symbol _ for substitutions are unlike ordinary predicational symbols */
object DotFormula extends NamedSymbol with AtomicFormula {
  def name: String = "\\_"
  def index: Option[Int] = None
}

/** Predicate symbol applied to argument child */
case class PredOf(func: Function, child: Term) extends AtomicFormula with ApplicationOf {
  require(func.sort == Bool, "expected predicate sort Bool: " + this)
  require(child.sort == func.domain, "expected argument sort: " + this)
}
/** Predicational symbol applied to argument formula child */
case class PredicationalOf(func: Function, child: Formula) extends AtomicFormula with ApplicationOf {
  require(func.sort == Bool, "expected argument sort Bool: " + this)
  require(func.domain == Bool, "expected domain simplifies to Bool: " + this)
}

/** Composite formulas */
sealed trait CompositeFormula extends Formula with Composite

/** Unary Composite Formulas, i.e. formulas composed of one formula. */
trait UnaryCompositeFormula extends CompositeFormula {
  def child: Formula
}

/** Binary Composite Formulas, i.e. formulas composed of two formulas. */
trait BinaryCompositeFormula extends CompositeFormula {
  def left: Formula
  def right: Formula
}

/** ! logical negation: not */
case class Not(child: Formula) extends UnaryCompositeFormula
/** & logical conjunction: and */
case class And(left: Formula, right:Formula) extends BinaryCompositeFormula
/** | logical disjunction: or */
case class Or(left: Formula, right:Formula) extends BinaryCompositeFormula
/** -> logical implication: implies */
case class Imply(left: Formula, right:Formula) extends BinaryCompositeFormula
/** <-> logical biimplication: equivalent */
case class Equiv(left: Formula, right:Formula) extends BinaryCompositeFormula

/** Quantified formulas */
trait Quantified extends /*Unary?*/CompositeFormula {
  def vars: immutable.Seq[Variable]
  def child: Formula
}
/** \forall vars universally quantified formula */
case class Forall(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula with Quantified {
  require(vars.nonEmpty, "quantifiers bind at least one variable")
  require(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
  require(vars.forall(x => x.sort == vars.head.sort), "all vars have the same sort")
}
/** \exists vars existentially quantified formula */
case class Exists(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula with Quantified {
  require(vars.nonEmpty, "quantifiers bind at least one variable")
  require(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
  require(vars.forall(x => x.sort == vars.head.sort), "all vars have the same sort")
}

/** Modal formulas */
trait Modal extends CompositeFormula {
  def program: Program
  def child: Formula
}
/** box modality all runs of program satisfy child */
case class Box(program: Program, child: Formula) extends CompositeFormula with Modal
/** diamond modality some run of program satisfies child */
case class Diamond(program: Program, child: Formula) extends CompositeFormula with Modal

/** Differential formula are differentials of formulas in analogy to differential terms */
case class DifferentialFormula(child: Formula) extends UnaryCompositeFormula

/*********************************************************************************
  * Programs of differential dynamic logic
  *********************************************************************************
  */

/**
  * Hybrid programs of differential dynamic logic.
  * @author aplatzer
  */
sealed trait Program extends Expression {
  final def kind: Kind = ProgramKind
  final def sort: Sort = Trafo
}

/** Atomic programs */
sealed trait AtomicProgram extends Program with Atomic

/** Uninterpreted program constant */
sealed case class ProgramConst(name: String) extends NamedSymbol with AtomicProgram {
  def index: Option[Int] = None
}

/** x:=e assignment */
case class Assign(x: Variable, e: Term) extends AtomicProgram {
  require(e.sort == x.sort, "assignment of compatible sort")
}
/** x':=e differential assignment */
case class DiffAssign(xp: DifferentialSymbol, e: Term) extends AtomicProgram {
  require(e.sort == Real, "differential assignment of real sort")
}
/** x:=* nondeterministic assignment */
case class AssignAny(x: Variable) extends AtomicProgram
/** ?cond test a formula as a condition on the current state */
case class Test(cond: Formula) extends AtomicProgram

/** composite programs */
sealed trait CompositeProgram extends Program with Composite

/** Unary Composite Programs, i.e. programs composed of one program. */
trait UnaryCompositeProgram extends CompositeProgram {
  def child: Program
}

/** Binary Composite Programs, i.e. programs composed of two programs. */
trait BinaryCompositeProgram extends CompositeProgram {
  def left: Program
  def right: Program
}


/** left++right nondeterministic choice */
case class Choice(left: Program, right: Program) extends BinaryCompositeProgram
/** left;right sequential composition */
case class Compose(left: Program, right: Program) extends BinaryCompositeProgram
/** child* nondeterministic repetition */
case class Loop(child: Program) extends UnaryCompositeProgram
//case class Dual(child: Program) extends CompositeProgram

/** differential programs */
sealed trait DifferentialProgram extends Program
/** Atomic differential programs */
sealed trait AtomicDifferentialProgram extends DifferentialProgram with AtomicProgram
/** Differential equation system ode with given evolution domain constraint */
case class ODESystem(ode: DifferentialProgram, constraint: Formula)
  extends Program with DifferentialProgram
/** Uninterpreted differential program constant */
sealed case class DifferentialProgramConst(name: String) extends NamedSymbol with AtomicDifferentialProgram {
  def index: Option[Int] = None
}
/** x'=e atomic differential equation */
case class AtomicODE(xp: DifferentialSymbol, e: Term) extends AtomicDifferentialProgram {
  require(e.sort == Real, "expected argument sort real " + this)
  /* @NOTE Soundness: AtomicODE requires explicit-form so f(?) cannot verbatim mention differentials/differential symbols,
     which is required for soundness of axiom "DE differential effect (system)" */
  require(!StaticSemantics.isDifferential(e), "Explicit-form differential equations expected, without any differentials on right-hand side " + this)
}

/**
 * left,right parallel product of differential programs.
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
   * @note Completeness: reassociate needed in DifferentialProduct data structures for
   *       axiom "DE differential effect (system)" so as not to get stuck after it.
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