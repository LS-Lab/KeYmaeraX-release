/**
 * Differential Dynamic Logic expression data structures.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
package edu.cmu.cs.ls.keymaera

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.elidable
import scala.annotation.elidable._

import scala.math._

import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter  // external

/*******************************
 * Sorts
 */
sealed abstract class Sort

object Unit extends Sort

/* sort of booleans: true, false */
//object Bool extends Sort

/* sort of reals: 0, 1, 2.73 */
object Real extends Sort

/* user defined sort */
case class ObjectSort(name : String) extends Sort


sealed trait NamedSymbol {}

sealed case class Function(name: String, domain: Sort, sort: Sort) extends NamedSymbol {}

/**
 * Expressions of differential dynamic logic.
 * @author aplatzer
 */
sealed trait Expr {
  override def toString = "(" + prettyString() + ")"
  def prettyString() = ??? //new KeYmaeraPrettyPrinter().stringify(this)
}

sealed trait Atomic extends Expr
sealed trait Composite extends Expr

/********************************************
 * Terms of differential dynamic logic.
 * @author aplatzer
 * @TODO For Term but not the others could move to Term[T<Sort] to statically distinguish Term[Real] from Term[ObjectSort] even if not statically distinguishing Term[ObjectSort("A")] from Term[ObjectSort("B")] :-)
 * @TODO Alternatively could duplicate Equals/NotEquals/FuncOf/Function/Variable for non-real sorts :-/
 */
sealed trait Term extends Expr {}

// atomic terms
sealed trait AtomicTerm extends Term with Atomic {}

sealed case class Variable(name: String, index: Option[Int] = None, sort: Sort) extends NamedSymbol with AtomicTerm {}
sealed case class DifferentialSymbol(e: Variable/*NamedSymbol?*/) extends NamedSymbol with AtomicTerm {
  require(e.sort == Real, "differentials are only defined in the reals")
}

case class Number(value: BigDecimal) extends AtomicTerm

case class FuncOf(func: Function, child: Term) extends AtomicTerm

// composite terms
sealed trait CompositeTerm extends Term with Composite {}

//@TODO require(left.sort == Real && right.sort == Real) in the following
case class Plus(left: Term, right: Term) extends CompositeTerm
case class Minus(left: Term, right: Term) extends CompositeTerm
case class Times(left: Term, right: Term) extends CompositeTerm

//@TODO require(left.sort == Real && right.sort == Real) in the following
case class Differential(child: Term) extends CompositeTerm

/********************************************
 * Formulas of differential dynamic logic.
 * @author aplatzer
 */

sealed trait Formula extends Expr {}

// atomic formulas
sealed trait AtomicFormula extends Formula with Atomic {}

case class Equal(left: Term, right: Term) extends AtomicFormula //@TODO sort
case class NotEqual(left: Term, right: Term) extends AtomicFormula //@TODO sort
//@TODO require(left.sort == Real && right.sort == Real) in the following
case class GreaterEqual(left: Term, right: Term) extends AtomicFormula
case class Greater(left: Term, right: Term) extends AtomicFormula
case class LessEqual(left: Term, right: Term) extends AtomicFormula
case class Less(left: Term, right: Term) extends AtomicFormula

case class PredOf(pred: Function, child: Term) extends AtomicFormula
case class PredicationalOf(pred: Function, child: Formula) extends AtomicFormula

// composite formulas
sealed trait CompositeFormula extends Formula with Composite {}

case class Not(child: Formula) extends CompositeFormula
case class And(left: Formula, right:Formula) extends CompositeFormula
case class Or(left: Formula, right:Formula) extends CompositeFormula
case class Imply(left: Formula, right:Formula) extends CompositeFormula
case class Equiv(left: Formula, right:Formula) extends CompositeFormula

case class Forall(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula
case class Exists(vars: immutable.Seq[Variable], child: Formula) extends CompositeFormula

case class Modality(modal: ModalOp, child: Formula) extends CompositeFormula

sealed trait ModalOp extends Expr {}
case class Box(program: Program) extends ModalOp
case class Diamond(program: Program) extends ModalOp

case class DifferentialFormula(child: Formula) extends CompositeFormula

/********************************************
  * Programs of differential dynamic logic.
  * @author aplatzer
  */

sealed trait Program extends Expr {}

// atomic programs
sealed trait AtomicProgram extends Program with Atomic {}
sealed case class ProgramConstant(name: String) extends NamedSymbol with AtomicProgram {}

case class Assign(target: Variable, e: Term) extends AtomicProgram
case class DiffAssign(target: DifferentialSymbol, e: Term) extends AtomicProgram
case class Test(cond: Formula) extends AtomicProgram
case class ODESystem(ode: DifferentialProgram, constraint: Formula) extends Program

// composite programs
sealed trait CompositeProgram extends Program with Composite {}
case class Choice(left: Program, right: Program) extends Program {}
case class Compose(left: Program, right: Program) extends Program {}
case class Star(child: Program) extends Program {}
//case class Dual(child: Program) extends Program {}

// differential programs
sealed trait DifferentialProgram extends Program {}
sealed case class DifferentialProgramConstant(name: String) extends NamedSymbol with DifferentialProgram {}
case class AtomicODE(xp: DifferentialSymbol, e: Term) extends DifferentialProgram {}
case class ODEProduct(left: DifferentialProgram, right: DifferentialProgram) extends DifferentialProgram {}
//@TODO either enforce auto-normalization during construction via an apply method? :-)
//@TODO Or flexibilize equals to be as sets that is modulo associative/commutative but possibly breaking symmetry and all kinds of things :-(