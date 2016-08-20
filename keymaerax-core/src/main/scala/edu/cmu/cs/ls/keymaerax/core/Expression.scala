/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Differential Dynamic Logic expression data structures.
  * @author Andre Platzer
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @note Code Review: 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.math._

/**
  * Kinds of expressions (term, formula, program, differential program).
  */
sealed trait Kind
/** All expressions that are neither terms nor formulas nor programs nor functions are of kind ExpressionKind */
object ExpressionKind extends Kind { override def toString = "Expression" }
/** All terms are of kind TermKind */
object TermKind extends Kind { override def toString = "Term" }
/** All formulas are of kind FormulaKind */
object FormulaKind extends Kind { override def toString = "Formula" }
/** All programs are of kind ProgramKind */
object ProgramKind extends Kind { override def toString = "Program" }
/** All differential programs are of kind DifferentialProgramKind */
object DifferentialProgramKind extends Kind/*ProgramKind.type*/ { override def toString = "DifferentialProgram" }
/** Function/predicate symbols that are not themselves terms or formulas are of kind FunctionKind */
object FunctionKind extends Kind { override def toString = "Function" }

/**
  * Sorts of expressions (real, bool, etc).
  */
sealed trait Sort
/** Unit type of [[edu.cmu.cs.ls.keymaerax.core.Nothing Nothing]] */
object Unit extends Sort { override def toString = "Unit" }
/** Sort of booleans: [[edu.cmu.cs.ls.keymaerax.core.True True]], [[edu.cmu.cs.ls.keymaerax.core.False False]]. */
object Bool extends Sort { override def toString = "Bool" }
/** Sort of real numbers: 0, 1, 2.5 */
object Real extends Sort { override def toString = "Real" }
/** Sort of state transformations (i.e. programs) */
object Trafo extends Sort { override def toString = "Trafo" }
/** Tuple sort for [[edu.cmu.cs.ls.keymaerax.core.Pair Pair]]. */
case class Tuple(left: Sort, right: Sort) extends Sort { override def toString = "(" + left + "," + right + ")" }
/** User-defined object sort */
case class ObjectSort(name : String) extends Sort { override def toString = name }

/** Sorts of state spaces for state-dependent operators */
sealed trait Space
/** The sort denoting the whole state space alias list of all variables as arguments \bar{x} (axioms that allow any variable dependency) */
object AnyArg extends Space { override def toString: String = "||" }
/** The sort denoting a slice of the state space that does not include/depend on/affect variable `taboo`. */
case class Except(taboo: Variable) extends Space { override def toString: String = "|" + taboo.asString + "|" }


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
  * 4. differential programs are of type [[edu.cmu.cs.ls.keymaerax.core.DifferentialProgram]] of kind [[edu.cmu.cs.ls.keymaerax.core.DifferentialProgramKind]]
  *
  * See [[http://dx.doi.org/10.1007/s10817-016-9385-1 Section 2.1]]
  * @author Andre Platzer
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser#apply]]
  * @see [[http://symbolaris.com/logic/dL.html Syntax of differential dynamic logic]]
  */
sealed trait Expression {
  /** What kind of an expression this is, e.g., [[TermKind]], [[FormulaKind]], [[ProgramKind]]. */
  val kind : Kind
  /** The sort of this expression, e.g., [[Real]], [[Bool]]. */
  val sort : Sort
  //override def toString : String = "(" + prettyString + ")@" + canonicalString
  override def toString : String = prettyString
  /** Pretty-printed string representing this expression */
  def prettyString : String = PrettyPrinter.printer(this)
}

/** Atomic expressions */
sealed trait Atomic extends Expression
/** Composite expressions that are composed of subexpressions */
sealed trait Composite extends Expression

/** Unary composite expressions that are composed of one subexpression */
sealed trait UnaryComposite extends Composite {
  /** The child of this unary composite expression */
  val child: Expression
}

/** Binary composite expressions that are composed of two subexpressions */
sealed trait BinaryComposite extends Composite {
  /** The left child of this binary composite expression */
  val left: Expression
  /** The right child of this binary composite expression */
  val right: Expression
}

/** Function/predicate/predicational application
  * @requires child.sort == func.domain
  * @ensures sort == func.sort */
sealed trait ApplicationOf extends Composite {
  insist(child.sort == func.domain, "expected argument sort " + child.sort + " to match domain sort " + func.domain + " when applying " + func + " to " + child)
  //@note initialization order would dictate that subclasses either provide lazy val or early initializer.
  //insist(sort == func.sort, "sort of application is the sort of the function")
  /** The function/predicate/predicational that this application applies. */
  val func : Function
  /** The child argument that this function/predicate/predicational application is applied to. */
  val child : Expression
}

/**
  * A named symbol such as a variable or function symbol or predicate symbol.
  * @note User-level symbols should not use underscores, which are reserved for the core.
  */
sealed trait NamedSymbol extends Expression with Ordered[NamedSymbol] {
  //@note initialization order uses explicit dataStructureInvariant that is called in all nontrivial subclasses after val have been initialized.
  private[core] final def namingConvention: Unit = {
    insist(!name.isEmpty && !name.substring(0, name.length - 1).contains("_"), "non-empty names without underscores (except at end for internal names): " + name)
    //@note in particular: names cannot have primes
    insist(name.charAt(0).isLetter && name.forall(c => c.isLetterOrDigit || c == '_'), "alphabetical name expected: " + name)
    insist(index.getOrElse(0) >= 0, "nonnegative index if any " + this)
  }

  val name: String
  val index: Option[Int]

  /** Compare named symbols lexicographically: by name, index, category.
    * @note not used in the core, so not soundness-critical, but breaks tactics if wrong. */
  def compare(other: NamedSymbol): Int = {
    val cmp = name.compare(other.name)
    if (cmp != 0) cmp else {
      val cmp2 = index.getOrElse(-1) - other.index.getOrElse(-1)
      //@note .getCanonicalName would cause no collisions if same class name in different packages, but expressions are sealed in core.
      if (cmp2 != 0) cmp2 else getClass.getSimpleName.compareTo(other.getClass.getSimpleName)
    }
  } ensuring(r => r!=0 || this==other, "no different categories of symbols with same name " + this + " compared to " + other)

  /** Get name with index of this NamedSymbol. */
  def asString: String = index match {
    case None => name
    case Some(idx) => name + "_" + idx
  }

  /** Full string with names and full types */
  def fullString: String = asString + ":" + sort

  override def toString: String = asString
}

/** Expressions whose semantic interpretations have access to the state.
  * @note Not soundness-critical, merely speeds up matching in [[SubstitutionPair.freeVars]]. */
sealed trait StateDependent extends Expression

/** Expressions limited to a given state-space.
  * @since 4.2 */
sealed trait SpaceDependent extends StateDependent {
  /** The space that this expression lives on. */
  val space: Space
  final val index: Option[Int] = None
}



/*********************************************************************************
  * Terms of differential dynamic logic
  *********************************************************************************
  */

/**
  * Terms of differential dynamic logic.
  *
  * Terms are of the form
  *     - `x` variable as [[Variable]], including differential symbol `x'` as [[DifferentialSymbol]]
  *     - `f(e)` function application as [[FuncOf]]([[Function]], [[Term]])
  *     - `5` number literals as [[Number]]
  *     - `-e` negation as [[Neg]]([[Term]])
  *     - `e+d` addition as [[Plus]]([[Term]], [[Term]])
  *     - `e-d` subtraction as [[Minus]]([[Term]], [[Term]])
  *     - `e*d` multiplication as [[Times]]([[Term]], [[Term]])
  *     - `e/d` division as [[Divide]]([[Term]], [[Term]])
  *     - `e^d` power as [[Power]]([[Term]], [[Term]])
  *     - (e)'` differential as [[Differential]]([[Term]])
  *     - `F` nullary functional as [[UnitFunctional]]
  *     - `.` dot as reserved nullary function symbol [[DotTerm]] for term argument placeholders
  *     - `(e,d)` for pair as [[Pair]] for arguments
  *     - Nothing for empty arguments [[Nothing]] for nullary functions
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser#termParser]]
  * @see [[http://symbolaris.com/logic/dL.html Syntax of differential dynamic logic]]
  */
sealed trait Term extends Expression {
  final val kind: Kind = TermKind
}

/** Atomic terms */
sealed trait AtomicTerm extends Term with Atomic

/** Real terms */
private[core] sealed trait RTerm extends Term {
  final val sort: Sort = Real
}

/** Variables have a name and index and sort. They are either [[BaseVariable]] or [[DifferentialSymbol]]. */
sealed trait Variable extends NamedSymbol with AtomicTerm
object Variable {
  /** Create a BaseVariable called 'name' with the given index and sort. */
  def apply(name: String, index: Option[Int]=None, sort: Sort=Real): BaseVariable = new BaseVariable(name,index,sort)
}

/** Elementary variable called `name` with an index of a fixed sort */
case class BaseVariable(name: String, index: Option[Int]=None, sort: Sort=Real) extends Variable {
  namingConvention
}

/** Differential symbol x' for variable x */
case class DifferentialSymbol(x: Variable) extends Variable with RTerm {
  insist(x.sort == Real, "differential symbols expect real sort")
  //@see SetLattice.except(x) which cannot currently represent the exclusion of all x''
  insist(!x.isInstanceOf[DifferentialSymbol], "Higher-order differential symbols are not supported " + this)
  final val name: String = x.name
  final val index: Option[Int] = x.index
  override def asString: String = x.asString + "'"
  override def toString: String = asString
  namingConvention
}

/** Number literal */
case class Number(value: BigDecimal) extends AtomicTerm with RTerm

/** Function symbol or predicate symbol or predicational symbol `name_index:domain->sort`
  * @param interpreted when `true` this function symbol has a fixed interpretation/definition.
  */
sealed case class Function(name: String, index: Option[Int] = None, domain: Sort, sort: Sort, interpreted: Boolean = false)
  extends Expression with NamedSymbol {
  final val kind: Kind = FunctionKind
  /** Full string with names and full types */
  override def fullString: String = asString + ":" + domain + "->" + sort
  namingConvention
}

/** •: Placeholder for terms in uniform substitutions of given sort. Reserved nullary function symbol \\cdot for uniform substitutions are unlike ordinary function symbols */
sealed case class DotTerm(s: Sort = Real) extends Expression with NamedSymbol with AtomicTerm {
  final val sort: Sort = s
  final val name: String = "\\cdot"
  final val index: Option[Int] = None
}

/** The empty argument of Unit sort (as argument for arity 0 function/predicate symbols) */
object Nothing extends NamedSymbol with AtomicTerm {
  final val sort: Sort = Unit
  final val name: String = "\\nothing"
  final val index: Option[Int] = None
}

/** Function symbol applied to argument child func(child) */
case class FuncOf(func: Function, child: Term) extends CompositeTerm with ApplicationOf {
  /** The sort of an ApplicationOf is the sort of func
    * @ensures sort == func.sort */
  final val sort: Sort = func.sort
}

/** Arity 0 functional symbol `name:sort`, limited to the given state space.
  * The semantics of arity 0 functional symbol is given by the state, with the additional promise
  * that taboo is not free so the value does not depend on taboo when space=Except(taboo). */
case class UnitFunctional(name: String, space: Space, sort: Sort) extends AtomicTerm with SpaceDependent with NamedSymbol {
  override def asString: String = super.asString + "(" + space + ")"
  namingConvention
}


/** Composite terms */
sealed trait CompositeTerm extends Term with Composite

/** Unary Composite Terms, i.e. terms composed of one real term. */
sealed trait UnaryCompositeTerm extends UnaryComposite with CompositeTerm {
  /** Create a term of this constructor but with the given argument as child instead. (copy)
    * @note Convenience method not used in the soundness-critical core but simplifies homogeneous data processing.
    * @example {{{
    *         Neg(Number(77)).reapply(Number(99)) == Neg(Number(99))
    *         Neg(Variable("x")).reapply(Plus(Number(42),Number(69))) == Neg(Plus(Number(42),Number(69)))
    *         }}}
    */
  def reapply: Term=>Term
  val child: Term
}

/** Unary Composite Real Terms, i.e. real terms composed of one real term. */
private[core] sealed trait RUnaryCompositeTerm extends UnaryCompositeTerm with RTerm {
  insist(child.sort == Real, "expected argument sort real: " + child.sort)
}

/** Binary Composite Terms, i.e. terms composed of two terms. */
sealed trait BinaryCompositeTerm extends BinaryComposite with CompositeTerm {
  /** Create a term of this constructor but with the give left and right arguments instead. (copy)
    * @note Convenience method not used in the soundness-critical core but simplifies homogeneous data processing.
    * @example {{{
    *         Times(Number(7), Variable("v")).reapply(Variable("a"), Number(99)) == Times(Variable("a"), Number(99))
    *         }}}
    */
  def reapply: (Term,Term)=>Term
  val left: Term
  val right: Term
}

/** Binary Composite Real Terms, i.e. real terms composed of two real terms. */
private[core] sealed trait RBinaryCompositeTerm extends BinaryCompositeTerm with RTerm {
  insist(left.sort == Real && right.sort == Real, "expected argument sorts real: " + left + " and " + right)
  val left: Term
  val right: Term
}

/** - unary negation: minus */
case class Neg(child: Term) extends RUnaryCompositeTerm { def reapply = copy }
/** + binary addition */
case class Plus(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** - binary subtraction */
case class Minus(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** * binary multiplication*/
case class Times(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** / real division */
case class Divide(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** real exponentiation or power: left^right^ */
//@note axiom("^' derive power") needs right to be a Term not just a Number
case class Power(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }

/** ' differential of a term */
case class Differential(child: Term) extends RUnaryCompositeTerm { def reapply = copy }

/** Pairs (left,right) for binary Function and FuncOf and PredOf */
case class Pair(left: Term, right: Term) extends BinaryCompositeTerm {
  def reapply = copy
  final val sort: Sort = Tuple(left.sort, right.sort)
}

/*********************************************************************************
  * Formulas of differential dynamic logic
  *********************************************************************************
  */

/**
  * Formulas of differential dynamic logic.
  *
  * Formulas are of the form
  *     - `e>=d` comparisons as [[GreaterEqual]]([[Term]],[[Term]]) and likewise [[Equal]], [[NotEqual]], [[Greater]], [[LessEqual]], [[Less]]
  *     - `p(e)` predicate application as [[PredOf([[Function]], [[Term]])
  *     - `P{Q}` predicational application or quantifier symbol as [[PredicationalOf([[Function]], [[Formula]])
  *     - `true` truth as [[True]] and `false` as [[False]]
  *     - `!P` logical negation as [[Not]]([[Formula]])
  *     - `P&Q` conjunction as [[And]]([[Formula]]], [[Formula]]])
  *     - `P|Q` disjunction as [[Or]]([[Formula]]], [[Formula]]])
  *     - `P->Q` implication as [[Imply]]([[Formula]]], [[Formula]]])
  *     - `P<->Q` biimplication as [[Equiv]]([[Formula]]], [[Formula]]])
  *     - `\forall x P` universal quantification as [[Forall]]([[Variable]]], [[Formula]]])
  *     - `\exists x P` existential quantification as [[Exists]]([[Variable]]], [[Formula]]])
  *     - `[a]P` box modality application for all runs as [[Box]]([[Program]]], [[Formula]]])
  *     - `⟨a⟩P` diamond modality application for some run as [[Diamond]]([[Program]]], [[Formula]]])
  *     - (P)'` differential formula as [[DifferentialFormula]]([[Formula]]])
  *     - `P` nullary predicational as [[UnitPredicational]]
  *     - `_` dot as reserved nullary predicational [[DotFormula]] for formula argument placeholders
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser#formulaParser]]
  */
sealed trait Formula extends Expression {
  final val kind: Kind = FormulaKind
  final val sort: Sort = Bool
}

/** Atomic formulas */
sealed trait AtomicFormula extends Formula with Atomic

/** Atomic comparison formula composed of two terms. */
sealed trait ComparisonFormula extends AtomicFormula with BinaryComposite {
  /** Create a formula of this constructor but with the give left and right arguments instead. (copy)
    * @example {{{
    *         GreaterEqual(Number(7), Variable("v")).reapply(Variable("a"), Number(99)) == GreaterEqual(Variable("a"), Number(99))
    *         }}}
    */
  def reapply: (Term,Term)=>Formula
  val left: Term
  val right: Term
}

/** Real comparison formula composed of two real terms. */
private[core] sealed trait RComparisonFormula extends ComparisonFormula {
  insist(left.sort == Real && right.sort == Real, "expected argument sorts real: " + left + " and " + right)
}

/** Verum formula true */
object True extends AtomicFormula
/** Falsum formula false */
object False extends AtomicFormula

/** ``=`` equality left = right */
case class Equal(left: Term, right: Term) extends ComparisonFormula {
  insist(left.sort == right.sort, "expected identical argument sorts: " + left + " and " + right)
  def reapply = copy
}
/** != disequality left != right */
case class NotEqual(left: Term, right: Term) extends ComparisonFormula {
  insist(left.sort == right.sort, "expected identical argument sorts: " + left + " and " + right)
  def reapply = copy
}

/** >= greater or equal comparison left >= right */
case class GreaterEqual(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }
/** > greater than comparison left > right */
case class Greater(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }
/** < less or equal comparison left <= right */
case class LessEqual(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }
/** <= less than comparison left < right */
case class Less(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }

/** ⎵: Placeholder for formulas in uniform substitutions. Reserved nullary predicational symbol _ for substitutions are unlike ordinary predicational symbols */
object DotFormula extends NamedSymbol with AtomicFormula with StateDependent {
  final val name: String = "\\_"
  final val index: Option[Int] = None
}

/** Predicate symbol applied to argument child func(child) */
case class PredOf(func: Function, child: Term) extends AtomicFormula with ApplicationOf {
  //@note redundant requires since ApplicationOf.sort and Formula.requires will check this already.
  insist(func.sort == Bool, "expected predicate sort Bool found " + func.sort + " in " + this)
}

/** Predicational or quantifier symbol applied to argument formula child. */
case class PredicationalOf(func: Function, child: Formula)
  extends AtomicFormula with ApplicationOf with StateDependent {
  //@note redundant requires since ApplicationOf.sort and Formula.requires will check this already.
  insist(func.sort == Bool, "expected argument sort Bool: " + this)
  insist(func.domain == Bool, "expected domain simplifies to Bool: " + this)
  insist(!func.interpreted, "only uninterpreted predicationals are currently supported: " + this)
}

/** Arity 0 predicational symbol `name:bool`, limited to the given state space.
  * The semantics of arity 0 predicational symbol is looked up by the state, with the additional promise
  * that taboo is not free so the value does not depend on taboo when space=Except(taboo). */
case class UnitPredicational(name: String, space: Space) extends AtomicFormula with SpaceDependent with NamedSymbol {
  override def asString: String = super.asString + "(" + space + ")"
  namingConvention
}


/** Composite formulas */
sealed trait CompositeFormula extends Formula with Composite

/** Unary Composite Formulas, i.e. formulas composed of one formula. */
sealed trait UnaryCompositeFormula extends UnaryComposite with CompositeFormula {
  /** Create a formula of this constructor but with the given argument as child instead. (copy)
    * @example {{{
    *         Not(GreaterEqual(Variable("x"),Number(0))).reapply(NotEqual(Number(7),Number(9))) == Not(NotEqual(Number(7),Number(9)))
    *         Not(True).reapply(False) == Not(False)
    *         }}}
    */
  def reapply: Formula=>Formula
  val child: Formula
}

/** Binary Composite Formulas, i.e. formulas composed of two formulas. */
sealed trait BinaryCompositeFormula extends BinaryComposite with CompositeFormula {
  /** Create a formula of this constructor but with the give left and right arguments instead. (copy)
    * @example {{{
    *         Or(GreaterEqual(Variable("x"),Number(0)), False).reapply(True, NotEqual(Number(7),Number(9))) == Or(True, NotEqual(Number(7),Number(9)))
    *         }}}
    */
  def reapply: (Formula,Formula)=>Formula
  val left: Formula
  val right: Formula
}

/** ! logical negation: not */
case class Not(child: Formula) extends UnaryCompositeFormula { def reapply = copy }
/** & logical conjunction: and */
case class And(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }
/** | logical disjunction: or */
case class Or(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }
/** -> logical implication: implies */
case class Imply(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }
/** <-> logical biimplication: equivalent */
case class Equiv(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }

/** Quantified formulas */
sealed trait Quantified extends CompositeFormula {
  insist(vars.length==1, "quantifiers bind exactly one variable at the moment")
//  require(vars.nonEmpty, "quantifiers bind at least one variable")
//  insist(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
//  insist(vars.forall(x => x.sort == vars.head.sort), "all vars have the same sort")
  /** Create a formula of this constructor but with the given variable list and child as argument instead. (copy)
    * @example {{{
    *         Forall(immutable.Seq(Variable("x")), PredOf(Function("p",None,Real,Bool),Variable("x"))).reapply(
    *                immutable.Seq(Variable("y")), PredOf(Function("q",None,Real,Bool),Variable("y")))
    *         == Forall(immutable.Seq(Variable("y")), PredOf(Function("q",None,Real,Bool),Variable("y"))))
    *         }}}
    */
  def reapply: (immutable.Seq[Variable],Formula)=>Formula
  /** The variables quantified here */
  val vars: immutable.Seq[Variable]
  val child: Formula
}
/** \forall vars universally quantified formula */
case class Forall(vars: immutable.Seq[Variable], child: Formula) extends Quantified { def reapply = copy }
/** \exists vars existentially quantified formula */
case class Exists(vars: immutable.Seq[Variable], child: Formula) extends Quantified { def reapply = copy }

/** Modal formulas */
sealed trait Modal extends CompositeFormula {
  /** Create a formula of this constructor but with the given program and formula child as argument instead. (copy)
    * @example {{{
    *         Box(ProgramConst("b"), Less(Variable("z"),Number(0))).reapply(
    *             Compose(ProgramConst("a"),AtomicODE(DifferentialSymbol(Variable("x")), Number(5))), GreaterEqual(Variable("x"),Number(2))
    *        ) == Box(Compose(ProgramConst("a"),AtomicODE(DifferentialSymbol(Variable("x")), Number(5))), GreaterEqual(Variable("x"),Number(2)))
    *         }}}
    */
  def reapply: (Program,Formula)=>Formula
  val program: Program
  val child: Formula
}
/** box modality all runs of program satisfy child [program]child */
case class Box(program: Program, child: Formula) extends Modal { def reapply = copy }
/** diamond modality some run of program satisfies child ⟨program⟩child */
case class Diamond(program: Program, child: Formula) extends Modal { def reapply = copy }

/** Differential formula are differentials of formulas in analogy to differential terms (child)' */
case class DifferentialFormula(child: Formula) extends UnaryCompositeFormula { def reapply = copy }

/*********************************************************************************
  * Programs of differential dynamic logic
  *********************************************************************************
  */

/**
  * Hybrid programs of differential dynamic logic.
  *
  * Hybrid Programs are of the form
  *     - `x:=e` assignment as [[Assign]]([[Variable]],[[Term]]) and likewise differential assignment `x':=e` as [[Assign]]([[DifferentialSymbol]],[[Term]])
  *     - `x:=*` nondeterministic assignment as [[AssignAny]]([[Variable]]) and likewise nondeterministic ifferential assignment `x':=*` as [[AssignAny]]([[DifferentialSymbol]](
  *     - `a` program constant as [[ProgramConst]]
  *     - `?P` test as [[Test]]([[Formula]])
  *     - `a++b` nondeterministic choice as [[Choice]]([[Program]]], [[Program]]])
  *     - `a;b` sequential composition as [[Compose]]([[Program]]], [[Program]]])
  *     - `{a}*` nondeterministic repetition as [[Loop]]([[Program]]])
  *     - `{a}^d` dual game as [[Dual]]([[Program]]])
  *     - `{c&Q}` differential equation system as [[ODESystem]]([[DifferentialProgram]], [[Formula]])
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser#programParser]]
  */
sealed trait Program extends Expression {
  val kind: Kind = ProgramKind
  final val sort: Sort = Trafo
}

/** Atomic programs */
sealed trait AtomicProgram extends Program with Atomic

/** Uninterpreted program constant */
sealed case class ProgramConst(name: String) extends NamedSymbol with AtomicProgram with StateDependent {
  final val index: Option[Int] = None
  namingConvention
}

/** x:=e assignment and/or differential assignment x':=e */
case class Assign(x: Variable, e: Term) extends AtomicProgram {
  insist(e.sort == x.sort, "assignment of compatible sort " + this)
}
/** x:=* nondeterministic assignment and/or nondeterministic differential assignment x':=* */
case class AssignAny(x: Variable) extends AtomicProgram
/** ?cond test a formula as a condition on the current state */
case class Test(cond: Formula) extends AtomicProgram


/** composite programs */
sealed trait CompositeProgram extends Program with Composite

/** Unary Composite Programs, i.e. programs composed of one program. */
sealed trait UnaryCompositeProgram extends UnaryComposite with CompositeProgram {
  /** Create a program of this constructor but with the given argument as child instead. (copy)
    * @example {{{
    *         Loop(ProgramConst("alpha")).reapply(Assign(Variable("x"),Number(42))) == Loop(Assign(Variable("x"),Number(42)))
    *         }}}
    */
  def reapply: Program=>Program
  val child: Program
}

/** Binary Composite Programs, i.e. programs composed of two programs. */
sealed trait BinaryCompositeProgram extends BinaryComposite with CompositeProgram {
  /** Create a program of this constructor but with the give left and right arguments instead. (copy)
    * @example {{{
    *         Choice(ProgramConst("alpha"), ProgramConst("beta")).reapply(ProgramConst("gamma"), ProgramConst("delta")) == Choice(ProgramConst("gamma"), ProgramConst("delta"))
    *         }}}
    */
  def reapply: (Program,Program)=>Program
  val left: Program
  val right: Program
}


/** left++right nondeterministic choice */
case class Choice(left: Program, right: Program) extends BinaryCompositeProgram { def reapply = copy }
/** left;right sequential composition */
case class Compose(left: Program, right: Program) extends BinaryCompositeProgram { def reapply = copy }
/** child* nondeterministic repetition */
case class Loop(child: Program) extends UnaryCompositeProgram { def reapply = copy }
/** `child^d` dual program */
case class Dual(child: Program) extends UnaryCompositeProgram { def reapply = copy
  require(false, "Hybrid games are currently disabled")
}

/** Differential equation system ode with given evolution domain constraint */
case class ODESystem(ode: DifferentialProgram, constraint: Formula = True) extends Program



/**
  * Differential programs of differential dynamic logic.
  *
  * Differential Programs are of the form
  *     - `x'=e` atomic differential equation as [[AtomicODE]]([[DifferentialSymbol]],[[Term]])
  *     - `c` differential program constant as [[DifferentialProgramConst]]
  *     - `c,d` differential product as [[DifferentialProduct]]([[DifferentialProgram]]], [[DifferentialProgram]]])
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser#differentialProgramParser]]
  */
sealed trait DifferentialProgram extends Program {
  override final val kind: Kind = DifferentialProgramKind
}

/** Atomic differential programs */
sealed trait AtomicDifferentialProgram extends AtomicProgram with DifferentialProgram

/** Uninterpreted differential program constant, limited to the given state space.
  * The semantics of arity 0 DifferentialProgramConst symbol is looked up by the state,
  * with the additional promise that taboo is neither free nor bound, so the run does
  * not depend on the value of taboo nor does the value of taboo change when space=Except(taboo). */
sealed case class DifferentialProgramConst(name: String, space: Space = AnyArg)
  extends AtomicDifferentialProgram with SpaceDependent with NamedSymbol {
  override def asString: String = if (space == AnyArg) super.asString else super.asString + "{" + space + "}"
  namingConvention
}

/** x'=e atomic differential equation */
case class AtomicODE(xp: DifferentialSymbol, e: Term) extends AtomicDifferentialProgram {
  insist(e.sort == Real, "expected argument sort real " + this)
  /* @NOTE Soundness: AtomicODE requires explicit-form so f(?) cannot verbatim mention differentials/differential symbols,
     which is required for soundness of axiom "DE differential effect (system)" */
  //@note avoid toString call, which could cause an infinite loop coming from contracts checking in pretty printer. But should probably be taken care of.
  insist(xp.x.isInstanceOf[BaseVariable] && !StaticSemantics.isDifferential(e), "Explicit-form differential equations expected, without any differentials on right-hand side: " + xp + "=" + e)
}

/**
  * left,right parallel product of differential programs.
  * This data structure automatically reassociates to list form
  * DifferentialProduct(AtomicDifferentialProgram, DifferentialProduct(AtomicDifferentialProgram, ....))
  * @note This is a case class except for an override of the apply function.
  * @note Private constructor so only [[DifferentialProduct.apply]] can ever create this, which will re-associate et al.
  */
final class DifferentialProduct private(final val left: DifferentialProgram, final val right: DifferentialProgram)
  extends DifferentialProgram with BinaryComposite {

  override def equals(e: Any): Boolean = e match {
    case a: DifferentialProduct => left == a.left && right == a.right
    case _ => false
  }

  override def hashCode: Int = 31 * left.hashCode() + right.hashCode()
}

object DifferentialProduct {
  /**
    * Construct an ODEProduct in reassociated normal form, i.e. as a list such that left will never be an ODEProduct in
    * the data structures.
    * @note Completeness: reassociate needed in DifferentialProduct data structures for
    *       axiom "DE differential effect (system)" so as not to get stuck after it.
    */
  def apply(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct = {
    insist(differentialSymbols(left).intersect(differentialSymbols(right)).isEmpty, "No duplicate differential equations when composing differential equations " + left + " and " + right)
    reassociate(left, right)
  } ensuring(r => listify(r) == listify(left) ++ listify(right), "reassociating DifferentialProduct does not change the list of atomic ODEs"
    ) ensuring(r => differentialSymbols(r).length == differentialSymbols(r).distinct.length,
    "No undetected duplicate differential equations when composing differential equations " + left + " and " + right + " to form " + reassociate(left, right))

  def unapply(e: Any): Option[(DifferentialProgram, DifferentialProgram)] = e match {
    case a: DifferentialProduct => Some(a.left, a.right)
    case _ => None
  }

  //@tailrec
  private def reassociate(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct = left match {
    // properly associated cases
    case l: AtomicODE => new DifferentialProduct(l, right)
    case l: DifferentialProgramConst => new DifferentialProduct(l, right)
    // reassociate so that there's no more differential product on the left
    case DifferentialProduct(ll, lr) =>
      assert(ll.isInstanceOf[AtomicDifferentialProgram], "reassociation has succeeded on the left")
      reassociate(ll, reassociate(lr, right))
  }

  /** Turn differential program ode along its DifferentialProduct into a list */
  private def listify(ode: DifferentialProgram): immutable.List[DifferentialProgram] = ode match {
    case p: DifferentialProduct => listify(p.left) ++ listify(p.right)
    case a: AtomicDifferentialProgram => a :: Nil
  }

  /** The list of all literal differential symbols in ODE */
  //@note Differential symbols can only occur on the left of AtomicODEs anyhow.
  //@note Could use the StaticSemantics from this contract equivalently.
  private def differentialSymbols(ode: DifferentialProgram): immutable.List[DifferentialSymbol] = {ode match {
    case p: DifferentialProduct => differentialSymbols(p.left) ++ differentialSymbols(p.right)
    case AtomicODE(xp, _) => xp :: Nil
    case a: DifferentialProgramConst => Nil
  }} ensuring(r => r.toSet==StaticSemantics.symbols(ode).filter(x=>x.isInstanceOf[DifferentialSymbol]),
    "StaticSemantics should agree since differential symbols only occur on the left-hand side of differential equations " + StaticSemantics.symbols(ode).toList.filter(x=>x.isInstanceOf[DifferentialSymbol]))

}