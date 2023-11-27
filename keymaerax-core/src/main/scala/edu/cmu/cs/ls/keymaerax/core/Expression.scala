/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Differential Dynamic Logic expression data structures.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @note Code Review: 2020-02-17
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.math._

/*********************************************************************************
  * Kinds, Sorts, Spaces giving typing information
  *********************************************************************************
  */

/**
  * Kinds of expressions (term, formula, program, differential program).
  * @see [[Expression]]
  */
sealed trait Kind
/** Expressions that are neither terms nor formulas nor programs nor functions would be of kind ExpressionKind */
case object ExpressionKind extends Kind { override def toString = "Expression" }
/** All terms are of kind TermKind. 
  * @see [[Term]] */
case object TermKind extends Kind { override def toString = "Term" }
/** All formulas are of kind FormulaKind.
  * @see [[Formula]] */
case object FormulaKind extends Kind { override def toString = "Formula" }
/** All programs are of kind ProgramKind.
  * @see [[Program]] */
case object ProgramKind extends Kind { override def toString = "Program" }
/** All differential programs are of kind DifferentialProgramKind.
  * @see [[DifferentialProgram]] */
case object DifferentialProgramKind extends Kind/*ProgramKind.type*/ { override def toString = "DifferentialProgram" }
/** Function/predicate symbols that are not themselves terms or formulas are of kind FunctionKind, so degenerate.
  * @see [[Function]] */
case object FunctionKind extends Kind { override def toString = "Function" }


/**
  * Sorts of expressions (real, bool, etc).
  * @see [[Expression]]
  */
sealed trait Sort
/** Unit type of [[edu.cmu.cs.ls.keymaerax.core.Nothing Nothing]] used as no argument. */
case object Unit extends Sort { override def toString = "Unit" }
/** Sort of booleans: [[edu.cmu.cs.ls.keymaerax.core.True True]], [[edu.cmu.cs.ls.keymaerax.core.False False]]. */
case object Bool extends Sort { override def toString = "Bool" }
/** Sort of real numbers: 0, 1, 2.5, 42. */
case object Real extends Sort { override def toString = "Real" }
/** Sort of state transformations (i.e. programs and games). */
case object Trafo extends Sort { override def toString = "Trafo" }
/** Tuple sort for [[edu.cmu.cs.ls.keymaerax.core.Pair Pair]]. */
case class Tuple(left: Sort, right: Sort) extends Sort { override def toString: String = "(" + left + "," + right + ")" }
/** User-defined object sort. */
case class ObjectSort(name : String) extends Sort { override def toString: String = name }


/** Sorts of state spaces for state-dependent operators.
  * @see [[SpaceDependent]] */
sealed trait Space
/** The sort denoting the whole state space alias list of all variables as arguments \bar{x} (axioms that allow any variable dependency) */
case object AnyArg extends Space { override def toString: String = "||" }
/** The sort denoting a slice of the state space that does not include/depend on/affect variables `taboos`. */
case class Except(taboos: immutable.Seq[Variable]) extends Space {
  //@note empty taboos should use AnyArg instead
  insist(taboos.nonEmpty, "taboos expect non-empty list of taboo variables")

  override def toString: String = "|" + taboos.mkString(",") + "|"
}


/*********************************************************************************
  * Expressions of differential dynamic logic and differential game logic
  *********************************************************************************
  */

/**
  * Expressions of differential dynamic logic.
  * Expressions are categorized according to the syntactic categories of the grammar of differential dynamic logic:
  *
  *  1. [[Term terms]] are of type [[edu.cmu.cs.ls.keymaerax.core.Term]] of kind [[edu.cmu.cs.ls.keymaerax.core.TermKind]]
  *  1. [[Formula formulas]] are of type [[edu.cmu.cs.ls.keymaerax.core.Formula]] of kind [[edu.cmu.cs.ls.keymaerax.core.FormulaKind]]
  *  1. [[Program hybrid programs]] are of type [[edu.cmu.cs.ls.keymaerax.core.Program]] of kind [[edu.cmu.cs.ls.keymaerax.core.ProgramKind]]
  *  1. [[DifferentialProgram differential programs]] are of type [[edu.cmu.cs.ls.keymaerax.core.DifferentialProgram]] of kind [[edu.cmu.cs.ls.keymaerax.core.DifferentialProgramKind]]
  *  1. [[Function function symbols]] are degenerate expressions that are syntactically incomplete, since not yet applied to arguments
  *     via [[FuncOf]] to form a term or via [[PredOf]] or [[PredicationalOf]] to form a formula.
  *
  * See [[https://doi.org/10.1007/s10817-016-9385-1 Section 2.1]]
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]]
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.apply]]
  * @see [[http://lfcps.org/logic/dL.html Syntax of differential dynamic logic]]
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  * @see [[Term]]
  * @see [[Formula]]
  * @see [[Program]]
  * @see [[DifferentialProgram]]
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

// partitioning into types of expressions in terms of atomicity, compositeness

/** Atomic expressions that do not have any proper subexpressions. */
trait Atomic extends Expression
/** Composite expressions that are composed of subexpressions */
trait Composite extends Expression

/** Unary composite expressions that are composed of one subexpression. */
trait UnaryComposite extends Composite {
  /** The child of this unary composite expression */
  val child: Expression
}

/** Binary composite expressions that are composed of two subexpressions. */
trait BinaryComposite extends Composite {
  /** The left child of this binary composite expression */
  val left: Expression
  /** The right child of this binary composite expression */
  val right: Expression
}

/** Function/predicate/predicational application.
  * @requires child.sort == func.domain
  * @ensures sort == func.sort */
trait ApplicationOf extends Composite {
  insist(child.sort == func.domain, "expected argument sort " + child.sort + " to match domain sort " + func.domain + " when applying " + func + " to " + child)
  //@note initialization order would dictate that subclasses either provide lazy val or early initializer.
  //insist(sort == func.sort, "sort of application is the sort of the function")
  /** The function/predicate/predicational that this application applies. */
  val func : Function
  /** The child argument that this function/predicate/predicational application is applied to. */
  val child : Expression
}

/**
  * A named symbol such as a variable or function symbol or predicate symbol or program constant symbol.
  * @note User-level symbols should not use underscores, which are reserved for the core.
  */
trait NamedSymbol extends Expression with Ordered[NamedSymbol] {
  //@note initialization order uses explicit dataStructureInvariant that is called in all nontrivial subclasses after val have been initialized.
  private[core] final def insistNamingConvention(): Unit = {
    insist(!name.isEmpty && !name.substring(0, name.length - 1).contains("_"), "non-empty names without underscores (except at end for internal names): " + name)
    //@note in particular: names cannot have primes
    insist(name.charAt(0).isLetter && name.forall(c => c.isLetterOrDigit || c == '_'), "alphabetical name expected: " + name)
    insist(index.getOrElse(0) >= 0, "nonnegative index if any " + this)
  }

  val name: String
  val index: Option[Int]

  /** Compare named symbols lexicographically: by name, index, category.
    * @return 0 for equal symbols
    *         <0 if this is lexicographically before `other`
    *         >0 if this is lexicographically after `other`
    * @note not used in the core, so not soundness-critical, but breaks tactics if wrong. */
  def compare(other: NamedSymbol): Int = {
    val cmp = name.compare(other.name)
    if (cmp != 0) cmp else {
      val cmp2 = index.getOrElse(-1) - other.index.getOrElse(-1)
      //@note .getCanonicalName would cause no collisions if same class name in different packages, but expressions are sealed in core.
      if (cmp2 != 0) cmp2 else getClass.getSimpleName.compareTo(other.getClass.getSimpleName)
    }
  } ensures(r => r!=0 || this==other, "no different categories of symbols with same name " + this + " compared to " + other)

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
trait StateDependent extends Expression

/** Expressions limited to a given sub state-space of only some variables and differential variables.
  * @since 4.2 */
trait SpaceDependent extends StateDependent {
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
  * Also terms of differential game logic, which only differ in the permitted mention of [[Dual]].
  *
  * Terms are of the form
  *   - [[AtomicTerm]] atomic terms are not composed of other terms
  *     - `x` variable as [[Variable]], including differential symbol `x'` as [[DifferentialSymbol]]
  *     - `5` number literals as [[Number]]
  *     - `F` nullary functional as [[UnitFunctional]] written `F(||)` in internal syntax.
  *     - `.` dot as reserved nullary function symbol [[DotTerm]] for term argument placeholders
  *     - Nothing for empty arguments [[Nothing]] for nullary functions
  *   - [[ApplicationOf]] terms that are function applications
  *     - `f(e)` function application as [[FuncOf]]([[Function]], [[Term]])
  *   - [[UnaryCompositeTerm]] unary composite terms composed of one child term
  *     - `-e` negation as [[Neg]]([[Term]])
  *     - `(e)'` differential as [[Differential]]([[Term]])
  *   - [[BinaryCompositeTerm]] binary composite terms composed of two children terms
  *     - `e+d` addition as [[Plus]]([[Term]], [[Term]])
  *     - `e-d` subtraction as [[Minus]]([[Term]], [[Term]])
  *     - `e*d` multiplication as [[Times]]([[Term]], [[Term]])
  *     - `e/d` division as [[Divide]]([[Term]], [[Term]])
  *     - `e^d` power as [[Power]]([[Term]], [[Term]])
  *     - `(e,d)` for pair as [[Pair]] for arguments
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.termParser]]
  * @see [[http://lfcps.org/logic/dL.html Syntax of differential dynamic logic]]
  */
sealed trait Term extends Expression {
  final val kind: Kind = TermKind
}

/** Atomic terms that have no proper subterms. */
trait AtomicTerm extends Term with Atomic

/** Real terms.
  * Used for commonality instead of leaking outside the core, because inferable from sort */
private[core] trait RTerm extends Term {
  final val sort: Sort = Real
}

/** Variables have a name and index and sort. They are either [[BaseVariable]] or [[DifferentialSymbol]]. */
trait Variable extends NamedSymbol with AtomicTerm
object Variable {
  /** Create a BaseVariable called 'name' with the given index and sort. */
  def apply(name: String, index: Option[Int]=None, sort: Sort=Real): BaseVariable = BaseVariable(name,index,sort)
}

/** Elementary variable called `name` with an index of a fixed sort (that is not a differential variable). */
case class BaseVariable(name: String, index: Option[Int]=None, sort: Sort=Real) extends Variable {
  insistNamingConvention()
}

/** Differential symbol x' for variable x.
  * Differential symbols are also called differential variables, because they are symbolic
  * but are also variables. */
case class DifferentialSymbol(x: Variable) extends Variable with RTerm {
  // In particular, this.sort==x.sort by extends Rterm
  insist(x.sort == Real, "differential symbols expect real sort")
  //@see SetLattice.except(x) which cannot currently represent the exclusion of all x''
  insist(!x.isInstanceOf[DifferentialSymbol], "Higher-order differential symbols are not supported " + this)
  final val name: String = x.name
  final val index: Option[Int] = x.index
  override def asString: String = x.asString + "'"
  override def toString: String = asString
  insistNamingConvention()
}

/** Number literal such as 0.5 or 42 etc. */
case class Number(value: BigDecimal) extends AtomicTerm with RTerm

/** Function symbol or predicate symbol or predicational symbol `name_index:domain->sort`
  * @param domain the sort of expected arguments.
  * @param sort the sort resulting when this function/predicate/predicational symbol has been applied to an argument.
  * @param interp if present, this function symbol `f` has a fixed interpretation defined by
  *   {{{
  *      y = f(x) <-> P(y,x)
  *   }}}
  *   where P is the interp formula, substituting (y,x) for the dot terms. That is
  *   {{{
  *     ._0 = f(._1) <-> P(._0,._1)
  *   }}}
  */
case class Function(name: String, index: Option[Int] = None, domain: Sort, sort: Sort, interp: Option[Formula] = None)
    extends NamedSymbol {
  final val kind: Kind = FunctionKind

  override def fullString: String = {
    val typeAnnotated = asString + ":" + domain + "->" + sort
    interp match {
      case Some(itp) => typeAnnotated + " = DotTerm() <-> " + itp.prettyString
      case None => typeAnnotated
    }
  }
  insistNamingConvention()

  override def asString: String = {
    interp match {
      case None => super.asString
      case Some(i) => super.asString + "<< " + i.prettyString + " >>"
    }
  }

  val interpreted : Boolean = interp.nonEmpty

  // Returns Some(n) if the sort is a right-associated Real domain of dimension n
  private def realDomain(s : Sort) : Option[Int] = {
    s match {
      case Tuple(Real, rest) => realDomain(rest).map(_ + 1)
      case Real => Some(1)
      case Unit => Some(0)
      case _ => None
    }
  }

  // Dimension of the domain interpreted as a Real domain
  val realDomainDim : Option[Int] = realDomain(domain)

  if (interpreted) {
    insist(sort == Real, "Interpreted function codomain must be Real.")
    insist(realDomainDim.isDefined, "Interpreted function domain must be Real(s).")

    insist(StaticSemantics.freeVars(interp.get).isEmpty, "Function interpretation must not mention free variables: " + interp.get)

    // The interpretation can only mention uninterpreted dot terms .0, ..., .n allowed by its domain dimension n
    val validDots = (0 to realDomainDim.get).map(i => DotTerm(Real, Some(i)))
    val signature = StaticSemantics.signature(interp.get).filter( f => f match {
      case f:Function if f.interpreted => false // by data structure invariant, f is a valid interpreted function symbol
      case _ => true
    })
    insist(signature.subsetOf(validDots.toSet),
      "Function interpretation can only mention uninterpreted dots: " + validDots + " but got: "+ signature)
  }

}

/** •: Placeholder for terms in uniform substitutions of given sort. Reserved nullary function symbols
  * \\cdot for uniform substitutions are unlike ordinary function symbols by convention. */
case class DotTerm(s: Sort = Real, idx: Option[Int] = None) extends Expression with NamedSymbol with AtomicTerm {
  final val sort: Sort = s
  final val name: String = "\\cdot"
  final val index: Option[Int] = idx
}

/** The empty argument of Unit sort (as argument for arity 0 function/predicate symbols). */
case object Nothing extends NamedSymbol with AtomicTerm {
  final val sort: Sort = Unit
  final val name: String = "\\nothing"
  final val index: Option[Int] = None
}

/** Function symbol applied to argument child `func(child)`. */
case class FuncOf(func: Function, child: Term) extends CompositeTerm with ApplicationOf {
  /** The sort of an ApplicationOf is the sort of func
    * @ensures sort == func.sort */
  final val sort: Sort = func.sort
}

/** Arity 0 functional symbol `name:sort`, written `f(||)`, or limited to the given state space `f(|x||)`.
  * The semantics of arity 0 functional symbol is given by the state, with the additional promise
  * that the taboos are not free so the value does not depend on taboos when `space=Except(taboos)`.
  * @note In theory, `f(||)` is written `f(\bar{x})` where `\bar{x}` is the vector of all variables.
  *       By analogy, `f(|x|)` is like having all variables other than taboo x as argument. */
case class UnitFunctional(name: String, space: Space, sort: Sort) extends AtomicTerm with SpaceDependent with NamedSymbol {
  override def asString: String = super.asString + "(" + space + ")"
  insistNamingConvention()
}


/** Composite terms that are composed of subterms. */
trait CompositeTerm extends Term with Composite

/** Unary Composite Terms, i.e. terms composed of one real subterm. */
trait UnaryCompositeTerm extends UnaryComposite with CompositeTerm {
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

/** Unary Composite Real Terms, i.e. real terms composed of one real term.
  * Used for commonality instead of leaking outside the core, because inferable from sort. */
private[core] trait RUnaryCompositeTerm extends UnaryCompositeTerm with RTerm {
  insist(child.sort == Real, "expected argument sort real: " + child.sort)
}

/** Binary Composite Terms, i.e. terms composed of two subterms. */
trait BinaryCompositeTerm extends BinaryComposite with CompositeTerm {
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

/** Binary Composite Real Terms, i.e. real terms composed of two real terms.
  * Used for commonality instead of leaking outside the core, because inferable from sort. */
private[core] trait RBinaryCompositeTerm extends BinaryCompositeTerm with RTerm {
  insist(left.sort == Real && right.sort == Real, "expected argument sorts real: " + left + " and " + right)
  val left: Term
  val right: Term
}

/** - unary negation of reals: minus. */
case class Neg(child: Term) extends RUnaryCompositeTerm { def reapply = copy }
/** + binary addition of reals. */
case class Plus(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** - binary subtraction of reals. */
case class Minus(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** * binary multiplication of reals. */
case class Times(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** / real division of reals where `right` nonzero. */
case class Divide(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }
/** real exponentiation or power: left^right^.
  * @note By mathematical conventions, powers are parsed in right-associative ways.
  *       That is, x^4^2 is parsed as x^(4^2).
  */
//@note axiom("^' derive power") needs right to be a Term not just a Number.
case class Power(left: Term, right: Term) extends RBinaryCompositeTerm { def reapply = copy }

/** (child)' differential of the term `child`.
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
case class Differential(child: Term) extends RUnaryCompositeTerm { def reapply = copy }

/** Pairs (left,right) for binary Function and FuncOf and PredOf.
  * @note By convention, pairs are usually used in right-associative ways.
  *       That is, n-ary argument terms (t1,t2,t3,...tn) are represented as (t1,(t2,(t3,...tn))).
  *       This is not a strict requirement, but the default parse and suggested use. */
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
  * Also includes formulas of differential game logic, which only differ in the permitted mention of [[Dual]].
  *
  * Formulas are of the form
  *   - [[AtomicFormula]] atomic formulas that are not composed of other formulas
  *     - `true` truth as [[True]] and `false` as [[False]]
  *     - `P` nullary predicational as [[UnitPredicational]] written `P(||)` in internal syntax.
  *     - `_` dot as reserved nullary predicational [[DotFormula]] for formula argument placeholders
  *   - [[ComparisonFormula]] are [[AtomicFormula]] composed of two terms but not composed of formulas
  *     - `e>=d` comparisons as [[GreaterEqual]]([[Term]],[[Term]]) and likewise [[Equal]], [[NotEqual]], [[Greater]], [[LessEqual]], [[Less]]
  *   - [[ApplicationOf]] predicate applications
  *     - `p(e)` predicate application as [[PredOf]]([[Function]], [[Term]])
  *     - `P{Q}` predicational application or quantifier symbol as [[PredicationalOf]]([[Function]], [[Formula]])
  *   - [[UnaryCompositeFormula]] unary composite formulas composed of one child formula
  *     - `!P` logical negation as [[Not]]([[Formula]])
  *     - `(P)'` differential formula as [[DifferentialFormula]]([[Formula]]])
  *   - [[BinaryCompositeFormula]] binary composite formulas composed of a left and a right formula
  *     - `P&Q` conjunction as [[And]]([[Formula]]], [[Formula]]])
  *     - `P|Q` disjunction as [[Or]]([[Formula]]], [[Formula]]])
  *     - `P->Q` implication as [[Imply]]([[Formula]]], [[Formula]]])
  *     - `P<->Q` biimplication as [[Equiv]]([[Formula]]], [[Formula]]])
  *   - [[Quantified]] quantified formulas quantifying a variable
  *     - `\forall x P` universal quantification as [[Forall]]([[Variable]]], [[Formula]]])
  *     - `\exists x P` existential quantification as [[Exists]]([[Variable]]], [[Formula]]])
  *   - [[Modal]] modal formulas with a program and a formula child
  *     - `[a]P` box modality application for all runs as [[Box]]([[Program]]], [[Formula]]])
  *     - `⟨a⟩P` diamond modality application for some run as [[Diamond]]([[Program]]], [[Formula]]])
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.formulaParser]]
  */
sealed trait Formula extends Expression {
  final val kind: Kind = FormulaKind
  final val sort: Sort = Bool
}

/** Atomic formulas that have no subformulas (but may still have subterms). */
trait AtomicFormula extends Formula with Atomic

/** Atomic comparison formula composed of two terms. */
trait ComparisonFormula extends AtomicFormula with BinaryComposite {
  insist(left.sort == right.sort, "expected arguments of the same sort: " + left + " and " + right)
  /** Create a formula of this constructor but with the give left and right arguments instead. (copy)
    * @example {{{
    *         GreaterEqual(Number(7), Variable("v")).reapply(Variable("a"), Number(99)) == GreaterEqual(Variable("a"), Number(99))
    *         }}}
    */
  def reapply: (Term,Term)=>Formula
  val left: Term
  val right: Term
}

/** Real comparison formula composed of two real terms.
  * Used for commonality instead of leaking outside the core, because inferable from sort. */
private[core] trait RComparisonFormula extends ComparisonFormula {
  insist(left.sort == Real && right.sort == Real, "expected argument sorts real: " + left + " and " + right)
}

/** Verum formula true. */
case object True extends AtomicFormula
/** Falsum formula false. */
case object False extends AtomicFormula

/** ``=`` equality left = right. */
case class Equal(left: Term, right: Term) extends ComparisonFormula { def reapply = copy }
/** != disequality left != right. */
case class NotEqual(left: Term, right: Term) extends ComparisonFormula { def reapply = copy }

/** >= greater or equal comparison left >= right of reals. */
case class GreaterEqual(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }
/** > greater than comparison left > right of reals. */
case class Greater(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }
/** < less or equal comparison left <= right of reals. */
case class LessEqual(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }
/** <= less than comparison left < right of reals. */
case class Less(left: Term, right: Term) extends RComparisonFormula { def reapply = copy }

/** ⎵: Placeholder for formulas in uniform substitutions. Reserved nullary predicational symbol
  * _ for substitutions is unlike ordinary predicational symbols by convention. */
case object DotFormula extends NamedSymbol with AtomicFormula with StateDependent {
  final val name: String = "\\_"
  final val index: Option[Int] = None
}

/** Predicate symbol applied to argument child `func(child)` where `func` is Boolean-valued .*/
case class PredOf(func: Function, child: Term) extends AtomicFormula with ApplicationOf {
  //@note redundant requires since ApplicationOf.sort and Formula.requires will check this already.
  insist(func.sort == Bool, "expected predicate sort Bool found " + func.sort + " in " + this)
}

/** Predicational or quantifier symbol applied to argument formula child, written `C{child}`.
  * Predicationals are similar to predicate symbol applications, except that they accept a formula
  * as an argument rather than a term. Also, their truth-value may depend on the entire truth table of `child` at any state.
  * @note In theory, `C{child}` is written `C(child)`. */
case class PredicationalOf(func: Function, child: Formula)
  extends AtomicFormula with ApplicationOf with StateDependent {
  //@note redundant requires since ApplicationOf.sort and Formula.requires will check this already.
  insist(func.sort == Bool, "expected argument sort Bool: " + this)
  insist(func.domain == Bool, "expected domain simplifies to Bool: " + this)
  insist(func.interp.isEmpty, "only uninterpreted predicationals are currently supported: " + this)
}

/** Arity 0 predicational symbol `name:bool`, written `P(||)`, or limited to the given state space `P(|x|)`.
  * The semantics of arity 0 predicational symbol is looked up by the state, with the additional promise
  * that taboos are not free so the value does not depend on taboos when `space=Except(taboos)`.
  * @note In theory, `P(||)` is written `P(\bar{x})` where `\bar{x}` is the vector of all variables.
  *       By analogy, `P(|x|)` is like having all variables other than taboo x as argument. */
case class UnitPredicational(name: String, space: Space) extends AtomicFormula with SpaceDependent with NamedSymbol {
  override def asString: String = super.asString + "(" + space + ")"
  insistNamingConvention()
}


/** Composite formulas composed of subformulas. */
trait CompositeFormula extends Formula with Composite

/** Unary Composite Formulas, i.e. formulas composed of one subformula. */
trait UnaryCompositeFormula extends UnaryComposite with CompositeFormula {
  /** Create a formula of this constructor but with the given argument as child instead. (copy)
    * @example {{{
    *         Not(GreaterEqual(Variable("x"),Number(0))).reapply(NotEqual(Number(7),Number(9))) == Not(NotEqual(Number(7),Number(9)))
    *         Not(True).reapply(False) == Not(False)
    *         }}}
    */
  def reapply: Formula=>Formula
  val child: Formula
}

/** Binary Composite Formulas, i.e. formulas composed of two subformulas. */
trait BinaryCompositeFormula extends BinaryComposite with CompositeFormula {
  /** Create a formula of this constructor but with the give left and right arguments instead. (copy)
    * @example {{{
    *         Or(GreaterEqual(Variable("x"),Number(0)), False).reapply(True, NotEqual(Number(7),Number(9))) == Or(True, NotEqual(Number(7),Number(9)))
    *         }}}
    */
  def reapply: (Formula,Formula)=>Formula
  val left: Formula
  val right: Formula
}

/** ! logical negation: not. */
case class Not(child: Formula) extends UnaryCompositeFormula { def reapply = copy }
/** & logical conjunction: and. */
case class And(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }
/** | logical disjunction: or. */
case class Or(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }
/** -> logical implication: implies. */
case class Imply(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }
/** <-> logical biimplication: equivalent. */
case class Equiv(left: Formula, right:Formula) extends BinaryCompositeFormula { def reapply = copy }

/** Quantified formulas. */
trait Quantified extends CompositeFormula {
  insist(vars.nonEmpty, "quantifiers bind at least one variable")
  insist(vars.distinct.size == vars.size, "no duplicates within one quantifier block")
  insist(vars.forall(x => x.sort == vars.head.sort), "all vars must have the same sort")
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
/** \forall vars universally quantified formula for all real values of vars. */
case class Forall(vars: immutable.Seq[Variable], child: Formula) extends Quantified { def reapply = copy }
/** \exists vars existentially quantified formula for some real value of vars. */
case class Exists(vars: immutable.Seq[Variable], child: Formula) extends Quantified { def reapply = copy }

/** Modal formulas. */
trait Modal extends CompositeFormula {
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
/** box modality all runs of program satisfy child: [program]child. */
case class Box(program: Program, child: Formula) extends Modal { def reapply = copy }
/** diamond modality some run of program satisfies child: ⟨program⟩child. */
case class Diamond(program: Program, child: Formula) extends Modal { def reapply = copy }

/** Differential formula are differentials of formulas in analogy to differential terms (child)'.
  * In theory they are only used in the form (e>=k)' which is (e)'>=(k)'. In practice, derived forms are useful. */
case class DifferentialFormula(child: Formula) extends UnaryCompositeFormula { def reapply = copy }

/*********************************************************************************
  * Programs of differential dynamic logic
  *********************************************************************************
  */

/**
  * Hybrid programs of differential dynamic logic.
  * Also includes hybrid games of differential game logic, which only differ in the permitted mention of [[Dual]].
  *
  * Hybrid Programs are of the form
  *   - [[AtomicProgram]] atomic programs that are not composed of other programs
  *     - `x:=e` assignment as [[Assign]]([[Variable]],[[Term]])
  *       and likewise differential assignment `x':=e` as [[Assign]]([[DifferentialSymbol]],[[Term]])
  *     - `x:=*` nondeterministic assignment as [[AssignAny]]([[Variable]])
  *       and likewise nondeterministic differential assignment `x':=*` as [[AssignAny]]([[DifferentialSymbol]])
  *     - `a` program constant as [[ProgramConst]] written `a{|^x|}` if x taboo.
  *     - `a` system constant as [[SystemConst]] without games, written `a{|^@|}` in internal syntax.
  *     - `?P` test as [[Test]]([[Formula]])
  *   - [[BinaryCompositeProgram]] binary composite programs composed of a left and right program
  *     - `a++b` nondeterministic choice as [[Choice]]([[Program]]], [[Program]]])
  *     - `a;b` sequential composition as [[Compose]]([[Program]]], [[Program]]])
  *   - [[UnaryCompositeProgram]] unary composite programs composed of a child program
  *     - `{a}*` nondeterministic repetition as [[Loop]]([[Program]]])
  *     - `{a}^@` dual game as [[Dual]]([[Program]]]) for hybrid games of differential game logic.
  *   - Special
  *     - `{c&Q}` differential equation system as [[ODESystem]]([[DifferentialProgram]], [[Formula]])
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.programParser]]
  */
sealed trait Program extends Expression {
  val kind: Kind = ProgramKind
  final val sort: Sort = Trafo
}

/** Atomic programs that have no subprograms (but may still have subterms or subformulas). */
trait AtomicProgram extends Program with Atomic

/** Uninterpreted program constant symbol / game symbol, possibly limited to the given state space.
  * The semantics of ProgramConst symbol is looked up by the state,
  * with the additional promise that taboos are neither free nor bound, so the run does
  * not depend on the value of taboos nor does the value of taboos change when space=Except(taboos).
  * @param space The part of the state space that the interpretation/replacement of this symbol
  *              is limited to have free or bound.
  *              - `AnyArg` is the default allowing full read/write access to the state.
  *              - `Taboo(x)` means `x` can neither be free nor bound. Written `a{|x|}` in internal syntax.
  * @note In theory, `a;` is written `a`.
  *       By analogy, `a{|x|}` has read/write access to the entire state except the taboo x. */
case class ProgramConst(name: String, space: Space = AnyArg) extends NamedSymbol with AtomicProgram with SpaceDependent {
  override def asString: String = if (space == AnyArg) super.asString else super.asString + "{" + space + "}"
  insistNamingConvention()
}

/** Uninterpreted hybrid system program constant symbols that are NOT hybrid games, limited to the given state space.
  * Written `a{|^@|}` in internal syntax.
  * @param space The part of the state space that the interpretation/replacement of this symbol
  *              is limited to have free or bound.
  *              - `AnyArg` is the default allowing full read/write access to the state.
  *              - `Taboo(x)` means `x` can neither be free nor bound. Written `a{|^@x|}` in internal syntax.
  * @since 4.7.4 also SpaceDependent with `space` parameter.
  */
case class SystemConst(name: String, space: Space = AnyArg) extends NamedSymbol with AtomicProgram with SpaceDependent {
  override def asString: String = super.asString + (space match {
    case AnyArg => "{|^@|}"
    case Except(taboos) => "{|^@" + taboos.mkString(",") + "|}"
  })
  insistNamingConvention()
}

/** x:=e assignment and/or differential assignment x':=e. */
case class Assign(x: Variable, e: Term) extends AtomicProgram {
  insist(e.sort == x.sort, "assignment of compatible sort " + this)
}
/** x:=* nondeterministic assignment and/or nondeterministic differential assignment x':=*. */
case class AssignAny(x: Variable) extends AtomicProgram
/** ?cond test a formula as a condition on the current state. */
case class Test(cond: Formula) extends AtomicProgram


/** Composite programs that are composed of subprograms. */
trait CompositeProgram extends Program with Composite

/** Unary Composite Programs, i.e. programs composed of one subprogram. */
trait UnaryCompositeProgram extends UnaryComposite with CompositeProgram {
  /** Create a program of this constructor but with the given argument as child instead. (copy)
    * @example {{{
    *         Loop(ProgramConst("alpha")).reapply(Assign(Variable("x"),Number(42))) == Loop(Assign(Variable("x"),Number(42)))
    *         }}}
    */
  def reapply: Program=>Program
  val child: Program
}

/** Binary Composite Programs, i.e. programs composed of two subprograms. */
trait BinaryCompositeProgram extends BinaryComposite with CompositeProgram {
  /** Create a program of this constructor but with the give left and right arguments instead. (copy)
    * @example {{{
    *         Choice(ProgramConst("alpha"), ProgramConst("beta")).reapply(ProgramConst("gamma"), ProgramConst("delta")) == Choice(ProgramConst("gamma"), ProgramConst("delta"))
    *         }}}
    */
  def reapply: (Program,Program)=>Program
  val left: Program
  val right: Program
}


/** left++right nondeterministic choice running either left or right. */
case class Choice(left: Program, right: Program) extends BinaryCompositeProgram { def reapply = copy }
/** left;right sequential composition running right after left. */
case class Compose(left: Program, right: Program) extends BinaryCompositeProgram { def reapply = copy }
/** child* nondeterministic repetition running child arbitrarily often. */
case class Loop(child: Program) extends UnaryCompositeProgram { def reapply = copy }
/** `child^d` dual program continuing game child after passing control to the opponent. */
case class Dual(child: Program) extends UnaryCompositeProgram { def reapply = copy }

/** Differential equation system `ode` with given evolution domain constraint. */
case class ODESystem(ode: DifferentialProgram, constraint: Formula = True) extends Program {
  /** differentials could be allowed according to JAR'17, but the implementation is simplified when disallowed.
    * But then ODE axioms would need generalizations to q(x,x') and DS DI Cont need [x':=f(x)] generalizations. */
  insist(!StaticSemantics.isDifferential(constraint), "No differentials in evolution domain constraints {" + ode + " & " + constraint + "}")
}



/**
  * Differential programs of differential dynamic logic.
  *
  * Differential Programs are of the form
  *   - [[AtomicDifferentialProgram]] atomic differential programs are not composed of other differential programs
  *     - `x'=e` atomic differential equation as [[AtomicODE]]([[DifferentialSymbol]],[[Term]])
  *     - `c` differential program constant as [[DifferentialProgramConst]]
  *   - BinaryCompositeDifferentialProgram except it's the only composition for differential programs.
  *     - `c,d` differential product as [[DifferentialProduct]]([[DifferentialProgram]]], [[DifferentialProgram]]])
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.differentialProgramParser]]
  */
sealed trait DifferentialProgram extends Program {
  override final val kind: Kind = DifferentialProgramKind
}

/** Atomic differential programs that have no sub-differential-equations (but may still have subterms) */
trait AtomicDifferentialProgram extends AtomicProgram with DifferentialProgram

/** Uninterpreted differential program constant, limited to the given state space.
  * The semantics of arity 0 DifferentialProgramConst symbol is looked up by the state,
  * with the additional promise that taboos are neither free nor bound, so the run does
  * not depend on the value of taboos nor does the value of taboos change when space=Except(taboos).
  * @param space The part of the state space that the interpretation/replacement of this symbol is limited to have free or bound.
  *              `AnyArg is` the default allowing full read/write access to the state.
  *              `Taboo(x)` means `x` can neither be free nor bound. */
case class DifferentialProgramConst(name: String, space: Space = AnyArg)
  extends AtomicDifferentialProgram with SpaceDependent with NamedSymbol {
  override def asString: String = if (space == AnyArg) super.asString else super.asString + "{" + space + "}"
  insistNamingConvention()
}

/** x'=e atomic differential equation where x is evolving for some time with time-derivative e. */
case class AtomicODE(xp: DifferentialSymbol, e: Term) extends AtomicDifferentialProgram {
  insist(e.sort == Real, "expected argument sort real " + this)
  /* @NOTE Soundness: AtomicODE requires explicit-form so f(?) cannot verbatim mention differentials/differential symbols,
     which is required for soundness of axiom "DE differential effect (system)" */
  //@note avoid toString call, which could cause an infinite loop coming from contracts checking in pretty printer. But should probably be taken care of.
  insist(xp.x.isInstanceOf[BaseVariable] && !StaticSemantics.isDifferential(e), "Explicit-form differential equations expected, without any differentials on right-hand side: " + xp + "=" + e)
}

/**
  * left,right parallel product of differential programs.
  * This data structure automatically left-reassociates to list form so that `left` never is a Differential Product.
  * DifferentialProduct(AtomicDifferentialProgram, DifferentialProduct(AtomicDifferentialProgram, ....))
  * @note This is a case class except for an override of the apply function to ensure left-associative representation.
  * @note Private constructor so only [[DifferentialProduct.apply]] can ever create this, which will re-associate et al.
  */
final class DifferentialProduct private(val left: DifferentialProgram, val right: DifferentialProgram)
  extends DifferentialProgram with BinaryComposite {

  override def equals(e: Any): Boolean = e match {
    case a: DifferentialProduct => left == a.left && right == a.right
    case _ => false
  }

  override def hashCode: Int = 31 * left.hashCode() + right.hashCode()
}

object DifferentialProduct {
  /**
    * Construct an ODEProduct in reassociated normal form, i.e. as a list such that `left` will never be an ODEProduct in
    * the data structures.
    * @note Completeness: reassociate needed in DifferentialProduct data structures for
    *       axiom "DE differential effect (system)" so as not to get stuck after it.
    */
  def apply(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct = {
    insist(differentialSymbols(left).intersect(differentialSymbols(right)).isEmpty, "No duplicate differential equations when composing differential equations " + left + " and " + right)
    reassociate(left, right)
  } ensures(r => listify(r) == listify(left) ++ listify(right), "reassociating DifferentialProduct does not change the list of atomic ODEs"
    ) ensures(r => differentialSymbols(r).length == differentialSymbols(r).distinct.length,
    "No undetected duplicate differential equations when composing differential equations " + left + " and " + right + " to form " + reassociate(left, right))

  def unapply(e: Any): Option[(DifferentialProgram, DifferentialProgram)] = e match {
    case a: DifferentialProduct => Some(a.left, a.right)
    case _ => None
  }

  /** Reassociate the data structure left-associative list form. */
  /** @tailrec */
  private def reassociate(left: DifferentialProgram, right: DifferentialProgram): DifferentialProduct = left match {
    // properly associated cases
    case l: AtomicODE => new DifferentialProduct(l, right)
    case l: DifferentialProgramConst => new DifferentialProduct(l, right)
    // reassociate so that there's no more differential product on the left
    case DifferentialProduct(ll, lr) =>
      assert(ll.isInstanceOf[AtomicDifferentialProgram], "reassociation has succeeded on the left")
      reassociate(ll, reassociate(lr, right))
  }

  /** Turn differential program `ode` along its DifferentialProduct into a list of atomic differential programs. */
  def listify(ode: DifferentialProgram): immutable.List[DifferentialProgram] = ode match {
    case p: DifferentialProduct => listify(p.left) ++ listify(p.right)
    case a: AtomicDifferentialProgram => a :: Nil
  }

  /** The list of all literal differential symbols in ODE.
    * DifferentialProgramConst is counted as having no symbols just yet, because its use is to check nonoverlap of present primed symbols. */
  //@note Differential symbols can only occur on the left of AtomicODEs anyhow.
  //@note Could use the StaticSemantics from this contract equivalently.
  private def differentialSymbols(ode: DifferentialProgram): immutable.List[DifferentialSymbol] = {ode match {
    case p: DifferentialProduct => differentialSymbols(p.left) ++ differentialSymbols(p.right)
    case AtomicODE(xp, _) => xp :: Nil
    case a: DifferentialProgramConst => Nil
  }} ensures(r => r.toSet==StaticSemantics.symbols(ode).filter(x=>x.isInstanceOf[DifferentialSymbol]),
    "StaticSemantics should agree since differential symbols only occur on the left-hand side of differential equations " + StaticSemantics.symbols(ode).toList.filter(x=>x.isInstanceOf[DifferentialSymbol]))

}
