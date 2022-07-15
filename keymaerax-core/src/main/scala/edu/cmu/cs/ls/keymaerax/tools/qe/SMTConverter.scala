/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.tools.ConversionException

import scala.annotation.tailrec

/** A default SMT converter with output as preferred by KeYmaera X. */
object DefaultSMTConverter extends SMTConverter {}

/**
  * Base class for SMT converters with conversion per SMTLib specification.
  * Created by ran on 8/24/15.
  * @author Ran Ji
  * @author Stefan Mitsch
  */
abstract class SMTConverter extends (Formula=>String) {
  /** Convert given formula to an SMTLib specification that, if SMT(\result) returns `unsat` says that `expr` is valid. */
  def apply(expr: Formula): String = generateAssertNegation(expr)

  // Prefixes that SMT accepts but NamedSymbol would refuse to make disjoint by construction
  private val VAR_PREFIX = "_v_"
  private val FUNC_PREFIX = "_f_"
  private val DIFFSYMBOL_PREFIX = "_d_"

  private val SMT_ABS = "absolute"
  private val SMT_MIN = "minimum"
  private val SMT_MAX = "maximum"

  //@todo Could translate "axiomatic" definitions of abs/min/max to SMT-definitions dynamically instead.
  private val SMT_INTERPRETED_FUNCTIONS = Map[NamedSymbol, String](
    InterpretedSymbols.absF -> ("(define-fun " + nameIdentifier(InterpretedSymbols.absF) + " ((x Real)) Real\n  (ite (>= x 0) x (- x)))"),
    InterpretedSymbols.minF -> ("(define-fun " + nameIdentifier(InterpretedSymbols.minF) + " ((x1 Real) (x2 Real)) Real\n  (ite (<= x1 x2) x1 x2))"),
    InterpretedSymbols.maxF -> ("(define-fun " + nameIdentifier(InterpretedSymbols.maxF) + " ((x1 Real) (x2 Real)) Real\n  (ite (>= x1 x2) x1 x2))")
  )

  /**
    * Convert KeYmaera X expression to SMT expression with negated formula form
    * the result SMT expression is checked by Z3 for satisfiability
    * if SMT solver returns:
    *   unsatisfiable => original KeYmaera X formula `expr` is valid
    *   satisfiable => original KeYmaera X formula `expr` is not valid, but is not necessarily equivalent to False.
    */
  private def generateAssertNegation(expr: Formula): String = {
    val (varDec, smtFormula) = generateSMT(expr)
    varDec + "(assert (not " + smtFormula + "))" + "\n(check-sat)\n"
  }

  /** Convert KeYmaera X expression to SMT form which contains: variable/function declaration and converted SMT formula */
  def generateSMT(expr: Expression): (String, String) = {
    val allSymbols = StaticSemantics.symbols(expr).toList.sorted
    val names = allSymbols.map(s => nameIdentifier(s))
    require(names.distinct.size == names.size, "Expect unique name_index identifiers")
    var varDec = allSymbols.map({
        case x: Variable =>
          //@note this check is redundant with the check from nameIdentifier
          require(x.sort==Real, "Can only deal with variable of type real, but not " + x.sort)
          "(declare-fun " + nameIdentifier(x) + " () " + x.sort + ")" //@note identical to (declare-const name sort)
        case fn@Function(_, _, _, _, Some(_)) =>
          if (SMT_INTERPRETED_FUNCTIONS.contains(fn)) SMT_INTERPRETED_FUNCTIONS(fn)
          else throw ConversionException("Conversion of interpreted function " + fn.prettyString + " not supported")
        case fn@Function(_, _, _, _, None) =>
          require(fn.sort==Real, "Only support functions of type real, but not " + fn.sort)
          "(declare-fun " + nameIdentifier(fn) + " (" + generateFuncParamSorts(fn.domain) +  ") " + fn.sort + ")"
      }
    ).mkString("\n")
    val smtFormula = convertToSMT(expr)
    //@note newline characters considered insignificant whitespace
    // @see [[http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf, p. 22]]
    if (varDec.nonEmpty) varDec += "\n"
    (varDec, smtFormula)
  }

  /** Identifier corresponding to a NamedSymbol including its index and a type-specific prefix. */
  private def nameIdentifier(s: NamedSymbol): String = {
    require(s.sort == Real, "Only real-valued symbols are currently supported, but got " + s.prettyString + " of sort " + s.sort)
    def nameOf(n: String, i: Option[Int]): String = if (i.isEmpty) n else n + "_" + i.get
    s match {
      case InterpretedSymbols.minF => SMT_MIN
      case InterpretedSymbols.maxF => SMT_MAX
      case InterpretedSymbols.absF => SMT_ABS
      case Function(name, index, _, _, None) => FUNC_PREFIX + nameOf(name, index)
      case BaseVariable(name, index, _) => VAR_PREFIX + nameOf(name, index)
      case DifferentialSymbol(BaseVariable(name, index, _)) => DIFFSYMBOL_PREFIX + nameOf(name, index)
      case _ => throw ConversionException("Name conversion of " + s.prettyString + " not supported")
    }
  }

  /** Converts an identifier back to a [[NamedSymbol]]. @see [[nameIdentifier]]. */
  private[tools] def nameFromIdentifier(s: String): NamedSymbol = {
    def toName(s: String): (String, Option[Int]) = {
      if (s.endsWith("_")) (s, None)
      else s.split("_").toSeq match {
        case n +: Nil =>  (n, None)
        case n +: i +: Nil => (n, Some(Integer.valueOf(i)))
        case n +: "" +: i +: Nil => (n + "_", Some(Integer.valueOf(i))) //@note case x__i
      }
    }
    if (s.startsWith(VAR_PREFIX)) { val (n, i) = toName(s.stripPrefix(VAR_PREFIX)); Variable(n, i) }
    else if (s.startsWith(FUNC_PREFIX)) { val (n, i) = toName(s.stripPrefix(FUNC_PREFIX)); Function(n, i, Unit, Real) }
    else if (s.startsWith(DIFFSYMBOL_PREFIX)) { val (n, i) = toName(s.stripPrefix(DIFFSYMBOL_PREFIX)); DifferentialSymbol(Variable(n, i)) }
    else throw ConversionException("Unable to convert " + s + " to a named symbol")
  }


  /** Convert sort to SMT parameter declaration syntax. */
  private def generateFuncParamSorts(t: Sort) : String = t match {
    case Unit => ""
    //@note: disassociate the arguments, since mapping from name to types is unique by assertion in [[generateSMT]]
    case Tuple(l, r) => generateFuncParamSorts(l) + " " + generateFuncParamSorts(r)
    case _ => t.toString
  }

  private def convertToSMT(expr: Expression) : String = expr match {
    case t: Term  => convertTerm(t)
    case f: Formula => convertFormula(f)
    case _ => throw ConversionException("The input expression: \n" + expr + "\nis expected to be a term or formula.")
  }

  /** Convert KeYmaera X formula to string in SMT notation */
  protected def convertFormula(f: Formula) : String = f match {
    case Not(ff)        => "(not "   + convertFormula(ff) + ")"
    case And(l, r)      => "(and "   + convertFormula(l) + " " + convertFormula(r) + ")"
    case Or(l, r)       => "(or "    + convertFormula(l) + " " + convertFormula(r) + ")"
    case Imply(l, r)    => "(=> "    + convertFormula(l) + " " + convertFormula(r) + ")"
    case Equiv(l, r)    => "(equiv " + convertFormula(l) + " " + convertFormula(r) + ")"
    case Equal(l, r)    => "(= "     + convertTerm(l) + " " + convertTerm(r) + ")"
    case NotEqual(l, r) => convertFormula(Not(Equal(l, r)))
    case Greater(l,r)   => "(> "     + convertTerm(l) + " " + convertTerm(r) + ")"
    case GreaterEqual(l,r) => "(>= " + convertTerm(l) + " " + convertTerm(r) + ")"
    case Less(l,r)      => "(< "     + convertTerm(l) + " " + convertTerm(r) + ")"
    case LessEqual(l,r) => "(<= "    + convertTerm(l) + " " + convertTerm(r) + ")"
    case True => "true"
    case False => "false"
    case f: Forall => convertQuantified(f, "forall")
    case e: Exists => convertQuantified(e, "exists")
    case m: Modal       => throw ConversionException("There is no conversion from modalities with hybrid programs to SMT " + m)
  }

  /** Convert KeYmaera X term to string in SMT notation */
  protected def convertTerm(t: Term) : String = {
    require(t.sort == Real || t.sort.isInstanceOf[Tuple], "SMT can only deal with reals or pairs, but not with sort " + t.sort)
    t match {
      case Neg(c)       => "(- " + convertTerm(c) + ")"
      case Plus(l, r)   => "(+ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Minus(l, r)  => "(- " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Times(l, r)  => "(* " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Divide(l, r) => "(/ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Power(l, r)  => "(^ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Number(n) =>
        //@@note SMTLib distinguishes numerals (0 | [^0]digit+) from decimals (numeral [\.] 0* numeral)
        //@note according to the SMTLib specification, numbers without . are numerals, numbers with . are decimals;
        // their meaning depends on the underlying theory!
        // @see [[http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf, p. 22, p. 25]]
        // Z3 interprets them as mathematical Integers and mathematical Reals

        /**@note decimalDouble is 64 bit IEEE 754 double-precision float,
          *      long is 64 bit signed value. -9223372036854775808 to 9223372036854775807
          *      both have the maximal range in their category */
        //@note n.signum < 0 is equivalent to n < BigDecimal(0)
        if (n.signum < 0) {
          //@note SMT form of negative number -5 is (- 5)
          // avoids conversion to double, uses 'signum' to determine sign and builtin negate function
          //@note negative form has to be representable, in particular n cannot have been MIN_LONG
          assert((-n).isDecimalDouble || (-n).isValidLong, throw ConversionException("Term contains illegal numbers: " + t))
          //@note if toString output contains '.' then SMTLib decimal, otherwise SMTLib numeral
          "(- " + (-n).toString() + ")"
        } else {
          assert(n.isDecimalDouble || n.isValidLong, throw ConversionException("Term contains illegal numbers: " + t))
          //@note if toString output contains '.' then SMTLib decimal, otherwise SMTLib numeral
          n.toString()
        }
      case t: BaseVariable => nameIdentifier(t)
      case t: DifferentialSymbol => nameIdentifier(t)
      case FuncOf(fn, Nothing) => nameIdentifier(fn)
      case FuncOf(fn, child) =>
        if (fn.interpreted && !SMT_INTERPRETED_FUNCTIONS.contains(fn)) fn match {
          // TODO: handle
          case _ => throw ConversionException("Interpreted function not supported presently by SMT: " + t)
        } else "(" + nameIdentifier(fn) + " " + convertTerm(child) + ")"
      //@note: disassociates the arguments and no extra parentheses for pairs, since mapping from name to types is unique by assertion in [[generateSMT]]
      case Pair(l, r)  => convertTerm(l) + " " + convertTerm(r)
      case _ => throw ConversionException("Conversion of term to SMT is not defined: " + t)
    }
  }

  /** Converts a quantified formula, converts nested quantifiers into block quantifier. */
  protected def convertQuantified(f: Quantified, op: String): String = {
    /** Recursively collect quantified variables, return variables+child formula */
    @tailrec
    def collectVars(vsSoFar: Array[Variable], candidate: Formula): (Array[Variable], Formula) = (f, candidate) match {
      // collect only from quantifiers that are the same as the root `f` quantifier
      case (_: Exists, Exists(nextVs, nextf)) => collectVars(vsSoFar ++ nextVs, nextf)
      case (_: Forall, Forall(nextVs, nextf)) => collectVars(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar, candidate)
    }
    val (vars, formula) = collectVars(f.vars.toArray, f.child)
    require(vars.forall(v => v.sort==Real), "Can only deal with functions with parameters of type real")
    "(" + op + " (" + vars.map(v => "(" + nameIdentifier(v) + " " + v.sort + ")").mkString(" ") + ") " +
      convertFormula(formula) + ")"
  }
}
