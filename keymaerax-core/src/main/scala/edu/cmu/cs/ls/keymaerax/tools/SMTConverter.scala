/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

import scala.collection.immutable._

/** A default SMT converter with output as preferred by KeYmaera X. */
object DefaultSMTConverter extends SMTConverter {}

/**
  * Base class for SMT converters with conversion per SMTLib specification.
  * Created by ran on 8/24/15.
  * @author Ran Ji
  * @author Stefan Mitsch
  */
abstract class SMTConverter extends (Formula=>String) {
  protected val DEBUG: Boolean = System.getProperty("DEBUG", "false")=="true"

  /** Convert given formula to an SMTLib specification that, if SMT(\result) returns `unsat` says that `expr` is valid. */
  def apply(expr: Formula): String = {
    val negation = generateAssertNegation(expr)
    val result = negation
    if(DEBUG) println(s"SMT output for ${expr.prettyString} (NEGATED AS: ${result}) is: \n${result}")
    result
  }

  // a prefix that SMT accepts but NamedSymbol would refuse to make disjoint by construction
  private val PREFIX = "_"

  private val SMT_ABS = "absolute"
  private val SMT_MIN = "minimum"
  private val SMT_MAX = "maximum"
  /**
    * Convert KeYmaera X expression to SMT expression with negated formula form
    * the result SMT expression is checked by Z3 or Polya for satisfiability
    * if SMT solver returns:
    *   unsatisfiable => original KeYmaera X formula `expr` is valid
    *   satisfiable => original KeYmaera X formula `expr` is not valid, but is not necessarily equivalent to False.
    */
  private def generateAssertNegation(expr: Formula): String = {
    val (varDec, smtFormula) = generateSMT(expr)
    varDec + "(assert (not " + smtFormula + "))" + "\n(check-sat)\n"
  }

  /** Convert KeYmaera X expression to SMT expression for checking if this expression can be simplified */
  //@todo Code Review: this is unused and may not be useful anyhow
  def generateSimplify(expr: Term): String = {
    val (varDec, smtFormula) = generateSMT(expr)
    varDec + "(simplify " + smtFormula + ")"
  }

  /** Convert KeYmaera X expression to SMT form which contains: variable/function declaration and converted SMT formula */
  private def generateSMT(expr: Expression): (String, String) = {
    val allSymbols = StaticSemantics.symbols(expr).toList.sorted
    val names = allSymbols.map(s => nameIdentifier(s))
    require(names.distinct.size == names.size, "Expect unique name_index identifiers")
    var varDec = allSymbols.map({
        case x: Variable =>
          //@note this check is redundant with the check from nameIdentifier
          require(x.sort==Real, "Can only deal with variable of type real, but not " + x.sort)
          "(declare-fun " + PREFIX + nameIdentifier(x) + " () " + x.sort + ")" //@note identical to (declare-const name sort)
        case f: Function =>
          require(f.sort==Real, "Can only deal with function of type real, but not " + f.sort)
          //@todo Could translate "axiomatic" definitions of abs/min/max to SMT-definitions dynamically instead.
          nameIdentifier(f) match {
            case "min" => "(define-fun " + SMT_MIN + " ((x1 Real) (x2 Real)) Real\n  (ite (<= x1 x2) x1 x2))"
            case "max" => "(define-fun " + SMT_MAX + " ((x1 Real) (x2 Real)) Real\n  (ite (>= x1 x2) x1 x2))"
            case "abs" => "(define-fun " + SMT_ABS + " ((x Real)) Real\n  (ite (>= x 0) x (- x)))"
            case _ => "(declare-fun " + PREFIX + nameIdentifier(f) + " (" + generateFuncPrmtSorts(f.domain) +  ") " + f.sort + ")"
          }
      }
    ).mkString("\n")
    val smtFormula = convertToSMT(expr)
    //@todo check whether newlines are nonsignificant so can be added unconditionally
    if(varDec.nonEmpty) varDec += "\n"
    (varDec, smtFormula)
  }

  /** Identifier corresponding to a NamedSymbol including its index.
    * @note the result is the same as `s.asString` whose implementation is allowed to change for user purposes, though.
    */
  private def nameIdentifier(s: NamedSymbol): String = {
    require(s.isInstanceOf[Function] || s.isInstanceOf[Variable])
    require(s.sort == Real, "only real-valued symbols are currently supported")
    if (s.index.isEmpty) s.name else s.name + "_" + s.index.get
  }


  /** Convert sort to SMT parameter declaration syntax. */
  private def generateFuncPrmtSorts(t: Sort) : String = t match {
    case Unit => ""
    //@note: disassociate the arguments
    case Tuple(l, r) => generateFuncPrmtSorts(l) + " " + generateFuncPrmtSorts(r)
    case _ => t.toString
  }

  private def convertToSMT(expr: Expression) : String = expr match {
    case t: Term  => convertTerm(t)
    case f: Formula => convertFormula(f)
    case _ => throw new SMTConversionException("The input expression: \n" + expr + "\nis expected to be formula.")
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
    case Forall(vs, ff) => convertForall(vs, ff)
    case Exists(vs, ff) => convertExists(vs, ff)
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
        //@todo Code Review: check number conventions supported by SMTLIB format
        //@note according to the SMTLib specification, numbers without . are mathematical integers, numbers with . are mathematical reals
        /**@note decimalDouble is 64 bit IEEE 754 double-precision float,
          *      long is 64 bit signed value. -9223372036854775808 to 9223372036854775807
          *      both have the maximal range in their category */
        assert(n.isDecimalDouble || n.isValidLong, throw new SMTConversionException("Term contains illegal numbers: " + t))
        //@note SMT form of negative number -5 is (- 5)
        // avoids conversion to double, uses 'signum' to determine sign and builtin negate function
        //@note n.signum < 0 is equivalent to n < BigDecimal(0)
        if (n.signum < 0) {
          //@note negative form has to be representable, in particular n cannot have been MIN_LONG
          assert((-n).isDecimalDouble || (-n).isValidLong, throw new SMTConversionException("Term contains illegal numbers: " + t))
          "(- " + (-n).toString() + ")"
        } else n.toString()
      case t: Variable => PREFIX + nameIdentifier(t)
      case FuncOf(fn, Nothing) => PREFIX + nameIdentifier(fn)
      case FuncOf(fn, child) if fn.interpreted => fn match {
        case Function("min",None,Tuple(Real,Real),Real,true) => "(" + SMT_MIN + " " + convertTerm(child) + ")"
        case Function("max",None,Tuple(Real,Real),Real,true) => "(" + SMT_MAX + " " + convertTerm(child) + ")"
        case Function("abs",None,Real,Real,true) => "(" + SMT_ABS + " " + convertTerm(child) + ")"
        case _ => throw new SMTConversionException("Interpreted function not supported presently by SMT: " + t)
      }
      case FuncOf(fn, child) if !fn.interpreted => "(" + PREFIX + nameIdentifier(fn) + " " + convertTerm(child) + ")"
      //@note: disassociates the arguments and no extra parentheses for pairs
      case Pair(l, r)  => convertTerm(l) + " " + convertTerm(r)
      case _ => throw new SMTConversionException("Conversion of term to SMT is not defined: " + t)
    }
  }

  /** Convert possibly nested forall KeYmaera X expression to SMT */
  private def convertForall(vs: Seq[Variable], f: Formula) : String = {
    val (vars, formula) = collectVarsForall(vs, f)
    //@todo code review: assert sort==real and use sort
    //@ran todo-resolved: changed as suggested
    require(vars.forall(v => v.sort==Real), "Can only deal with functions with parameters of type real")
    "(forall " + "(" + vars.map(v => "(" + PREFIX + nameIdentifier(v) + " " + v.sort + ")").mkString(" ") + ") " + convertFormula(formula) + ")"
  }

  /** Collect all quantified variables used in possibly nested forall expression */
  private def collectVarsForall(vsSoFar : Seq[Variable], candidate : Formula) : (Seq[Variable], Formula) = {
    candidate match {
      case Forall(nextVs, nextF) =>  collectVarsForall(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }

  /** Convert possibly nested exists KeYmaera X expression to SMT */
  private def convertExists(vs: Seq[Variable], f: Formula) : String = {
    val (vars, formula) = collectVarsExists(vs, f)
    require(vars.forall(v => v.sort==Real), "Can only deal with functions with parameters of type real")
    "(exists " + "(" + vars.map(v => "(" + PREFIX + nameIdentifier(v) + " " + v.sort + ")").mkString(" ") + ") " + convertFormula(formula) + ")"
  }

  /** Collect all quantified variables used in possibly nested exists expression */
  private def collectVarsExists(vsSoFar: Seq[Variable], candidate: Formula) : (Seq[Variable], Formula) = {
    candidate match {
      case Exists(nextVs, nextF) =>  collectVarsExists(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }
}
