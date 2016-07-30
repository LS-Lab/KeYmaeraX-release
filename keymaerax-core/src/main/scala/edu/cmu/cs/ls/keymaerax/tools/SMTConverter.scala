/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

import scala.collection.immutable.Seq

/**
 * Created by ran on 8/24/15.
 * @author Ran Ji
 */
object SMTConverter {
  def apply(expr: Formula): String = generateAssertNegation(expr)

  private val SMT_ABS = "absolute"
  private val SMT_MIN = "minimum"
  private val SMT_MAX = "maximum"
  /**
    * Convert KeYmaera X expression to SMT expression with negated formula form
    * the result SMT expression is checked by Z3 or Polya for satisfiability
    * if SMT solver returns:
    *   unsatisfied => original KeYmaera X formula is valid
    *   satisfiable => original KeYmaera X formula is not valid
    */
  private def generateAssertNegation(expr: Formula): String = {
    val (varDec, smtFormula) = generateSMT(expr)
    varDec + "(assert (not " + smtFormula + "))"
  }

  /** Convert KeYmaera X expression to SMT expression for checking if this expression can be simplified */
  def generateSimplify(expr: Term): String = {
    val (varDec, smtFormula) = generateSMT(expr)
    varDec + "(simplify " + smtFormula + ")"
  }

  /** Convert KeYmaera X expression to SMT form which contains: variable/function declaration and converted SMT formula */
  private def generateSMT(expr: Expression): (String, String) = {
    val allSymbols = StaticSemantics.symbols(expr).toList.sorted
    val names = allSymbols.map(s => nameIdentifier(s))
    require(names.distinct.size == names.size, "Expect unique name_index identifiers")
    require(!(names.contains(SMT_MIN)||names.contains(SMT_MAX)||names.contains(SMT_ABS)), "Variable and function names are not expected to be " + SMT_MIN + ", " +  SMT_MAX + "or " + SMT_ABS)
    var varDec = allSymbols.map({
        case x: Variable =>
          require(x.sort==Real, "Can only deal with variable of type real, but not " + x.sort)
          "(declare-fun " + nameIdentifier(x) + " () " + x.sort + ")"
        //@todo use Derived Axioms for abs/min/max
        case f: Function =>
          require(f.sort==Real, "Can only deal with function of type real, but not " + f.sort)
          nameIdentifier(f) match {
            case "min" => "(define-fun " + SMT_MIN + " ((x1 Real) (x2 Real)) Real\n  (ite (<= x1 x2) x1 x2))"
            case "max" => "(define-fun " + SMT_MAX + " ((x1 Real) (x2 Real)) Real\n  (ite (>= x1 x2) x1 x2))"
            case "abs" => "(define-fun " + SMT_ABS + " ((x Real)) Real\n  (ite (>= x 0) x (- x)))"
            case _ => "(declare-fun " + nameIdentifier(f) + " (" + generateFuncPrmtSorts(f.domain) +  ") " + f.sort + ")"
          }
      }
    ).mkString("\n")
    val smtFormula = convertToSMT(expr)
    if(varDec.nonEmpty) varDec += "\n"
    (varDec, smtFormula)
  }

  /** Generate parameters of function in the varDec of SMT */
  private def generateFuncPrmtSorts(t: Sort) : String = t match {
    case Unit => ""
    //@note: disassociate the arguments
    case Tuple(l, r) => generateFuncPrmtSorts(l) + " " + generateFuncPrmtSorts(r)
    case _ => t.toString
  }

  /** Identifier corresponding to a NamedSymbol */
  private def nameIdentifier(s: NamedSymbol): String = {
    require(s.isInstanceOf[Function] || s.isInstanceOf[Variable])
    require(s.sort == Real, "only real-valued symbols are currently supported")
    if (s.index.isEmpty) s.name else s.name + "_" + s.index.get
  }

  private def convertToSMT(expr: Expression) : String = expr match {
    case t: Term  => convertTerm(t)
    case f: Formula => convertFormula(f)
    case _ => throw new SMTConversionException("The input expression: \n" + KeYmaeraXPrettyPrinter(expr) + "\nis expected to be formula.")
  }

  /** Convert KeYmaera X formula to string in SMT notation */
  private def convertFormula(f: Formula) : String = {
    f match {
      case Not(ff)        => "(not " + convertFormula(ff) + ")"
      case And(l, r)      => "(and " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Or(l, r)       => "(or " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Imply(l, r)    => "(=> " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Equiv(l, r)    => "(equiv " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Equal(l, r)    => "(= " + convertTerm(l) + " " + convertTerm(r) + ")"
      case NotEqual(l, r) => convertFormula(Not(Equal(l, r)))
      case Greater(l,r)   => "(> " + convertTerm(l) + " " + convertTerm(r) + ")"
      case GreaterEqual(l,r) => "(>= " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Less(l,r)      => "(< " + convertTerm(l) + " " + convertTerm(r) + ")"
      case LessEqual(l,r) => "(<= " + convertTerm(l) + " " + convertTerm(r) + ")"
      case True => "true"
      case False => "false"
      case Forall(vs, ff) => convertForall(vs, ff)
      case Exists(vs, ff) => convertExists(vs, ff)
    }
  }

  /** Convert KeYmaera X term to string in SMT notation */
  private def convertTerm(t: Term) : String = {
    require(t.sort == Real || t.sort.isInstanceOf[Tuple], "SMT can only deal with real, but not with sort " + t.sort)
    t match {
      case Neg(c)       => "(- " + convertTerm(c) + ")"
      case Plus(l, r)   => "(+ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Minus(l, r)  => "(- " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Times(l, r)  => "(* " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Divide(l, r) => "(/ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Power(l, r)  => "(^ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Number(n) =>
        //@todo code review: check decimaldouble/long/double. Also binary versus base 10 representations don't have to match
        //@ran todo-resolved: double checked and see notes below
        /**@note decimalDouble is 64 bit IEEE 754 double-precision float,
          *      long is 64 bit signed value. -9223372036854775808 to 9223372036854775807
          *      both have the maximal range in their category */
        //@todo This is incorrect, because 64bit longs are not representable in 64bit doubles.
        assert(n.isDecimalDouble || n.isValidLong, throw new SMTConversionException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal numbers"))
        //@todo code review: maxlong?
        //@ran todo-resolved: also checks if negative value is in range, see comment below
        //@todo this is incorrect, because 2th-complement integer arithmetic is nonsymmetric.
        //@todo-resolved: avoids conversion to double, uses 'signum' to determine sign and builtin negate function
        // smt form of -5 is (- 5)
        if (n.signum < 0) {
          assert((-n).isDecimalDouble || (-n).isValidLong, throw new SMTConversionException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal numbers"))
          "(- " + (-n).toString() + ")"
        } else n.toString()
      case t: Variable => nameIdentifier(t)
      case FuncOf(fn, Nothing) => nameIdentifier(fn)
      case FuncOf(fn, child) => nameIdentifier(fn) match {
        case "min" => "(" + SMT_MIN + " " + convertTerm(child) + ")"
        case "max" => "(" + SMT_MAX + " " + convertTerm(child) + ")"
        case "abs" => "(" + SMT_ABS + " " + convertTerm(child) + ")"
        case _ => "(" + nameIdentifier(fn) + " " + convertTerm(child) + ")"
      }
      //@note: disassociate the arguments
      case Pair(l, r)  => convertTerm(l) + " " + convertTerm(r)
      case _ => throw new SMTConversionException("Conversion of term " + KeYmaeraXPrettyPrinter(t) + " is not defined")
    }
  }

  /** Convert possibly nested forall KeYmaera X expression to SMT */
  private def convertForall(vs: Seq[NamedSymbol], f: Formula) : String = {
    val (vars, formula) = collectVarsForall(vs, f)
    //@todo code review: assert sort==real and use sort
    //@ran todo-resolved: changed as suggested
    require(vars.forall(v => v.sort==Real), "Can only deal with functions with parameters of type real")
    "(forall " + "(" + vars.map(v => "(" + nameIdentifier(v) + " " + v.sort + ")").mkString(" ") + ") " + convertFormula(formula) + ")"
  }

  /** Collect all quantified variables used in possibly nested forall expression */
  private def collectVarsForall(vsSoFar : Seq[NamedSymbol], candidate : Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextF) =>  collectVarsForall(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }

  /** Convert possibly nested exists KeYmaera X expression to SMT */
  private def convertExists(vs: Seq[NamedSymbol], f: Formula) : String = {
    val (vars, formula) = collectVarsExists(vs, f)
    require(vars.forall(v => v.sort==Real), "Can only deal with functions with parameters of type real")
    "(exists " + "(" + vars.map(v => "(" + nameIdentifier(v) + " " + v.sort + ")").mkString(" ") + ") " + convertFormula(formula) + ")"
  }

  /** Collect all quantified variables used in possibly nested exists expression */
  private def collectVarsExists(vsSoFar: Seq[NamedSymbol], candidate: Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextF) =>  collectVarsExists(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }
}
