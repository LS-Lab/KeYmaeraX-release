/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
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
  def apply(expr: Expression): String = generateAssertNegation(expr, "Z3")
  def apply(expr: Expression, toolId: String) = generateAssertNegation(expr, toolId)

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
  private def generateAssertNegation(expr: Expression, toolId: String): String = {
    val (varDec, smtFormula) = generateSMT(expr, toolId)
    varDec + "\n" + "(assert (not " + smtFormula + "))"
  }

  /** Convert KeYmaera X expression to SMT expression for checking if this expression can be simplified */
  def generateSimplify(expr: Expression, toolId: String): String = {
    val (varDec, smtFormula) = generateSMT(expr, toolId)
    varDec + "\n" + "(simplify " + smtFormula + ")"
  }

  /** Convert KeYmaera X expression to SMT form which contains: variable/function declaration and converted SMT formula */
  private def generateSMT(expr: Expression, toolId: String): (String, String) = {
    val allSymbols = StaticSemantics.symbols(expr)
    val names = allSymbols.toList.map(s => nameIdentifier(s))
    require(names.distinct.size == names.size, "Expect unique name_index identifiers")
    require(!(names.contains(SMT_MIN)||names.contains(SMT_MAX)||names.contains(SMT_ABS)), "Variable and function names are not expected to be " + SMT_MIN + ", " +  SMT_MAX + "or " + SMT_ABS)
    val varDec = allSymbols.map(
      s => s match {
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
    val smtFormula = convertToSMT(expr, toolId)
    (varDec, smtFormula)
  }

  /** Generate parameters of function in the varDec of SMT */
  private def generateFuncPrmtSorts(t: Sort) : String = t match {
    case Unit => ""
    case Tuple(l, r) => generateFuncPrmtSorts(l) + " " + generateFuncPrmtSorts(r)
    case _ => t.toString
  }

  /** Identifier corresponding to a NamedSymbol */
  private def nameIdentifier(s: NamedSymbol): String = {
    require(s.isInstanceOf[Function] || s.isInstanceOf[Variable])
    require(s.sort == Real, "only real-valued symbols are currently supported")
    if (s.index.isEmpty) s.name else s.name + "_" + s.index.get
  }

  private def convertToSMT(expr: Expression, toolId: String) : String = expr match {
    case t: Term  => convertTerm(t, toolId)
    case f: Formula => convertFormula(f, toolId)
    case _ => throw new SMTConversionException("The input expression: \n" + KeYmaeraXPrettyPrinter(expr) + "\nis expected to be formula.")
  }

  /** Convert KeYmaera X formula to string in SMT notation */
  private def convertFormula(f: Formula, toolId: String) : String = {
    f match {
      case Not(ff)        => "(not " + convertFormula(ff, toolId) + ")"
      case And(l, r)      => "(and " + convertFormula(l, toolId) + " " + convertFormula(r, toolId) + ")"
      case Or(l, r)       => "(or " + convertFormula(l, toolId) + " " + convertFormula(r, toolId) + ")"
      case Imply(l, r)    => "(=> " + convertFormula(l, toolId) + " " + convertFormula(r, toolId) + ")"
      case Equiv(l, r)    => "(equiv " + convertFormula(l, toolId) + " " + convertFormula(r, toolId) + ")"
      case Equal(l, r)    => "(= " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case NotEqual(l, r) => convertFormula(Not(Equal(l, r)), toolId)
      case Greater(l,r)   => "(> " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case GreaterEqual(l,r) => "(>= " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case Less(l,r)      => "(< " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case LessEqual(l,r) => "(<= " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case True => "true"
      case False => "false"
      case Forall(vs, ff) => convertForall(vs, ff, toolId)
      case Exists(vs, ff) => convertExists(vs, ff, toolId)
    }
  }

  /** Convert KeYmaera X term to string in SMT notation */
  private def convertTerm(t: Term, toolId: String) : String = {
    require(t.sort == Real || t.sort == Unit || t.sort.isInstanceOf[Tuple], "SMT can only deal with real, but not with sort " + t.sort)
    t match {
      case Neg(c)       => "(- " + convertTerm(c, toolId) + ")"
      case Plus(l, r)   => "(+ " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case Minus(l, r)  => "(- " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case Times(l, r)  => "(* " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case Divide(l, r) => "(/ " + convertTerm(l, toolId) + " " + convertTerm(r, toolId) + ")"
      case Power(l, r)  => convertExp(l, r, toolId)
      case Number(n) =>
        assert(n.isValidDouble || n.isValidLong, throw new SMTConversionException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal numbers"))
        if (n.toDouble < 0)  "(- " + (0-n).underlying().toString + ")"
        else n.underlying().toString
      case t: Variable => nameIdentifier(t)
      case FuncOf(fn, Nothing) => nameIdentifier(fn)
      case FuncOf(fn, child) => nameIdentifier(fn) match {
        case "min" => "(" + SMT_MIN + " " + convertTerm(child, toolId) + ")"
        case "max" => "(" + SMT_MAX + " " + convertTerm(child, toolId) + ")"
        case "abs" => "(" + SMT_ABS + " " + convertTerm(child, toolId) + ")"
        case _ => "(" + nameIdentifier(fn) + " " + convertTerm(child, toolId) + ")"
      }
      case Pair(l, r)  => convertTerm(l, toolId) + " " + convertTerm(r, toolId)
      case _ => throw new SMTConversionException("Conversion of term " + KeYmaeraXPrettyPrinter(t) + " is not defined")
    }
  }

  //@todo get rid of this function and have a tactic depower that gets rid of all powers by proof steps
  /** Convert power to SMT notation */
  private def convertExp(l: Term, r: Term, toolId: String) : String = {
    val base = simplifyTerm(l, toolId)
    val exp = simplifyTerm(r, toolId)
    if(base.equals(Number(0))) {
      println("[warning] converting 0^0 to SMT")
      if(exp.equals(Number(0))) "1" // 0^0 =1
      else "0" // 0^x = 0
    } else {
      exp match {
        case Number(n) =>
          if(n.isValidInt) {
            // index is integer
            if(n.intValue() == 0) {
              "1"
            } else if(n.intValue() > 0 ) {
              val ba : String = convertTerm(base, toolId)
              var res : String = "(*"
              for (i <- 0 to n.intValue()-1) {
                res += " " + ba
              }
              res += ")"
              res
            } else "(/ 1 " + convertExp(base, Number(n.underlying().negate()), toolId) + ")"
          } else throw new SMTConversionException("Cannot convert exponential " + KeYmaeraXPrettyPrinter(Power(l,r)) + " with non-integer index")
        case Neg(Number(n)) => "(/ 1 " + convertExp(base, Number(n), toolId) + ")"
        case _ => throw new SMTConversionException("Conversion of exponential " + KeYmaeraXPrettyPrinter(Power(l,r)) + " is not defined")
      }
    }
  }

  /** Convert possibly nested forall KeYmaera X expression to SMT */
  private def convertForall(vs: Seq[NamedSymbol], f: Formula, toolId: String) : String = {
    val (vars, formula) = collectVarsForall(vs, f)
    "(forall " + "(" + vars.map(v => "(" + nameIdentifier(v) + " Real)").mkString(" ") + ") " + convertFormula(formula, toolId) + ")"
  }

  /** Collect all quantified variables used in possibly nested forall expression */
  private def collectVarsForall(vsSoFar : Seq[NamedSymbol], candidate : Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextF) =>  collectVarsForall(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }

  /** Convert possibly nested exists KeYmaera X expression to SMT */
  private def convertExists(vs: Seq[NamedSymbol], f: Formula, toolId: String) : String = {
    val (vars, formula) = collectVarsExists(vs, f)
    "(exists " + "(" + vars.map(v => "(" + nameIdentifier(v) + " Real)").mkString(" ") + ") " + convertFormula(formula, toolId) + ")"
  }

  /** Collect all quantified variables used in possibly nested exists expression */
  private def collectVarsExists(vsSoFar: Seq[NamedSymbol], candidate: Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextF) =>  collectVarsExists(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }

  /** Call Z3 or Polya to simplify a KeYmaera X term */
  private def simplifyTerm(t: Term, toolId: String) : Term = {
    //@todo This code is poor man's reflection. If retained then pass Tool, not tool name.
    if (toolId == "Z3") {
      val z3 = new Z3Solver
      z3.simplify(t)
    } else if (toolId == "Polya") {
      val polya = new PolyaSolver
      polya.simplify(t)
    } else throw new SMTConversionException("Cannot simplify term with: " + toolId)
  }
}
