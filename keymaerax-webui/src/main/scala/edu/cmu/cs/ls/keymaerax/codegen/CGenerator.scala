/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.codegen
import java.io.{FileWriter, File}

import edu.cmu.cs.ls.keymaerax.api.ComponentConfig
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser


/**
 * Created by ran on 6/16/15.
 * @author Ran Ji
 */
class CGenerator extends CodeGenerator {

  def apply(expr: Expression): String = apply(expr, "long double")
  /** Generate C Code for given expression using the data type cDataType throughout */
  def apply(expr: Expression, cDataType: String): String = generateCCode(expr, cDataType)

  private def generateCCode(expr: Expression, cDataType: String) : String = {
    val includeLib = "#include <math.h>\n" +
      "#include <stdbool.h>\n"
    val funcHead = "bool monitor (" + parameterDec(expr, cDataType) + ")"
    val funcBody = compileToC(expr)
    includeLib + funcHead + " {\n" + "  return " + funcBody + ";" + "\n}"
  }

  private def parameterDec(kExpr: Expression, cDataType: String) : String = {
    var parameters = ""
    val allSortedNames = StaticSemantics.symbols(kExpr).toList.sorted
    if (allSortedNames.size > 0) {
      val lastName = allSortedNames.last
      for (i <- allSortedNames) {
        i.getClass.getSimpleName match {
          case "Variable" =>
            parameters += cDataType + " " + i.name
            if(i.index.isDefined) parameters += "_" + i.index.get
            if(i != lastName) parameters += ", "
          case "Function" =>
            if (!i.name.equals("Abs")) {
              parameters += cDataType + " " + i.name
              if(i != lastName) parameters += ", "
            }
        }
      }
    }
    parameters
  }

  private def compileToC(e: Expression) = e match {
    case t : Term => compileTerm(t)
    case f : Formula => compileFormula(f)
    case _ => ???
  }

  //  def compileTerm(t: Term) : String = {
  //    require(t.sort == Real || t.sort == Unit, "can only deal with reals not with sort " + t.sort)
  //    t match {
  //      case Neg(c) => "(-" + compileTerm(c) + ")"
  //      case Plus(l, r) => "(" + compileTerm(l) + ") + (" + compileTerm(r) + ")"
  //      case Minus(l, r) => "(" + compileTerm(l) + ") - (" + compileTerm(r) + ")"
  //      case Times(l, r) => "(" + compileTerm(l) + ") * (" + compileTerm(r) + ")"
  //      case Divide(l, r) => "(" + compileTerm(l) + ") / (" + compileTerm(r) + ")"
  //      case Power(l, r) => compilePower(l, r)
  //      case Number(n) => n.underlying().toString
  //      case t: Variable =>
  //        if(t.index.isEmpty) t.name
  //        else t.name + "_" + t.index.get
  //      case FuncOf(fn, child) =>
  //        if(child.equals(Nothing)) fn.name
  //        else fn.name + "(" + compileTerm(child) + ")"
  //      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString + " is not defined")
  //    }
  //  }

  private def compileTerm(t: Term) : String = {
    require(t.sort == Real || t.sort == Unit, "can only deal with reals not with sort " + t.sort)
    t match {
      case Neg(c) => "(" + "-" + compileTerm(c) + ")"
      case Plus(l, r) => "(" + compileTerm(l) + "+" + compileTerm(r) + ")"
      case Minus(l, r) => "(" + compileTerm(l) + "-" + compileTerm(r) + ")"
      case Times(l, r) => "(" + compileTerm(l) + "*" + compileTerm(r) + ")"
      case Divide(l, r) => "(" + compileTerm(l) + "/" + compileTerm(r) + ")"
      case Power(l, r) => "(" + compilePower(l, r) + ")"
      // atomic terms
      case Number(n) =>
        assert(n.isValidDouble || n.isValidLong, throw new CodeGenerationException("Term " + t.prettyString + " contains illegal numbers"))
        n.underlying().toString
      case t: Variable =>
        if(t.index.isEmpty) t.name
        else t.name + "_" + t.index.get
      case FuncOf(fn, child) =>
        if(child.equals(Nothing)) fn.name
        else fn.name match {
          case "Abs" => "fabsl(" + compileTerm(child) + ")"
          case _ => fn.name + "(" + compileTerm(child) + ")"
        }
      // otherwise exception
      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString + " is not defined")
    }
  }

  /**
   * compile exponentials
   * @param base
   * @param exp
   * @return
   */
  private def compilePower(base: Term, exp: Term) : String = {
    if(base.equals(Number(0))) {
      "0"
    } else {
      exp match {
        case Number(n) =>
          if(n.isValidInt) {
            if(n.intValue() == 0) {
              assert(!base.equals(Number(0)), throw new CodeGenerationException("Conversion of power(0, 0) is not defined"))
              "1"
            } else if(n.intValue() > 0 ) {
              val ba : String = compileTerm(base)
              var res : String = ba
              for (i <- 1 to n.intValue()-1) {
                res += "*" + ba
              }
              res
            } else "1/" + "(" + compilePower(base, Number(n.underlying().negate())) + ")"
          } else "pow(" + compileTerm(base) + "," + compileTerm(exp) + ")"
        case Neg(Number(n)) => "1/" + "(" + compilePower(base, Number(n)) + ")"
        case _ => "pow(" + compileTerm(base) + "," + compileTerm(exp) + ")"
      }
    }
  }

  //  def compileFormula(f: Formula) : String = {
  //    f match {
  //      case Not(ff) => "!(" + compileFormula(ff) + ")"
  //      case And(l, r) => "(" + compileFormula(l) + ") && (" + compileFormula(r) + ")"
  //      case Or(l, r) => "(" + compileFormula(l) + ") || (" + compileFormula(r) + ")"
  //      case Imply(l, r) => "!(" + compileFormula(l) + ") || (" + compileFormula(r) + ")"
  //      case Equiv(l, r) => "(" + "!(" + compileFormula(l) + ") || (" + compileFormula(r) + ")" +
  //        ") && (" + "!(" + compileFormula(r) + ") || (" + compileFormula(l) +  "))"
  //      case Equal(l, r) => "(" + compileTerm(l) + ") == (" + compileTerm(r) + ")"
  //      case NotEqual(l, r) => "(" + compileTerm(l) + ") != (" + compileTerm(r) + ")"
  //      case Greater(l, r) => "(" + compileTerm(l) + ") > (" + compileTerm(r) + ")"
  //      case GreaterEqual(l, r) => "(" + compileTerm(l) + ") >= (" + compileTerm(r) + ")"
  //      case Less(l, r) => "(" + compileTerm(l) + ") < (" + compileTerm(r) + ")"
  //      case LessEqual(l, r) => "(" + compileTerm(l) + ") <= (" + compileTerm(r) + ")"
  //      case True => "1"
  //      case False => "0"
  //      case Box(bp, bc) | Diamond(dp, dc)  => throw new CodeGenerationException("Conversion of formula " + f.prettyString + " is not defined")
  //    }
  //  }

  private def compileFormula(f: Formula) : String = {
    f match {
      case Not(ff) => "(!" + compileFormula(ff) + ")"
      case And(l, r) => "(" + compileFormula(l) + "&&" + compileFormula(r) + ")"
      case Or(l, r) => "(" + compileFormula(l) + "||" + compileFormula(r) + ")"
      case Imply(l, r) => "(" + "(!" + compileFormula(l) + ")" + "||" + compileFormula(r) + ")"
      case Equiv(l, r) =>
        "(" +
          "(" + "(!" + compileFormula(l) + ")" + "||" + compileFormula(r) + ")" +
          "&&" +
          "(" + "(!" + compileFormula(r) + ")" + "||" + compileFormula(l) + ")" +
          ")"
      case Equal(l, r) => "(" + compileTerm(l) + "==" + compileTerm(r) + ")"
      case NotEqual(l, r) => "(" + compileTerm(l) + "!=" + compileTerm(r) + ")"
      case Greater(l,r) => "(" + compileTerm(l) + ">" + compileTerm(r) + ")"
      case GreaterEqual(l,r) => "(" + compileTerm(l) + ">=" + compileTerm(r) + ")"
      case Less(l,r) => "(" + compileTerm(l) + "<" + compileTerm(r) + ")"
      case LessEqual(l,r) => "(" + compileTerm(l) + "<=" + compileTerm(r) + ")"
      case True => "1"
      case False => "0"
      case Box(_, _) | Diamond(_, _) => throw new CodeGenerationException("Conversion of Box or Diamond modality is not allowed")
      case _ => throw new CodeGenerationException("Conversion of formula " + f.prettyString + " is not defined")
    }
  }
}

