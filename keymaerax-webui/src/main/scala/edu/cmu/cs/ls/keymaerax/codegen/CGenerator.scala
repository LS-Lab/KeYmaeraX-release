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
object CGenerator extends CodeGenerator {

  def apply(expr: Expression): String = apply(expr, "long double")
  /** Generate C Code for given expression using the data type cDataType throughout */
  def apply(expr: Expression, cDataType: String): String = generateCCode(expr, cDataType)

  private def generateCCode(expr: Expression, cDataType: String) : String = {
    val includeLib = "#include <math.h>\n" +
      "#include <stdbool.h>\n"
    val funcHead = "bool monitor (" + parameterDeclaration(expr, cDataType) + ")"
    val funcBody = compileToC(expr)
    includeLib + funcHead + " {\n" + "  return " + funcBody + ";" + "\n}"
  }

  private def parameterDeclaration(kExpr: Expression, cDataType: String) : String =
    StaticSemantics.symbols(kExpr).toList.sorted.map(
      s => s match {
        case x: Variable => cDataType + " " + nameIdentifier(x)
        case f: Function if f.domain==Unit && f.sort==Real => cDataType + " " + nameIdentifier(f)
      }
    ).mkString(", ")

  private def compileToC(e: Expression) = e match {
    case t : Term => compileTerm(t)
    case f : Formula => compileFormula(f)
    case _ => ???
  }


  /** Compile a term to a C expression evaluating it (in the same arithmetic) */
  //@note Using local parentheses to be locally correct.
  private def compileTerm(t: Term) : String = {
    require(t.sort == Real || t.sort == Unit, "can only deal with reals not with sort " + t.sort)
    t match {
      case Neg(c)       => "-" + "(" + compileTerm(c) + ")"
      case Plus(l, r)   => "(" + compileTerm(l) + ")" + " + " + "(" + compileTerm(r) + ")"
      case Minus(l, r)  => "(" + compileTerm(l) + ")" + " - " + "(" + compileTerm(r) + ")"
      case Times(l, r)  => "(" + compileTerm(l) + ")" +  "*"  + "(" + compileTerm(r) + ")"
      case Divide(l, r) => "(" + compileTerm(l) + ")" +  "/"  + "(" + compileTerm(r) + ")"
      case Power(l, r)  => "(" + compilePower(l, r) + ")"
      // atomic terms
      case Number(n) =>
        assert(n.isValidDouble || n.isValidLong, throw new CodeGenerationException("Term " + t.prettyString + " contains illegal-precision numbers"))
        //@note assume the C compiler will detect representation-size errors
        n.underlying().toString
      case t: Variable  => nameIdentifier(t)
      case FuncOf(fn, Nothing) => nameIdentifier(fn)
      case FuncOf(fn, child) => nameIdentifier(fn) + "(" + compileTerm(child) + ")"
      // otherwise exception
      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString + " is not defined")
    }
  }

  /** C Identifier corresponding to a NamedSymbol */
  private def nameIdentifier(s: NamedSymbol): String = {
    require(s.isInstanceOf[Function] || s.isInstanceOf[Variable])
    require(s.sort == Real, "only real-valued symbols are currently supported")
    if (s.index.isEmpty) s.name else s.name + "_" + s.index.get
  }

  /**
   * compile exponentials
   * @param base
   * @param exp
   * @return
   */
  private def compilePower(base: Term, exp: Term) : String = {
    if(base.equals(Number(0))) {
      //@todo since when is that the case?
      if(exp.equals(Number(0))) "1.0" // 0^0 =1
      else "0.0"
    } else {
      exp match {
        case Number(n) =>
          if(n.isValidInt) {
            if(n.intValue() == 0) {
              assert(!base.equals(Number(0)), throw new CodeGenerationException("Conversion of 0^0 is not defined"))
              "1.0"
            } else if(n.intValue() > 0 ) {
              val ba : String = compileTerm(base)
              var res : String = "(" + ba + ")"
              for (i <- 1 to n.intValue()-1) {
                res += "*" + "(" + ba + ")"
              }
              res
            } else "1.0/" + "(" + compilePower(base, Number(n.underlying().negate())) + ")"
          } else "pow(" + "(" + compileTerm(base) + ")" + "," + "(" + compileTerm(exp) + ")" + ")"
        case Neg(Number(n)) => "1.0/" + "(" + compilePower(base, Number(n)) + ")"
        case _ => "pow(" + "(" + compileTerm(base) + ")" + "," + "(" + compileTerm(exp) + ")" + ")"
      }
    }
  }

  /** Compile a formula to a C expression checking it (in the same arithmetic) */
  private def compileFormula(f: Formula) : String = {
    f match {
      case Not(ff)     => "!" + "(" + compileFormula(ff) + ")"
      case And(l, r)   => "(" + compileFormula(l) + ")" + "&&" + "(" + compileFormula(r) + ")"
      case Or(l, r)    => "(" + compileFormula(l) + ")" + "||" + "(" + compileFormula(r) + ")"
      case Imply(l, r) => compileFormula(Or(Not(l), r))
      case Equiv(l, r) => compileFormula(And(Imply(l, r), Imply(r, l)))
        //compileFormula(Or(And(l,r),And(Not(l),Not(r))))
      case Equal(l, r)       => "(" + compileTerm(l) + ")" + "==" + "(" + compileTerm(r) + ")"
      case NotEqual(l, r)    => "(" + compileTerm(l) + ")" + "!=" + "(" + compileTerm(r) + ")"
      case Greater(l,r)      => "(" + compileTerm(l) + ")" + ">"  + "(" + compileTerm(r) + ")"
      case GreaterEqual(l,r) => "(" + compileTerm(l) + ")" + ">=" + "(" + compileTerm(r) + ")"
      case Less(l,r)         => "(" + compileTerm(l) + ")" + "<"  + "(" + compileTerm(r) + ")"
      case LessEqual(l,r)    => "(" + compileTerm(l) + ")" + "<=" + "(" + compileTerm(r) + ")"
      case True              => "true"
      case False             => "false"
      case Box(_, _) | Diamond(_, _) => throw new CodeGenerationException("Conversion of Box or Diamond modality is not allowed")
      case _ => throw new CodeGenerationException("Conversion of formula " + f.prettyString + " is not defined")
    }
  }
}

