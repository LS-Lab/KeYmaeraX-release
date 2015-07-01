package edu.cmu.cs.ls.keymaerax.codegeneration
import java.io.{FileWriter, File}

import edu.cmu.cs.ls.keymaerax.api.ComponentConfig
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser


/**
 * Created by ran on 6/16/15.
 * @author Ran Ji
 */
class CCodeGenerator extends (Expression => String) {

  def apply(kExpr: Expression, cDataType: String): String = generateCCode(kExpr, cDataType)
  def apply(kExpr: Expression): String = apply(kExpr, "long double")

//  def generateCCodeFromKeyFile(path: String) : String = {
//    val content = io.Source.fromInputStream(getClass.getResourceAsStream(path)).mkString
//    new KeYmaeraParser(false, ComponentConfig).runParser(content) match {
//      case f: Formula => generateCCode(f)
//      case a => throw new IllegalArgumentException("Parsing the input did not result in a formula but in: " + a)
//    }
//  }

  def generateCFileFromCCode(cCode: String, fileName: String) : File = {
    val cTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    val cFile = new File(cTempDir, fileName)
    val writer = new FileWriter(cFile)
    writer.write(cCode)
    writer.flush()
    writer.close()
    cFile
  }

  private def generateCCode(kExpr: Expression, cDataType: String) : String = {
    val include = "#include \"math.h\"" + "\n"
    val parameters = parameterDec(kExpr, cDataType)
    val function = "int monitor (" + parameters + ")"
    val body = compileToC(kExpr)
    val program = include + function + " {\n" + "  return " + body + ";" + "\n}"
    program
  }

  def parameterDec(kExpr: Expression, cDataType: String) : String = {
    var parameter = ""
    val allSortedNames = StaticSemantics.symbols(kExpr).toList.sorted
    if (allSortedNames.size > 0) {
      val lastName = allSortedNames.last
      for (i <- allSortedNames) {
        i.getClass.getSimpleName match {
          case "Variable" =>
            parameter += cDataType + " " + i.name
            if(i.index.isDefined) parameter += "_" + i.index.get
            if(i != lastName) parameter += ", "
          case "Function" =>
            if (!i.name.equals("Abs")) {
              parameter += cDataType + " " + i.name
              if(i != lastName) parameter += ", "
            }
        }
      }
    }
    parameter
  }

  def compileToC(e: Expression) = e match {
    case t : Term => compileTerm(t)
    case t : Formula => compileFormula(t)
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
  //      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString() + " is not defined")
  //    }
  //  }

  def compileTerm(t: Term) : String = {
    require(t.sort == Real || t.sort == Unit, "can only deal with reals not with sort " + t.sort)
    t match {
      case Neg(c) => "(" + "-" + compileTerm(c) + ")"
      case Plus(l, r) => "(" + compileTerm(l) + "+" + compileTerm(r) + ")"
      case Minus(l, r) => "(" + compileTerm(l) + "-" + compileTerm(r) + ")"
      case Times(l, r) => "(" + compileTerm(l) + "*" + compileTerm(r) + ")"
      case Divide(l, r) => "(" + compileTerm(l) + "/" + compileTerm(r) + ")"
      case Power(l, r) => "(" + compilePower(l, r) + ")"
      // atomic terms
      case Number(n) => n.underlying().toString
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
      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString() + " is not defined")
    }
  }

  /**
   * compile exponentials
   * @param base
   * @param exp
   * @return
   */
  def compilePower(base: Term, exp: Term) : String = {
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
  //      case Box(bp, bc) | Diamond(dp, dc)  => throw new CodeGenerationException("Conversion of formula " + f.prettyString() + " is not defined")
  //    }
  //  }

  def compileFormula(f: Formula) : String = {
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
      case _ => throw new CodeGenerationException("Conversion of formula " + f.prettyString() + " is not defined")
    }
  }
}

class CodeGenerationException(s: String) extends Exception(s)