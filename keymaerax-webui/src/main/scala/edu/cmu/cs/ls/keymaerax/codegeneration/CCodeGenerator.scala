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
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  
  def apply(e: Expression): String = generateCCode(e)

  def generateCCodeFromKeyFile(path: String) : String = {
    val content = io.Source.fromInputStream(getClass.getResourceAsStream(path)).mkString
    new KeYmaeraParser(false, ComponentConfig).runParser(content) match {
      case f: Formula => generateCCode(f)
      case a => throw new IllegalArgumentException("Parsing the input did not result in a formula but in: " + a)
    }
  }

  def generateCFileFromCCode(cCode: String, fileName: String) : File = {
    val cTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    val cFile = new File(cTempDir, fileName)
    val writer = new FileWriter(cFile)
    writer.write(cCode)
    writer.flush()
    writer.close()
    cFile
  }

  def generateCCode(e : KExpr) : String = {
    val include = "#include \"math.h\"" + "\n"
    val parameters = parameterDec(e)
    val function = "int monitor (" + parameters + ")"
    val body = compileToC(e)
    val program = include + function + " {\n" + "  return " + body + ";" + "\n}"
    program
  }

  def parameterDec(e : KExpr) : String = {
    var parameter = ""
    val allNames = StaticSemantics.symbols(e)
    if (allNames.size > 0) {
      val lastName = allNames.last
      for (i <- allNames) {
        parameter += "long double " + i.name
        if(i != lastName) parameter += ", "
      }
    }
    parameter
  }

  def compileToC(e : KExpr) = e match {
    case t : Term => compileTerm(t)
    case t : Formula => compileFormula(t)
    case _ => ???
  }

  def compileTerm(t : Term) : String = {
    require(t.sort == Real || t.sort == Unit, "can only deal with reals not with sort " + t.sort)
    t match {
      case Neg(c) => "(-" + compileTerm(c) +")"
      case Plus(l, r) => "(" + compileTerm(l) + "+" + compileTerm(r) + ")"
      case Minus(l, r) => "(" + compileTerm(l) + "-" + compileTerm(r) + ")"
      case Times(l, r) => "(" + compileTerm(l) + "*" + compileTerm(r) + ")"
      case Divide(l, r) => "(" + compileTerm(l) + "/" + compileTerm(r) + ")"
      case Power(l, r) => "(" + compilePower(l, r) + ")"
      case Number(n) => n.underlying().toString
      case t: Variable => t.name
      case FuncOf(fn, _) => fn.name
      case _ => throw new CodeGenerationException("Conversion of term " + t.prettyString() + " is not defined")
    }
  }

  /**
   * compile exponentials
   * @param base
   * @param index
   * @return
   */
  def compilePower(base: Term, index: Term) : String = {
    if(base.equals(Number(0))) {
      "0"
    } else {
      index match {
        case Number(n) =>
          if(n.isValidInt) {
            if(n.intValue() == 0) {
              "1"
            } else if(n.intValue() > 0 ) {
              val ba : String = compileTerm(base)
              var res : String = ba
              for (i <- 1 to n.intValue()-1) {
                res += "*" + ba
              }
              res
            } else throw new CodeGenerationException("Cannot compile exponential " + Power(base,index).prettyString() + " with negative index")
          } else "pow(" + compileTerm(base) + "," + compileTerm(index) + ")"
        case Neg(Number(n)) => "1/" + compilePower(base, Number(n))
        case _ => "pow(" + compileTerm(base) + "," + compileTerm(index) + ")"
      }
    }
  }

  def compileFormula(f : Formula) : String = {
    f match {
      case Not(ff) => "!(" + compileFormula(ff) + ")"
      case And(l, r) => "(" + compileFormula(l) + "&&" + compileFormula(r) + ")"
      case Or(l, r) => "(" + compileFormula(l) + "||" + compileFormula(r) + ")"
      case Imply(l, r) => "!(" + compileFormula(l) + ") || (" + compileFormula(r) + ")"
      //case Imply(l, r) => "(" + "!" + compileFormula(l) + "||" + compileFormula(r) + ")"
      case Equiv(l, r) => "((" + "!" + compileFormula(l) + "||" + compileFormula(r) + ")" +
        "&&" + "(" +  "!" + compileFormula(r) + "||" + compileFormula(l) +  "))"
      case Equal(l, r) => "(" + compileTerm(l) + "==" + compileTerm(r) + ")"
      case NotEqual(l, r) => "(" + compileTerm(l) + "!=" + compileTerm(r) + ")"
      case Greater(l,r) => "(" + compileTerm(l) + ">" + compileTerm(r) + ")"
      case GreaterEqual(l,r) => "(" + compileTerm(l) + ">=" + compileTerm(r) + ")"
      case Less(l,r) => "(" + compileTerm(l) + "<" + compileTerm(r) + ")"
      case LessEqual(l,r) => "(" + compileTerm(l) + "<=" + compileTerm(r) + ")"
      case True => "1"
      case False => "0"
    }
  }
}

class CodeGenerationException(s:String) extends Exception(s)