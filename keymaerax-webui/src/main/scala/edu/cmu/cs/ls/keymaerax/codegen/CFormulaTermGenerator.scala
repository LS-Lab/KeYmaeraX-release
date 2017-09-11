/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.codegen.CFormulaTermGenerator._

/**
  * Conversion of names.
  * @author Stefan Mitsch
  * @author Ran Ji
  */
object CFormulaTermGenerator {
  /** C Identifier corresponding to a NamedSymbol */
  def nameIdentifier(s: NamedSymbol): String = {
    require(s.sort == Real, "Expected named symbol of sort Real, but got " + s.sort)
    s match {
      case _: Function | _: Variable => if (s.index.isEmpty) s.name else s.name + "_" + s.index.get
      case _ => throw new CodeGenerationException("Unsupported named symbol " + s.prettyString)
    }
  }

  /** Indicates whether the name `f` is an interpreted function symbol. */
  def isInterpreted(f: NamedSymbol) : Boolean = f match {
    case Function(_, _, _, _, interpreted) => interpreted
    case _ => false
  }

  /** Prints a struct declaration named `structName` with a field for each of the names in `vars`. */
  def printStructDeclaration[T <: NamedSymbol](structName: String, vars: Set[T]): String = {
    // stable ordering by NamedSymbol.compare
    val fields = vars.toList.sorted[NamedSymbol].map({
      case x: Variable => printSort(x.sort) + " " + nameIdentifier(x) + ";"
      case f: Function =>
        assert(!isInterpreted(f), "Parameter must not be an interpreted function")
        assert(f.domain == Unit, "If declared as function, parameter must have domain Unit, but has " + f.domain)
        printSort(f.sort) + " " + nameIdentifier(f) + ";"
      case _ => None
    }).mkString("\n  ")
    val structBody = if (vars.isEmpty) "" else "{\n  " + fields + "\n} "
    s"typedef struct $structName $structBody$structName;\n\n"
  }

  /** Print sort `s` as a C type. */
  def printSort(s: Sort): String = s match {
    case Unit => "void"
    case Real => "long double"
    case Bool => "bool"
    case Tuple(l, r) => ??? //printSort(l) + ", " + printSort(r)
    case _ => s.toString
  }
}


/**
  * Generates formula and term evaluation C code. `termContainer` configures the location where primitive terms are
  * looked up (e.g., structs).
  * @author Stefan Mitsch
  * @author Ran Ji
  */
class CFormulaTermGenerator(termContainer: Expression => String) extends CodeGenerator {
  override def apply(expr: Expression, stateVars: Set[BaseVariable], modelName: String): String = expr match {
    case f: Formula if f.isFOL => compileFormula(f)
    case t: Term => compileTerm(t)
  }

  /** Compile a term to a C expression evaluating it (in the same arithmetic) */
  private def compileTerm(t: Term) : String = {
    require(t.sort == Real || t.sort == Unit || t.sort.isInstanceOf[Tuple], "Expected sort Real, but got unsupported sort " + t.sort)
    t match {
      case Neg(c)       => "-" + "(" + compileTerm(c) + ")"
      case Plus(l, r)   => "(" + compileTerm(l) + ")" + " + " + "(" + compileTerm(r) + ")"
      case Minus(l, r)  => "(" + compileTerm(l) + ")" + " - " + "(" + compileTerm(r) + ")"
      case Times(l, r)  => "(" + compileTerm(l) + ")" +  "*"  + "(" + compileTerm(r) + ")"
      case Divide(l, r) => "(" + compileTerm(l) + ")" +  "/"  + "(" + compileTerm(r) + ")"
      case Power(l, r)  => "(" + compilePower(l, r) + ")"
      // atomic terms
      case Number(n) =>
        assert(n.isDecimalDouble || n.isValidLong, throw new CodeGenerationException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal-precision numbers"))
        //@note assume the C compiler will detect representation-size errors
        //if(n.toDouble < 0)  "(" + n.underlying().toString + ")"
        //else n.underlying().toString
        //@note with parentheses in case literal is negative
        "(" + n.underlying().toString + ")"
      case t: Variable => termContainer(t) + nameIdentifier(t)
      //@note _idx are aliases for the same post variable, todo: preprocess with tactic
      case t@FuncOf(Function(fname, _, fdom, fsort, fintr), Nothing) if fname.endsWith("post") =>
        termContainer(t) + nameIdentifier(Function(fname.stripSuffix("post"), None, fdom, fsort, fintr))
      case t@FuncOf(fn, Nothing) => termContainer(t) + nameIdentifier(fn)
      case FuncOf(fn, child) if fn.interpreted =>
        nameIdentifier(fn) match {
          case name@("abs" | "min" | "max") => convertInterpretedFunction(name) + "(" + compileTerm(child) + ")"
          case _ => nameIdentifier(fn) + "(" + compileTerm(child) + ")"
        }
      case FuncOf(fn, _) if !fn.interpreted => throw new CodeGenerationException("Uninterpreted function symbols with arguments not supported")
      case Pair(l, r)  => compileTerm(l) + ", " + compileTerm(r)
      case _ => throw new CodeGenerationException("Conversion of term " + KeYmaeraXPrettyPrinter(t) + " is not defined")
    }
  }

  /**
    * Compile exponentials
    * @param base  base of the exponential
    * @param exp   index of the exponential
    * @return      simplified generation of exponential
    */
  private def compilePower(base: Term, exp: Term) : String = {
    if(base.equals(Number(0))) {
      //@todo since when is that the case?
      println("[warning] generating 0^0")
      if(exp.equals(Number(0))) "1.0" // 0^0 =1
      else "0.0"  // 0^x = 0
    } else {
      exp match {
        case Number(n) =>
          if(n.isValidInt) {
            // index is integer
            if(n.intValue() == 0) {
              // index is 0, x^0 = 1
              //            assert(!base.equals(Number(0)), throw new CodeGenerationException("Conversion of 0^0 is not defined"))
              "1.0"
            } else if (n.intValue() > 0 ) {
              // index n is a positive integer, expand n times of *
              val ba : String = compileTerm(base)
              (0 until n.intValue()).map(_ => s"($ba)").mkString("*")
            } else "1.0/" + "(" + compilePower(base, Number(n.underlying().negate())) + ")" // index is negative integer
          } else "pow(" + "(" + compileTerm(base) + ")" + "," + "(" + compileTerm(exp) + ")" + ")" // index is not integer, use pow function in C
        case Neg(Number(n)) => "1.0/" + "(" + compilePower(base, Number(n)) + ")"  // index is negative
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
      //@todo the following two transformations of formulas should be done by a tactic and just asserted here that these cases no longer happen.
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
      case _ => throw new CodeGenerationException("Conversion of formula " + KeYmaeraXPrettyPrinter(f) + " is not defined")
    }
  }

  /** Convert interpreted functions to corresponding C functions.
    *
    * C 99 standard:
    *   double fabs()
    *   float fabsf()
    *   long double fabsl()
    */
  private def convertInterpretedFunction(fn: String) : String = {
    fn match {
      case "abs" | "min" | "max" => "f" + fn + "l" // long double
      case _ => throw new CodeGenerationException("Unsupported interpreted function " + fn)
    }
  }
}
