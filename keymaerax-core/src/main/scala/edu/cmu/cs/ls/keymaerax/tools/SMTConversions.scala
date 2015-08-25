/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

import scala.collection.immutable.Seq

/**
 * Represents an accumulator for SMTLib file input, which is ultimately a triple of strings.
 * @author Ran Ji
 */
class SMTLib {
  /** Comments and description of problem */
  private var description : String = ""
  /** Variable declaration list */
  private var variableList : String  = ""
  /** The formula to check for validity */
  private var formula : String = ""

  /**
   * Retrieves the description
   * @return Description
   */
  def getDescription = this.description

  /**
   * Sets the description
   * @param desc New description
   */
  def setDescription(desc : String) = {
    this.description = desc
  }

  /**
   * Retrieves the variablelist as string
   *
   * @return Variablelist
   */
  def getVariableList = this.variableList

  /**
   * Sets the list of Variables. Format like "(x,y)"
   *
   * @param varList New list of variables
   */
  def setVariableList(varList : String) = {
    this.variableList = varList
  }

  /**
   * Gets the formula
   *
   * @return Formula
   */
  def getFormula = this.formula

  /**
   * Sets the formula
   *
   * @param formula New formula
   */
  def setFormula(formula : String) = {
    this.formula = formula
  }

  /**
   * Get the SMT input as a string, which conjectures validity of getFormula
   * in terms of unsatisfiability of its negation.
   *
   * @return result the result string SMT input
   * @todo only used in tests?
   */
  def getAssertNot : String = this.getDescription + this.getVariableList + "(assert (not " + this.getFormula + "))"
}

object SMTLib {
  def apply(desc : String, varList : String, formula : String) = {
    val smt = new SMTLib
    smt.setDescription(desc)
    smt.setVariableList(varList)
    smt.setFormula(formula)
    smt
  }
}

class SMTConversionException(s:String) extends Exception(s)

/**
 * Convert KeYmaera expression to the SMT solver named toolId
 */
class KeYmaeraToSMT(toolId : String) {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  type SExpr = SMTLib
  private val smtLib : SExpr = new SExpr // Result
  private var existingVars : Seq[String] = Nil // List of existing variables

  //@todo disjoint names check as in Mathematica
  //@todo contract: convert back is identity
  def convertToSMT(e : KExpr) : SExpr = {
    val formula = convertToString(e)
    smtLib.setFormula(formula)
    smtLib
  }

  private def convertToString(e : KExpr) = e match {
    case t : Term => convertTerm(t)
    case t : Formula => convertFormula(t)
    case _ => ???
  }

  /** Convert term to string in SMT/lisp prefix notation */
  private def convertTerm(t : Term) : String = {
    require(t.sort == Real || t.sort == Unit, "SMT can only deal with reals not with sort " + t.sort)
    t match {
      case Neg(c)       => "(- " + convertTerm(c) + ")"
      case Plus(l, r)   => "(+ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Minus(l, r)  => "(- " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Times(l, r)  => "(* " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Divide(l, r) => "(/ " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Power(l, r)  => convertExp(l, r)
      case Number(n) =>
        assert(n.isValidDouble || n.isValidLong, throw new SMTConversionException("Term " + KeYmaeraXPrettyPrinter(t) + " contains illegal numbers"))
        if (n.toDouble < 0)  "(- " + (0-n).underlying().toString + ")"
        else n.underlying().toString
      case t: Variable => convertVariable(t)
      case FuncOf(fn, _) => convertConstantFunction(fn)
      case _ => throw new SMTConversionException("Conversion of term " + KeYmaeraXPrettyPrinter(t) + " is not defined")
    }
  }

  private def convertVariable(t: Variable): String = {
    val varName = {
      //@todo assert no underscore issues in names
      //@todo this will conflate Variable("x_5",None) and Variable("x",Some(5))
      if(t.index.isEmpty) t.name
      else t.name + "_" + t.index.get
    }
    if(!existingVars.contains(varName)) {
      existingVars = existingVars :+ varName
      val vl : String = smtLib.getVariableList.concat("(declare-fun " + varName + " () Real)\n")
      //@todo turn into one-step compilation from StaticSemantics.symbols
      smtLib.setVariableList(vl)
    }
    varName
  }

  private def convertConstantFunction(fun: Function) : String = {
    if(!existingVars.contains(fun.name)) {
      existingVars = existingVars :+ fun.name
      //@todo turn into one-step compilation from StaticSemantics.symbols / .signature
      val vl : String = smtLib.getVariableList.concat("(declare-fun " + fun.name + " () Real)\n")
      smtLib.setVariableList(vl)
    }
    //@todo index lost so will conflate names
    fun.name
  }

  /**
   * Convert exponentials
   * @param l
   * @param r
   * @return
   * @todo see CGenerator
   * @todo use axiom x^(c()+1) = x*(x^c()) <- c()>=0
   */
  private def convertExp(l : Term, r : Term) : String = {
    val base = simplifyTerm(l)
    val index = simplifyTerm(r)
    if(base.equals(Number(0))) {
      if(index.equals(Number(0))) "1" // 0^0 =1
      else "0"
    } else {
      index match {
        case Number(n) =>
          if(n.isValidInt) {
            if(n.intValue() == 0) {
              "1"
            } else if(n.intValue() > 0 ) {
              val ba : String = convertTerm(base)
              var res : String = "(*"
              for (i <- 0 to n.intValue()-1) {
                res += " " + ba
              }
              res += ")"
              res
            } else "(/ 1 " + convertExp(base, Number(n.underlying().negate())) + ")"
          } else throw new SMTConversionException("Cannot convert exponential " + KeYmaeraXPrettyPrinter(Power(l,r)) + " with non-integer index")
        case Neg(Number(n)) => "(/ 1 " + convertExp(base, Number(n)) + ")"
        case _ => throw new SMTConversionException("Conversion of exponential " + KeYmaeraXPrettyPrinter(Power(l,r)) + " is not defined")
      }
    }
  }

  private def simplifyTerm(t: Term) : Term = {
    //@todo This code is poor man's reflection. If retained then pass Tool, not tool name.
    if (toolId == "Z3") {
      val z3 = new Z3Solver
      z3.simplify(t)
    } else if (toolId == "Polya") {
      val polya = new PolyaSolver
      polya.simplify(t)
    } else throw new SMTConversionException("Cannot simplify term with: " + toolId)
  }

  def convertFormula(f : Formula) : String = {
    f match {
      case Not(ff)        => "(not " + convertFormula(ff) + ")"
      case And(l, r)      => "(and " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Or(l, r)       => "(or " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Imply(l, r)    => "(=> " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Equiv(l, r)    => "(equiv " + convertFormula(l) + " " + convertFormula(r) + ")"
      case Equal(l, r)    => "(= " + convertTerm(l) + " " + convertTerm(r) + ")"
      case NotEqual(l, r) => "(not (= " + convertTerm(l) + " " + convertTerm(r) + "))" //@todo convertFormula(Not(Equal(l,r))) or ask prover?
      case Greater(l,r)   => "(> " + convertTerm(l) + " " + convertTerm(r) + ")"
      case GreaterEqual(l,r) => "(>= " + convertTerm(l) + " " + convertTerm(r) + ")"
      case Less(l,r)      => "(< " + convertTerm(l) + " " + convertTerm(r) + ")"
      case LessEqual(l,r) => "(<= " + convertTerm(l) + " " + convertTerm(r) + ")"
      case True => "true"
      case False => "false"
      case Forall(vs, ff) => convertForall(vs, ff)
      case Exists(vs, ff) => convertExists(vs,ff)
    }
  }

  def convertForall(vs : Seq[NamedSymbol], f : Formula) : String = {
    val (vars, formula) = collectVarsForall(vs, f)
    "(forall " + array2String(vars) + " " + convertFormula(formula) + ")"
  }

  private def collectVarsForall(vsSoFar : Seq[NamedSymbol], candidate : Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextF) =>  collectVarsForall(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }

  def convertExists(vs : Seq[NamedSymbol], f : Formula) : String = {
    val (vars, formula) = collectVarsExists(vs, f)
    "(exists " + array2String(vars) + " " + convertFormula(formula) + ")"
  }

  private def collectVarsExists(vsSoFar : Seq[NamedSymbol], candidate : Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextF) =>  collectVarsExists(vsSoFar ++ nextVs, nextF)
      case _ => (vsSoFar, candidate)
    }
  }

  //@todo map( ++ + " Real").mkString(" ")
  private def array2String(args : Seq[NamedSymbol]) : String = {
    if (args == null)
      return ""
    var result : String = "("
    for (i <- 0 to args.length-1) {
      result += "(" + args(i).name + " Real)"
      if (i != args.length - 1) {
        result += " "
      }
    }
    result + ")"
  }
}



