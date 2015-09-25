/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._
import scala.math.BigDecimal


/**
 * Converts com.wolfram.jlink.Expr -> edu.cmu...keymaerax.core.Expr
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object MathematicaToKeYmaera {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  //@TODO Code Review: turn to false in qe calls
  private val LAX = System.getProperty("LAX", "true")=="true"

  /**
   * Converts a Mathematica expression to a KeYmaera expression.
   */
  //@todo contract: convert back is identity
  def fromMathematica(e : MExpr): KExpr = {
    //Exceptional states
    if (isAborted(e)) throw abortExn(e)
    else if (isFailed(e))  throw failExn(e)

    //Numbers
    else if (e.numberQ() && !e.rationalQ()) {
      try {
        val number = e.asBigDecimal()
        Number(BigDecimal(number))
      }
      catch {
        case exn : NumberFormatException => throw mathExnMsg(e, "Could not convert number: " + e.toString)
        case exn : ExprFormatException => throw mathExnMsg(e, "Could not represent number as a big decimal: " + e.toString)
      }
    }
    else if (e.rationalQ()) {assert(hasHead(e,MathematicaSymbols.RATIONAL)); convertBinary(e, Divide.apply)}

    // Arith expressions
    else if (hasHead(e,MathematicaSymbols.PLUS))  convertBinary(e, Plus.apply)
    else if (hasHead(e,MathematicaSymbols.MINUS)) convertBinary(e, Minus.apply)
    else if (hasHead(e,MathematicaSymbols.MULT))  convertBinary(e, Times.apply)
    else if (hasHead(e,MathematicaSymbols.DIV))   convertBinary(e, Divide.apply)
    else if (hasHead(e,MathematicaSymbols.EXP))   convertBinary(e, Power.apply)

    // Comparisons
    else if (hasHead(e, MathematicaSymbols.EQUALS))         convertComparison(e, Equal.apply)
    else if (hasHead(e, MathematicaSymbols.UNEQUAL))        convertComparison(e, NotEqual.apply)
    else if (hasHead(e, MathematicaSymbols.GREATER))        convertComparison(e, Greater.apply)
    else if (hasHead(e, MathematicaSymbols.GREATER_EQUALS)) convertComparison(e, GreaterEqual.apply)
    else if (hasHead(e, MathematicaSymbols.LESS))           convertComparison(e, Less.apply)
    else if (hasHead(e, MathematicaSymbols.LESS_EQUALS))    convertComparison(e, LessEqual.apply)
    else if (hasHead(e, MathematicaSymbols.INEQUALITY))     convertInequality(e)

    // Formulas
    else if (hasHead(e, MathematicaSymbols.TRUE))   True
    else if (hasHead(e, MathematicaSymbols.FALSE))  False
    else if (hasHead(e, MathematicaSymbols.NOT))    convertUnary(e, Not.apply)
    else if (hasHead(e, MathematicaSymbols.AND))    convertBinary(e, And.apply)
    else if (hasHead(e, MathematicaSymbols.OR))     convertBinary(e, Or.apply)
    else if (hasHead(e, MathematicaSymbols.IMPL))   convertBinary(e, Imply.apply)
    else if (hasHead(e, MathematicaSymbols.BIIMPL)) convertBinary(e, Equiv.apply)

    //Quantifiers
    else if (hasHead(e,MathematicaSymbols.FORALL)) convertQuantifier(e, Forall.apply)
    else if (hasHead(e,MathematicaSymbols.EXISTS)) convertQuantifier(e, Exists.apply)

    // Rules and List of rules
    else if (hasHead(e, MathematicaSymbols.RULE)) convertRule(e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(hasHead(_, MathematicaSymbols.RULE))))
      convertRuleList(e)

    // Functions
    else if (e.head().symbolQ() && !MathematicaSymbols.keywords.contains(e.head().toString)) convertAtomicTerm(e)

    //Variables. This case intentionally comes last, so that it doesn't gobble up
    //and keywords that were not declared correctly in MathematicaSymbols (should be none)
    else if (e.symbolQ() && !MathematicaSymbols.keywords.contains(e.asString())) {
      convertAtomicTerm(e)
    }
    else {
      throw mathExn(e) //Other things to handle: integrate, rule, minussign, possibly some list.
    }
  }

  private def convertUnary[T<:Expression](e : MExpr, op: T=>T): T = {
    val subformula = fromMathematica(e.args().head).asInstanceOf[T]
    op(subformula)
  }

  private def convertBinary[T<:Expression](e : MExpr, op: (T,T) => T): T = {
    val subexpressions = e.args().map(fromMathematica)
    require(subexpressions.length >= 2, "binary operator expects 2 arguments")
    val asTerms = subexpressions.map(_.asInstanceOf[T])
    asTerms.reduce((l,r) => op(l,r))
  }

  private def convertComparison[S<:Expression,T<:Expression](e : MExpr, op: (S,S) => T): T = {
    val subexpressions = e.args().map(fromMathematica)
    require(subexpressions.length == 2, "binary operator expects 2 arguments")
    val asTerms = subexpressions.map(_.asInstanceOf[S])
    op(asTerms(0), asTerms(1))
  }

  private def convertQuantifier(e : com.wolfram.jlink.Expr, op:(Seq[Variable], Formula)=>Formula) = {
    require(e.args().size == 2, "Expected args size 2.")

    val quantifiedVariables = e.args().headOption.getOrElse(
      throw new ConversionException("Found non-empty list after quantifier."))

    val quantifiedVars: List[Variable] = if (quantifiedVariables.head().equals(MathematicaSymbols.LIST)) {
      //Convert the list of quantified variables
      quantifiedVariables.args().toList.map(n => MathematicaNameConversion.toKeYmaera(n).asInstanceOf[Variable])
    } else {
      List(fromMathematica(quantifiedVariables).asInstanceOf[Variable])
    }

    //Recurse on the body of the expression.
    val bodyOfQuantifier = fromMathematica(e.args().last).asInstanceOf[Formula]

    // convert quantifier block into chain of single quantifiers
    quantifiedVars.foldRight(bodyOfQuantifier)((v, fml) => op(v :: Nil, fml))
  }


  private def convertRuleList(e: MExpr): Formula = {
    val convertedRules = e.args().map(_.args().map(r => convertRule(r)).reduceLeft((lhs, rhs) => And(lhs, rhs)))
    if (convertedRules.isEmpty) False
    else convertedRules.reduceLeft((lhs, rhs) => Or(lhs, rhs))
  }

  private def convertRule(e: MExpr): Formula = {
    assert(LAX, "Not converting rules yet" + e)
    // TODO is Equals correct for rules?
    Equal(fromMathematica(e.args()(0)).asInstanceOf[Term], fromMathematica(e.args()(1)).asInstanceOf[Term])
  }
  
  private def convertAtomicTerm(e: MExpr): KExpr = {
    MathematicaNameConversion.toKeYmaera(e) match {
      case result: Function =>
        val arguments = e.args().map(fromMathematica).map(_.asInstanceOf[Term])
        if (arguments.nonEmpty) {
          val args = if (arguments.length > 1) arguments.reduceRight[Term]((l, r) => Pair(l, r))
          else { assert(arguments.length == 1); arguments.head }
          FuncOf(result, args)
        } else {
          FuncOf(result, Nothing)
        }
      case result: Variable => result
    }
  }

  /** Converts inequality chains of the form a <= b < c < 0 to conjunctions of individual inequalities a <= b & b < c & c < 0 */
  private def convertInequality(e: MExpr): Formula = {
    /** Extract overlapping inequalities from a chain of inequalities, so x<y=z<=d will be x<y, y=z, z<=d */
    def extractInequalities(exprs: Array[Expr]): List[(MExpr, MExpr, MExpr)] = {
      require(exprs.length >= 3 && exprs.length % 2 == 1, "Need pairs of expressions separated by operators")
      if (exprs.length == 3) (exprs(0), exprs(1), exprs(2)) :: Nil
      else (exprs(0), exprs(1), exprs(2)) :: extractInequalities(exprs.tail.tail)
    }

    // conjunction of converted indidivual inequalities
    extractInequalities(e.args()).
      map({case (arg1, op, arg2) => new MExpr(op, Array[MExpr](arg1, arg2))}).
      map(fromMathematica(_).asInstanceOf[Formula]).reduce(And)
  }

  /**
   * Whether e is thing or starts with head thing.
   * @return true if ``e" and ``thing" are .equals-related. 
   */
  private def hasHead(e:com.wolfram.jlink.Expr, thing:com.wolfram.jlink.Expr) =
    e.equals(thing) || e.head().equals(thing)

  // error catching and reporting

  private def isAborted(e : com.wolfram.jlink.Expr) = {
    e.toString.equalsIgnoreCase("$Aborted") ||
    e.toString.equalsIgnoreCase("Abort[]")
  }
  
  private def isFailed(e : com.wolfram.jlink.Expr) = {
    e.toString.equalsIgnoreCase("$Failed")
  }

  private def failExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationFailedException(e)
  private def abortExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationAbortedException(e)

  private def mathExnMsg(e:MExpr, s:String) : Exception =
    new ConversionException("Conversion of " + e.toString + " failed because: " + s)
  
  private def mathExn(e:com.wolfram.jlink.Expr) : Exception =
    new ConversionException("conversion not defined for Mathematica expr: " + e.toString + " with infos: " + mathInfo(e))
  
  private def mathInfo(e : com.wolfram.jlink.Expr) : String = {
    "args:\t" + {if (e.args().size == 0) { "empty" } else {e.args().map(_.toString).reduce(_+","+_)}} +
    "\n" +
    "toString:\t" + e.toString
  }
}
  
