/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.{ConversionException, MathematicaComputationAbortedException, MathematicaComputationFailedException}

// favoring immutable Seqs
import scala.collection.immutable._

/**
 * Converts [[com.wolfram.jlink.Expr]] to [[Expression]].
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object MathematicaToKeYmaera extends MathematicaToKeYmaera
class MathematicaToKeYmaera extends M2KConverter[KExpr] {

  /** Backconversion for contracts. */
  def k2m: K2MConverter[KExpr] = KeYmaeraToMathematica

  /** Converts a Mathematica expression to a KeYmaera expression. */
  private[tools] def convert(e: MExpr): KExpr = {
    //Exceptional states
    if (isAborted(e)) throw MathematicaComputationAbortedException(e.toString)
    else if (isFailed(e)) throw MathematicaComputationFailedException(e.toString)

    // explicit Numbers that are not rationals
    else if (e.numberQ() && !e.rationalQ()) {
      if (e.bigDecimalQ()) Number(e.asBigDecimal()) //@note asBigDecimal does not convert doubles correctly!
      else if (e.realQ()) Number(e.asDouble()) //@note see internal type identifiers in realQ and asDouble (they fit!)
      else if (e.integerQ()) Number(BigDecimal(e.asBigInteger())) //@note e.asLong would lose precision since it truncates if not representable as long
      else throw ConversionException("Cannot convert number " + e + " (neither double nor big decimal)") //@note complexQ
    }
    //@note self-created MExpr with head RATIONAL are not rationalQ (type identifiers do not match)
    else if (MathematicaOpSpec.rational.applies(e)) convertBinary(e, Divide.apply)

    // Arith expressions
    else if (MathematicaOpSpec.plus.applies(e))   convertNary  (e, Plus.apply)
    else if (MathematicaOpSpec.minus.applies(e))  convertBinary(e, Minus.apply)
    else if (MathematicaOpSpec.times.applies(e))  convertNary  (e, Times.apply)
    else if (MathematicaOpSpec.divide.applies(e)) convertBinary(e, Divide.apply)
    else if (MathematicaOpSpec.power.applies(e))  convertBinary(e, Power.apply)
    else if (MathematicaOpSpec.neg.applies(e))    convertUnary (e, Neg.apply)

    // Comparisons
    else if (MathematicaOpSpec.equal.applies(e))        convertComparison(e, Equal.apply)
    else if (MathematicaOpSpec.unequal.applies(e))      convertComparison(e, NotEqual.apply)
    else if (MathematicaOpSpec.greater.applies(e))      convertComparison(e, Greater.apply)
    else if (MathematicaOpSpec.greaterEqual.applies(e)) convertComparison(e, GreaterEqual.apply)
    else if (MathematicaOpSpec.less.applies(e))         convertComparison(e, Less.apply)
    else if (MathematicaOpSpec.lessEqual.applies(e))    convertComparison(e, LessEqual.apply)
    else if (MathematicaOpSpec.inequality.applies(e))   convertInequality(e)

    // Formulas
    else if (MathematicaOpSpec.ltrue.applies(e))      True
    else if (MathematicaOpSpec.lfalse.applies(e))     False
    else if (MathematicaOpSpec.not.applies(e))        convertUnary(e, Not.apply)
    else if (MathematicaOpSpec.and.applies(e))        convertNary(e, And.apply)
    else if (MathematicaOpSpec.or.applies(e))         convertNary(e, Or.apply)
    else if (MathematicaOpSpec.implies.applies(e))    convertBinary(e, Imply.apply)
    else if (MathematicaOpSpec.equivalent.applies(e)) convertBinary(e, Equiv.apply)

    //Quantifiers
    else if (MathematicaOpSpec.forall.applies(e)) convertQuantifier(e, Forall.apply)
    else if (MathematicaOpSpec.exists.applies(e)) convertQuantifier(e, Exists.apply)

    // Rules and List of rules not supported -> override if needed
    else if (MathematicaOpSpec.rule.applies(e)) throw ConversionException("Unsupported conversion RULE " + e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(
      MathematicaOpSpec.rule.applies))) throw ConversionException("Unsupported conversion List[RULE] " + e)

    // Pairs
    else if (MathematicaOpSpec.pair.applies(e)) convertList(e)

    // Variables and function symbols
    else if (MathematicaOpSpec.variable.applies(e)) convertAtomicTerm(e)
    else if (MathematicaOpSpec.func.applies(e)) convertAtomicTerm(e)
    else if (MathematicaOpSpec.mapply.applies(e)) convertAtomicTerm(e)

    //todo: more cases for converting interpreted symbols, possibly make this more generic
    else if (MathematicaOpSpec.interpretedSymbols.exists(_._1.applies(e))) convertAtomicTerm(e)

    // not supported in soundness-critical conversion, but can be overridden for non-soundness-critical tools (CEX, ODE solving)
    else throw ConversionException("Unsupported conversion for Mathematica expr: " + e.toString + " with infos: " + mathInfo(e))
  } ensures(r => StaticSemantics.symbols(r).forall({
    case fn@Function(_, _, _, _, Some(_)) => MathematicaOpSpec.interpretedSymbols.exists(_._2 == fn)
    case _ => true
  }), "Interpreted functions must have expected domain and sort for conversion of " + e)

  /** Converts an unary expression. */
  private def convertUnary[T<:Expression](e: MExpr, op: T=>T): T = {
    require(e.args.length == 1, "unary operator expects 1 argument")
    op(convert(e.args.head).asInstanceOf[T])
  }

  /** Converts a binary expression. */
  private def convertBinary[T<:Expression](e: MExpr, op: (T,T) => T): T = {
    require(e.args.length == 2, "binary operator expects 2 arguments")
    convertNary(e, op)
  }

  /** Converts an n-ary expression. */
  private def convertNary[T<:Expression](e: MExpr, op: (T,T) => T): T = {
    val subexpressions = e.args.map(convert)
    require(subexpressions.length >= 2, "nary operator expects at least 2 arguments")
    subexpressions.map(_.asInstanceOf[T]).reduce(op)
  }

  /** Converts a comparison. */
  private def convertComparison[S<:Term, T<:Formula](e: MExpr, op: (S,S) => T): T = {
    val subexpressions = e.args.map(convert)
    require(subexpressions.length == 2, "binary operator expects 2 arguments")
    val asTerms = subexpressions.map(_.asInstanceOf[S])
    op(asTerms(0), asTerms(1))
  }

  /** Converts a sequence of quantified variables into nested quantifiers. */
  private def convertQuantifier(e: MExpr, op:(Seq[Variable],Formula)=>Formula): Formula = {
    require(e.args.length == 2, "Expected args size 2.")

    val variableBlock = e.args.head

    val quantifiedVars: List[Variable] =
      if (MathematicaOpSpec.list.applies(variableBlock)) {
        //Convert the list of quantified variables
        variableBlock.args.toList.map(n => MathematicaNameConversion.toKeYmaera(n).asInstanceOf[Variable])
      } else {
        List(convert(variableBlock).asInstanceOf[Variable])
      }

    //Recurse on the body of the expression.
    val bodyOfQuantifier = convert(e.args.tail.head).asInstanceOf[Formula]

    // convert quantifier block into chain of single quantifiers
    quantifiedVars.foldRight(bodyOfQuantifier)((v, fml) => op(v :: Nil, fml))
  }

  /** Converts (nested) lists of length 2 into pairs. */
  protected def convertList(e: MExpr): Pair = {
    if (e.listQ) {
      assert(e.args.length == 2, "pairs are represented as lists of length 2 in Mathematica")
      Pair(convert(e.args.head).asInstanceOf[Term], convert(e.args.tail.head).asInstanceOf[Term])
    } else throw ConversionException("Expected a list, but got " + e)
  }

  /** Converts an atomic term (either interpreted/uninterpreted function symbol or variable). */
  protected def convertAtomicTerm(e: MExpr): KExpr =
    MathematicaOpSpec.interpretedSymbols.find(_._1.applies(e)) match {
    case Some((_,fn)) => convertFunction(fn, e.args)
    case None =>
      //@note insists on [[MathematicaNameConversion.NAMESPACE_PREFIX]] to avoid clash with Mathematica names
      MathematicaNameConversion.toKeYmaera(e) match {
        case fn: Function =>
          insist(!fn.interpreted, "Expected uninterpreted function symbol, but got interpreted " + fn)
          convertFunction(fn, e.args)
        case result: Variable => result
    }
  }

  /** Convert the arguments of a function and combine with fn into a FuncOf */
  protected def convertFunction(fn: Function, args: Array[MExpr]): KExpr = {
    assert(args.length <= 2, "Pairs are expected to be represented as nested lists (at most 2 args), but got " + args)
    val arguments = args.map(convert).map(_.asInstanceOf[Term]).reduceRightOption[Term](Pair).getOrElse(Nothing)
    FuncOf(fn, arguments)
  }

  /** Converts inequality chains of the form a <= b < c < 0 to conjunctions of individual inequalities a <= b & b < c & c < 0 */
  private def convertInequality(e: MExpr): Formula = {
    /** Extract overlapping inequalities from a chain of inequalities, so x<y=z<=d will be x<y, y=z, z<=d */
    def extractInequalities(exprs: Array[MExpr]): List[ComparisonFormula] = {
      require(exprs.length % 2 == 1, "Expected pairs of expressions separated by operators")
      if (exprs.length == 1) Nil
      //@note Instead of importing from a newly created Mathematica expression, could also copy the comparison conversion again
      else importResult(MathematicaOpSpec(exprs(1))(exprs(0) :: exprs(2) :: Nil), convert).asInstanceOf[ComparisonFormula] ::
        // keep right-child exprs(2) around because that's the left-child for the subsequent inequality if any
        extractInequalities(exprs.tail.tail)
    }

    // conjunction of converted individual inequalities
    extractInequalities(e.args).reduceRight(And)
  }

  // reporting

  /** Prints debug information. */
  private def mathInfo(e: MExpr): String = "args:\t" + e.args.map(_.toString).mkString(",") + "\ntoString:\t" + e
}
  
