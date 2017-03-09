/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.KMComparator.hasHead

/**
 * Converts com.wolfram.jlink.Expr -> edu.cmu...keymaerax.core.Expr
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object MathematicaToKeYmaera extends MathematicaToKeYmaera
class MathematicaToKeYmaera extends M2KConverter[KExpr] {

  def k2m: K2MConverter[KExpr] = KeYmaeraToMathematica

  /** Converts a Mathematica expression to a KeYmaera expression. */
  private[tools] def convert(e: MExpr): KExpr = {
    //Exceptional states
    if (isAborted(e)) throw new MathematicaComputationAbortedException(e.toString)
    else if (isFailed(e)) throw new MathematicaComputationFailedException(e.toString)

    // explicit Numbers that are not rationals
    else if (e.numberQ() && !e.rationalQ()) {
      if (e.bigDecimalQ()) Number(e.asBigDecimal()) //@note asBigDecimal does not convert doubles correctly!
      else if (e.realQ()) Number(e.asDouble()) //@note see internal type identifiers in realQ and asDouble (they fit!)
      else if (e.integerQ()) Number(BigDecimal(e.asBigInteger())) //@note e.asLong would lose precision since it truncates if not representable as long
      else throw new ConversionException("Cannot convert number " + e + " (neither double, long, nor big decimal)") //@note complexQ
    }
    //@note self-created MExpr with head RATIONAL are not rationalQ (type identifiers do not match)
    else if (e.rationalQ() || hasHead(e,MathematicaSymbols.RATIONAL)) {
      assert(hasHead(e,MathematicaSymbols.RATIONAL)); convertBinary(e, Divide.apply)}

    // Arith expressions
    else if (hasHead(e,MathematicaSymbols.PLUS))  convertNary(e, Plus.apply)
    else if (hasHead(e,MathematicaSymbols.MINUS)) convertBinary(e, Minus.apply)
    else if (hasHead(e,MathematicaSymbols.MULT))  convertNary(e, Times.apply)
    else if (hasHead(e,MathematicaSymbols.DIV))   convertBinary(e, Divide.apply)
    else if (hasHead(e,MathematicaSymbols.EXP))   convertBinary(e, Power.apply)
    else if (hasHead(e,MathematicaSymbols.MINUSSIGN)) convertUnary(e, Neg.apply)

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
    else if (hasHead(e, MathematicaSymbols.AND))    convertNary(e, And.apply)
    else if (hasHead(e, MathematicaSymbols.OR))     convertNary(e, Or.apply)
    else if (hasHead(e, MathematicaSymbols.IMPL))   convertBinary(e, Imply.apply)
    else if (hasHead(e, MathematicaSymbols.BIIMPL)) convertBinary(e, Equiv.apply)

    //Quantifiers
    else if (hasHead(e,MathematicaSymbols.FORALL)) convertQuantifier(e, Forall.apply)
    else if (hasHead(e,MathematicaSymbols.EXISTS)) convertQuantifier(e, Exists.apply)

    // Rules and List of rules not supported -> override if needed
    else if (hasHead(e, MathematicaSymbols.RULE)) throw new ConversionException("Unsupported conversion RULE " + e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(
      hasHead(_, MathematicaSymbols.RULE)))) throw new ConversionException("Unsupported conversion List[RULE] " + e)

    // Pairs
    else if (e.listQ()) convertList(e)

    // Functions
    else if (e.head().symbolQ() && !MathematicaSymbols.keywords.contains(e.head().toString)) convertAtomicTerm(e)

    //Variables. This case intentionally comes last, so that it doesn't gobble up
    //and keywords that were not declared correctly in MathematicaSymbols (should be none)
    else if (e.symbolQ() && !MathematicaSymbols.keywords.contains(e.asString())) convertAtomicTerm(e)

    // not supported in soundness-critical conversion, but can be overridden for non-soundness-critical tools (CEX, ODE solving)
    else throw mathExn(e)
  } ensuring(r => StaticSemantics.symbols(r).forall({case fn@Function(_, _, _, _, true) => MathematicaConversion.interpretedSymbols.contains(fn) case _ => true}), "Interpreted functions must have expected domain and sort for conversion of " + e)


  private def convertUnary[T<:Expression](e : MExpr, op: T=>T): T = {
    require(e.args().length == 1, "unary operator expects 1 argument")
    val subformula = convert(e.args().head).asInstanceOf[T]
    op(subformula)
  }

  private def convertBinary[T<:Expression](e : MExpr, op: (T,T) => T): T = {
    require(e.args().length == 2, "binary operator expects 2 arguments")
    convertNary(e, op)
  }

  private def convertNary[T<:Expression](e : MExpr, op: (T,T) => T): T = {
    val subexpressions = e.args().map(convert)
    require(subexpressions.length >= 2, "nary operator expects at least 2 arguments")
    val asTerms = subexpressions.map(_.asInstanceOf[T])
    asTerms.reduce((l,r) => op(l,r))
  }

  private def convertComparison[S<:Expression,T<:Expression](e : MExpr, op: (S,S) => T): T = {
    val subexpressions = e.args().map(convert)
    require(subexpressions.length == 2, "binary operator expects 2 arguments")
    val asTerms = subexpressions.map(_.asInstanceOf[S])
    op(asTerms(0), asTerms(1))
  }

  private def convertQuantifier(e: MExpr, op:(Seq[Variable], Formula)=>Formula) = {
    require(e.args().length == 2, "Expected args size 2.")

    val variableBlock = e.args().headOption.getOrElse(
      throw new ConversionException("Found unexpected empty variable list after quantifier."))

    val quantifiedVars: List[Variable] = if (variableBlock.head().equals(MathematicaSymbols.LIST)) {
      //Convert the list of quantified variables
      variableBlock.args().toList.map(n => MathematicaNameConversion.toKeYmaera(n).asInstanceOf[Variable])
    } else {
      List(convert(variableBlock).asInstanceOf[Variable])
    }

    //Recurse on the body of the expression.
    val bodyOfQuantifier = convert(e.args().tail.head).asInstanceOf[Formula]

    // convert quantifier block into chain of single quantifiers
    quantifiedVars.foldRight(bodyOfQuantifier)((v, fml) => op(v :: Nil, fml))
  }

  protected def convertList(e: MExpr): Pair = {
    if (e.listQ) {
      assert(e.args.length == 2, "pairs are represented as lists of length 2 in Mathematica")
      Pair(convert(e.args().head).asInstanceOf[Term], convert(e.args().tail.head).asInstanceOf[Term])
    } else throw new ConversionException("Expected a list, but got " + e)
  }

  protected def convertAtomicTerm(e: MExpr): KExpr = interpretedSymbols.get(e.head) match {
    case Some(fn) => convertFunction(fn, e.args())
    case None =>
      MathematicaNameConversion.toKeYmaera(e) match {
        case fn: Function =>
          insist(!fn.interpreted, "Expected uninterpreted function symbol, but got interpreted " + fn)
          convertFunction(fn, e.args())
        case result: Variable => result
    }
  }

  /** Convert the arguments of a function and combine with fn into a FuncOf */
  protected def convertFunction(fn: Function, args: Array[MExpr]): KExpr = {
    assert(args.length <= 2, "Pairs are expected to be represented as nested lists (at most 2 args), but got " + args)
    val arguments = args.map(convert).map(_.asInstanceOf[Term])
    FuncOf(fn, arguments.reduceRightOption[Term]((l, r) => Pair(l, r)).getOrElse(Nothing))
  }

  /** Converts inequality chains of the form a <= b < c < 0 to conjunctions of individual inequalities a <= b & b < c & c < 0 */
  private def convertInequality(e: MExpr): Formula = {
    /** Extract overlapping inequalities from a chain of inequalities, so x<y=z<=d will be x<y, y=z, z<=d */
    def extractInequalities(exprs: Array[MExpr]): List[ComparisonFormula] = {
      require(exprs.length % 2 == 1, "Expected pairs of expressions separated by operators")
      if (exprs.length == 1) Nil
      //@note Instead of importing from a newly created Mathematica expression, could also copy the comparison conversion again
      else importResult(new MExpr(exprs(1), Array[MExpr](exprs(0), exprs(2))), convert).asInstanceOf[ComparisonFormula] ::
        // keep right-child exprs(2) around because that's the left-child for the subsequent inequality if any
        extractInequalities(exprs.tail.tail)
    }

    // conjunction of converted individual inequalities
    extractInequalities(e.args()).reduceRight(And)
  }

  // error catching and reporting

  //@todo MathematicaSymbols.ABORTED
  private def isAborted(e: MExpr) = e.toString.equalsIgnoreCase("$Aborted") || e.toString.equalsIgnoreCase("Abort[]")
  private def isFailed(e: MExpr) = e.toString.equalsIgnoreCase("$Failed")

  private def mathExn(e: MExpr) : Exception =
    new ConversionException("Unsupported conversion for Mathematica expr: " + e.toString + " with infos: " + mathInfo(e))
  
  private def mathInfo(e: MExpr) : String = {
    "args:\t" + {if (e.args().length == 0) { "empty" } else {e.args().map(_.toString).reduce(_+","+_)}} +
    "\n" +
    "toString:\t" + e.toString
  }
}
  
