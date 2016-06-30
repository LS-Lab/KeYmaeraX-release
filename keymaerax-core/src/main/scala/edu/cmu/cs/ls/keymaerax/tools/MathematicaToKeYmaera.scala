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
class MathematicaToKeYmaera extends BaseM2KConverter[KExpr] {

  def k2m: K2MConverter[KExpr] = KeYmaeraToMathematica

  /** Converts a Mathematica expression to a KeYmaera expression. */
  def convert(e: MExpr): KExpr = {
    //Exceptional states
    if (isAborted(e)) throw abortExn(e)
    else if (isFailed(e))  throw failExn(e)

    //Numbers
    else if (e.numberQ() && !e.rationalQ()) {
      if (e.realQ()) Number(e.asDouble()) //@note see internal type identifiers in realQ and asDouble (they fit)
      else if (e.integerQ()) Number(e.asLong()) //@note see internal type identifiers in integerQ and asLong (they fit)
      else if (e.bigDecimalQ()) Number(e.asBigDecimal()) //@note asBigDecimal does not convert doubles correctly!
      else throw new ConversionException("Cannot convert " + e + " (neither double, long, nor big decimal)") //@note complexQ
    }
    //@todo Code Review: assert arity 2 --> split into convertBinary and convertNary (see DIV, EXP, MINUS)
    //@solution: introduced explicit convertNary (used for plus/times/and/or), convertBinary forwards to convertNary after contract checking (2 args)
    else if (e.rationalQ()) {assert(hasHead(e,MathematicaSymbols.RATIONAL)); convertBinary(e, Divide.apply)}

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
    else if (hasHead(e, MathematicaSymbols.RULE)) throw new ConversionException("Unsupported conversion RULE")
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(
      hasHead(_, MathematicaSymbols.RULE)))) throw new ConversionException("Unsupported conversion List[RULE]")

    // Functions
    else if (e.head().symbolQ() && !MathematicaSymbols.keywords.contains(e.head().toString)) convertAtomicTerm(e)

    // Pairs
    else if (e.listQ()) convertList(e)

    //Variables. This case intentionally comes last, so that it doesn't gobble up
    //and keywords that were not declared correctly in MathematicaSymbols (should be none)
    else if (e.symbolQ() && !MathematicaSymbols.keywords.contains(e.asString())) {
      convertAtomicTerm(e)
    }
    else {
      throw mathExn(e) //Other things to handle: integrate, rule, minussign, possibly some list.
    }
  } ensuring(r => StaticSemantics.symbols(r).
    map(s => (s.name.toLowerCase, s)).
    filter({ case (n, s) => (n == "abs" || n == "min" || n == "max") && s.index.isEmpty }). //@note e.g., abs_idx is ok
    forall({ case (_, s) => s match {
      case Function("abs", None, Real, Real) => true
      case Function("max", None, Tuple(Real, Real), Real) => true
      case Function("min", None, Tuple(Real, Real), Real) => true
      case _ => false
    }}), "Special functions must have expected domain and sort")

  private def convertUnary[T<:Expression](e : MExpr, op: T=>T): T = {
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
      throw new ConversionException("Found non-empty list after quantifier."))

    val quantifiedVars: List[Variable] = if (variableBlock.head().equals(MathematicaSymbols.LIST)) {
      //Convert the list of quantified variables
      variableBlock.args().toList.map(n => MathematicaNameConversion.toKeYmaera(n).asInstanceOf[Variable])
    } else {
      List(convert(variableBlock).asInstanceOf[Variable])
    }

    //Recurse on the body of the expression.
    val bodyOfQuantifier = convert(e.args().last).asInstanceOf[Formula]

    // convert quantifier block into chain of single quantifiers
    quantifiedVars.foldRight(bodyOfQuantifier)((v, fml) => op(v :: Nil, fml))
  }

  private def convertList(e: MExpr): Pair = {
    if (e.listQ) {
      assert(e.args.length == 2)
      Pair(convert(e.args().head).asInstanceOf[Term], convert(e.args()(1)).asInstanceOf[Term])
    } else throw new ConversionException("Expected a list, but got " + e)
  }

  protected def convertAtomicTerm(e: MExpr): KExpr = MathematicaNameConversion.toKeYmaera(e) match {
    case fn: Function =>
      assert(e.args().length <= 2, "Pairs are expected to be represented as nested lists (at most 2 args), but got " + e.args())
      val arguments = e.args().map(convert).map(_.asInstanceOf[Term])
      FuncOf(fn, arguments.reduceRightOption[Term]((l, r) => Pair(l, r)).getOrElse(Nothing))
    case result: Variable => result
  }

  //@todo could streamline this implementation
  //@solution: streamlined + memory management
  /** Converts inequality chains of the form a <= b < c < 0 to conjunctions of individual inequalities a <= b & b < c & c < 0 */
  private def convertInequality(e: MExpr): Formula = {
    /** Extract overlapping inequalities from a chain of inequalities, so x<y=z<=d will be x<y, y=z, z<=d */
    def extractInequalities(exprs: Array[MExpr]): List[ComparisonFormula] = {
      require(exprs.length % 2 == 1, "Expected pairs of expressions separated by operators")
      if (exprs.length == 1) Nil
      else safeResult(new MExpr(exprs(1), Array[MExpr](exprs(0), exprs(2))), convert).asInstanceOf[ComparisonFormula] ::
        extractInequalities(exprs.tail.tail)
    }

    // conjunction of converted individual inequalities
    extractInequalities(e.args()).reduceRight(And)
  }

  // error catching and reporting

  private def isAborted(e : com.wolfram.jlink.Expr) = {
    e.toString.equalsIgnoreCase("$Aborted") ||
    e.toString.equalsIgnoreCase("Abort[]")
  }
  
  private def isFailed(e : com.wolfram.jlink.Expr) = {
    e.toString.equalsIgnoreCase("$Failed")
  }

  private def failExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationFailedException(e.toString)
  private def abortExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationAbortedException(e.toString)

  private def mathExn(e:com.wolfram.jlink.Expr) : Exception =
    new ConversionException("conversion not defined for Mathematica expr: " + e.toString + " with infos: " + mathInfo(e))
  
  private def mathInfo(e : com.wolfram.jlink.Expr) : String = {
    "args:\t" + {if (e.args().length == 0) { "empty" } else {e.args().map(_.toString).reduce(_+","+_)}} +
    "\n" +
    "toString:\t" + e.toString
  }
}
  
