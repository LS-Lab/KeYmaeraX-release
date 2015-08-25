/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._
import scala.math.BigDecimal


class ConversionException(s:String) 
  extends Exception(s)
class MathematicaComputationFailedException(e:com.wolfram.jlink.Expr) 
  extends ConversionException(e.toString)
class MathematicaComputationAbortedException(e:com.wolfram.jlink.Expr) 
  extends ConversionException(e.toString)

/**
 * Handles conversion to/from Mathematica.
 * 
 * TODO-nrf assertion that maskName and removeMask are inverses (compose to
 * id).
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
private object NameConversion {
  private val PREFIX = "KeYmaera`"
  private val SEP    = "$beginIndex$"
  private val MUNDERSCORE = "$underscore$" //Mathematica Underscore

  val CONST_FN_PREFIX: String = "constfn$"

  private def regexOf(s: String) = {
    s.replace("$", "\\$")
  }

  private def maskIdentifier(name : String) = {
    //Ensure that none of the "special" strings occur in the variable name.
    if (name.contains(MUNDERSCORE)) {
      throw new ConversionException("Please do not use the string " + MUNDERSCORE + " in your variable names.")
    }
    //Do replacements.
    name.replace("_", MUNDERSCORE)
  }

  
  def toMathematica(ns : NamedSymbol) : com.wolfram.jlink.Expr = {
    //The identifier (portion of name excluding index) has one of the forms:
    //   name (for external functions)
    //   KeYmaera + name
    val identifier : String = ns match {
      //@note special function
      case Function("abs",None,Real,Real) => "Abs"
      case Function("Abs",None,Real,Real) => throw new IllegalArgumentException("Refuse translating Abs to Mathematica to avoid confusion with abs")
      case Function("min",None,Tuple(Real,Real),Real) => "Min"
      case Function("Min",None,Tuple(Real,Real),Real) => throw new IllegalArgumentException("Refuse translating Min to Mathematica to avoid confusion with min")
      case Function("max",None,Tuple(Real,Real),Real) => "Max"
      case Function("Max",None,Tuple(Real,Real),Real) => throw new IllegalArgumentException("Refuse translating Max to Mathematica to avoid confusion with max")
//      case n: Function if n.external => n.name
      case _ => PREFIX + maskIdentifier(ns.name)
    }

    //Add the index if it exists.
    val fullName : String   = ns.index match {
      case Some(idx) => identifier + SEP + idx.toString
      case None      => identifier
    }
    new com.wolfram.jlink.Expr(com.wolfram.jlink.Expr.SYMBOL, fullName)
  } ensuring (r => r.symbolQ(), "symbol names expected as result")

  ////
  // toKeYmaera section. We decompose by function vs. variable. In each case, we
  // decompose based upon the possible forms of the name:
  // PREFIX + base + SEP + index ---> name + index
  // PREFIX + base               ---> name only
  // base                        ---> external function
  ///
  def toKeYmaera(e: com.wolfram.jlink.Expr): NamedSymbol = {
    if (e.args().isEmpty) nullaryNameToKeYmaera(e)
    else functionToKeYmaera(e)
  }
  
  private def unmaskName(e: com.wolfram.jlink.Expr): (String, Option[Int]) = {
    val maskedName = e.asString().replaceAll(regexOf(MUNDERSCORE), "_")
    if (maskedName.contains(PREFIX) && maskedName.contains(SEP)) {
      //Get the parts of the masked name.
      val parts = maskedName.replace(PREFIX, "").split(regexOf(SEP))
      if (parts.size != 2) throw new ConversionException("Expected " + SEP + " once only.")
      val (name, unparsedIndex) = (parts.head, parts.last)

      val index = try {
        Integer.parseInt(unparsedIndex)
      } catch {
        case e : NumberFormatException => throw new ConversionException("Expected number for index")
      }
      (name, Some(index))
    }
    else if (maskedName.contains(PREFIX) && !maskedName.contains(SEP)) {
      (maskedName.replace(PREFIX, ""), None)
    } else {
      (maskedName, None)
    }
  }

  /** Returns a variable or function, depending on the prefix of the name */
  private def nullaryNameToKeYmaera(e: com.wolfram.jlink.Expr): NamedSymbol = {
    require(e.args().isEmpty, "Nullary names have no arguments")
    val (name, index) = unmaskName(e)
    if (name.startsWith(NameConversion.CONST_FN_PREFIX)) Function(name.replace(CONST_FN_PREFIX, ""), index, Unit, Real)
    else Variable(name, index, Real)
  }

  private def functionToKeYmaera(e : com.wolfram.jlink.Expr) : NamedSymbol = {
    val (name, index) = unmaskName(e.head())
    require(!name.startsWith(NameConversion.CONST_FN_PREFIX), "Proper functions are not constant functions")
    name match {
      //@note special function
      case "Abs" => Function("abs", None, Real, Real)
      case "Min" => Function("min", None, Tuple(Real, Real), Real)
      case "Max" => Function("max", None, Tuple(Real, Real), Real)
      case _ => Function(name, index, Real, Real) //TODO get the (co)domain correct. //TODO again we need to be very careful, as in the symmetric variable case.
    }
  }
}

/**
 * Converts com.wolfram.jlink.Expr -> edu.cmu...keymaerax.core.Expr
 * @TODO the correctness of quantifier handling is non-obvious
 * 
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
object MathematicaToKeYmaera {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  //@TODO Code Review: turn to false in qe calls
  private val LAX = true

  /**
   * Converts a Mathematica expression to a KeYmaera expression.
   */
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
    else if (e.rationalQ()) {assert(isThing(e,MathematicaSymbols.RATIONAL)); convertBinary(e, Divide.apply)}

    // Arith expressions
    else if (isThing(e,MathematicaSymbols.PLUS))  convertBinary(e, Plus.apply)
    else if (isThing(e,MathematicaSymbols.MINUS)) convertBinary(e, Minus.apply)
    else if (isThing(e,MathematicaSymbols.MULT))  convertBinary(e, Times.apply)
    else if (isThing(e,MathematicaSymbols.DIV))   convertBinary(e, Divide.apply)
    else if (isThing(e,MathematicaSymbols.EXP))   convertBinary(e, Power.apply)

    // Comparisons
    else if (isThing(e, MathematicaSymbols.EQUALS))         convertComparison(e, Equal.apply)
    else if (isThing(e, MathematicaSymbols.UNEQUAL))        convertComparison(e, NotEqual.apply)
    else if (isThing(e, MathematicaSymbols.GREATER))        convertComparison(e, Greater.apply)
    else if (isThing(e, MathematicaSymbols.GREATER_EQUALS)) convertComparison(e, GreaterEqual.apply)
    else if (isThing(e, MathematicaSymbols.LESS))           convertComparison(e, Less.apply)
    else if (isThing(e, MathematicaSymbols.LESS_EQUALS))    convertComparison(e, LessEqual.apply)
    else if (isThing(e, MathematicaSymbols.INEQUALITY))     convertInequality(e)

    // Formulas
    else if (isThing(e, MathematicaSymbols.TRUE))   True
    else if (isThing(e, MathematicaSymbols.FALSE))  False
    else if (isThing(e, MathematicaSymbols.NOT))    convertUnary(e, Not.apply)
    else if (isThing(e, MathematicaSymbols.AND))    convertBinary(e, And.apply)
    else if (isThing(e, MathematicaSymbols.OR))     convertBinary(e, Or.apply)
    else if (isThing(e, MathematicaSymbols.IMPL))   convertBinary(e, Imply.apply)
    else if (isThing(e, MathematicaSymbols.BIIMPL)) convertBinary(e, Equiv.apply)

    //Quantifiers
    else if (isThing(e,MathematicaSymbols.FORALL)) convertQuantifier(e, Forall.apply)
    else if (isThing(e,MathematicaSymbols.EXISTS)) convertQuantifier(e, Exists.apply)

    // Rules and List of rules
    else if (isThing(e, MathematicaSymbols.RULE)) convertRule(e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(isThing(_, MathematicaSymbols.RULE))))
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
      quantifiedVariables.args().toList.map(n => NameConversion.toKeYmaera(n).asInstanceOf[Variable])
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
    NameConversion.toKeYmaera(e) match {
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

  //Illustrative example of the following conversion methods:
  //	input: a ~ b ~ c where ~ \in { =,<,>,<=,>= }
  //	subterms: a,b,c
  //	staggeredPairs: (a,b),(b,c)
  //	staggeredFormuals: (a ~ b), (b ~ c)
  //	output: (a ~ b) && (b ~ c)
  /** converts expressions of the form a <= b < c < 0 */
  def convertInequality(e: MExpr): Formula = {
    def extractInequalities(exprs: Array[Expr]): List[(MExpr, MExpr, MExpr)] = {
      require(exprs.length >= 3 && exprs.length % 2 == 1, "Need pairs of expressions separated by operators")
      if (exprs.length == 3) (exprs(0), exprs(1), exprs(2)) :: Nil
      else (exprs(0), exprs(1), exprs(2)) :: extractInequalities(exprs.tail.tail)
    }

    extractInequalities(e.args()).
      map({case (arg1, op, arg2) => new MExpr(op, Array[MExpr](arg1, arg2))}).
      map(fromMathematica(_).asInstanceOf[Formula]).reduce(And)
  }
  def makeOverlappingPairs[T](s : Seq[T]):Seq[(T,T)] = {
    if (s.size == 2) {
      (s.head, s.last) :: Nil
    }
    else {
      makeOverlappingPairs(s.tail) :+ (s.head, s.tail.head)
    }
  }
  
  /**
   * @return true if ``e" and ``thing" are .equals-related. 
   * 
   * This can be used in conjunction
   * with MathematicaSymbols to test if a given expression has a syntactic form.
   */
  def isThing(e:com.wolfram.jlink.Expr, thing:com.wolfram.jlink.Expr) = 
    e.equals(thing) || e.head().equals(thing)

  def isAborted(e : com.wolfram.jlink.Expr) = {
    e.toString.equalsIgnoreCase("$Aborted") ||
    e.toString.equalsIgnoreCase("Abort[]")
  }
  
  def isFailed(e : com.wolfram.jlink.Expr) = {
    e.toString.equalsIgnoreCase("$Failed")
  }

  def failExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationFailedException(e)
  def abortExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationAbortedException(e)

  def mathExnMsg(e:MExpr, s:String) : Exception =
    new ConversionException("Conversion of " + e.toString + " failed because: " + s)
  
  def mathExn(e:com.wolfram.jlink.Expr) : Exception = 
    new ConversionException("conversion not defined for Mathematica expr: " + e.toString + " with infos: " + mathInfo(e))
  
  def mathInfo(e : com.wolfram.jlink.Expr) : String = {
    "args:\t" + {if (e.args().size == 0) { "empty" } else {e.args().map(_.toString).reduce(_+","+_)}} +
    "\n" +
    "toString:\t" + e.toString
  }
}
  
/**
 * Converts KeYmaeara X [[edu.cmu.cs.ls.keymaerax.core.Expression expression data structures]]
 * into Mathematica Expr objects.
 * @author Nathan Fulton
 */
object KeYmaeraToMathematica {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  def fromKeYmaera(e : KExpr): MExpr = e match {
    case t : Term => convertTerm(t)
    case t : Formula => convertFormula(t)
  }

  /** 
   * Converts a KeYmaera terms to a Mathematica expression.
   */
  def convertTerm(t : Term) : MExpr = {
    /** Convert tuples to list of sorts */
    def flattenSort(s: Sort): List[Sort] = s match {
      case Tuple(ls, rs) => ls :: rs :: Nil
      case _ => s :: Nil
    }

    require(t.sort == Real || t.sort == Unit || flattenSort(t.sort).forall(_ == Real), "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      case FuncOf(fn, child) => convertFnApply(fn, child)
      case Neg(c) => new MExpr(MathematicaSymbols.MINUSSIGN, Array[MExpr](convertTerm(c)))
      case Plus(l, r) =>
        new MExpr(MathematicaSymbols.PLUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Minus(l, r) =>
        new MExpr(MathematicaSymbols.MINUS, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Times(l, r) =>
        new MExpr(MathematicaSymbols.MULT, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Divide(l, r) =>
        new MExpr(MathematicaSymbols.DIV, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Power(l, r) =>
        new MExpr(MathematicaSymbols.EXP, Array[MExpr](convertTerm(l), convertTerm(r)))
      case Differential(c) =>
        new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convertTerm(c)))
      case DifferentialSymbol(c) =>
        new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convertTerm(c)))
      case Number(n) => new MExpr(n.underlying())
      case Pair(l, r) =>     //@todo handle nested pairs (flatten to a list?)
        new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(l), convertTerm(r)))

      case t: Variable => NameConversion.toMathematica(t)
    }
  }
  
  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  def convertFormula(f : Formula) : MExpr = f match {
    case And(l,r)   => new MExpr(MathematicaSymbols.AND, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equiv(l,r) => new MExpr(MathematicaSymbols.BIIMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Imply(l,r) => new MExpr(MathematicaSymbols.IMPL, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Or(l,r)    => new MExpr(MathematicaSymbols.OR, Array[MExpr](convertFormula(l), convertFormula(r)))
    case Equal(l,r) => new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case NotEqual(l,r) => new MExpr(MathematicaSymbols.UNEQUAL, Array[MExpr](convertTerm(l), convertTerm(r)))
    case LessEqual(l,r) => new MExpr(MathematicaSymbols.LESS_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Less(l,r)   => new MExpr(MathematicaSymbols.LESS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case GreaterEqual(l,r) => new MExpr(MathematicaSymbols.GREATER_EQUALS, Array[MExpr](convertTerm(l), convertTerm(r)))
    case Greater(l,r) => new MExpr(MathematicaSymbols.GREATER, Array[MExpr](convertTerm(l), convertTerm(r)))
    case False => MathematicaSymbols.FALSE
    case True => MathematicaSymbols.TRUE
    case Not(phi) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertFormula(phi)))
    case Exists(vs, phi) => convertExists(vs,phi)
    case Forall(vs, phi) => convertForall(vs,phi)
  }
  
  def convertFnApply(fn: Function, child: Term): MExpr = child match {
    case Nothing => NameConversion.toMathematica(new Function(NameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
    case _ =>
      //@todo Code Review: figure out how nested lists affect binary functions
      val args = Array[MExpr](NameConversion.toMathematica(fn), new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(child))))
      new MExpr(MathematicaSymbols.APPLY, args)
  }

  /** Convert block of exists quantifiers into a single exists quantifier block */
  def convertExists(vs:Seq[NamedSymbol],f:Formula) = {
    val (vars, formula) = collectVarsExists(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(NameConversion.toMathematica).toArray)
    new MExpr(MathematicaSymbols.EXISTS, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsExists(vsSoFar:Seq[NamedSymbol],candidate:Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextf) =>  collectVarsExists(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }

  /** Convert block of forall quantifiers into a single forall quantifier block */
  def convertForall(vs:Seq[NamedSymbol],f:Formula) = {
    val (vars, formula) = collectVarsForall(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(NameConversion.toMathematica).toArray)
    new MExpr(MathematicaSymbols.FORALL, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsForall(vsSoFar:Seq[NamedSymbol],candidate:Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextf) =>  collectVarsForall(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }
  
  def keyExn(e: KExpr) : Exception =
    new ConversionException("conversion not defined for KeYmaera expr: " + PrettyPrinter.printer(e))
}
