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
    if(name.contains(MUNDERSCORE)) {
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
  }

  ////
  // toKeYmaera section. We decompose by function vs. variable. In each case, we
  // decompose based upon the possible forms of the name:
  // PREFIX + base + SEP + index ---> name + index
  // PREFIX + base               ---> name only
  // base                        ---> external function
  ///
  def toKeYmaera(e : com.wolfram.jlink.Expr) : NamedSymbol = {
    if(e.args().isEmpty) variableToKeYmaera(e)
    else functionToKeYmaera(e)
  }
  
  private def variableToKeYmaera(e : com.wolfram.jlink.Expr) : NamedSymbol = {
    val maskedName = e.asString().replaceAll(regexOf(MUNDERSCORE), "_")
    if(maskedName.contains(PREFIX) && maskedName.contains(SEP)) {
      //Get the parts of the masked name.
      val parts = maskedName.replace(PREFIX, "").split(regexOf(SEP))
      if(parts.size != 2) throw new ConversionException("Expected " + SEP + " once only.")
      val (name, unparsedIndex) = (parts.head, parts.last)
      
      val index = try {
        Integer.parseInt(unparsedIndex)
      } catch {
        case e : NumberFormatException => throw new ConversionException("Expected number for index")
      }
      Variable(name, Some(index), Real)
    }
    else if(maskedName.contains(PREFIX) && !maskedName.contains(SEP)) {
      Variable(maskedName.replace(PREFIX, ""), None, Real)
    }
    else {
      Variable(maskedName, None, Real) //TODO um... this can happen (new quantified vars) but we need to be very careful.
    }
  }
  
  private def functionToKeYmaera(e : com.wolfram.jlink.Expr) : NamedSymbol = {
    val maskedName = e.head().asString().replaceAll(regexOf(MUNDERSCORE), "_")
    if(maskedName.contains(PREFIX) && maskedName.contains(SEP)) {
      //Get the parts of the masked name.
      val parts = maskedName.replace(PREFIX, "").split(regexOf(SEP))
      if(parts.size != 2) throw new ConversionException("Expected " + SEP + " once only.")
      val (name, unparsedIndex) = (parts.head, parts.last)
      
      val index = try {
        Integer.parseInt(unparsedIndex)
      } catch {
        case e : NumberFormatException => throw new ConversionException("Expected number for index")
      }
      Function(name, Some(index), Real, Real) //TODO get the (co)domain correct
    }
    else if(maskedName.contains(PREFIX) && !maskedName.contains(SEP)) {
      Function(maskedName.replace(PREFIX, ""), None, Real, Real) //TODO get the (co)domain correct.
    }
    else {
       maskedName match {
         //@note special function
         case "Abs" => Function("abs",None,Real,Real)
         case "Min" => Function("min",None,Tuple(Real,Real),Real)
         case "Max" => Function("max",None,Tuple(Real,Real),Real)
         case _ => Function(maskedName, None, Real, Real) //TODO get the (co)domain correct. //TODO again we need to be very careful, as in the symmetric variable case.
       }
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

  /**
   * Converts a Mathematica expression to a KeYmaera expression.
   */
  def fromMathematica(e : MExpr): KExpr = {
    //Numbers
    if(e.numberQ() && !e.rationalQ()) {
      try {
        val number = e.asBigDecimal()
        Number(BigDecimal(number))
      }
      catch {
        case exn : NumberFormatException => throw mathExnMsg(e, "Could not convert number: " + e.toString)
        case exn : ExprFormatException => throw mathExnMsg(e, "Could not represent number as a big decimal: " + e.toString)
      }
    }
    else if(e.rationalQ()) convertDivision(e)
    
    //Exceptional states
    else if(isAborted(e)) throw abortExn(e)
    else if(isFailed(e))  throw failExn(e)
    
    
    //Arith expressions
    else if(isThing(e,MathematicaSymbols.PLUS))  convertAddition(e)
    else if(isThing(e,MathematicaSymbols.MULT))  convertMultiplication(e)
    else if(isThing(e,MathematicaSymbols.DIV))   convertDivision(e)
    else if(isThing(e,MathematicaSymbols.MINUS)) convertSubtraction(e)
    else if(isThing(e,MathematicaSymbols.EXP))   convertExponentiation(e)
    
    //Quantifiers
    else if(isQuantifier(e)) convertQuantifier(e)
    
    //Boolean algebra
    else if(isThing(e, MathematicaSymbols.TRUE))   True
    else if(isThing(e, MathematicaSymbols.FALSE))  False
    else if(isThing(e, MathematicaSymbols.AND))    convertAnd(e)
    else if(isThing(e, MathematicaSymbols.OR))     convertOr(e)
    else if(isThing(e, MathematicaSymbols.NOT))    convertNot(e)
    else if(isThing(e, MathematicaSymbols.IMPL))   convertImpl(e)
    else if(isThing(e, MathematicaSymbols.BIIMPL)) convertEquiv(e)
    
    //Relations
    else if(isThing(e, MathematicaSymbols.EQUALS))         convertEquals(e)
    else if(isThing(e, MathematicaSymbols.UNEQUAL))        convertNotEquals(e)
    else if(isThing(e, MathematicaSymbols.GREATER))        convertGreaterThan(e)
    else if(isThing(e, MathematicaSymbols.GREATER_EQUALS)) convertGreaterEqual(e)
    else if(isThing(e, MathematicaSymbols.LESS))           convertLessThan(e)
    else if(isThing(e, MathematicaSymbols.LESS_EQUALS))    convertLessEqual(e)

    else if(isThing(e, MathematicaSymbols.RULE)) convertRule(e)

    // List of rules
    else if(e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(isThing(_, MathematicaSymbols.RULE))))
      convertRuleList(e)

    // Functions
    else if(e.head().symbolQ() && !MathematicaSymbols.keywords.contains(e.head().toString)) convertName(e)

    //Variables. This case intentionally comes last, so that it doesn't gobble up
    //and keywords that were not declared correctly in MathematicaSymbols (should be none)
    else if(e.symbolQ() && !MathematicaSymbols.keywords.contains(e.asString())) {
      convertName(e)
    }
    else {
      throw mathExn(e) //Other things to handle: integrate, rule, minussign, possibly some list.
    }
  }

  def convertRuleList(e: MExpr): Formula = {
    val convertedRules = e.args().map(_.args().map(r => convertRule(r)).reduceLeft((lhs, rhs) => And(lhs, rhs)))
    if (convertedRules.isEmpty) False
    else convertedRules.reduceLeft((lhs, rhs) => Or(lhs, rhs))
  }

  def convertRule(e: MExpr): Formula = {
    // TODO is Equals correct for rules?
    Equal(fromMathematica(e.args()(0)).asInstanceOf[Term], fromMathematica(e.args()(1)).asInstanceOf[Term])
  }
  
  def convertQuantifiedVariable(e : MExpr) : edu.cmu.cs.ls.keymaerax.core.Variable = {
    val result = NameConversion.toKeYmaera(e)
    result match {
      case result : Variable => result
      case _ => throw new ConversionException("Expected variables but found non-variable:" + result.getClass.toString)
    }
  }
  
  def convertName(e : MExpr) : KExpr = {
    val result = NameConversion.toKeYmaera(e)
    result match {
      case result : Function => {
        val arguments = e.args().map(fromMathematica).map(_.asInstanceOf[Term])
        if(arguments.nonEmpty) {
          assert(arguments.length == 1)
//          val argumentsAsPair = arguments.reduceRight[Term](
//            (l, r) => Pair(TupleT(l.sort, r.sort), l, r)
//          )
//          FuncOf(result, argumentsAsPair)
          FuncOf(result, arguments.head)
        }
        else {
          result
        }
      }
      case _ if  result.name.startsWith(NameConversion.CONST_FN_PREFIX) =>
        FuncOf(Function(result.name.substring(NameConversion.CONST_FN_PREFIX.length), result.index, Unit, result.sort), Nothing)
      case _ if !result.name.startsWith(NameConversion.CONST_FN_PREFIX) => result
    }
  }

  def convertAddition(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Plus(l,r))
  }
  def convertDivision(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Divide(l,r))
  }
  def convertSubtraction(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Minus(l,r))
  }
  def convertMultiplication(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Times(l,r))
  }
  def convertExponentiation(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Power(l,r.asInstanceOf[Number]))
  }
  
  def convertAnd(e : MExpr) = {
    val subformulas = e.args().map(fromMathematica(_).asInstanceOf[Formula])
    subformulas.reduceRight( (l,prev) => And(l,prev))
  }
  def convertOr(e : MExpr) = {
    val subformulas = e.args().map(fromMathematica(_).asInstanceOf[Formula])
    subformulas.reduceRight( (l,prev) => Or(l,prev))
  }
  def convertImpl(e : MExpr) = {
    val subformulas = e.args().map(fromMathematica(_).asInstanceOf[Formula])
    subformulas.reduceRight( (l,prev) => Imply(l,prev))
  }
  def convertEquiv(e : MExpr) = {
    val subformulas = e.args().map(fromMathematica(_).asInstanceOf[Formula])
    subformulas.reduceRight( (l,prev) => Equiv(l,prev))
  }
  def convertNot(e : MExpr) = {
    val subformula = fromMathematica(e.args().head).asInstanceOf[Formula]
    Not(subformula)
  }
  
  //Illustrative example of the following conversion methods:
  //	input: a ~ b ~ c where ~ \in { =,<,>,<=,>= }
  //	subterms: a,b,c
  //	staggeredPairs: (a,b),(b,c)
  //	staggeredFormuals: (a ~ b), (b ~ c)
  //	output: (a ~ b) && (b ~ c)
  def convertEquals(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(IndexedSeq() ++ subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => Equal(pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertNotEquals(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(IndexedSeq() ++ subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => NotEqual(pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertGreaterEqual(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(IndexedSeq() ++ subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => GreaterEqual(pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertLessEqual(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(IndexedSeq() ++ subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => LessEqual(pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertLessThan(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(IndexedSeq() ++ subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => Less(pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertGreaterThan(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(IndexedSeq() ++ subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => Greater(pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def makeOverlappingPairs[T](s : Seq[T]):Seq[(T,T)] = {
    if(s.size == 2) {
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

  def isQuantifier(e : com.wolfram.jlink.Expr) = 
    isThing(e,MathematicaSymbols.FORALL) || isThing(e,MathematicaSymbols.EXISTS)
  
  def convertQuantifier(e : com.wolfram.jlink.Expr) = {
    if(e.args().size != 2)
      throw new ConversionException("Expected args size 2.")
    
    val quantifiedVariables = e.args().headOption.getOrElse(
        throw new ConversionException("Found non-empty list after quantifier."))
        
    if (quantifiedVariables.head().equals(MathematicaSymbols.LIST)) {
      //Convert the list of quantified variables  
      val quantifiedVars = quantifiedVariables.args().map(n => convertQuantifiedVariable(n))

      //Recurse on the body of the expression.
      val bodyAsExpr = fromMathematica(e.args().last)
      val bodyOfQuantifier = try {
        bodyAsExpr.asInstanceOf[Formula]
      }
      catch {
        case e : Exception => 
          throw new ConversionException("Expected a formula in the body of the quanfiier, but found a non-variable expression: " + PrettyPrinter.printer(bodyAsExpr))
      }
        
      //Create the final expression.
      if(isThing(e, MathematicaSymbols.FORALL)) {
        //Forall(IndexedSeq() ++ quantifiedVars, bodyOfQuantifier)
        quantifiedVars.foldRight(bodyOfQuantifier)((v, fml) => Forall(v :: Nil, fml))
      }
      else if(isThing(e, MathematicaSymbols.EXISTS)) {
        //Exists(IndexedSeq() ++ quantifiedVars, bodyOfQuantifier)
        quantifiedVars.foldRight(bodyOfQuantifier)((v, fml) => Exists(v :: Nil, fml))
      }
      else {
        throw mathExnMsg(e, "Tried to convert a quantifier-free expression using convertQuantifier. The check in fromMathematica must be wrong.")
      }
    }
    else if(quantifiedVariables.head().equals(MathematicaSymbols.INEQUALITY)) {
      ???
    }
    else {
      //This is similar to the first case in this if/else block, except
      //the expression looks like ForAll[x, ...] instead of ForAll[{x}, ...].
      val variableAsExpr = fromMathematica(quantifiedVariables)
      val formulaAsExpr = fromMathematica(e.args().last)
      
      val variable = try{ variableAsExpr.asInstanceOf[Variable] } catch {
        case exn : Exception => throw mathExnMsg(e, "expected variable in quantifier but found other expr")
      }
      val formula = try{formulaAsExpr.asInstanceOf[Formula]} catch {
        case exn : Exception => throw mathExnMsg(e, "Expected formula in quantifier but found other expression.")
      }
      
      //code clone
      if(isThing(e, MathematicaSymbols.FORALL)) {
        Forall(Seq(variable), formula)
      }
      else if(isThing(e, MathematicaSymbols.EXISTS)) {
        Exists(Seq(variable), formula)
      }
      else {
        throw mathExnMsg(e, "Tried to convert a quantifier-free expression using convertQuantifier. The check in fromMathematica must be wrong.")
      }
    }
  }
  
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
    "args:\t" + {if(e.args().size == 0) { "empty" } else {e.args().map(_.toString).reduce(_+","+_)}} +
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
  def fromKeYmaera(e : KExpr) = e match {
    case t : Term => convertTerm(t)
    case t : Formula => convertFormula(t)
  }

  /** 
   * Converts a KeYmaera terms to a Mathematica expression.
   */
  def convertTerm(t : Term) : MExpr = {
    def flattenSort(s: Sort): List[Sort] = s match {
      case Tuple(ls, rs) => ls :: rs :: Nil
      case _ => s :: Nil
    }

    require(t.sort == Real || t.sort == Unit || flattenSort(t.sort).forall(_ == Real), "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      case FuncOf(fn, child) => convertFnApply(fn, child)
      case Neg(c) => new MExpr(MathematicaSymbols.MINUSSIGN, Array[MExpr](convertTerm(c)))
      case Plus(l, r) => convertAdd(l, r)
      case Minus(l, r) => convertSubtract(l, r)
      case Times(l, r) => convertMultiply(l, r)
      case Divide(l, r) => convertDivide(l, r)
      case Power(l, r) => convertExp(l, r)
      case Differential(c) => convertDerivative(c)
      case DifferentialSymbol(c) => convertDerivative(c)
      case Number(n) => new MExpr(n.underlying())
      case Pair(l, r) => convertPair(l, r)
      case t: Variable => convertNS(t)
    }
  }
  
  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  def convertFormula(f : Formula) : MExpr = f match {
    case And(l,r) => convertAnd(l,r)
    case Equiv(l,r) => convertEquiv(l,r)
    case Imply(l,r) => convertImply(l,r)
    case Or(l,r) => convertOr(l,r)
    case Equal(l,r) => convertEquals(l,r)
    case NotEqual(l,r) => convertNotEquals(l,r)
    case LessEqual(l,r) => convertLessEqual(l,r)
    case Less(l,r) => convertLessThan(l,r)
    case GreaterEqual(l,r) => convertGreaterEqual(l,r)
    case Greater(l,r) => convertGreaterThan(l,r)
    case False => MathematicaSymbols.FALSE
    case True => MathematicaSymbols.TRUE
    case Not(phi) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertFormula(phi)))
    case Exists(vs, phi) => convertExists(vs,phi)
    case Forall(vs, phi) => convertForall(vs,phi)
  }
  
  def convertAdd(l : Term, r : Term) = {
    val args = Array[MExpr](convertTerm(l), convertTerm(r))
    new MExpr(MathematicaSymbols.PLUS, args)
  }
  def convertSubtract(l : Term, r: Term) = {
    val args = Array[MExpr](convertTerm(l), convertTerm(r))
    new MExpr(MathematicaSymbols.MINUS, args)
  }
  def convertMultiply(l : Term, r: Term) = {
    val args = Array[MExpr](convertTerm(l), convertTerm(r))
    new MExpr(MathematicaSymbols.MULT, args)
  }
  def convertDivide(l : Term, r: Term) = {
    val args = Array[MExpr](convertTerm(l), convertTerm(r))
    new MExpr(MathematicaSymbols.DIV, args)
  }
  def convertExp(l : Term, r: Term) = {
    val args = Array[MExpr](convertTerm(l), convertTerm(r))
    new MExpr(MathematicaSymbols.EXP, args)
  }
  def convertFnApply(fn: Function, child: Term) = child match {
    case Nothing => convertNS(new Function(NameConversion.CONST_FN_PREFIX + fn.name, fn.index, fn.domain, fn.sort))
    case _ =>
      val args = Array[MExpr](convertNS(fn), new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(child))))
      new MExpr(MathematicaSymbols.APPLY, args)
  }
  def convertDerivative(t:Term) = {
    val args = Array[MExpr](convertTerm(t))
    new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), args)
  }

  /** Converts a pair of terms to Mathematica */
  def convertPair(l: Term, r: Term): MExpr = {
    //@todo handle nested pairs (flatten to a list?)
    new MExpr(Expr.SYM_LIST, Array[MExpr](convertTerm(l), convertTerm(r)))
  }
  
  /**
   * Converts a named symbol into Mathematica
   */
  def convertNS(ns : NamedSymbol) = {
    val result = NameConversion.toMathematica(ns)
    if(!result.symbolQ()) {
      throw new Exception("Expected named symbol to be a symbol, but it was not.")
    }
    result
  }

  def convertExists(vs:Seq[NamedSymbol],f:Formula) = {
    val (vars, formula) = collectVarsExists(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(convertNS).toArray)
    new MExpr(MathematicaSymbols.EXISTS, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsExists(vsSoFar:Seq[NamedSymbol],candidate:Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Exists(nextVs, nextf) =>  collectVarsExists(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }

  def convertForall(vs:Seq[NamedSymbol],f:Formula) = {
    val (vars, formula) = collectVarsForall(vs, f)
    val variables = new MExpr(MathematicaSymbols.LIST, vars.map(convertNS).toArray)
    new MExpr(MathematicaSymbols.FORALL, Array[MExpr](variables, convertFormula(formula)))
  }
  private def collectVarsForall(vsSoFar:Seq[NamedSymbol],candidate:Formula) : (Seq[NamedSymbol], Formula) = {
    candidate match {
      case Forall(nextVs, nextf) =>  collectVarsForall(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar,candidate)
    }
  }
  
  def convertEquals(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.EQUALS, args)
  }
  def convertGreaterEqual(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.GREATER_EQUALS, args)
  }
  def convertLessEqual(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.LESS_EQUALS, args)
  }
  def convertNotEquals(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.UNEQUAL, args)
  }
  def convertLessThan(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.LESS, args)
  }
  def convertGreaterThan(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.GREATER, args)
  }
  
  def convertAnd(left:Formula, right:Formula) = {
    val args = Array[MExpr](convertFormula(left), convertFormula(right))
    new MExpr(MathematicaSymbols.AND, args)
  }
  def convertEquiv(left:Formula, right:Formula) = {
    val args = Array[MExpr](convertFormula(left), convertFormula(right))
    new MExpr(MathematicaSymbols.BIIMPL, args)
  }
  def convertImply(left:Formula, right:Formula) = {
    val args = Array[MExpr](convertFormula(left), convertFormula(right))
    new MExpr(MathematicaSymbols.IMPL, args)
  }
  def convertOr(left:Formula, right:Formula) = {
    val args = Array[MExpr](convertFormula(left), convertFormula(right))
    new MExpr(MathematicaSymbols.OR, args)
  }
  
  def keyExn(e: KExpr) : Exception =
    new ConversionException("conversion not defined for KeYmaera expr: " + PrettyPrinter.printer(e))
}
