package edu.cmu.cs.ls.keymaera.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.math.BigDecimal


class ConversionException(s:String) 
  extends Exception(s)
class MathematicaComputationFailedException(e:com.wolfram.jlink.Expr) 
  extends ConversionException(e.toString())
class MathematicaComputationAbortedException(e:com.wolfram.jlink.Expr) 
  extends ConversionException(e.toString())

object TranslationConstants {

}

/**
 * Handles conversion to/from Mathematica.
 * 
 * TODO-nrf assertion that maskName and removeMask are inverses (compose to
 * id).
 *
 * @author Nathan Fulton
 */
object NamedSymbolConversion {
  private val PREFIX = "KeYmaera"
  private val SEP    = "$beginIndex$"
  private val MUNDERSCORE = "$underscore$" //Mathematica Underscore

  private def maskIdentifier(name : String) = {
    //Ensure that none of the "special" strings occur in the variable name.
    if(name.contains(MUNDERSCORE)) {
      throw new ConversionException("Please do not use the string " + MUNDERSCORE + " in your variable names.")
    }
    
    //Do replacements.
    name.replace("_", MUNDERSCORE)
  }

  private def removeMask(name : String) = {
    name.replace(PREFIX, "").replace(MUNDERSCORE, "_")
  }

  def toMathematica(ns : NamedSymbol) : com.wolfram.jlink.Expr = {
    val identifier = PREFIX + maskIdentifier(ns.name)
    val fullName   = ns.index match {
      case Some(idx) => identifier + SEP + idx.toString()
      case None      => identifier
    }
    new com.wolfram.jlink.Expr(com.wolfram.jlink.Expr.SYMBOL, fullName)
  }

  def toKeYmaera(e : com.wolfram.jlink.Expr) = {
    val nameStr = e.asString() //Note: This cold be KeYmaeravarName or KeYmaeravarName$beginIndex$N
    if(nameStr.contains(SEP)) {
      val parts = nameStr.split(SEP)
      if(parts.size != 2) {
        throw new ConversionException("Received a non-masked name from Mathematica. Perhaps Mathematica returned an expression with bound variables?")
      }
      val (name, index) = (parts.head, parts.last)
      Variable(removeMask(name), Some(Integer.parseInt(index)), Real)
    }
    else {
      Variable(removeMask(nameStr), None, Real)
    }
  }

}

/**
 * Converts com.wolfram.jlink.Expr -> edu.cmu...keymaera.core.Expr
 * @TODO the correctness of quantifier handling is non-obvious
 * 
 * @author Nathan Fulton
 */
object MathematicaToKeYmaera {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaera.core.Expr

  /**
   * Converts a Mathematica expression to a KeYmaera expression.
   */
  def fromMathematica(e : com.wolfram.jlink.Expr) 
    : edu.cmu.cs.ls.keymaera.core.Expr = 
  {
    //Numbers
    if(e.numberQ() && !e.rationalQ()) {
      try {
        val number = e.asBigDecimal()
        Number(Real, BigDecimal(number))
      }
      catch {
        case exn : NumberFormatException => throw mathExnMsg(e, "Could not convert number: " + e.toString())
        case exn : ExprFormatException => throw mathExnMsg(e, "Could not represent number as a big decimal: " + e.toString())
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
    else if(isThing(e,MathematicaSymbols.TRUE))    True
    else if(isThing(e,MathematicaSymbols.FALSE))   False
    else if(isThing(e, MathematicaSymbols.AND))    convertAnd(e)
    else if(isThing(e, MathematicaSymbols.OR))     convertOr(e)
    else if(isThing(e, MathematicaSymbols.NOT))    convertNot(e)
    else if(isThing(e, MathematicaSymbols.IMPL))   convertImpl(e)
    else if(isThing(e, MathematicaSymbols.BIIMPL)) convertEquiv(e)
    
    //Relations
    else if(isThing(e,MathematicaSymbols.EQUALS))          convertEquals(e)
    else if(isThing(e, MathematicaSymbols.UNEQUAL))        convertNotEquals(e)
    else if(isThing(e, MathematicaSymbols.GREATER))        convertGreaterThan(e)
    else if(isThing(e, MathematicaSymbols.GREATER_EQUALS)) convertGreaterEquals(e)
    else if(isThing(e, MathematicaSymbols.LESS))           convertLessThan(e)
    else if(isThing(e, MathematicaSymbols.LESS_EQUALS))    convertLessEquals(e)
    
    //Variables. This case intentionally comes last, so that it doesn't gobble up
    //and keywords that were not declared correctly in MathematicaSymbols (should be none)
    else if(e.symbolQ() && !MathematicaSymbols.keywords.contains(e.asString()))
    {
      convertName(e)
    }
    else {
      throw mathExn(e) //Other things to handle: integrate, rule, minussign, possibly some list.
    }
  }
  
  def convertName(e : MExpr) = {
    NamedSymbolConversion.toKeYmaera(e)
  }

  def convertAddition(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Add(Real,l,r))
  }
  def convertDivision(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Divide(Real,l,r))
  }
  def convertSubtraction(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Subtract(Real,l,r))
  }
  def convertMultiplication(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Multiply(Real,l,r))
  }
  def convertExponentiation(e : MExpr) = {
    val subexpressions = e.args().map(fromMathematica)
    val asTerms = subexpressions.map(_.asInstanceOf[Term])
    asTerms.reduce((l,r) => Exp(Real,l,r))
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
    val staggeredPairs = makeOverlappingPairs(subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => Equals(Real,pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertNotEquals(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => NotEquals(Real,pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertGreaterEquals(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => GreaterEquals(Real,pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertLessEquals(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => LessEquals(Real,pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertLessThan(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => LessThan(Real,pair._1,pair._2))
    staggeredFormauls.reduce((l,r) => And(l,r))
  }
  def convertGreaterThan(e : MExpr) : Formula = {
    val subterms = e.args().map(fromMathematica(_).asInstanceOf[Term])
    val staggeredPairs = makeOverlappingPairs(subterms)
    val staggeredFormauls : Seq[Formula] = 
      staggeredPairs.map(pair => GreaterThan(Real,pair._1,pair._2))
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
      val quantifiedVars = quantifiedVariables.args().map(n => convertName(n))

      //Recurse on the body of the expression.
      val bodyAsExpr = fromMathematica(e.args().last)
      val bodyOfQuantifier = try {
        bodyAsExpr.asInstanceOf[Formula]
      }
      catch {
        case e : Exception => 
          throw new ConversionException("Expected a formula in the body of the quanfiier, but found a non-variable expression: " + KeYmaeraPrettyPrinter.stringify(bodyAsExpr))
      }
        
      //Create the final expression.
      if(isThing(e, MathematicaSymbols.FORALL)) {
        Forall(quantifiedVars, bodyOfQuantifier)
      }
      else if(isThing(e, MathematicaSymbols.EXISTS)) {
        Exists(quantifiedVars, bodyOfQuantifier)
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
    e.toString().equalsIgnoreCase("$Aborted") ||
    e.toString().equalsIgnoreCase("Abort[]")
  }
  
  def isFailed(e : com.wolfram.jlink.Expr) = {
    e.toString().equalsIgnoreCase("$Failed")
  }

  def failExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationFailedException(e)
  def abortExn(e:com.wolfram.jlink.Expr) = new MathematicaComputationAbortedException(e)

  def mathExnMsg(e:MExpr, s:String) : Exception =
    new ConversionException("Conversion of " + e.toString() + " failed because: " + s)
  
  def mathExn(e:com.wolfram.jlink.Expr) : Exception = 
    new ConversionException("conversion not defined for Mathematica expr: " + e.toString() + " with infos: " + mathInfo(e))
  
  def mathInfo(e : com.wolfram.jlink.Expr) : String = {
    "args:\t" + {if(e.args().size == 0) { "empty" } else {e.args().map(_.toString()).reduce(_+","+_)}} +
    "\n" +
    "toString:\t" + e.toString()
  }
}
  
/**
 * Converts KeYmaeara core.Expr terms and formulas into Mathematica Expr objects.
 * @author Nathan Fulton
 */
object KeYmaeraToMathematica {
  type MExpr = com.wolfram.jlink.Expr
  type KExpr = edu.cmu.cs.ls.keymaera.core.Expr

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  def fromKeYmaera(e : KExpr) = e match {
    case t : Term => convertTerm(t)
    case t : Formula => convertFormula(t)
    case _ => ???
  }

  /** 
   * Converts a KeYmaera terms to a Mathematica expression.
   */
  def convertTerm(t : Term) : MExpr = {
    require(t.sort == Real, "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      case t: Apply => ???
      case t: IfThenElseTerm => ???
      case t: Pair => ???
      case t: Right => ???
      case t: Left => ???
      case Add(s, l, r) => convertAdd(l, r)
      case Subtract(s, l, r) => convertSubtract(l, r)
      case Multiply(s, l, r) => convertMultiply(l, r)
      case Divide(s, l, r) => convertDivide(l, r)
      case Exp(s, l, r) => convertExp(l, r)
      case Derivative(s, c) => convertDerivative(c)
      case False() => MathematicaSymbols.FALSE
      case True() => MathematicaSymbols.TRUE
      case Neg(s, c) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertTerm(c)))
      case Number(s, n) => new MExpr(n.underlying())
      case t: Variable => convertNS(t)
    }
  }
  
  /**
   * Converts KeYmaera formulas into Mathematica objects
   */
  def convertFormula(f : Formula) : MExpr = f match {
    case f : ApplyPredicate => ???
    case f : BinaryFormula => f match {
      case And(l,r) => convertAnd(l,r)
      case Equiv(l,r) => convertEquiv(l,r)
      case Imply(l,r) => convertImply(l,r)
      case Or(l,r) => convertOr(l,r)
    }
    case f : BinaryRelation => f match {
      case f : ProgramEquals => ???
      case f : ProgramNotEquals => ???
      case Equals(s,l,r) => convertEquals(l,r)
      case NotEquals(s,l,r) => convertNotEquals(l,r)
      case LessEquals(s,l,r) => convertLessEquals(l,r)
      case LessThan(s,l,r) => convertLessThan(l,r)
      case GreaterEquals(s,l,r) => convertGreaterEquals(l,r)
      case GreaterThan(s,l,r) => convertGreaterThan(l,r)      
    }
    case t : Modality => ???
    case t : Finally => ???
    case t : FormulaDerivative => ??? //of?
    case t : Globally => ???
    case False() => MathematicaSymbols.FALSE
    case True() => MathematicaSymbols.TRUE
    case PredicateConstant(name,index) => new MExpr(name)
    case Not(f) => new MExpr(MathematicaSymbols.NOT, Array[MExpr](convertFormula(f)))
    case Exists(vs, f) => convertExists(vs,f)
    case Forall(vs, f) => convertForall(vs,f)
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
  def convertDerivative(t:Term) = {
    val args = Array[MExpr](convertTerm(t))
    new MExpr(MathematicaSymbols.DERIVATIVE, args)
  }
  
  /**
   * Converts a named symbol into Mathematica
   */
  def convertNS(ns : NamedSymbol) = {
    val result = NamedSymbolConversion.toMathematica(ns)
    if(!result.symbolQ()) {
      throw new Exception("Expected named symbol to be a symbol, but it was not.")
    }
    result
  }
  
  def convertExists(vs:Seq[NamedSymbol],f:Formula) = {
    val variables = new MExpr(MathematicaSymbols.LIST, vs.map(convertNS).toArray)
    val formula = convertFormula(f)
    new MExpr(MathematicaSymbols.EXISTS, Array[MExpr](variables, formula))
  }
  def convertForall(vs:Seq[NamedSymbol],f:Formula) = {
    val variables = new MExpr(MathematicaSymbols.LIST, vs.map(convertNS).toArray)
    val formula = convertFormula(f)
    new MExpr(MathematicaSymbols.FORALL, Array[MExpr](variables, formula))
  }
  
  def convertEquals(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.EQUALS, args)
  }
  def convertGreaterEquals(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.LESS_EQUALS, args)
  }
  def convertLessEquals(left:Term,right:Term) = {
    val args = Array[MExpr](convertTerm(left), convertTerm(right))
    new MExpr(MathematicaSymbols.GREATER_EQUALS, args)
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
  
  def keyExn(e:edu.cmu.cs.ls.keymaera.core.Expr) : Exception = 
    new ConversionException("conversion not defined for KeYmaera expr: " + KeYmaeraPrettyPrinter.stringify(e))
}
