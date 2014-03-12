package edu.cmu.cs.ls.keymaera.parser

import edu.cmu.cs.ls.keymaera.core._

/**
 * Usage: KeYmaeraPrettyPrinter.stringify(e);
 * @author Nathan Fulton
 */
object KeYmaeraPrettyPrinter {
  import edu.cmu.cs.ls.keymaera.parser.ParseSymbols._
  
  def stringify(e:Expr) = prettyPrinter(e)
  
  def sortPrinter(s:Sort):String = "type" //TODO
    
  def prettyPrinter(expressionToPrint:Expr):String = expressionToPrint match {
    //arith
  	case Add(s,l,r) => recInfix(l,r,PLUS)
    case Multiply(s,l,r) => recInfix(l,r,MULTIPLY)
    case Divide(s,l,r) => recInfix(l,r,DIVIDE)
    case Subtract(s,l,r) => recInfix(l,r,MINUS)
    
    //boolean ops
    case And(l,r) => recInfix(l,r,AND)
    case Or(l,r) => recInfix(l,r,OR)
    case Not(e) => recPrefix(e,NEGATE)
    case Imply(l,r) =>  recInfix(l,r,ARROW)
    //Now, alphabetically down the type hierarchy (TODO clean this up so that things
    //are grouped in a reasonable way.)
    
    case Apply(function,child) => 
      prettyPrinter(function) + "(" + prettyPrinter(child) + ")"
    
    case ApplyPredicate(function,child) => 
      prettyPrinter(function) + "(" + prettyPrinter(child) + ")"

    case Assign(l,r) => recInfix(l,r,ASSIGN)
    
    case BoxModality(p,f) => BOX_OPEN + prettyPrinter(p) + BOX_CLOSE + prettyPrinter(f)
    case ContEvolve(child) => OPEN_CBRACKET + prettyPrinter(child) + CLOSE_CBRACKET
    case Derivative(s, child) => recPostfix(child, PRIME)
    case DiamondModality(p,f) => DIA_OPEN + prettyPrinter(p) + DIA_CLOSE + prettyPrinter(f)
    case Equiv(l,r) => recInfix(l,r,EQUIV)
    
    case Exp(s,l,r) => recInfix(l,r,EXP)
    
    
    //BinaryProgram
    case Choice(l,r) => recInfix(l,r,CHOICE)
    case Parallel(l,r) => recInfix(l,r,PARALLEL)
    case Sequence(l,r) => recInfix(l,r,SCOLON)
    
    //BinaryRelation
    case Equals(s,l,r) => recInfix(l,r,EQ) 
    case GreaterEquals(s,l,r) => recInfix(l,r,GEQ)
    case LessEquals(s,l,r) => recInfix(l,r,LEQ)
    case LessThan(s,l,r) => recInfix(l,r,LT)
    case GreaterThan(s,l,r) => recInfix(l,r,GT)
    case NotEquals(s,l,r) => recInfix(l,r,NEQ)
    
    case IfThen(l,r) => "if " + recInfix(l,r," then ")
    case IfThenElse(test,l,r) => "if " + 
      recInfix(test,l," then ") + 
      " else " + 
      groupIfNotAtomic(r, prettyPrinter(r))
      
    case Pair(s,l,r) => PAIR_OPEN + recInfix(l,r,COMMA) + PAIR_CLOSE
    
    case False => FALSE
    case True => TRUE
    
    case PredicateConstant(name,_) => name
    case ProgramConstant(name, _) => name
    case Variable(name, _,_) => name
    
    case Function(name,index,domain,argSorts) => name
    
    /** Normal form ODE data structures
 * \exists R a,b,c. (\D{x} = \theta & F)
 */
    case NFContEvolve(vars,x,theta,f) => EXISTS + 
      vars.map(v => groupIfNotAtomic(v, prettyPrinter(v))).reduce(_ + "," + _) +
      groupIfNotAtomic(theta, prettyPrinter(theta)) +
      groupIfNotAtomic(f, prettyPrinter(f))
    
    case Number(n) => Number.unapply(expressionToPrint) match {
      case Some((ty, number:BigDecimal)) => number.toString()
      case _ => ???
      
    }
    
    
    case Neg(s,e) => NEGATIVE + recurse(e)
    case Test(e) => TEST + recurse(e)
    
    case Loop(p) => recurse(p) + KSTAR
    
    //These we cannot pattern match on...
//    case edu.cmu.cs.ls.keymaera.core.Quantifier(variables, child)
//    case FormulaDerivative(f) => recPostfix(f, PRIME)
//    case edu.cmu.cs.ls.keymaera.core.Finally(f) => BOX + recurse(e)
//    case edu.cmu.cs.ls.keymaera.core.Globally(f) => DIA + recurse(e)
//    case Left(domain,child) => ???
//    case Right(domain,child) => ???
    
    //And these we can pattern match on but are not implemented yet.
    case Modality(_,_) => ???
    case Exists(_,_) => ???
  }
  
  def recurse(e:Expr) = groupIfNotAtomic(e, prettyPrinter(e))
  
  def recPrefix(e:Expr, sign:String):String = 
    sign + groupIfNotAtomic(e,prettyPrinter(e))
    
  def recInfix(l:Expr,r:Expr,sign:String):String = 
    groupIfNotAtomic(l,prettyPrinter(l)) + 
    sign + 
    groupIfNotAtomic(l,prettyPrinter(r)) 
  
  def recPostfix(e:Expr, sign:String):String = 
    groupIfNotAtomic(e, prettyPrinter(e)) + sign
  
  def groupIfNotAtomic(e:Expr,s:String):String = s //TODO 

  
//  def recPrefix = recApplyPrefix(prettyPrinter)_
//  def recInfix = recApplyInfix(prettyPrinter)_
//  
//  def recApplyPrefix[T <: Expr](fn:T=>String)(e:T, sign:String):String = 
//    sign + groupIfNotAtomic(e,fn(e))
//    
//  def recApplyInfix[T <: Expr](fn:T=>String)(l:T,r:T,sign:String):String = 
//    groupIfNotAtomic(l,fn(l)) + 
//    sign + 
//    groupIfNotAtomic(l,fn(r)) 
//  object TermPrettyPrinter {
//    
//	  /**
//	   * @parameter e - the expression to pretty print
//	   * @returns pretty printed expression.
//	   */
//	  def prettyPrint(e:Term):String = e match {
//	    case Add(sort,l,r) =>  recInfix(l,r,PLUS)
//	  }
//	  
//	  val recInfix = recApplyInfix[Term](prettyPrint)_
//	  val recPrefix = recApplyPrefix[Term](prettyPrint)_
//  }
//  
}