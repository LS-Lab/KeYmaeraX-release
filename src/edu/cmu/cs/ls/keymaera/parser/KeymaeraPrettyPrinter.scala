package edu.cmu.cs.ls.keymaera.parser

import edu.cmu.cs.ls.keymaera.core._

/**
 * Usage: KeYmaeraPrettyPrinter.stringify(e);
 * @author Nathan Fulton
 */
object KeYmaeraPrettyPrinter {
  import edu.cmu.cs.ls.keymaera.parser.ParseSymbols._
  
  def stringify(e:Expr) = prettyPrinter(e)
  
  private def sortPrinter(s:Sort):String = "type" //TODO
    
  private def prettyPrinter(expressionToPrint:Expr):String = expressionToPrint match {
    //arith
  	case Add(s,l,r) => recInfix(l,r,PLUS)
    case Multiply(s,l,r) => recInfix(l,r,MULTIPLY)
    case Divide(s,l,r) => recInfix(l,r,DIVIDE)
    case Subtract(s,l,r) => recInfix(l,r,MINUS)
    
    //boolean ops
    case And(l,r) => {
      val leftString = l match {
        case Imply(_,_)	=> paren(prettyPrinter(l))
        case Or(_,_)	=> paren(prettyPrinter(l))
        case _			=> prettyPrinter(l)
      }
      val rightString = r match {
        case Or(_,_)	=> paren(prettyPrinter(r))
        case Imply(_,_)	=> paren(prettyPrinter(r))
        case _			=> prettyPrinter(r)
      }
      leftString + AND + rightString
    }
    
    case Or(l,r) => {
      val leftString = l match {
        case Imply(_,_)		=> paren(prettyPrinter(l))
        case And(_,_)		=> paren(prettyPrinter(l))
        case _				=> prettyPrinter(l)
      }
      val rightString = r match {
        case And(_,_)	=> paren(prettyPrinter(r))
        case Imply(_,_)	=> paren(prettyPrinter(r))
        case _			=> prettyPrinter(r)
      }
      leftString + OR + rightString
    }
    
    
    case Not(e) => recPrefix(e,NEGATE)
    
    case Imply(l,r) =>  {
      val rightString = prettyPrinter(r) 
      val leftString = l match {
        case Imply(_,_)	=> paren(prettyPrinter(l))
        case _				=> prettyPrinter(l)
      }
      leftString + ARROW + rightString
    }
    
    //Now, alphabetically down the type hierarchy (TODO clean this up so that things
    //are grouped in a reasonable way.)
    
    case Apply(function,child) => 
      prettyPrinter(function) + "(" + prettyPrinter(child) + ")"
    
    case ApplyPredicate(function,child) => 
      prettyPrinter(function) + "(" + prettyPrinter(child) + ")"

    case Assign(l,r) => prettyPrinter(l) + ASSIGN + recurse(r)
    
    case BoxModality(p,f) => BOX_OPEN + prettyPrinter(p) + BOX_CLOSE + prettyPrinter(f)
    case ContEvolve(child) => OPEN_CBRACKET + prettyPrinter(child) + CLOSE_CBRACKET
    case Derivative(s, child) => recPostfix(child, PRIME)
    case DiamondModality(p,f) => DIA_OPEN + prettyPrinter(p) + DIA_CLOSE + prettyPrinter(f)
    case Equiv(l,r) => recInfix(l,r,EQUIV)
    
    case Exp(s,l,r) => recInfix(l,r,EXP)
    
    //BinaryProgram
    case Choice(l,r) => {
      val leftString = l match {
        case Choice(ll,lr) => prettyPrinter(l)
        case _ => recurse(l)
      }
      val rightString = r match {
        case Choice(rl,rr) => prettyPrinter(r)
        case _ => recurse(r)
      }
      leftString + CHOICE + rightString
    }
    
    case Parallel(l,r) => {
      val leftString = l match {
        case Parallel(ll,lr) => prettyPrinter(l)
        case _ => recurse(l)
      }
      val rightString = r match {
        case Parallel(rl,rr) => prettyPrinter(r)
        case _ => recurse(r)
      }
      leftString + PARALLEL + rightString
    } 
    
    case Sequence(l,r) => {
      val leftString = l match {
        case Sequence(ll,lr) => prettyPrinter(l)
        case _ => recurse(l)
      }
      val rightString = r match {
        case Sequence(rl,rr) => prettyPrinter(r)
        case _ => recurse(r)
      }
      leftString + SCOLON + rightString
    } 
    
    //BinaryRelation
    //TODO is this OK?
    case Equals(s,l,r) => prettyPrinter(l) + EQ + prettyPrinter(r) 
    case GreaterEquals(s,l,r) => prettyPrinter(l) + GEQ + prettyPrinter(r)
    case LessEquals(s,l,r) => prettyPrinter(l) + LEQ + prettyPrinter(r)
    case LessThan(s,l,r) => prettyPrinter(l) + LT + prettyPrinter(r)
    case GreaterThan(s,l,r) => prettyPrinter(l) + GT + prettyPrinter(r)
    case NotEquals(s,l,r) => prettyPrinter(l) + NEQ + prettyPrinter(r)
    
    case IfThen(l,r) => "if " + recInfix(l,r," then ")
    case IfThenElse(test,l,r) => "if " + 
      recInfix(test,l," then ") + 
      " else " + 
      recurse(r)
      
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
  
  private def recurse(e:Expr) = groupIfNotAtomic(e, prettyPrinter(e))
  
  private def recPrefix(e:Expr, sign:String):String = 
    sign + groupIfNotAtomic(e,prettyPrinter(e))
    
  private def recInfix(l:Expr,r:Expr,sign:String):String = 
    groupIfNotAtomic(l,prettyPrinter(l)) + 
    sign + 
    groupIfNotAtomic(l,prettyPrinter(r)) 
  
  private def recPostfix(e:Expr, sign:String):String = 
    groupIfNotAtomic(e, prettyPrinter(e)) + sign
  
  private def groupIfNotAtomic(e:Expr,s:String):String = 
    if(isAtomic(e)) s else "("+s+")"
  
  /**
   * Returns true if this expression does NOT need to be placed in parens.
   */
  private def isAtomic(e:Expr):Boolean = e match {
    case False => true
    case True => true
    case PredicateConstant(name,_) => true
    case ProgramConstant(name, _) => true
    case Variable(name, _,_) => true
    case NFContEvolve(vars,x,theta,f) => true
    case Number(n) => true
    case Loop(p) => true 
    case Neg(s,e) => isAtomic(e)
    case Test(e) => isAtomic(e)
    case Not(e) => isAtomic(e)
    
      //arith
  	case Add(s,l,r) => false
    case Multiply(s,l,r) => false
    case Divide(s,l,r) => false
    case Subtract(s,l,r) => false
    
    //boolean ops
    case And(l,r) => false
    case Or(l,r) => false
    
    case Imply(l,r) =>  false
    //Now, alphabetically down the type hierarchy (TODO clean this up so that things
    //are grouped in a reasonable way.)
    
    case Apply(function,child) => false
    case ApplyPredicate(function,child) => false
    
    case Assign(l,r) => false
    
    case BoxModality(p,f) => false
    case ContEvolve(child) => false
    case Derivative(s, child) => false
    case DiamondModality(p,f) => false
    case Equiv(l,r) => false
    
    case Exp(s,l,r) => false
    
    
    //BinaryProgram
    case Choice(l,r) => false
    case Parallel(l,r) => false
    case Sequence(l,r) => false
    
    //BinaryRelation
    case Equals(s,l,r) => false
    case GreaterEquals(s,l,r) => false
    case LessEquals(s,l,r) => false
    case LessThan(s,l,r) => false
    case GreaterThan(s,l,r) => false
    case NotEquals(s,l,r) => false
    
    case IfThen(l,r) => false
    case IfThenElse(test,l,r) => false
      
    case Pair(s,l,r) => false
    
    case Function(name,index,domain,argSorts) => false
    
    /** Normal form ODE data structures
 * \exists R a,b,c. (\D{x} = \theta & F)
 */
    
    
    
    //These we cannot pattern match on...
//    case edu.cmu.cs.ls.keymaera.core.Quantifier(variables, child)
//    case FormulaDerivative(f) => recPostfix(f, PRIME)
//    case edu.cmu.cs.ls.keymaera.core.Finally(f) => BOX + recurse(e)
//    case edu.cmu.cs.ls.keymaera.core.Globally(f) => DIA + recurse(e)
//    case Left(domain,child) => ???
//    case Right(domain,child) => ???
    
    //And these we can pattern match on but are not implemented yet.
    case Modality(_,_) => false
    case Exists(_,_) => false    
  }

}