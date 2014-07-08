package edu.cmu.cs.ls.keymaera.parser

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._

/**
 * Usage: KeYmaeraPrettyPrinter.stringify(e);
 * @author Nathan Fulton
 */
object KeYmaeraPrettyPrinter {
  import edu.cmu.cs.ls.keymaera.parser.ParseSymbols._
  
  def stringify(e:Expr) = prettyPrinter(e)
      
  def header(ns : List[NamedSymbol]) : String = ??? 
    
  private def sortPrinter(s:Sort):String = s match {
    case Bool => "B"
    case s : EnumT => s.name
    case GameSort => ???
    case ProgramSort => "P"
    case Real => "R"
  }

  private def endsWithColon(e:Expr, parent:Expr)  = e match {
    case Assign(_) => !needsParens(e,parent)
    case Test(_) => !needsParens(e,parent)
    case NDetAssign(_) => !needsParens(e,parent)
    case ContEvolve(_) => !needsParens(e,parent)
    case _ => false
  }

  private def prettyPrinter(expressionToPrint:Expr):String = expressionToPrint match {
    //arith
  	case Add(s,l,r) => recInfix(l,r,expressionToPrint,PLUS)
    case Multiply(s,l,r) => recInfix(l,r,expressionToPrint,MULTIPLY)
    case Divide(s,l,r) => recInfix(l,r,expressionToPrint,DIVIDE)
    case Subtract(s,l,r) => recInfix(l,r,expressionToPrint,MINUS)
    
    //quantifiers
    case Forall(variables, child) => {
      assert(!variables.isEmpty, "no empty universal quantifiers for " + child);
      FORALL + " " +
      variables.map(prettyPrinter(_)).mkString(",") +
      "." + 
      parensIfNeeded(child, expressionToPrint)
    }
    
    case Exists(variables, child) => {
      assert(!variables.isEmpty, "no empty existential quantifiers for " + child);
      EXISTS + " " +
      variables.map(prettyPrinter(_)).mkString(",") +
      "." + 
      parensIfNeeded(child, expressionToPrint)
    }
    
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
        case And(_,_) => paren(prettyPrinter(r))
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
        case Or(_,_) => paren(prettyPrinter(r))
        case _			=> prettyPrinter(r)
      }
      leftString + OR + rightString
    }
    
    case Not(e) => recPrefix(e,NEGATE)
    
    case Imply(l,r) =>  {
      parensIfNeeded(l,expressionToPrint) + ARROW + 
      parensIfNeeded(r,expressionToPrint)
    }
    
    //Now, alphabetically down the type hierarchy (TODO clean this up so that things
    //are grouped in a reasonable way.)
    
    case Apply(function,child) => 
      parensIfNeeded(function,expressionToPrint) + "(" + prettyPrinter(child) + ")"
    
    case ApplyPredicate(function,child) => 
      parensIfNeeded(function,expressionToPrint) + "(" + prettyPrinter(child) + ")"

    case Assign(l,r) => recInfix(l,r,expressionToPrint, ASSIGN) + SCOLON
    case NDetAssign(l) => prettyPrinter(l) + ASSIGN + KSTAR + SCOLON
    
    case BoxModality(p,f) => BOX_OPEN + parensIfNeeded(p,expressionToPrint) + BOX_CLOSE + parensIfNeeded(f,expressionToPrint)
    case ContEvolve(child) => prettyPrinter(child) + SCOLON 
    case Derivative(s, child) => recPostfix(child, PRIME)
    case DiamondModality(p,f) => DIA_OPEN + parensIfNeeded(p,expressionToPrint) + DIA_CLOSE +parensIfNeeded(f,expressionToPrint)
    case Equiv(l,r) => recInfix(l,r,expressionToPrint,EQUIV)
    

    case Exp(s,l,r) => recInfix(l,r,expressionToPrint,EXP)
    
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
      val leftString = parensIfNeeded(l, Sequence(l,r))
      val rightString = parensIfNeeded(r, Sequence(l,r))
      if(!endsWithColon(l,Sequence(l,r))) {
        leftString + SCOLON + rightString
      }
      else {
        leftString + rightString
      }
    } 
    
    //BinaryRelation
    //TODO is this OK?
    case Equals(s,l,r) => prettyPrinter(l) + EQ + prettyPrinter(r) 
    case GreaterEqual(s,l,r) => prettyPrinter(l) + GEQ + prettyPrinter(r)
    case LessEqual(s,l,r) => prettyPrinter(l) + LEQ + prettyPrinter(r)
    case LessThan(s,l,r) => prettyPrinter(l) + LT + prettyPrinter(r)
    case GreaterThan(s,l,r) => prettyPrinter(l) + GT + prettyPrinter(r)
    case NotEquals(s,l,r) => prettyPrinter(l) + NEQ + prettyPrinter(r)
    
    case IfThen(l,r) => "if " + "(" + prettyPrinter(l) + ") then " + prettyPrinter(r) + " fi"
    case IfThenElse(test,l,r) => 
      "if " + "(" + prettyPrinter(test) + ") then " + 
      prettyPrinter(l) + " else " + prettyPrinter(r) + " fi"
      
    case Pair(s,l,r) => PAIR_OPEN + recInfix(l,r,expressionToPrint,COMMA) + PAIR_CLOSE
    
    case False() => FALSE
    case True() => TRUE
    
    case PredicateConstant(name,i) => name + (i match {
      case Some(idx) => "_" + idx
      case None => ""
    })
    case ProgramConstant(name, i) => name + (i match {
      case Some(idx) => "_" + idx
      case None => ""
    })
    case Variable(name, i,_) => name + (i match {
      case Some(idx) => "_" + idx
      case None => ""
    })
    
    case Function(name,index,domain,argSorts) => name + (index match {
      case Some(idx) => "_" + idx
      case None => ""
    })

    /** Normal form ODE data structures
 * \exists R a,b,c. (\D{x} = \theta & F)
 */
    case NFContEvolve(vars,x,theta,f) => EXISTS + 
      vars.map(v => groupIfNotAtomic(v, prettyPrinter(v))).mkString(",") +
      groupIfNotAtomic(theta, prettyPrinter(theta)) +
      groupIfNotAtomic(f, prettyPrinter(f))
    
    case Number(n) => Number.unapply(expressionToPrint) match {
      case Some((ty, number:BigDecimal)) => number.toString()
      case _ => ???
      
    }
    
    
    case Neg(s,e) => NEGATIVE + recurse(e)
    case Test(e) => TEST + prettyPrinter(e) + SCOLON
    
    case Loop(p) => recurse(p) + KSTAR
   
    case FormulaDerivative(f) => recPostfix(f, PRIME)
    //These we cannot pattern match on...
//    case edu.cmu.cs.ls.keymaera.core.Quantifier(variables, child)
//    case edu.cmu.cs.ls.keymaera.core.Finally(f) => BOX + recurse(e)
//    case edu.cmu.cs.ls.keymaera.core.Globally(f) => DIA + recurse(e)
//    case Left(domain,child) => ???
//    case Right(domain,child) => ???
    
    //And these we can pattern match on but are not implemented yet.
    case Modality(_,_) => ???
    case Exists(_,_) => ???
    
    case _ => throw new Exception("Ended up in the _ case of the pretty printer for: " + expressionToPrint.getClass())
  }
  
  private def recurse(e:Expr) = groupIfNotAtomic(e, prettyPrinter(e))
  
  private def recPrefix(e:Expr, sign:String):String = 
    sign + groupIfNotAtomic(e,prettyPrinter(e))
    
  private def recInfix(l:Expr,r:Expr,parent:Expr,sign:String):String = 
    parensIfNeeded(l,parent) + 
    sign + 
    parensIfNeeded(r,parent) 
  
  private def recPostfix(e:Expr, sign:String):String = 
    groupIfNotAtomic(e, prettyPrinter(e)) + sign
  
  private def groupIfNotAtomic(e:Expr,s:String):String = {
    val parens = 
      if(e.isInstanceOf[Program]) {
        ("{","}")
      }
      else {
        ("(",")")
      }
    if(isAtomic(e)) s else parens._1+s+parens._2
  }
  
  private def parensIfNeeded(child:Expr, parent:Expr) = {
    val parens = 
      if(child.isInstanceOf[Program]) {
        ("{","}")
      }
      else {
        ("(",")")
      }
    if(needsParens(child,parent)) {
      parens._1 + prettyPrinter(child) + parens._2
    }
    else {
      prettyPrinter(child)
    }
  }
  
  /**
   * @TODO-nrf this is incredible hacky and needs to be replaced!
   */
  private def needsParens(child : Expr, parent : Expr) = {
    val precedenceDS =    
      //Terms.
      //TODO expP?
      Add.getClass().getCanonicalName() ::
      Subtract.getClass().getCanonicalName() ::
      Multiply.getClass().getCanonicalName() ::
      Divide.getClass().getCanonicalName() ::
      Exp.getClass().getCanonicalName() ::
      Neg.getClass().getCanonicalName() ::
      Derivative.getClass().getCanonicalName() ::
      Apply.getClass().getCanonicalName() ::
      Function.getClass().getCanonicalName() ::
      ProgramConstant.getClass().getCanonicalName() :: //real-valued.
      Number.getClass().getCanonicalName()   ::
      //Formulas
      Equiv.getClass().getCanonicalName() ::
      Imply.getClass().getCanonicalName()  ::
      Or.getClass().getCanonicalName() ::
      And.getClass().getCanonicalName() ::
      Not.getClass().getCanonicalName() :: 
      BoxModality.getClass().getCanonicalName()   ::
      DiamondModality.getClass().getCanonicalName() ::
      Modality.getClass().getCanonicalName() ::
      Forall.getClass().getCanonicalName() ::
      Exists.getClass().getCanonicalName() ::
      Equals.getClass().getCanonicalName() ::
      NotEquals.getClass().getCanonicalName() ::
      LessThan.getClass().getCanonicalName()    ::
      LessEqual.getClass().getCanonicalName()    ::
      GreaterEqual.getClass().getCanonicalName()    ::
      GreaterThan.getClass().getCanonicalName()    ::
      FormulaDerivative.getClass().getCanonicalName() ::
      PredicateConstant.getClass().getCanonicalName() ::
      ApplyPredicate.getClass().getCanonicalName() ::
      True.getClass().getCanonicalName() ::
      False.getClass().getCanonicalName() ::
      //Programs.
      Choice.getClass().getCanonicalName()     ::
      Sequence.getClass().getCanonicalName()   ::
      Loop.getClass().getCanonicalName() ::
      Assign.getClass().getCanonicalName() ::
      NDetAssign.getClass().getCanonicalName() ::
      Test.getClass().getCanonicalName() ::
      ContEvolve.getClass().getCanonicalName() ::
      ProgramConstant.getClass().getCanonicalName() ::
      Variable.getClass().getCanonicalName() ::
      Number.NumberObj.getClass().getCanonicalName() ::
      Nil
    val precedence = precedenceDS.map(_.replace("$",""))
    
    val childPrecedence = precedence.indexOf(child.getClass().getCanonicalName().replace("$",""))
    val parentPrecedence = precedence.indexOf(parent.getClass().getCanonicalName().replace("$",""))
    if(childPrecedence == -1) {
      val classes = precedence.reduce(_ + "\n" + _)
      throw new Exception("child not found in precedence list: " + child.getClass().getCanonicalName() + " in: " + "\n" + classes)
    }
    if(parentPrecedence == -1) {
      val classes = precedence.reduce(_ + "\n" + _)
      throw new Exception("parent not found in precedence list: " + parent.getClass().getCanonicalName() + " in: " + "\n" + classes)
    }
    childPrecedence < parentPrecedence
  }
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
    case Number(_) => true
    case Number(_,_) => true
    case Loop(p) => true 
    case Neg(s,e) => isAtomic(e)
    case Test(e) => isAtomic(e)
    case Not(e) => isAtomic(e)
    case FormulaDerivative(f) => isAtomic(f)
    
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

    case Forall(_,_) => true
    case Exists(_,_) => true
    case BoxModality(p,f) => true
    case ContEvolve(child) => true
    case Derivative(s, child) => true
    case DiamondModality(p,f) => true
    case Equiv(l,r) => false
    
    case Exp(s,l,r) => false
    
    
    //BinaryProgram
    case Choice(l,r) => false
    case Parallel(l,r) => false
    case Sequence(l,r) => false
    
    //BinaryRelation
    case Equals(s,l,r) => false
    case GreaterEqual(s,l,r) => false
    case LessEqual(s,l,r) => false
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
//    case edu.cmu.cs.ls.keymaera.core.Finally(f) => BOX + recurse(e)
//    case edu.cmu.cs.ls.keymaera.core.Globally(f) => DIA + recurse(e)
//    case Left(domain,child) => ???
//    case Right(domain,child) => ???
    
    //And these we can pattern match on but are not implemented yet.
    case Modality(_,_) => false
    case Exists(_,_) => false    
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Proofs
  //////////////////////////////////////////////////////////////////////////////
  def saveProof(file : java.io.File, f : Formula, ev : Evidence) = {
    val namesToDeclare = Helper.freeNames(f).toList
    val header = KeYmaeraPrettyPrinter.proofHeader(namesToDeclare)
    val fString = KeYmaeraPrettyPrinter.stringify(f)
    
    val fileContents = header + "Lemma " + "\"" + file.getName() + "\"." + "\n" +
    				   fString + "\nEnd.\n" + stringifyEvidence(ev)
    
    val pw = new java.io.PrintWriter(file)
    pw.write(fileContents)
    //@TODO Read and parse file again. Compare with f.
    pw.close()
  }
  
  def stringifyEvidence(e:Evidence) = e match {
    case e : ProofEvidence => ??? //TODO
    case e : ExternalEvidence => "External.\n\t" + e.file.toString() + "\nEnd."
    case e : ToolEvidence => "Tool.\n\t" + e.info.map( p => p._1 + "\t\"" + p._2 + "\"").mkString("\n\t") + "\nEnd."
  }
  
  def proofHeader(ns : List[NamedSymbol]) : String = {
      val varDecls = ns.map(symbol => sortProofPrinter(symbol.domain) + " " + symbol.name + ".")
      "Variables.\n" + varDecls.mkString("\n") + "\nEnd.\n"
  }
  private def sortProofPrinter(s:Sort):String = s match {
    case Bool => "T"
    case s : EnumT => s.name
    case GameSort => ???
    case ProgramSort => "P"
    case Real => "T"
    case Unit => "T" //FIXME is this the right thing to return?
  }

}
