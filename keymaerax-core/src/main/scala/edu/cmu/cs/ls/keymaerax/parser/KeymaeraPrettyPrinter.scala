/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence


object KeYmaeraPrettyPrinter extends KeYmaeraPrettyPrinter(ParseSymbols) {

}

/**
 * Usage: KeYmaeraPrettyPrinter.stringify(e);
 * @author Nathan Fulton
 */
class KeYmaeraPrettyPrinter(symbolTable : KeYmaeraSymbols = ParseSymbols) extends (Expression => String) {
  def apply(e:Expression) = prettyPrinter(e)
  def stringify(e:Expression) = apply(e)

  def header(ns : List[NamedSymbol]) : String = ??? 
    
  private def sortPrinter(s:Sort):String = s match {
    case Bool        => "B"
    case Trafo       => "P"
    case Real        => "R"
    case Unit        => ???
    case _: ObjectSort  => ???
  }

  private def endsWithColon(e:Expression, parent:Expression)  = e match {
    case Assign(_, _) => !needsParens(e,parent, false )
    case Test(_) => !needsParens(e,parent, false )
    case AssignAny(_) => !needsParens(e,parent, false)
    case _: DifferentialProgram => !needsParens(e,parent, false)
    case _ => false
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Methods extracted from the main pretty printer because they might be parametric in the symbol used for equality
  // due to "check marks" on evolutions.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * This is extracted from the pretty printer because it is used in both the
   */
  private def processNFContEvolve(x: DifferentialSymbol, theta:Term, eqSymbol:String) =
    groupIfNotAtomic(x, prettyPrinter(x)) + eqSymbol + groupIfNotAtomic(theta, prettyPrinter(theta))

  private def prettyPrinter(expressionToPrint:Expression):String = expressionToPrint match {
    //arith
    case Neg(e) => symbolTable.NEGATIVE + recurse(e)
  	case Plus(l,r) => recInfix(l,r,expressionToPrint,symbolTable.PLUS, Some(LeftAssoc()))
    case Times(l,r) => recInfix(l,r,expressionToPrint,symbolTable.MULTIPLY, Some(LeftAssoc()))
    case Divide(l,r) => {
      //This is a recursive infix.
      symbolTable.divide(parensIfNeeded(l,expressionToPrint, false), parensIfNeeded(r,expressionToPrint, true))
    }
    case Minus(l,r) => recInfix(l,r,expressionToPrint,symbolTable.MINUS, Some(LeftAssoc()))
    
    //quantifiers
    case Forall(variables, child) => {
      assert(!variables.isEmpty, "no empty universal quantifiers for " + child);
      symbolTable.FORALL + " " +
      variables.map(prettyPrinter(_)).mkString(",") +
      "." + 
      parensIfNeeded(child, expressionToPrint, false)
    }
    
    case Exists(variables, child) => {
      assert(!variables.isEmpty, "no empty existential quantifiers for " + child);
      symbolTable.EXISTS + " " +
      variables.map(prettyPrinter(_)).mkString(",") +
      "." + 
      parensIfNeeded(child, expressionToPrint, false)
    }
    
    //boolean ops
    case And(l,r) => {
      val leftString = l match {
        case Imply(_,_)	=> symbolTable.paren(prettyPrinter(l))
        case Or(_,_)	=> symbolTable.paren(prettyPrinter(l))
        case _			=> prettyPrinter(l)
      }
      val rightString = r match {
        case Or(_,_)	=> symbolTable.paren(prettyPrinter(r))
        case Imply(_,_)	=> symbolTable.paren(prettyPrinter(r))
        case And(_,_) => symbolTable.paren(prettyPrinter(r))
        case _			=> prettyPrinter(r)
      }
      leftString + symbolTable.AND + rightString
    }
    
    case Or(l,r) => {
      val leftString = l match {
        case Imply(_,_)		=> symbolTable.paren(prettyPrinter(l))
        case And(_,_)		=> symbolTable.paren(prettyPrinter(l))
        case _				=> prettyPrinter(l)
      }
      val rightString = r match {
        case And(_,_)	=> symbolTable.paren(prettyPrinter(r))
        case Imply(_,_)	=> symbolTable.paren(prettyPrinter(r))
        case Or(_,_) => symbolTable.paren(prettyPrinter(r))
        case _			=> prettyPrinter(r)
      }
      leftString + symbolTable.OR + rightString
    }
    
    case Not(e) => recPrefix(e,symbolTable.NEGATE)
    
    case Imply(l,r) =>  {
      parensIfNeeded(l,expressionToPrint, false) + symbolTable.ARROW +
      parensIfNeeded(r,expressionToPrint, true)
    }
    
    //Now, alphabetically down the type hierarchy (TODO clean this up so that things
    //are grouped in a reasonable way.)
    
    case FuncOf(function,child) => child match {
      // cannot use parensIfNeeded, because that suppresses parentheses for variables and numbers
      case Pair(_, _) => prettyPrinter (function) + prettyPrinter (child)
      case Nothing => prettyPrinter(function) + "()"
      case Anything => prettyPrinter(function) + "(?)"
      case _ => prettyPrinter (function) + "(" + prettyPrinter (child) + ")"
    }
    
    case PredOf(function,child) => child match {
      // cannot use parensIfNeeded, because that suppresses parentheses for variables and numbers
      case Pair(_, _) => prettyPrinter (function) + prettyPrinter (child)
      case Nothing => prettyPrinter(function)
      case Anything => prettyPrinter(function) + "(?)"
      case _ => prettyPrinter (function) + "(" + prettyPrinter (child) + ")"
    }

    case PredicationalOf(predicational,child) => prettyPrinter(predicational) + "{" + prettyPrinter(child) + "}"

    case Assign(l,r) => recInfix(l,r,expressionToPrint, symbolTable.ASSIGN, None) + symbolTable.SCOLON
    case AssignAny(l) => prettyPrinter(l) + symbolTable.ASSIGN + symbolTable.KSTAR + symbolTable.SCOLON
    
    case Box(p,f) => symbolTable.BOX_OPEN + parensIfNeeded(p,expressionToPrint, false) + symbolTable.BOX_CLOSE + parensIfNeeded(f,expressionToPrint, false)
    case Differential(child) => {
      //(x)' should not print as x' in order to distinguish Differential(Variable(x)) from DifferentialSymbol(Variable(x))
      child match {
        case c : Variable => symbolTable.paren(prettyPrinter(c)) + symbolTable.PRIME
        case _            => recPostfix(child, symbolTable.PRIME)
      }
    }
    case Diamond(p,f) => symbolTable.DIA_OPEN + parensIfNeeded(p,expressionToPrint, false) + symbolTable.DIA_CLOSE +parensIfNeeded(f,expressionToPrint, false)
    case Equiv(l,r) => recInfix(l,r,expressionToPrint,symbolTable.EQUIV, Some(RightAssoc()))

    case Power(l, r) => recInfix(l,r,expressionToPrint,symbolTable.EXP, None)
    
    //BinaryProgram
    case c@Choice(l,r) => {
      val leftString = l match {
        // left choice in a choice needs parens, because ++ is right-associative
        case Choice(ll,lr) => "{" + prettyPrinter(l) + "}"
        case _ => recurse(l)
      }
      val rightString = r match {
        case Choice(rl,rr) => prettyPrinter(r)
        case _ => recurse(r)
      }
      leftString + symbolTable.CHOICE + rightString
    }

    case s@Compose(l,r) => {
      val leftString = l match {
        // left sequence in a sequence needs parens, because ; is right-associative
        case Compose(_, _) => "{" + parensIfNeeded(l, s, false) + "}"
        case _ => parensIfNeeded(l, s, false)
      }
      val rightString = parensIfNeeded(r, s, false)
      if(endsWithColon(l, s)) leftString + rightString
      else leftString + symbolTable.SCOLON + rightString
    }
    
    //BinaryRelation
    //TODO is this OK?
    case Equal(l,r) => prettyPrinter(l) + symbolTable.EQ + prettyPrinter(r)
    case GreaterEqual(l,r) => prettyPrinter(l) + symbolTable.GEQ + prettyPrinter(r)
    case LessEqual(l,r) => prettyPrinter(l) +symbolTable. LEQ + prettyPrinter(r)
    case Less(l,r) => prettyPrinter(l) + symbolTable.LT + prettyPrinter(r)
    case Greater(l,r) => prettyPrinter(l) + symbolTable.GT + prettyPrinter(r)
    case NotEqual(l,r) => prettyPrinter(l) + symbolTable.NEQ + prettyPrinter(r)

    case Pair(l,r) => symbolTable.PAIR_OPEN + recInfix(l,r,expressionToPrint,symbolTable.COMMA, None) + symbolTable.PAIR_CLOSE

    case False => symbolTable.FALSE
    case True => symbolTable.TRUE
    case ProgramConst(name) => name
    case Variable(name, i,_) => name + (i match {
      case Some(idx) => "_" + idx
      case None => ""
    })
    case DifferentialProgramConst(name) => name
    case DotTerm => "•"
    case Anything => "?"
    case Nothing => ""
    case DotFormula => "_"

    case Function(name,index,domain,argSorts) => name + (index match {
      case Some(idx) => "_" + idx
      case None => ""
    })

    case AtomicODE(x, theta) => processNFContEvolve(x, theta, symbolTable.EQ)

    case DiffAssign(x, theta) => x.name + (x.index match {
      case Some(idx) => "_" + idx
      case None => ""
    }) + symbolTable.PRIME + symbolTable.ASSIGN + prettyPrinter(theta)

    case p@DifferentialProduct(l, r) => {
      val leftString = parensIfNeeded(l, p, false,
        c => { val s = prettyPrinter(c); if (s.endsWith(symbolTable.SCOLON)) s.substring(0, s.length - 1) else s })
      val rightString = parensIfNeeded(r, p, false,
          c => { val s = prettyPrinter(c); if (s.endsWith(symbolTable.SCOLON)) s.substring(0, s.length - 1) else s })
          leftString + symbolTable.COMMA + rightString
    }

    case ODESystem(a, f) =>
      def printEvolDom(f: Formula) = f match {
        case True => ""
        case _ => " " + symbolTable.AND + " " + groupIfNotAtomic(f, prettyPrinter(f))
      }
      prettyPrinter(a) + printEvolDom(f) + symbolTable.SCOLON

    case Number(n) => n.toString()

    case Not(e) => symbolTable.NEGATIVE + recurse(e)
    case Test(e) => symbolTable.TEST + prettyPrinter(e) + symbolTable.SCOLON
    
    case Loop(p) => "{" + prettyPrinter(p) + "}" + symbolTable.KSTAR
   
    case DifferentialFormula(f) => recPostfix(f, symbolTable.PRIME)
    //These we cannot pattern match on...
//    case edu.cmu.cs.ls.keymaerax.core.Quantifier(variables, child)
//    case edu.cmu.cs.ls.keymaerax.core.Finally(f) => BOX + recurse(e)
//    case edu.cmu.cs.ls.keymaerax.core.Globally(f) => DIA + recurse(e)
//    case Left(domain,child) => ???
//    case Right(domain,child) => ???
    
    //And these we can pattern match on but are not implemented yet.
    case Exists(_,_) => ???

    case DifferentialSymbol(x : NamedSymbol) => x.name + (x.index match {
      case None => ""
      case Some(idx) => "_" + idx
    }) + symbolTable.PRIME
    
    case _ => throw new Exception("Ended up in the _ case of the pretty printer for: " + expressionToPrint.getClass())
  }
  
  private def recurse(e:Expression) = groupIfNotAtomic(e, prettyPrinter(e))
  
  private def recPrefix(e:Expression, sign:String):String =
    sign + groupIfNotAtomic(e,prettyPrinter(e))


  abstract class Assoc
  case class LeftAssoc() extends Assoc
  case class RightAssoc() extends Assoc

  private def recInfix(l:Expression,r:Expression,parent:Expression,sign:String, assoc : Option[Assoc]):String =
    parensIfNeeded(l,parent, assoc.getOrElse(false).isInstanceOf[RightAssoc]) + //sic
    sign + 
    parensIfNeeded(r,parent, assoc.getOrElse(false).isInstanceOf[LeftAssoc]) //sic
  
  private def recPostfix(e:Expression, sign:String):String =
    groupIfNotAtomic(e, prettyPrinter(e)) + sign
  
  private def groupIfNotAtomic(e:Expression,s:String):String = {
    val parens = 
      if(e.isInstanceOf[Program]) {
        ("{","}")
      }
      else {
        ("(",")")
      }
    if(isAtomic(e)) s else parens._1+s+parens._2
  }

  private def parensIfNeeded(child:Expression, parent:Expression, enforceAssociativity : Boolean, printer: Expression=>String = prettyPrinter) = {
    val parens =
      if(child.isInstanceOf[Program]) {
        ("{","}")
      }
      else {
        ("(",")")
      }
    if(needsParens(child,parent, enforceAssociativity)) {
      parens._1 + printer(child) + parens._2
    }
    else {
      printer(child)
    }
  }
  
  /**
   * @todo this is incredible hacky and needs to be replaced!
   */
  private def needsParens(child : Expression, parent : Expression, enforceAssociativity : Boolean) = {
    val precedenceDS =
      //Terms.
      //TODO expP?
      Neg.getClass.getCanonicalName ::
      Plus.getClass.getCanonicalName ::
      Minus.getClass.getCanonicalName ::
      Times.getClass.getCanonicalName ::
      Divide.getClass.getCanonicalName ::
      Power.getClass.getCanonicalName ::
      Not.getClass.getCanonicalName ::
      Differential.getClass.getCanonicalName ::
      FuncOf.getClass.getCanonicalName ::
      Function.getClass.getCanonicalName ::
      Pair.getClass.getCanonicalName ::
      ProgramConst.getClass.getCanonicalName :: //real-valued.
      Number.getClass.getCanonicalName   ::
      //Formulas
      Equiv.getClass.getCanonicalName ::
      Imply.getClass.getCanonicalName  ::
      Or.getClass.getCanonicalName ::
      And.getClass.getCanonicalName ::
      Not.getClass.getCanonicalName ::
      Box.getClass.getCanonicalName   ::
      Diamond.getClass.getCanonicalName ::
      Forall.getClass.getCanonicalName ::
      Exists.getClass.getCanonicalName ::
      Equal.getClass.getCanonicalName ::
      NotEqual.getClass.getCanonicalName ::
      Less.getClass.getCanonicalName    ::
      LessEqual.getClass.getCanonicalName    ::
      GreaterEqual.getClass.getCanonicalName    ::
      Greater.getClass.getCanonicalName    ::
      DifferentialFormula.getClass.getCanonicalName ::
      PredOf.getClass.getCanonicalName ::
      PredicationalOf.getClass.getCanonicalName :: //@TODO Check
      DotFormula.getClass.getCanonicalName :: //@TODO Check
      True.getClass.getCanonicalName ::
      False.getClass.getCanonicalName ::
      //Programs.
      Choice.getClass.getCanonicalName     ::
      Compose.getClass.getCanonicalName   ::
      Loop.getClass.getCanonicalName ::
      Assign.getClass.getCanonicalName ::
      DiffAssign.getClass.getCanonicalName ::
      AssignAny.getClass.getCanonicalName ::
      Test.getClass.getCanonicalName ::
      DifferentialProduct.getClass.getCanonicalName ::
      ODESystem.getClass.getCanonicalName ::
      AtomicODE.getClass.getCanonicalName ::
      ProgramConst.getClass.getCanonicalName ::
      DifferentialProgramConst.getClass.getCanonicalName ::
      DotTerm.getClass.getCanonicalName ::
      DifferentialSymbol.getClass.getCanonicalName ::
      Variable.getClass.getCanonicalName ::
      Number.getClass.getCanonicalName ::
      Nil
    val precedence = precedenceDS.map(_.replace("$",""))
    
    val childPrecedence = precedence.indexOf(child.getClass.getCanonicalName.replace("$",""))
    val parentPrecedence = precedence.indexOf(parent.getClass.getCanonicalName.replace("$",""))
    if(childPrecedence == -1) {
      val classes = precedence.reduce(_ + "\n" + _)
      throw new Exception("child not found in precedence list: " + child.getClass.getCanonicalName + " in: " + "\n" + classes)
    }
    if(parentPrecedence == -1) {
      val classes = precedence.reduce(_ + "\n" + _)
      throw new Exception("parent not found in precedence list: " + parent.getClass.getCanonicalName + " in: " + "\n" + classes)
    }

    if(!enforceAssociativity) {
      childPrecedence < parentPrecedence
    }
    else {
      childPrecedence <= parentPrecedence
    }
  }
  /**
   * Returns true if this expression does NOT need to be placed in parens.
   */
  private def isAtomic(e:Expression):Boolean = e match {
    case False => true
    case True => true
    case DotTerm => true
    case DotFormula => true
    case ProgramConst(name) => true
    case Variable(name, _,_) => true
    case AtomicODE(_, _) => true
    case DifferentialProduct(_, _) => false
    case ODESystem(a, _) => isAtomic(a)
    case Number(_) => true
    case Loop(p) => true
    case Not(e) => isAtomic(e)
    case Test(e) => isAtomic(e)
    case Not(e) => isAtomic(e)
    case DifferentialSymbol(_) => true
    case DifferentialFormula(f) => isAtomic(f)
    
      //arith
    case Neg(l) => isAtomic(l)
  	case Plus(l,r) => false
    case Times(l,r) => false
    case Divide(l,r) => false
    case Minus(l,r) => false
    
    //boolean ops
    case And(l,r) => false
    case Or(l,r) => false
    
    case Imply(l,r) =>  false
    //Now, alphabetically down the type hierarchy (TODO clean this up so that things
    //are grouped in a reasonable way.)
    
    case FuncOf(function,child) => false
    case PredOf(function,child) => false
    
    case Assign(l,r) => false
    case AssignAny(l) => false //@TODO check

    case Forall(_,_) => true
    case Exists(_,_) => true
    case Box(p,f) => true
    case Differential(child) => true
    case Diamond(p,f) => true
    case Equiv(l,r) => false
    
    case Power(l,r) => false
    
    
    //BinaryProgram
    case Choice(l,r) => false
    case Compose(l,r) => false
    
    //BinaryRelation
    case Equal(l,r) => false
    case GreaterEqual(l,r) => false
    case LessEqual(l,r) => false
    case Less(l,r) => false
    case Greater(l,r) => false
    case NotEqual(l,r) => false

    case Pair(l,r) => false

    case Function(name,index,domain,argSorts) => false
    
    /** Normal form ODE data structures
 * \exists R a,b,c. (\D{x} = \theta & F)
 */
    
    
    
    //These we cannot pattern match on...
//    case edu.cmu.cs.ls.keymaerax.core.Quantifier(variables, child)
//    case edu.cmu.cs.ls.keymaerax.core.Finally(f) => BOX + recurse(e)
//    case edu.cmu.cs.ls.keymaerax.core.Globally(f) => DIA + recurse(e)
//    case Left(domain,child) => ???
//    case Right(domain,child) => ???
    
    //And these we can pattern match on but are not implemented yet.
    case Exists(_,_) => false
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Proofs
  //////////////////////////////////////////////////////////////////////////////
  def stringifyEvidence(e:Evidence) = e match {
    case e : ProofEvidence => ??? //TODO
    case e : ExternalEvidence => "External.\n\t" + /*e.file.toString() +*/ "\nEnd."
    case e : ToolEvidence => "Tool.\n\t" + e.info.map( p => p._1 + "\t\"" + p._2 + "\"").mkString("\n\t") + "\nEnd."
  }
  
  def proofHeader(ns : List[NamedSymbol]) : String = {
    val varDecls = ns.map({
      case Variable(n, i, s) => sortProofPrinter(s) + " " + n + printIndex(i) + "."
      case Function(n, i, Unit, s) => sortProofPrinter(s) + " " + n + printIndex(i) + "()" + "."
      case Function(n, i, d, s) => sortProofPrinter(s) + " " + n + printIndex(i) + "(" + sortProofPrinter(d) + ")" + "."
    })
    "Variables.\n" + varDecls.mkString("\n") + "\nEnd.\n"
  }

  private def printIndex(index: Option[Int]) = index match {
    case None => ""
    case Some(i) => "_" + i
  }

  private def sortProofPrinter(s:Sort):String = s match {
    case Bool        => "T"
    case Trafo       => "P"
    case Real        => "T"
    case Unit        => "Void"
    case _: ObjectSort => ???
  }

}
