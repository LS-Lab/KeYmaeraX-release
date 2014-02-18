package pdl.core

object PrettyPrinter {  
  import pdl.core._
  import pdl.core.Symbols._
  
  def formulaToString(f:Formula):String = f match {
    case FVar(v:Var)	=> v.name
    case True()		=> TRUE
    case False()	=> FALSE
    case Not(f)		=> 
      if(f.isAtomic) NEGATE+formulaToString(f)
      else NEGATE+"("+formulaToString(f)+")"
    case Impl(l,r)	=> {
      val rightString = formulaToString(r) 
      val leftString = l match {
        case Impl(_,_)	=> paren(formulaToString(l))
        case _				=> formulaToString(l)
      }
      leftString + ARROW + rightString
    }
    case And(l,r)	=> {
      val leftString = l match {
        case Impl(_,_)	=> paren(formulaToString(l))
        case Or(_,_)	=> paren(formulaToString(l))
        case _			=> formulaToString(l)
      }
      val rightString = r match {
        case Or(_,_)	=> paren(formulaToString(r))
        case Impl(_,_)	=> paren(formulaToString(r))
        case _			=> formulaToString(r)
      }
      leftString + AND + rightString
    }
    case Or(l,r)	=> {
      val leftString = l match {
        case Impl(_,_)		=> paren(formulaToString(l))
        case And(_,_)		=> paren(formulaToString(l))
        case _				=> formulaToString(l)
      }
      val rightString = r match {
        case And(_,_)	=> paren(formulaToString(r))
        case Impl(_,_)	=> paren(formulaToString(r))
        case _			=> formulaToString(r)
      }
      leftString + OR + rightString
    }
    case Box(p,f) => 
      BOX_OPEN + programToString(p) + BOX_CLOSE + formulaToString(f)
    case Diamond(p,f) => 
      DIA_OPEN + programToString(p) + DIA_OPEN + formulaToString(f)
    
    case Geq(f_1,f_2) => formulaToString(f_1) + GEQ + formulaToString(f_2)
    case Leq(f_1,f_2) => formulaToString(f_1) + LEQ + formulaToString(f_2)
    case Lt(f_1,f_2) => formulaToString(f_1) + GT + formulaToString(f_2)
    case Gt(f_1,f_2) => formulaToString(f_1) + LT + formulaToString(f_2)
    case Eq(f_1,f_2) => formulaToString(f_1) + EQ + formulaToString(f_2)
    
    case Sum(f_1,f_2) => formulaToString(f_1) + PLUS + formulaToString(f_2)
    case Product(f_1,f_2) => formulaToString(f_1) + TIMES + (f_2)
    case Quotient(f_1,f_2) => formulaToString(f_1) + DIVIDE + formulaToString(f_2)
    case Difference(f_1,f_2) => formulaToString(f_1) + MINUS + formulaToString(f_2)
    case Number(s) => s
  }
    
  /**
   * I'm really not sure about this. Basically, no parens except for when
   * taking the st closure of a non-atomic statement 
   * (that is, anything except PVar or STClsure).
   */
  def programToString(p:Program):String = p match {
    case PVar(v) => v.name
    case Assignment(v,p)	=> programToString(v) + ASSIGN + programToString(p)
    case NonDetAssignment(v)	=> programToString(v) + ASSIGN + KSTAR
    case STClosure(p)		=> 
      if(p.isAtomic)	programToString(p) + KSTAR
      else				paren(programToString(p)) + KSTAR
    case Choice(l,r)		=> programToString(l) + CHOICE + programToString(r)
    case Sequence(l,r)		=> programToString(l) + SCOLON + programToString(r)
//    case Sequence(l,r)		=> "Sequence(" + programToString(l) + ", " + programToString(r) + ")"
    case Test(f) => TEST + formulaToString(f)
    
    case Label(l) => "Label(" + l.toString + ")"
    case Remainder(r) => "\\dotuline{" + programToString(r) + "}"
    
    case Evolution(diffEqs, domain) => {
      OPEN_CBRACKET +
      diffEqs.foldLeft("")( (s,f) => s + COMMA + formulaToString(f) ) + 
      COMMA +
      formulaToString(domain) + 
      CLOSE_CBRACKET
    }
    
    case Derivative(v:PVar) => programToString(v) + PRIME
    
    //////////////////////
    
    case Receive(channel,vars) => channel.name + 
      RECEIVE + 
      vars.foldLeft(OPEN_CBRACKET)((s,v) => s + programToString(v)) + 
      CLOSE_CBRACKET
    
    case Send(channel, vars, value) => channel.name + 
      SEND + 
      vars.foldLeft(OPEN_CBRACKET)((s,v) => s + programToString(v)) + 
      CLOSE_CBRACKET +
      formulaToString(value)
      
    case Forward(channel, vars, value) => channel.name.toUpperCase() +
      RECEIVE + vars.foldLeft(OPEN_CBRACKET)((s,v) => s + programToString(v)) + 
      CLOSE_CBRACKET +
      formulaToString(value)
    
    case Parallel(p1,p2) => programToString(p1) + PCOMP + programToString(p2) 
    case JoinedParallel(p1,p2) => programToString(p1) + PCOMP_JOINED + programToString(p2)
    
    case CursorBefore(program) => CURSOR + programToString(program)
    case CursorAfter(program) => programToString(program) + CURSOR
    case NoCursor(program) => "cursorfree(" + programToString(p) + ")"
    case null => throw new Exception("Found a null program somehow")
    
    case Epsilon() => "ε"
    case Deadlock() => "DEADLOCK"
    case Bottom() => "BOT"
  }
}