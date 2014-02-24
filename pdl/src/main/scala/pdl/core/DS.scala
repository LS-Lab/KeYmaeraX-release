package pdl.core

class Var(val name:String) {
  override def equals(other:Any) = {
    if(other.isInstanceOf[Var]) {
      val result = this.name.equals(other.asInstanceOf[Var].name)
      result
    }
    else false
  }
}

////////////////////////////////////////////////////////////////////////////////
// "Extra stuff" for PdL
////////////////////////////////////////////////////////////////////////////////

/**
 * In addition, we need a collection of channels.
 */
sealed class Channel(val name:String) {
  override def equals(other : Any) = 
    if(other.isInstanceOf[Channel]) 
      name.equals(other.asInstanceOf[Channel].name)
    else 
      super.equals(other)
}

/**
 * Programs with cursors.
 * This is here, as opposed to in CursorRewrite, because of C2.
 */
sealed trait CursorProgram extends Program {
  /**
   * removes the outer-most cursor
   */
   def program = this match {
    case CursorBefore(p) => p
    case CursorAfter(p)  => p
    case NoCursor(p)     => p
    case JoinedParallel(a,b) => Parallel(a,b)
  }
}

case class CursorBefore(p:Program) extends CursorProgram
case class CursorAfter(p:Program)  extends CursorProgram
case class NoCursor(p:Program)     extends CursorProgram //?
case class JoinedParallel(a:Program,b:Program) extends CursorProgram

////////////////////////////////////////////////////////////////////////////////
// PDL Programs
////////////////////////////////////////////////////////////////////////////////


object ProgramHelpers {
  /**
   * @returns programs as a normalized sequence.
   */
  def normalize(programs:List[Program]) = {
    programs.reduceRight((left,right) => left match {
      case Sequence(ll,lr) => Sequence(ll,Sequence(lr,right))
      case _               => Sequence(left,right)
    })
  }
}


/**
 * Differential Dynamic Logic logic programs.
 */
sealed trait Program {  
  def prettyString = PrettyPrinter.programToString(this)
  override def toString = prettyString //might not want this so that you can get the IR to string. However, it's useful in debugging.
  
  def communicationType : Set[Channel] = null //TODO
  
  /**
   * @returns pair of programs split at the cursor, with the cursor removed.
   */
  def splitAtCursor : Pair[Option[Program],Option[Program]] = this match {
    case CursorBefore(p) => (None, Some(p))
    case CursorAfter(p)  => (Some(p), None)
    case Sequence(l,r) => r match {
      case CursorBefore(rPrime) => (Some(l), Some(rPrime))
      case CursorAfter(rPrime) => (Some(this),None)
      case _ => (Some(this),None)
    }
    case _ => (Some(this),None)
  }
  
  
//Moved to C1 where it belongs.
//	/**
//	 * This is a transliteration of the #^1 footnote in the cursor rules, and
//	 * captures the "additional" assumptions of the C1 rewrite rule.
//	 */
//	def primitiveIn(channels:Set[Channel]) = this match {
//	  case Assignment(v,p)     => true
//	  case NonDetAssignment(p) => true
//	  case Test(f)             => true
//	  case Send(c,_,_)         => !channels.contains(c)
//	  case Receive(c,_)        => !channels.contains(c)
//	  case _                   => false
//	}
	

  /**
   * Not even sure what this means anymore.
   */
	def isAtomic:Boolean = this match {
	  case PVar(_)			=> true
	  case STClosure(_)		=> true //?
	  case Assignment(_,_) 	=> false
	  case Choice(_,_)		=> false
	  case Sequence(_,_)	=> false
	  case Parallel(_,_)	=> false
	  case Test(_)			=> false
	  case Evolution(_,_)	=> false
	  case NonDetAssignment(_) => true
	  case Receive(_,_) => false
	  case Send(_,_) => false
	  case CursorAfter(_) => false
	  case CursorBefore(_) => false
	  case NoCursor(_) => false
	  case JoinedParallel(_,_) => false
	  case Epsilon() => true
	  case Deadlock() => true
	  case Bottom() => true
	  case Forward(_,_,_) => false 
	  case Label(_) => false
	  case Remainder(p:Program) => p.isAtomic
//	  case CursorBefore(p:Program) => p.isAtomic //?
//	  case CursorAfter(p:Program) => p.isAtomic
//	  case NoCursor(p:Program) => p.isAtomic
	}
	
	def isCursorFree:Boolean = this match {
	  case CursorAfter(a) => false
	  case CursorBefore(a) => false
	  case Assignment(v,f) => true
	  case Choice(a,b) => a.isCursorFree && b.isCursorFree
	  case NoCursor(a) => true
	  case STClosure(p) => p.isCursorFree
	  case Evolution(a,b) => true
	  case JoinedParallel(a,b) => a.isCursorFree && b.isCursorFree
	  case NonDetAssignment(a) => a.isCursorFree
	  case PVar(v) => true
	  case Parallel(a,b) => a.isCursorFree && b.isCursorFree
	  case Receive(c,v) => v.map(_.isCursorFree).foldLeft(true)((x,y) => x && y)
	  case Send(c,t) => true
	  case Forward(c,v,f) => v.map(_.isCursorFree).foldLeft(true)((x,y) => x && y)
	  case Sequence(l,r) => l.isCursorFree && r.isCursorFree
	  case Test(f) => true
	  case Epsilon() => true
	  case Deadlock() => true
	  case Bottom() => true
	  case Label(_) => true
	  case Remainder(p:Program) => p.isCursorFree
    }
	
	/**
	 * Syntactic equivalence for programs.
	 * TODO epsilon-stutter-equivalence of programs.
	 */
	override def equals(other:Any) = if(other.isInstanceOf[Program])
	  equalsOtherProgram(other.asInstanceOf[Program])
	else
	  super.equals(other)
	  
	def equalsOtherProgram(other : Program):Boolean = this match {
	  case PVar(n) 			=> other match {
	    case PVar(other_n) => n.equals(other_n)
	    case _			  => false
	  }
	  case Assignment(v,p)	=> other match {
	    case Assignment(other_v, other_p)	=> v match {
	      case PVar(v) => other_v match {
	        case PVar(v_o) => v.equals(v_o)
	        case _ => false
	      }
	      case _ => false
	    }
	    case _								=> false
	  }
	  case STClosure(p)		=> other match {
	    case STClosure(other_p)	=> p.equals(other_p)
	    case _					=> false
	  }
	  case Choice(l,r)		=> other match {
	    case Choice(other_l,other_r)	=> l.equals(other_l) && r.equals(other_r)
	    case _							=> false
	  }
	  case Sequence(l,r)	=> other match {
	    case Sequence(other_l, other_r)	=> l.equals(other_l) && r.equals(other_r)
	    case _							=> false
	  }
	  case Evolution(l,r) => other match {
	    case Evolution(other_l,other_r) => l.equals(other_l) && r.equals(other_r)
	    case _							=> false
	  }
	  case Parallel(l,r) => other match {
	    case Parallel(other_l,other_r) => l.equals(other_l) && r.equals(other_r)
	    case _							=> false
	  }
	  case Test(f) => other match {
	    case Test(f_o) => f.equals(f_o)
	    case _         => false
	  }
	  case NonDetAssignment(p) => other match {
	    case NonDetAssignment(p_o) => p.equals(p_o)
	    case _                     => false
	  }
	  case Send(c,value) => other match {
	    case Send(c_o,v_v) => {
	      c.equals(c_o)
	    }
	    case _                  => false
	  }
	  case Receive(c:Channel,v:Set[PVar]) => other match {
	    case Receive(c_o,v_o) => {
	      val varSetsMutuallyInclusive = 
	        v.filterNot(v_o.contains(_)).isEmpty &&
            v_o.filterNot(v.contains(_)).isEmpty
            
	      c.equals(c_o) && varSetsMutuallyInclusive
	    }
	    case _                => false
	  }
	  case Forward(c, vs:Set[PVar], f:Formula) => other match {
	    case Forward(c_o, vs_o, f_o) => {
	      val varSetsMI = 
	        vs.filterNot(vs_o.contains(_)).isEmpty &&
	        vs_o.filterNot(vs.contains(_)).isEmpty
	      
	      varSetsMI && f.equals(f_o) && c.equals(c_o)
	    }
	    case _ => false
	  }
	  //Should each of these cases return yes for all cursors?
	  case CursorAfter(p) => other match {
	    case CursorAfter(p_o) => p.equals(p_o)
	    case _                => false
	  }
	  case CursorBefore(p) => other match {
	    case CursorBefore(p_o) => p.equals(p_o)
	    case _                => false
	  }
	  case NoCursor(p) => other match {
	    case NoCursor(p_o) => p.equals(p_o)
	    case _ => false
	  }
	  case JoinedParallel(a,b) => other match {
	    case JoinedParallel(a_o, b_o) => a.equals(a_o) && b.equals(b_o)
	    case _ => false
	  }
	  case Epsilon() => other match {
	    case Epsilon() => true
	    case _ => false
	  }
	  case Deadlock() => other match {
	    case Deadlock() => true
	    case _ => false
	  }
	  case Bottom() => other match {
	    case Bottom() => true
	    case _ => false
	  }
	  case Label(x:Int) => other match {
	    case Label(y:Int) => x==y
	    case _ => false
	  }
	  case Remainder(p:Program) => other match{
	    case Remainder(p2:Program) => p.equals(p2)
	    case _ => false
	  }
	}
	
	/**
	 * Code clone of isCursorFree with CursorAfter changed to true, so the name
	 * is very misleading. TODO figure out exactly how this is being used.
	 */
	def isSynchronizationFree:Boolean = this match {
	  case CursorAfter(a) => true //only difference b/w this and cursor-free.
	  case CursorBefore(a) => false
	  case Assignment(v,f) => true
	  case Choice(a,b) => a.isSynchronizationFree && b.isSynchronizationFree
	  case NoCursor(a) => true
	  case STClosure(p) => p.isSynchronizationFree
	  case Evolution(a,b) => true
	  case JoinedParallel(a,b) => a.isSynchronizationFree && b.isSynchronizationFree
	  case NonDetAssignment(a) => a.isSynchronizationFree
	  case PVar(v) => true
	  case Parallel(a,b) => a.isSynchronizationFree && b.isSynchronizationFree
	  case Receive(c,v) => v.map(_.isSynchronizationFree).foldLeft(true)((x,y) => x && y)
	  case Send(c,f) => true //TODO e.g. this should be contextual.
	  case Forward(c,vs,f) => vs.map(_.isSynchronizationFree).foldLeft(true)((x,y) => x && y)
	  case Sequence(l,r) => l.isSynchronizationFree && r.isSynchronizationFree
	  case Test(f) => true
	  case Epsilon() => true
	  case Deadlock() => true
	  case Bottom() => true
	  case Label(_) => true
	  case Remainder(p) => p.isSynchronizationFree
    }
	
	
	/**
	 * TODO: Add a specification which explains exactly what this does. It does
	 * not appear to do the correct thing.
	 */
	def applyToSubprograms(fn:Function[Program, Program]):Program = this match {
	  case Assignment(v,f) => Assignment(v,f)
	  case Choice(l,r) => Choice(l.applyToSubprograms(fn), r.applyToSubprograms(fn))
	  case JoinedParallel(l,r) => JoinedParallel(l.applyToSubprograms(fn), r.applyToSubprograms(fn))
	  case Parallel(l,r) => Parallel(l.applyToSubprograms(fn), r.applyToSubprograms(fn))
	  case Sequence(l,r) => Sequence(l.applyToSubprograms(fn), r.applyToSubprograms(fn))
	  
	  case CursorAfter(p) => CursorAfter(p.applyToSubprograms(fn))
	  case CursorBefore(p) => CursorBefore(p.applyToSubprograms(fn))
	  case NoCursor(p) => NoCursor(p.applyToSubprograms(fn))
	  case Remainder(p) => Remainder(p.applyToSubprograms(fn))
	  case STClosure(p) => STClosure(p.applyToSubprograms(fn))
	  
	  case Deadlock() => this
	  case Epsilon() => this
	  case Forward(a,b,c) => this
	  case PVar(v) => this
	  case Receive(_,_) => this
	  case Send(_,_) => this
	  case Test(p) => this
	  case Label(p) => this
	  case NonDetAssignment(p) => this
	  case Evolution(l,r) => this
	  case Bottom() => fn(this)
	}
}

//  x | x := p | ?F | p* | p;p 
//| x:=* | p \cup p 
//| x` | {a'=x, b'=y, H}  
//| a||b | (c,X)!\phi | c?X
case class PVar(v:Var)                                           extends Program
{
  def toFvar = FVar(v)
}                                                                
case class Assignment(v : PVar, f: Formula)                      extends Program
case class STClosure(p : Program)                                extends Program
case class Sequence(left : Program, right : Program)             extends Program
{
  if(left.isInstanceOf[Sequence]) 
    throw new Exception("Sequences look like S(1, S(2, 3))."
        + "Left should never be sequence:" + left.prettyString)
  
  def append(newProgram:Program):Sequence = Sequence(left, right match {
    case Sequence(rl,rr) => Sequence(rl,rr).append(newProgram)
    case _               => Sequence(right, newProgram)
  })
}                                                                
  
case class Test(f:Formula)                                       extends Program

case class NonDetAssignment(v : PVar)                            extends Program
case class Choice(left : Program, right : Program)               extends Program

case class Evolution(diffEq : Set[Formula], domain : Formula)    extends Program

case class Parallel(left : Program, right : Program)             extends Program
case class Send(channel:Channel, term:Formula)  extends Program
case class Receive(channel:Channel, vars:Set[PVar])              extends Program
case class Forward(channel:Channel, vars:Set[PVar], value:Formula)              extends Program
case class Epsilon()                                             extends Program
case class Deadlock()                                            extends Program
/**
 * As used in the linear form rewrites.
 */
case class Bottom()                                              extends Program
/**
 * Used in merge rules.
 */
case class Remainder(p:Program)                                  extends Program
/**
 * Labels used in the Merge algorithm.
 */
case class Label(label:Int)                                      extends Program
////////////////////////////////////////////////////////////////////////////////
// Formulas and Terms of dL (identical to PdL)
////////////////////////////////////////////////////////////////////////////////


/**
 * Formulas and "special" terms (e.g. numbers, +, -, *, /
 */
sealed trait Formula {
//  override def toString = prettyString
  def prettyString = PrettyPrinter.formulaToString(this)
  
  def isTerm:Boolean = this match {
    case Not(f)			=> false
    case True()			=> false //?
    case False()		=> false //?
//    case Derivative(_)	=> false 
    case Impl(_,_)		=> false
    case And(_,_)		=> false
    case Or(_,_)		=> false
    case Box(_,_)		=> false
    case Diamond(_,_)	=> false
    case Eq(_,_)		=> false
    case Geq(_,_)		=> false
    case Leq(_,_)		=> false
    case Gt(_,_)		=> false
    case Lt(_,_)		=> false
    
    case Number(_)      => true
    case Sum(_,_)       => true
    case Difference(_,_)=> true
    case Product(_,_)   => true
    case Quotient(_,_)  => true
    case FVar(_)		=> true //?
    case Derivative(v:PVar) => true //?
    case Negative(f) => f.isTerm
    case Symbol(_,args) => args.map(_.isTerm).reduce(_|_)
  }
  
  def isAtomic:Boolean = this match {
    case Not(f)			=> f.isAtomic
    case Number(_)      => true
    case FVar(_)			=> true
    case True()			=> true
    case False()		=> true
    case Derivative(_)	=> true 
    case Impl(_,_)		=> false
    case And(_,_)		=> false
    case Or(_,_)		=> false
    case Box(_,_)		=> false
    case Diamond(_,_)	=> false
    case Eq(_,_)		=> false
    case Geq(_,_)		=> false
    case Leq(_,_)		=> false
    case Gt(_,_)		=> false
    case Lt(_,_)		=> false
    case Sum(_,_)       => false
    case Difference(_,_)=> false
    case Product(_,_)   => false
    case Quotient(_,_)  => false
    case Negative(f) => f.isAtomic
    case Symbol(_,args) => args.map(_.isAtomic).reduce(_|_)
  }
  
  /**
   * Equivalence of formulas
   */
  override def equals(other:Any) = if(other.isInstanceOf[Formula])
      equalsFormula(other.asInstanceOf[Formula])
    else
      super.equals(other)
      
  def equalsFormula(other : Formula):Boolean = this match {
    case Symbol(name, args) => other match {
      case Symbol(other_name, other_args) => {
        val leftInRight = args.map(other_args.contains(_)).reduce(_&&_)
        val rightInLeft = other_args.map(args.contains(_)).reduce(_&&_)
        name.equals(other_name) && (leftInRight && rightInLeft)
      }  
      case _ => false
    }
    case Impl(l,r)	=> other match {
      case Impl(o_l,o_r) => l.equals(o_l) && r.equals(o_r)
      case _			 => false
    }
    case And(l,r)	=> other match {
      case And(o_l,o_r)	=> l.equals(o_l) && r.equals(o_r)
      case _			=> false
    }
    case Or(l,r)	=> other match {
      case Or(o_l,o_r)	=> l.equals(o_l) && r.equals(o_r)
      case _			=> false
    }
    case Not(f)		=> other match {
      case Not(o_f)	=> f.equals(o_f)
      case _		=> false
    }
    case FVar(v:Var) => other match {
      case FVar(v_o) => v.equals(v_o)
      case _				=> false
    }
    case Box(p:Program,f:Formula)	=> other match{
      case Box(o_p:Program, o_f:Formula) => p.equals(o_p) && f.equals(o_f)
      case _							 => false
    }
    case Diamond(p:Program,f:Formula)	=> other match{
      case Diamond(o_p:Program, o_f:Formula) => p.equals(o_p) && f.equals(o_f)
      case _							 => false
    }
    case True()		=> other match {
      case True()	=> true
      case _		=> false
    }
    case False()	=> other match {
      case False()	=> true
      case _		=> false
    }
    case Eq(l,r) => other match { 
      case Eq(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Geq(l,r) => other match { 
      case Geq(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Leq(l,r) => other match { 
      case Leq(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Gt(l,r) => other match { 
      case Gt(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Lt(l,r) => other match { 
      case Lt(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
//    case Derivative(e) => other match {
//      case Derivative(other_e) => e.equals(other_e)
//      case _					=> false
//    }
    case FVar(v) => other match {
      case FVar(v_o) => v.equals(v_o)
      case _ => false
    }
    case Number(s:String) => other match {
      case Number(o_s:String) => s.equals(o_s)
      case _                  => false
    }
    case Sum(l,r) => other match {
      case Sum(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Difference(l,r) => other match {
      case Difference(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Product(l,r) => other match {
      case Product(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Quotient(l,r) => other match {
      case Quotient(l_o, r_o) => l.equals(l_o) && r.equals(r_o)
      case _ => false
    }
    case Derivative(variable) => other match {
      case Derivative(other_variable) => variable match {
        case PVar(v)   => other_variable match {
          case PVar(v_o) => v.equals(v_o)
          case _        => false
        }
        case _        => false
      }
      case _ => false
    }
    case Negative(f) => other match {
      case Negative(other_f) => f.equals(other_f)
      case _ => false
    }
  }
}

case class True()                                   extends Formula
case class False()                                  extends Formula

case class FVar(v:Var)                              extends Formula 
case class Symbol(name:String, args:List[Formula])  extends Formula
case class Not(f:Formula)                           extends Formula
case class And(left : Formula, right : Formula)     extends Formula
case class Or(left : Formula, right : Formula)      extends Formula
case class Impl(left : Formula, right : Formula)    extends Formula

case class Eq(left : Formula, right : Formula)      extends Formula
case class Geq(left : Formula, right : Formula)     extends Formula
case class Leq(left : Formula, right : Formula)     extends Formula
case class Gt(left : Formula, right : Formula)      extends Formula
case class Lt(left : Formula, right : Formula)      extends Formula

case class Box(p:Program, f:Formula)                extends Formula
case class Diamond(p:Program, f:Formula)            extends Formula

case class Number(s:String)                         extends Formula
case class Sum(left:Formula, right:Formula)         extends Formula
case class Difference(left:Formula, right:Formula)  extends Formula
case class Product(left:Formula,right:Formula)      extends Formula
case class Quotient(left:Formula,right:Formula)     extends Formula
case class Negative(f:Formula)                      extends Formula

case class Derivative(variable : PVar)              extends Formula
