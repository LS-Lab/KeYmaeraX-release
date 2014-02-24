package pdl.core

/**
 * Thrown by CursorRules when a rule does not apply.
 */
class CRDoesNotApply(s:String="Did you check with applies before applying?") 
extends Exception {
  override def toString = s
}

object CursorRewrite {
  def log(s:String) = println(s)
//  def log(s:String) = null
  
  def rewrite(p:Program, ctx:Set[Channel]):Program = rewriter(p,ctx,false)
  
  def rewriteWithJoin(p:Program, ctx:Set[Channel]):Program = rewriter(p,ctx,true)
  
  def rewriter(p:Program, ctx:Set[Channel],include789:Boolean):Program = {
    def rewriteStep(p:Program, ctx:Set[Channel], include789:Boolean):Program = {
      if(C1.applies(p, ctx))
        {log("Applying C1");(C1.apply(p, ctx))}
      else if(C2.applies(p, ctx))
        {log("Applying C2");(C2.apply(p,ctx))}
      else if(C3.applies(p, ctx))
        {log("Applying C3");(C3.apply(p, ctx))}
      else if(C4.applies(p, ctx))
        {log("Applying C4");(C4.apply(p, ctx))}
      else if(C5.applies(p, ctx))
        {log("Applying C5");(C5.apply(p, ctx))}
      else if(C6.applies(p, ctx))
        {log("Applying C6");(C6.apply(p, ctx))}
      else if(C7.applies(p,ctx))
        {log("Applying C7");(C7.apply(p, ctx))}
      else if(C8.applies(p,ctx))
        {log("Applying C8");(C8.apply(p, ctx))}
      else if(C9.applies(p,ctx))
        {log("Applying C9");(C9.apply(p, ctx))}
      else 
      {log("No cursor rules are applicable");(p)}
    }
        
    //This saturates iff a one-step progress lemma holds  for rewriteStep
    val next = rewriteStep(p,ctx,false)
    
    log("Result of one-step cursor rewrite: " + 
        PrettyPrinter.programToString(p) + 
        "-->" + 
        PrettyPrinter.programToString(next))

    if(next.equals(p)) p                  //equals is syntactic equivalence.
    else               rewriter(next,ctx,include789)
  

  }
}


/**
 * Naming conventions follow those in the paper.
 * TODO should we remove the ctx from the applies methods
 * TODO restructure ruels with temp vars so that the structures of apply and applies
 * are basically identical, e.g. as is in C9
 */
sealed trait CursorRule {  
  /**
   * For most rules, we could just apply and then return true if there's no
   * exception. The only rules this doesn't work for are C1, which is context
   * sensitive, and C7, because we don't want to apply join when the rule
   * is inapplicable.
   */
  def applies(p:Program, ctx:Set[Channel]) : Boolean
  
  /**
   * @throws CRDoesNotApply if the rule does not apply.
   */
  def apply(p:Program, ctx:Set[Channel]) : Program
}

/**
 * C1. Move the cursor past primitive programs and irrelevant communication.
 * Note that we move cursors into sequence, but do not add cursors to the left
 * hand of a bare sequence.
 */
object C1 extends CursorRule {
  /**
   * "u is either a primitive operation (ie, of the form x:=Theta,x:=*,?F) or
   * u is a communication operation of a channel c not mentioned in C.
   */
  def applies(p:Program, ctx:Set[Channel]):Boolean = p match {
    case CursorAfter(program)  => false
    case NoCursor(program)     => false
    case CursorBefore(program) => program match {
      case CursorBefore(p)      => applies(p,ctx)
      case Send(c,_)            => !ctx.contains(c)
      case Receive(c,_)         => !ctx.contains(c)
      case Epsilon()            => true //TODO-nrf warning: allowing Epsilons as input for testing.
      case Assignment(v,p)      => true
      case NonDetAssignment(p)  => true
      case Test(f)              => true
      case Sequence(l,r)        => {
        val newL = if(l.isCursorFree) CursorBefore(l) else l
        applies(newL,ctx)
      }
      case _                    => false
    }
    case Sequence(l,r)          => applies(l, ctx)
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = if(applies(p,ctx)) {
    p match {
      //Move cursors into sequences.
      case CursorBefore(Sequence(l,r)) => Sequence(apply(if(l.isCursorFree) CursorBefore(l) else l,ctx), r)
      case CursorBefore(p)             => CursorAfter(p)
      case Sequence(l,r)               => Sequence(apply(l,ctx),r)
      case _                           => throw new CRDoesNotApply
    }
  } else throw new CRDoesNotApply

}

/**
 * C2b. If the cursor is in front of a compound statement, evaluate in parallel.
 * modified because the way the rule is written in the paper is ambiguos and
 * inconsistent. We tear off the first statement is a;b but not the furst
 * statement in a\cup b...
 */
//case class C2b extends CursorRule {
//  def applies(p:Program, ctx:Set[Channel]) = p match {
//    case CursorBefore(s) => s match {
//      case Sequence(a,b) => b.isCursorFree
//      case _ => false
//    }
//    case _ => false
//  }
//  
//  def apply(p:Program, ctx:Set[Channel]) = p match {
//    case CursorBefore(s) => s match {
//      case Sequence(a,b) => {
//        CursorAfter(Sequence(CursorRewrite.rewrite(CursorBefore(a),ctx),CursorRewrite.rewrite(CursorBefore(b),ctx)))
//      }
//      case _ => throw new CRDoesNotApply
//    }
//    case _ => throw new CRDoesNotApply
//  }
//}

object C2 extends CursorRule {
//  def applies(p:Program, ctx:Set[Channel]) = p match {
//    case Sequence(l_cursor, r) => 
//      l_cursor.isInstanceOf[CursorAfter] && r.isCursorFree
//    case CursorBefore(sequence) => sequence match {
//      case Sequence(a,b) => b.isCursorFree
//      case _ => false
//    }
//    case _ => false
//  }
  //Should be same as above, but this matches apply's structure.
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case Sequence(l_cursor, right) => {
      val leftHasCursor = l_cursor match {
        case CursorAfter(left) => true
        case _ => false
      } 
      leftHasCursor && right.isCursorFree
    }
    case CursorBefore(sequence) => false
//      sequence match {
//        case Sequence(a,b) => true
//        case _ => false
//      }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case Sequence(l_cursor, right) => {
      val left = l_cursor match {
        case CursorAfter(leftWithoutCursor) => leftWithoutCursor
        case _ => throw new CRDoesNotApply(p.prettyString)
      }
      if(!right.isCursorFree) 
        throw new CRDoesNotApply
      else {
        val rightResult = right match {
          case Sequence(rl,rr) => Sequence(CursorBefore(rl), rr)
          case _               => CursorBefore(right)
        }
        
        //TODO can we get rid of the requirement to do a big step here?
        val rewrittenRightResult = CursorRewrite.rewrite(rightResult,ctx)
        
        //This is another difference from the rules. We need a;b. to be (a;b).
        //or else recursion won't do the right thing. TODO this seems like a bug
        rewrittenRightResult match {
          case CursorAfter(rightResultWithoutCursor) => 
            CursorAfter(Sequence(left,rightResultWithoutCursor))
          case _ => Sequence(left, rightResult)
        }
      }
    }
    //Note: we want that .(a;b) --> (.a;b) because otherwise rewriting is
    //stuck off the bat.
    case CursorBefore(sequence) => sequence match {
      case Sequence(a,b) => {
        val aResult = CursorRewrite.rewrite(CursorBefore(a), ctx)
        apply(Sequence(aResult, b), ctx)       
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

///**
// * C2. If the left side of a semicolon is complete, move on to the right.
// *  
// * TODO-t Do we care about the structure of p? ie does \alpha in C2 range over programs,
// * or programs with possible cursors in them? If cursors are allowed then the second condition
// * in applies can be removed. apply should match whatever checks happen in applies.
// */
//case class C2 extends CursorRule {
//  def applies(p:Program, ctx:Set[Channel]) = p match {
//    case Sequence(l,r) => l.isInstanceOf[CursorAfter] && (r match {
//      case CursorBefore(_) => false
//      case CursorAfter(_)  => false
//      case NoCursor(_)     => true
//      case _               => true
//    })
//    
//    case _ => false
//  }
//
//  def apply(p:Program) = p match {
//    case Sequence(l,r) => l match {
//      case CursorAfter(left_program) => Sequence(left_program, CursorBefore(r))
//      case _                         => throw new CRDoesNotApply 
//    }
//    case _ => throw new CRDoesNotApply
//  }
//}

object C3 extends CursorRule {
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(choice) => choice match {
      case Choice(a,b) => a.isCursorFree && b.isCursorFree
      case _ => false
    }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(choice) => choice match {
      case Choice(a,b) => {
        if(!a.isCursorFree || !b.isCursorFree) throw new CRDoesNotApply
        val aRewrite = CursorRewrite.rewrite(CursorBefore(a), ctx)
        val bRewrite = CursorRewrite.rewrite(CursorBefore(b), ctx) 
        CursorBefore(Choice(aRewrite, bRewrite))
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

object C4 extends CursorRule {
  /**
   * TODO refactor this applies method so that it looks more like apply;
   * the nested cases get to be a bit much
   * TODO which makes more sense for verification?
   */
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(program) => program match {
      case Choice(l_cursor, r_cursor) => l_cursor match {
        case CursorAfter(_) => r_cursor match {
          case CursorAfter(_) => true
          case _ => false
        }
        case _ => false
      }
      case _ => false
    }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(choice) => choice match {
      case Choice(l_cursor, r_cursor) => {
        val left = l_cursor match {
          case CursorAfter(left) => left
          case _ => throw new CRDoesNotApply
        }
        
        val right = r_cursor match {
          case CursorAfter(right) => right
          case _ => throw new CRDoesNotApply
        }
        
        val result = CursorAfter(Choice(left,right))
//        CursorRewrite.rewrite(result, ctx)
        result
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

object C5 extends CursorRule {
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(closure) => closure match {
      case STClosure(p) => p.isCursorFree
      case _ => false
    }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(closure) => closure match {
      case STClosure(program) => {
        val programRewrite = CursorRewrite.rewrite(CursorBefore(program), ctx)
        val newClosure = CursorBefore(STClosure(programRewrite))
        CursorRewrite.rewrite(newClosure, ctx)
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

object C6 extends CursorRule {
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(closure) => closure match {
      case STClosure(completed) => completed match {
        case CursorAfter(program) => true
        case _ => false
      }
      case _ => false
    }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(closure) => closure match {
      case STClosure(completed) => completed match {
        case CursorAfter(program) => {
          val result = CursorAfter(STClosure(program))
          CursorRewrite.rewrite(result, ctx)
        }
        case _ => throw new CRDoesNotApply
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

object C7 extends CursorRule {
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(program:Program) => program match {
      case Parallel(a,b) => a.isCursorFree && b.isCursorFree
      case _ => false
    }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(program) => program match {
      case Parallel(a,b) => {
        val result = CursorBefore(PdlRewrite.join(a, b))
        CursorRewrite.rewrite(result, ctx)
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

/**
 * Local abbreviations:
 *   jpar = joined parallel program.
 */
object C8 extends CursorRule {
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(jpar) => jpar match {
      case JoinedParallel(a,b) => a.isCursorFree && b.isCursorFree
      case _ => false
    }
    case _ => false
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(jpar) => jpar match {
      case JoinedParallel(a,b) => {
        val result = CursorBefore(JoinedParallel(CursorBefore(a), CursorBefore(b)))
        CursorRewrite.rewrite(result, ctx)
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}

object C9 extends CursorRule {
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(jpar) => jpar match {
      case JoinedParallel(a_complete,b_complete) => {
        val a_ok = a_complete match {
          case CursorAfter(p) => true
          case _ => false
        }
        val b_ok = b_complete match {
          case CursorAfter(p) => true
          case _ => false
        }
        
        a_ok && b_ok
      }
      case _ => false
    }
    case _ => false
  }

  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(jpar) => jpar match {
      case JoinedParallel(a_complete,b_complete) => {
        val a = a_complete match {
          case CursorAfter(p) => p
          case _ => throw new CRDoesNotApply
        }
        val b = b_complete match {
          case CursorAfter(p) => p
          case _ => throw new CRDoesNotApply
        }
        
        val result = CursorAfter(JoinedParallel(a,b))
        CursorRewrite.rewrite(result, ctx)
      }
      case _ => throw new CRDoesNotApply
    }
    case _ => throw new CRDoesNotApply
  }
}
