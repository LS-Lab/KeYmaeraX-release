package pdl.core

object LFRewrite {
  def log(s:String) = {println(s)}
//  def log(s:String) = null
  
  def rewrite(p:Program,ctx:Set[Channel]):LFResult = {
    //This saturates iff a one-step progress lemma holds  for rewriteStep
    val bigStepResult = bigStep(p,ctx)
    
    log("Result of bigStep rewrite: " + PrettyPrinter.programToString(p) + "-LF->" + bigStepResult.toString())
    
    bigStepResult
  }
  
  def bigStep(p:Program, ctx:Set[Channel]):LFResult = {
    if(L1.applies(p, ctx))
      {log("Applying L1");(L1.apply(p,ctx))}
    else if(L2.applies(p, ctx))
      {log("Applying L2 to " + PrettyPrinter.programToString(p));(L2.apply(p,ctx))}
    else if(L3.applies(p, ctx))
      {log("Applying L3");(L3.apply(p,ctx))}
    else if(L4.applies(p, ctx))
      {log("Applying L4");(L4.apply(p,ctx))}
    else {log("No LF rules are applicable to " + PrettyPrinter.programToString(p));(LinearForm(None, Some(p), None,None))}
  }
}

/**
 * The result of a rewrite of lf[program]
 */
sealed trait LFResult {
  def prettyString = PrettyPrinter.LFResultToString(this)
  
  def toSet:Set[LinearForm] = this match {
    case LinearForm(_,_,_,_)        => Set(this.asInstanceOf[LinearForm])
    case LFChoice(left,right)       => left.toSet.union(right.toSet)
  }
  
  override def equals(right:Any):Boolean = if(right.isInstanceOf[LFResult]) {
    resultEqual(right.asInstanceOf[LFResult])
  } else {
    super.equals(right)
  }
  
  def resultEqual(other:LFResult) = this match {
    case LinearForm(u,sync,v,gamma) => other match {
      case LinearForm(o_u,o_sync,o_v,o_gamma) => 
        u.equals(o_u) &&
        sync.equals(o_sync) &&
        v.equals(o_v) &&
        gamma.equals(o_gamma)
      case LFChoice(_,_) => false
    }
    case LFChoice(l,r) => other match {
      case LFChoice(o_l, o_r)  => l.equals(o_l) && r.equals(o_r)
      case LinearForm(_,_,_,_) => false
    }
  }
}

/**
 * The final result of a rewrite
 */
case class LinearForm(val u:Option[Program], val sync:Option[Program], val v:Option[Program], val gamma:Option[Program]) extends LFResult {
   override def toString():String = {
    val ts : Function[Option[Program], String] = p => p match {
      case Some(p1) => PrettyPrinter.programToString(p1)
      case None => "_"
    }
    "(" + ts(u) + "," + ts(sync) + "," + ts(v) + "," + ts(gamma) + ")"
  }
   
   
   /**
    * Apply fn to each of the elements, if it's defined.
    */
  def apply(fn:Function[Program, Program]) = {
    val new_u = this.u match {
      case Some(uPrime) => Some(fn(uPrime))
      case None         => None
    }
    val new_sync = this.sync match {
      case Some(sync) => Some(fn(sync))
      case None       => None
    }
    val new_v = this.v match {
      case Some(vPrime) => Some(fn(vPrime))
      case None   => None
    }
    val new_gamma = this.gamma match {
      case Some(gammaPrime) => Some(fn(gammaPrime))
      case None             => None
    }
    
    new LinearForm(new_u, new_sync, new_v, new_gamma)
  }
}
/**
 * A partial result of a rewrite.
 */
case class LFChoice(left:LFResult, right:LFResult) extends LFResult {
  override def toString() = {
    left.toString() + Symbols.CHOICE + right.toString()
  }
}

/**
 * Thrown by Linear Form rules when a rule does not apply.
 */
class LRDoesNotApply(val msg:String="Did you check with applies before applying?") 
extends Exception

/**
 * Linear form rewrites
 */
sealed trait LFRule {
  /**
   * We don't just call apply and return false on exceptions because the check
   * should only consider one step
   */
  def applies(p:Program, ctx : Set[Channel]) : Boolean
  
  def apply(p:Program, ctx : Set[Channel]) : LFResult
  
  /**
   * Motivation for this type: The linear form rules are all of the form
   * u.A;g where u is a predecessor, A is the sub-program at the head of
   * the cursor, and gamma is some sequence of program statements following
   * the cursor.
   * 
   * The input to a rewrite is a sequence, with the cursor in the middle. In 
   * order to apply the rules, we have to break the program up into the three
   * portions identified by the rules.
   * 
   * Values of this type are introduced by splitSequence, and eliminated through-out
   * the LF rule application of the code base.
   * 
   * Position 1 = everything before the cursor
   * Position 2 = sub-program identified by the cursor
   * Position 3 = program after the identified program
   */
  type ProgramTriple = Triple[Option[Program],Option[Program],Option[Program]]
  
  /**
   * Splits a Sequence into three parts: a precursor, a cursor operation, and a 
   * postcursor or remainder. E.g.:
   * a;!b;c => [a, b, c]
   * !b;c => [NONE, b, c]
   * a;!b => [a,b,MPME]
   * a; !b; !c; d => [a, !b, !c, d]
   * vocabulary: [pred, synch, succ]; input sequence: (left,right)
   * 
   * Relies upon the invariant that sequences look like s(1,s(2,s(...s(n,n+1))))
   * This is enforced in the constructor for sequences.
   * See source control history for a much more complicated version of this
   * algorithm which does not rely on sequences being in normal form.
   * 
   * This is tested by the L2 rule rewrite tests.
   */
  def splitSequence(s:Sequence, triple:ProgramTriple=(None,None,None)) : ProgramTriple = {
    val(left,right) = s match {
      case Sequence(l,r) => (l,r)
    }
    
    if(left.isInstanceOf[Sequence]) throw new Exception("s not in normal form.")

    val tripleWithLeft  = addToTriple(left, triple)
    val tripleWithLeftAndRight = addToTriple(right, tripleWithLeft) //recursive
    
    tripleWithLeftAndRight
  }
  
  /**
   * @param triple A sequential prefix of p
   * @param p The suffix of p
   * @returns the program triple for invsplit(triple);p
   * 
   * Adds a program to the correct place in a triple. It suffices to consider 
   * whether p is cursor free and 2 is defined.
   * 
   * If p is not synchronization free, then we should place p in the center if
   * the center is not defined (00). However, if the center is defined, we 
   * should instead place p on the right (01).
   * 
   * If p is synchronization free, then we should place p on the left if the 
   * center is not defined (10). Otherwise, p must go on the right (11).
   * 
   * This is tested by the L2 rule rewrite tests.
   */
  private def addToTriple(p:Program, triple:ProgramTriple):ProgramTriple = p match {
    case Sequence(l,r) => splitSequence(Sequence(l,r), triple)
    case _             => {
      if(!p.isCursorFree && !triple._2.isDefined) {
        (triple._1, Some(p), triple._3)
      }
      else if(!p.isCursorFree && triple._2.isDefined) {
        val suffix = triple._3 match {
          case Some(Sequence(_,_)) => Some(triple._3.get.asInstanceOf[Sequence].append(p))
          case Some(_)             => Some(Sequence(triple._3.get, p))
          case None                => None
        }
        (triple._1, Some(p), suffix)
      }
      else if(p.isCursorFree && !triple._2.isDefined) {
        val prefix = triple._1 match {
          case Some(Sequence(_,_)) => triple._1.get.asInstanceOf[Sequence].append(p)
          case Some(_)             => Sequence(triple._1.get, p)
          case None                => p
        }
        (Some(prefix), triple._2, triple._3)
      }
      else if(p.isCursorFree && triple._2.isDefined) {
        val suffix = triple._3 match {
          case Some(Sequence(l3,r3)) => Sequence(l3,r3).append(p)
          case Some(threePrime)      => Sequence(threePrime, p)
          case None                  => p
        }
        (triple._1, triple._2, Some(suffix))
      }
      else {
        throw new Exception("Unreachable code (00 01 10 11)")
      }
    }
  }

  /**
   * Removes all cursors from a subprogram.
   * TODO in principle should this even be allowed?
   */
  def decurse(p:Program):Program = p match {
    case CursorBefore(p_) => decurse(p_)
    case CursorAfter(p_)  => decurse(p_)
    case NoCursor(p_)     => decurse(p_)
    
    case _                => p.applyToSubprograms(decurse)
  }
  
  /**
   * Rewrites a program p -> (cursor-free portion, g). Strips the leading
   * cursor.
   * Not convinced that this is bug-free.
   */
  def cursorRewriteSubprogram(p:Program, ctx:Set[Channel]) = {
//    //Ensure that the passed-in program has a cursor; if it doesn't, insert one
//    //at the beginning of the program.
//    val p = if(pInput.isCursorFree) CursorBefore(pInput) else pInput
    if(p.isCursorFree) {
      throw new Exception("Trying to re-write a cursor-free subprogram. This will fail: " +
          p.prettyString)
    }
    
    val rewriteResult = CursorRewrite.rewrite(p, ctx) 
    
    val combinedResult = rewriteResult match {
      //Remove the leading cursor, since that's what the rules do.
      case CursorBefore(pPrime) => (None, Some(pPrime))
      case Sequence(l,r)        => {
        //Split into three parts, and then combine everything after the initial
        //cursor into a single program.
        val (v,pPrime1, pPrime2) = splitSequence(Sequence(l,r))
        (v, sequenceOfOptions(pPrime1, pPrime2))
      }
      case CursorAfter(pPrime) => (Some(pPrime), None)
      case _ => throw new LRDoesNotApply
    }
    
    combinedResult
  }
  
  /**
   * Returns a sequence of the two values if both are defined, or only one value
   * (or None) if one or more of the values is not defined.
   */
  def sequenceOfOptions(o1:Option[Program], o2:Option[Program]) = o1 match {
    case None => None
    case Some(o1v) => o2 match {
      case None => o1
      case Some(o2v) => Some(Sequence(o1v,o2v))
    }
  }
  
  /**
   * Projects the defined portions of a list of program options, then 
   * combines them in a sequence. Examples:
   * [None, P1, P2] => Sequence(P1,P2)
   * [P1, None, P2, P2] => Sequence(p1,Sequence(p2,p3))
   */
  def sequentializeDefined(l : List[Option[Program]]) = {
    val filtered = l.filter(_.isDefined).map(x => x match {
      case Some(x) => x
      case _ => throw new Exception("Unreachable.") //won't get here.
    })
    ProgramHelpers.normalize(filtered)
  }
}

object L1 extends LFRule {
  def apply(cp:Program, ctx:Set[Channel]) = cp match {
    case CursorAfter(program) => 
      new LinearForm(Some(program), Some(Bottom()), None, None)
    case _ => throw new LRDoesNotApply
  }
  
  def applies(cp:Program, ctx : Set[Channel]) = cp match {
    case CursorAfter(program) => true
    case _ => false
  }
}

object L2 extends LFRule {
  def apply(p:Program, ctx:Set[Channel]) = {
    LFRewrite.log("Applying L2 to " + p.prettyString); //TODO remove.
    p match {
      case CursorBefore(syncOrEpsilon) => syncOrEpsilon match {
        case Send(_,_)    => LinearForm(None,Some(syncOrEpsilon),None,None)
        case Receive(_,_)   => LinearForm(None,Some(syncOrEpsilon),None,None)
        case Epsilon()      => LinearForm(None,Some(syncOrEpsilon),None,None)
        case Evolution(_,_) => LinearForm(None,Some(syncOrEpsilon),None,None)
        case _              => throw new LRDoesNotApply
      }
      
      case Sequence(l,r) => {
        val (predOpt, syncOpt, sucOpt) = splitSequence(Sequence(l,r))
        
        //remove the cursor from the sync operation
        val sync = syncOpt match {
          case Some(CursorBefore(sync)) => sync
          case None => throw new LRDoesNotApply
          case _    => throw new Exception("split is implemented incorrectly.") //non-cursor sync. shouldn't even get here.
        }

        //cursor-rewrite anything after the sync operation.
        //Note: cursorRewriteSubprogram strips the leading cursor from gamma.
        val (v,gammaPrime) = sucOpt match {
          case Some(gamma)               => cursorRewriteSubprogram(CursorBefore(gamma), ctx)
          case None                      => (None,None)
        }
        
//        if(v.isDefined && !v.get.isCursorFree)
//          throw new LRDoesNotApply("Failed assertion: v should be CF")
//        if(gammaPrime.isDefined && !gammaPrime.get.isCursorFree)
//          throw new LRDoesNotApply("Failed assertion: v should be CF")

        val remainder:Option[Program] = if(!v.isDefined && !gammaPrime.isDefined) {
          None
        }
        else if(!v.isDefined && gammaPrime.isDefined) {
          Some(decurse(gammaPrime.get))
        }
        else if(v.isDefined && !gammaPrime.isDefined) {
          Some(decurse(v.get))
        }
        else if(v.isDefined && gammaPrime.isDefined) {
          Some(Sequence(decurse(v.get), decurse(gammaPrime.get)))
        }
        else {
          None
        }
        
        LinearForm(predOpt, Some(sync), None, remainder)
      } 
      
      case _ => throw new LRDoesNotApply //non-cursor and non-sequence
    }
  }
  
  def applies(p:Program, ctx:Set[Channel]) = {
    p match {
      case CursorBefore(syncOrEpsilon) => syncOrEpsilon match {
        case Send(_,_)    => true
        case Receive(_,_)   => true
        case Epsilon()      => true
        case Evolution(_,_) => true
        case _              => false
      }
      
      case Sequence(l,r) => {
        val (predOpt, syncOpt, sucOpt) = splitSequence(Sequence(l,r))
        syncOpt match {
          case None => false
          case Some(CursorBefore(sync)) => sync match {
            case Send(_,_) => true
            case Receive(_,_) => true
            case Epsilon() => true
            case Evolution(_,_) => true
            case _ => false
          }
          case _ => false
          //Justification for returning false and not raising error: (.a)* is not cursor
          //free but does not have a cursor at the beginning.
//          case _ => throw new Exception("split is implemented incorrectly: " + syncOpt.getOrElse[Program](PVar(new Var("SYNC WAS NONE"))).prettyString) //non-cursor sync. shouldn't even get here.
        }
      } 
      
      case _ => false //non-cursor and non-sequence
    }
  }
}


object L3 extends LFRule {
  def applyWith(u:Option[Program], p:CursorBefore, ctx:Set[Channel], gamma:Option[Program]) = {
    val (a,b) = p match {
      case CursorBefore(Choice(l,r)) => (l,r)
      case _           => throw new LRDoesNotApply
    }
    
    val (v,aPrime) = cursorRewriteSubprogram(CursorBefore(a), ctx)
    val (w,bPrime) = cursorRewriteSubprogram(CursorBefore(b), ctx)
    
    //Filter out all the nones and convert the list to a sequence.
    val left  = sequentializeDefined(u :: v :: aPrime :: gamma :: Nil)
    val right = sequentializeDefined(u :: w :: bPrime :: gamma :: Nil)
    
    LFChoice(LFRewrite.rewrite(left, ctx),LFRewrite.rewrite(right, ctx))
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(Choice(a,b)) => applyWith(None, CursorBefore(Choice(a,b)), ctx, None)
    case Sequence(l,r) => {
      val (uOpt, choiceOpt, gammaOpt) = splitSequence(Sequence(l,r))
      choiceOpt match {
        case Some(CursorBefore(Choice(a,b))) => applyWith(uOpt, CursorBefore(Choice(a,b)), ctx, gammaOpt)
        case _ => throw new LRDoesNotApply
      }
    }
    case _ => throw new LRDoesNotApply
  }
  
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(Choice(a,b)) => true
    case Sequence(l,r) => {
      val (uOpt, choiceOpt, gammaOpt) = splitSequence(Sequence(l,r))
      choiceOpt match {
        case Some(CursorBefore(Choice(a,b))) => true
        case _ => false
      }
    }
    case _ => false
  }
}


object L4 extends LFRule {
  /**
   * applyWith does the action of apply with an optionally defined u and gamma.
   */
  def applyWith(u:Option[Program], p:CursorBefore, ctx:Set[Channel], gamma:Option[Program]) = p match {
    case CursorBefore(STClosure(a)) => {
      val (v,aPrimeOpt) = if(!a.isCursorFree)
        cursorRewriteSubprogram(a, ctx)
        else
          cursorRewriteSubprogram(CursorBefore(a), ctx)

      val aPrimeWithC = aPrimeOpt match {
        case Some(CursorBefore(_)) => aPrimeOpt
        case Some(_) => Some(aPrimeOpt.get)
        case None => aPrimeOpt
      }
      
      val aNoCursor = decurse(a)
      if(!aNoCursor.isCursorFree) 
        throw new LRDoesNotApply("Cursor found where it shouldn't be.") //bad exception class
      
      val left = sequentializeDefined(u::v::aPrimeWithC::Some(Epsilon())::Some(STClosure(aNoCursor))::gamma::Nil)
      val right = sequentializeDefined(u::Some(CursorBefore(Epsilon()))::gamma::Nil)
      
      LFChoice(LFRewrite.rewrite(left, ctx), LFRewrite.rewrite(right,ctx))
    }
    case _ => throw new LRDoesNotApply("No cursor found where one was expected.")
  }
  
  def apply(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(STClosure(a)) => applyWith(None, CursorBefore(STClosure(a)), ctx, None)
    case Sequence(l,r) => {
      val (u, s, gamma) = splitSequence(Sequence(l,r))
      s match {
        case Some(CursorBefore(STClosure(a))) => applyWith(u, CursorBefore(STClosure(a)), ctx, gamma)
        case _ => throw new LRDoesNotApply
      }
    }
    case _ => throw new LRDoesNotApply
  }
  
  def applies(p:Program, ctx:Set[Channel]) = p match {
    case CursorBefore(STClosure(a)) => true
    case Sequence(l,r) => {
      val (u, s, gamma) = splitSequence(Sequence(l,r))
      s match {
        case Some(CursorBefore(STClosure(a))) => true
        case _ => false
      }
    }
    case _ => false
  }
}


//case class L3 extends LFRule {
//  /**
//   * Implemented by first defining the rewrite for choice, and then defining
//   * the behavior for the when the elements around the choice are non-epsilon.
//   */
//  def apply(p:Program, ctx:Set[Channel]) = p match {
//    case CursorBefore(choice) => choice match {
//      case Choice(a,b) => {
//        val aCursorResult = CursorRewrite.rewrite(a, ctx)
//        val bCursorResult = CursorRewrite.rewrite(b, ctx)
//      
//        val aResult = aCursorResult match {
//          case Sequence(_,_) =>  {
//            val (av,as,_) = splitSequence(aCursorResult.asInstanceOf[Sequence])
//            LFRewrite.rewrite(Sequence(av,as), ctx)   
//          }
//          case CursorBefore(_) => LFRewrite.rewrite(aCursorResult, ctx) 
//          case _ => throw new LRDoesNotApply
//        }
//      
//        val bResult = bCursorResult match {
//          case Sequence(_,_) =>  {
//            val (bv,bs,_) = splitSequence(bCursorResult.asInstanceOf[Sequence])
//            LFRewrite.rewrite(Sequence(bv,bs), ctx)   
//          }
//          case CursorBefore(_) => LFRewrite.rewrite(bCursorResult, ctx) 
//          case _ => throw new LRDoesNotApply
//        }
//     
//        LFChoice(aResult, bResult)
//      }
//      case _ => throw new LRDoesNotApply
//    }
//    
//    case Sequence(_,_) => {
//      val (u, csynch, gamma) = splitSequence(p.asInstanceOf[Sequence])
//      val (a,b) = csynch match {
//        case Choice(a,b) => (a,b)
//        case _ => throw new LRDoesNotApply
//      }
//      
//      val aCursorResult = CursorRewrite.rewrite(a, ctx)
//      val bCursorResult = CursorRewrite.rewrite(b, ctx)
//      
//      val aRewrite = aCursorResult match {
//        case Sequence(_,_) => {
//          val (av,as,_) = splitSequence(aCursorResult.asInstanceOf[Sequence])
//          val target = Sequence(Sequence(Sequence(u,av), as), gamma)
//          LFRewrite.rewrite(target, ctx)
//        }
//        case CursorBefore(_) => LFRewrite.rewrite(aCursorResult, ctx)
//        case _ => throw new LRDoesNotApply
//      }
//      
//      val bRewrite = bCursorResult match {
//        case Sequence(_,_) => {
//          val (bv,bs,_) = splitSequence(bCursorResult.asInstanceOf[Sequence])
//          val target = Sequence(Sequence(Sequence(u,bv), bs), gamma)
//          LFRewrite.rewrite(target, ctx)
//        }
//        case CursorBefore(_) => LFRewrite.rewrite(bCursorResult, ctx)
//        case _ => throw new LRDoesNotApply
//      }
//      
//      LFChoice(aRewrite, bRewrite)
//    }
//    
//    case _ => throw new LRDoesNotApply
//  }
//  
//  def applies(p:Program, ctx:Set[Channel]) = p match {
//    case CursorBefore(choice) => choice match {
//      case Choice(a,b) => {
//        try {
//          val aCursorResult = CursorRewrite.rewrite(a, ctx)
//          val bCursorResult = CursorRewrite.rewrite(b, ctx)
//          
//          val aResult = aCursorResult match {
//            case Sequence(_,_) =>  true
//            case CursorBefore(_) => true
//            case _ => false
//          }
//      
//          val bResult = bCursorResult match {
//            case Sequence(_,_) =>  true
//            case CursorBefore(_) => true 
//            case _ => false
//          }
//          aResult && bResult
//        } 
//        catch {
//          case e:CRDoesNotApply => false
//        }
//      }
//      case _ => false
//    }
//    case Sequence(_,_) => {
//      val (u, csynch, gamma) = splitSequence(p.asInstanceOf[Sequence])
//      csynch match {
//        case Choice(a,b) => true
//        case _ => false
//      }
//    }
//    case _ => false
//  }
//}

//case class L4 extends LFRule {
//  /**
//   * apply, but with u as a prefix and gamma as a suffix. 
//   * Removes redundant epsilons in accordance with the rules (see constructSequence)
//   * @param u Some predecessor or None
//   * @param gamma Some successor or None
//   */
//  def applyWith(u:Option[Program], p:CursorBefore, ctx:Set[Channel], gamma:Option[Program]) = {
//    val constructSequence : Function[List[Program], Program] = (list:List[Program]) => {
//      val plist = u match {
//        case Some(u) => gamma match {
//          case Some(gamma) => (u::Nil) ++ list ++ (gamma::Nil) 
//          case None => (u::Nil) ++ list
//        }
//        case None => list
//      }
//      plist.reduce((a,b) => Sequence(a,b))
//    }
//    
//    val right_sequence = constructSequence(CursorBefore(Epsilon()) :: Nil)
//    val right = LFRewrite.rewrite(right_sequence, ctx)
//    
//    val left = p match {
//      case CursorBefore(STClosure(a)) => {
//        val aCursorResult = CursorRewrite.rewrite(CursorBefore(a), ctx)   
//        
//        aCursorResult match {
//          case Sequence(_,_) => {
//            val (lv,ls,_) = splitSequence(aCursorResult.asInstanceOf[Sequence])
//            val target = constructSequence(lv::ls::Epsilon()::STClosure(a)::Nil)
//            LFRewrite.rewrite(target, ctx) 
//          }
//          case CursorBefore(aPrime) => {
//            if(!aPrime.equals(a)) 
//              throw new Exception("Assert: no cursor rewrite, so no change to a")
//            
//            val target = constructSequence(a::Epsilon()::STClosure(a)::Nil)
//            LFRewrite.rewrite(target, ctx)
//          }
//          case _ => throw new LRDoesNotApply
//        }
//      }
//      case _ => throw new LRDoesNotApply
//    }
//    LFChoice(left,right)
//  }
//  
//  def apply(p:Program, ctx:Set[Channel]) = p match {
//    case Sequence(_,_) => {
//      val (u, cursorClosure, gamma) = splitSequence(p.asInstanceOf[Sequence])
//      cursorClosure match {
//        case CursorBefore(closure) => 
//          applyWith(Some(u),cursorClosure.asInstanceOf[CursorBefore],ctx,Some(gamma))
//        case _ => throw new LRDoesNotApply
//      }
//    }
//    case CursorBefore(STClosure(a)) => 
//      applyWith(None, p.asInstanceOf[CursorBefore], ctx, None)    
//    case _ => throw new LRDoesNotApply
//  }
//  
//  /**
//   * UNDER-esttimate!
//   */
//  def applies(p:Program, ctx:Set[Channel]) = p match {
//    case Sequence(_,_) => {
//      val (u, cursorClosure, gamma) = splitSequence(p.asInstanceOf[Sequence])
//      cursorClosure match {
//        case CursorBefore(closure) => true
//        case _ => false
//      }
//    }
//    case CursorBefore(STClosure(a)) => true   
//    case _ => false
//  }
//}
