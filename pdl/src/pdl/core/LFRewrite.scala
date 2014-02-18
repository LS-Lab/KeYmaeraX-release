package pdl.core

object LFRewrite {
//  def log(s:String) = {println(s)}
  def log(s:String) = null
  
  def rewrite(p:Program,ctx:Set[Channel]):LFResult = {
    //This saturates iff a one-step progress lemma holds  for rewriteStep
    val bigStepResult = bigStep(p,ctx)
    
    log("Result of bigStep rewrite: " + PrettyPrinter.programToString(p) + "-LF->" + bigStepResult.toString())
    
    bigStepResult
  }
  
  def bigStep(p:Program, ctx:Set[Channel]):LFResult = {
    if(L1().applies(p, ctx))
      {log("Applying L1");(L1().apply(p,ctx))}
    else if(L2().applies(p, ctx))
      {log("Applying L2 to " + PrettyPrinter.programToString(p));(L2().apply(p,ctx))}
    else if(L3().applies(p, ctx))
      {log("Applying L3");(L3().apply(p,ctx))}
    else if(L4().applies(p, ctx))
      {log("Applying L4");(L4().apply(p,ctx))}
    else {log("No LF rules are applicable to " + PrettyPrinter.programToString(p));(LinearForm(None, Some(p), None,None))}
  }
}

/**
 * The result of a rewrite of lf[program]
 */
sealed trait LFResult {
  def toSet:Set[LinearForm] = this match {
    case LinearForm(_,_,_,_)        => Set(this.asInstanceOf[LinearForm])
    case LFChoice(left,right)       => left.toSet.union(right.toSet)
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
   * Splits a Sequence into three parts: a precursor, a synch operation, and a 
   * successor or remainder. E.g.:
   * a;!b;c => [a, b, c]
   * !b;c => [NONE, b, c]
   * a;!b => [a,b,MPME]
   * a; !b; !c; d => [a, !b, !c, d]
   * vocabulary: [pred, synch, succ]; input sequence: (left,right)
   */
  def splitSequence(s:Sequence) : ProgramTriple = {
  
    val (unnormalLeft,unnormalRight) = s match {
      case Sequence(l,r) => (l,r)
    }
    
    //Put left and right into a form in which cursors do not precede a Sequence.
    //This is necessary for recursion to go all the way through, and is the 
    //correct behavior sense there is no LinearForm rule defined on sequences.
    def removeLeadingCursors(p:Program):Program = p match {
      case CursorBefore(next) => removeLeadingCursors(next)
      case _                  => p
    }
  
    val left = removeLeadingCursors(unnormalLeft) match {
      case Sequence(l_left, l_right) => Sequence(l_left, l_right)
      case _                         => unnormalLeft
    }
    val right = removeLeadingCursors(unnormalRight) match {
      case Sequence(r_left, r_right) => Sequence(r_left, r_right)
      case _                         => unnormalRight
    }
    
    //Recurse structurally on the left, and handle the base case.
    val leftResult = left match {
      case Sequence(_,_) => splitSequence(left.asInstanceOf[Sequence])
      case _             => 
        if(left.isSynchronizationFree)
          Triple.apply(Some(left),None,None)
        else
          Triple.apply(None,Some(left),None)
    }
    
    //Recurse structurally on the right, and handle the base case.
    val rightResult = right match {
      case Sequence(_,_) => splitSequence(right.asInstanceOf[Sequence])
      case _ => 
        if(right.isSynchronizationFree) 
          Triple.apply(Some(right), None, None)
        else
          Triple.apply(None,Some(right), None)
    }
    
    //Extract out the options on the left and right sides.
    val (lpredOpt,lsyncOpt,lsucOpt) = Triple.unapply(leftResult) match {
      case None          => (None,None,None)
      case Some((a,b,c)) => (a,b,c)
    }
    
    val (rpredOpt,rsyncOpt,rsucOpt) = Triple.unapply(rightResult) match {
      case None          => (None,None,None)
      case Some((a,b,c)) => (a,b,c)
    }
    
    /* Merge the left and right results.
     * 
     * In this explanation, ? indicates we don't care if the place is defined or
     * not, and _ indicates we expect that it is not defined. A name indicates
     * we expect the place is defined.
     * 
     * We consider 5 possible cases for the results of recursion on the left and
     * right hand sides.
     * 
     * The first sync will be on the left, on the right, or nowhere (in a sync-free
     * sequence). If a sync does occur, then we have to compose the entire right
     * with the suc of left, or the entire left with the pred of right. So we
     * have 5 cases to consider:
     *  - no sync
     *  - sync on left, left.suc defined
     *  - sync on left, left.suc not defined
     *  - sync on right, right.pred defined
     *  - sync on right, right.pred not defined
     * 
     * If left.sync is defined, then we want to compose the left successor with
     * the right side:
     *     Case 1: left = [?, lsync, _]     ---> [?, lsync, right].
     *     Case 2: left = [?, lsync, lsuc] ---> [?, lsync, lsuc; right].
     *     
     * If left.sync is not defined, then we know that the entire left hand side
     * is sync free. Now we have to consider right.sync. If
     * right.sync is not defined, then there is no sync on the left or the right
     * In this case, we can simply put everything in the first position:
     *     Case 3: right = [?, _, _] --> [left;right, _, _]
     * 
     * However, if right.sync is defined then we want to put right.pred and left
     * into pred. To do this, we have to consider whether right.pred is defineD:
     *     case 4: right = [rpred, rsync, ?] --> [left;rpred, rsync, ?]
     *     case 5: right = [_, rsync, ?] --> [left, rsync, ?]
     */

    //left = [pred, sync, succ] ---> 
    lsyncOpt match {
      case Some(_) => lsucOpt match {
        case None => Triple.apply(lpredOpt, lsyncOpt, Some(right)) //case 1
        case Some(lsuc) => Triple.apply(lpredOpt, lsyncOpt, Some(Sequence(lsuc,right))) //case 2
      }
      case None    => rsyncOpt match {
        case None        => Triple.apply(Some(s),None,None) //case 3
        case Some(rsync) => {
          //Choose the value of predecessor for cases 4 and 5.
          val pred = rpredOpt match {
            case None        => left //case 4
            case Some(rpred) => Sequence(left, rpred) //case 5
          }
          Triple.apply(rpredOpt, rsyncOpt, Some(pred)) //finish up cases 4&5
        }
      }
    }
//    
//    //Finally, ensure that the result's sync is not a sequence.
//    //This should never hapen for normal sequences, but could happen if the 
//    //sequence is preceeded by some number of cursors.
//    val(predOpt, syncOpt, sucOpt) = Triple.unapply(result) match {
//      case Some((a,b,c)) => (a,b,c)
//      case None          => (None,None,None)
//    }
//    
//    val syncIsSequence = syncOpt match {
//      case Some(CursorBefore(Sequence(l,r))) => true
//      case Some(Sequence(l,r)) => throw new Exception("split doesn't meet spec.")
//    }
//    
//    if(syncIsSequence) {
//      val syncResult = syncOpt.get match {
//        case CursorBefore(Sequence(l,r)) => splitSequence(Sequence(l,r)) 
//      }
//      
//      val (syncpred, syncsync, syncsuc) = Triple.unapply(syncResult) match {
//        case Some((a,b,c)) => (a,b,c)
//        case None          => (None,None,None)
//      }
//      
//      
//    }
//    else {
//      result
//    }
  }

  /**
   * Rewrites a program p -> (cursor-free portion, g). Strips the leading
   * cursor.
   */
  def cursorRewriteSubprogram(p:Program, ctx:Set[Channel]) = {
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
   * Projects out the defined portions of a list of program options, then 
   * combines them in a sequence. Examples:
   * [None, P1, P2] => Sequence(P1,P2)
   * [P1, None, P2, P2] => Sequence(Sequence(p1,p2),p3)
   */
  def sequentializeDefined(l : List[Option[Program]]) = {
    val filtered = l.filter(_.isDefined).map(x => x match {
      case Some(x) => x
      case _ => throw new Exception //won't get here.
    })
    filtered.reduce((a,b) => Sequence(a,b))
  }
}

case class L1 extends LFRule {
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

case class L2 extends LFRule {
  def apply(p:Program, ctx:Set[Channel]) = {
    p match {
      case CursorBefore(syncOrEpsilon) => syncOrEpsilon match {
        case Send(_,_,_)    => LinearForm(None,Some(syncOrEpsilon),None,None)
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
          case Some(gamma)               => cursorRewriteSubprogram(gamma, ctx)
          case None                      => (None,None)
        }

        LinearForm(predOpt, Some(sync), v, gammaPrime)
      } 
      
      case _ => throw new LRDoesNotApply //non-cursor and non-sequence
    }
  }
  
  def applies(p:Program, ctx:Set[Channel]) = {
    p match {
      case CursorBefore(syncOrEpsilon) => syncOrEpsilon match {
        case Send(_,_,_)    => true
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
            case Send(_,_,_) => true
            case Receive(_,_) => true
            case Epsilon() => true
            case Evolution(_,_) => true
            case _ => false
          }
          case _ => throw new Exception("split is implemented incorrectly.") //non-cursor sync. shouldn't even get here.
        }
      } 
      
      case _ => false //non-cursor and non-sequence
    }
  }
}


case class L3 extends LFRule {
  def applyWith(u:Option[Program], p:CursorBefore, ctx:Set[Channel], gamma:Option[Program]) = {
    val (a,b) = p match {
      case CursorBefore(Choice(l,r)) => (l,r)
      case _           => throw new LRDoesNotApply
    }
    
    val (v,aPrime) = cursorRewriteSubprogram(a, ctx)
    val (w,bPrime) = cursorRewriteSubprogram(b, ctx)
    
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


case class L4 extends LFRule {
  def applyWith(u:Option[Program], p:CursorBefore, ctx:Set[Channel], gamma:Option[Program]) = p match {
    case CursorBefore(STClosure(a)) => {
      val (v,aPrimeOpt) = cursorRewriteSubprogram(a, ctx)
      
      val aPrime = aPrimeOpt match {
        case Some(CursorBefore(_)) => aPrimeOpt
        case Some(_) => Some(CursorBefore(aPrimeOpt.get))
        case None => aPrimeOpt
      }
      
      val left = sequentializeDefined(u::v::aPrime::Some(Epsilon())::Some(STClosure(a))::gamma::Nil)
      val right = sequentializeDefined(u::Some(CursorBefore(Epsilon()))::gamma::Nil)
      
      LFChoice(LFRewrite.rewrite(left, ctx), LFRewrite.rewrite(right,ctx))
    }
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