package pdl.core

object PdlRewrite {
  def rewrite(p:Program):Program = {
    val result = if(p.isCursorFree) {
      CursorRewrite.rewriteWithJoin(CursorBefore(p), Set[Channel]())
    }
    else {
      CursorRewrite.rewriteWithJoin(p, Set[Channel]())
    }
    
    ExtraRewrites.cleanup(result) 
  }
  
  def join(a:Program,b:Program):Program = JoinAlgorithm.join(a,b)
}

object JoinAlgorithm {
  def join(alpha:Program, beta:Program):Program	 = {
    //line 2
    val alpha_type = alpha.communicationType
    val beta_type  = beta.communicationType
    
    //Line 3
    val alphaParallelbeta = JoinedParallel(alpha,beta)
    val initialR = 
      new Element(alphaParallelbeta, Label(LabelFactory.consume))
    val initialS = 
      new Element(Label(LabelFactory.current), alphaParallelbeta)
    var H = List[Element]()
    var R = List[Element](initialR)
    var S = List[Element](initialS)
    
    //Lines 4-21
    while(!S.isEmpty) {
      //line 5: pick e = (Sm = l||r) from S
      val e     = S.last
      val S_m   = e.lhs
      val (l,r) = e.rhs match {
        case JoinedParallel(left,right) => (left,right)
        case _                          => throw new Exception
      }
      
      //line 6: apply (Li) rewrites to compute Ll=lf[.l] and Lr=lf[.r]
      val Ll = LFRewrite.rewrite(CursorBefore(l), beta_type)
      val Lr = LFRewrite.rewrite(CursorBefore(r), alpha_type)
      
      //Line 7: P = \epsilon
      var P = List[PElement]()
      
      /* create pairs containing all e- and non-e-transitions */
      
      //Line 8-10: for each non-epsilon-transition li=(ui,si,ai) in Ll and 
      //rj=(vj, sj, bj) in Lr, P=P ++ li~rj
      for(li <- Ll.toSet) {
        for(rj <- Lr.toSet) {
          P = P :+ PTilde(li, rj)
        }
      }
      
      //lines 11-12: for each e-transition li=(ui,e,ai) in Ll, P=P++R(ui;ai||r)
      for(li <- Ll.toSet.filter(_.sync.equals(Epsilon()))) {
        //Project out the u and gamma values.
        val sequence = li.u match {
          case Some(u_i) => li.gamma match {
            case Some(a_i) => Sequence(u_i,a_i)
            case None      => u_i
          }
          case None      => li.gamma.getOrElse(Epsilon()) //?
        }
        //Add the new remainder to P
        val remainder = Remainder(JoinedParallel(sequence,r))
        P = P :+ PProgram(remainder)
      }
      /* e-transitions */
      //Line 13: same thing for Lr
      for(ri <- Lr.toSet.filter(_.sync.equals(Epsilon()))) {
        val sequence = ri.u match {
          case Some(v_i) => ri.gamma match {
            case Some(b_i) => Sequence(b_i,b_i)
            case None      => v_i
          }
          case None      => ri.gamma.getOrElse(Epsilon()) //?
        }
        val remainder = Remainder(JoinedParallel(sequence,l))
        P = P :+ PProgram(remainder)
      }
    
      /* merging */
      //Line 14: Apply (Mi) rewrites to P and remove deadlocks in compositions.
      P = P.map(element => element match {
        case PTilde(left,right) => PProgram(MergeRewrite.rewrite(left, right))
        case _                  => element
      })
      P = P.map(_.removeDeadlocks)
    
      /* recursion */
      //For each remainder alpha_i||beta_j in P do: lines 16-21
      val PBeforeRecursion =  null//prevent inf recursion due to modifications of P
      for(r <- P.filter(_.isRemainder())) {
        //get alpha_i and beta_i from the PElement.
        val remainder = r.getRemainder()
        val (alpha_i, beta_j) = remainder match {
          case JoinedParallel(left,right) => (left,right)
          case _                          => throw new Exception
        }
        val composition = JoinedParallel(alpha_i, beta_j)
    
        //Line 16-18
        val elementWithMatchingRhs = H.union(S).find(
            x=>x.rhs.equals(composition) && x.lhs.isInstanceOf[Label])
        //line 16
        if(elementWithMatchingRhs.isDefined) {
          //line 17
          val S_n = elementWithMatchingRhs.get.lhs.asInstanceOf[Label]
          P = P.map(_.replace(remainder, S_n))
        }
        else {
          //Line 119: Allocate a fresh label
          val S_n = Label(LabelFactory.consume)
          //Line 20: Add s_n=a_i||b_j to S
          S = S :+ new Element(composition, S_n)
          //Line 21: Replace as in line 17.
          P = P.map(_.replace(remainder, S_n))
        }
      }
        
      //This deviates from the algorithm in the paper. We need to convert P
      //into a program.
      val PasProgram = P.map(_.asProgram).reduce(Choice(_,_))

      //Line 22 - 24
      H = H :+ e
      R = R :+ new Element(S_m, PasProgram)
      S = S.filter(!_.equals(e))

    }
    
    //Temporary: show what we have after line 24.
    log("After line 24:")
    logSets(H,R,S)
    log("beginning transformation into loop form.")
    
    /* transformation back into loop form */
    //line 25
    while(!candidatesForTransform(R,initialR).isEmpty)
    {
      //Temporary
      log("Beginning of outer while loop:")
      logSets(H,R,S)
   
      //line 26
      while(!line26filter(R,alphaParallelbeta).isEmpty) {
        val elementToRemove = line26filter(R,alphaParallelbeta).last
        //line 28
        R = R.filter(!_.equals(elementToRemove))
        //line 27
        R = R.map(_.replace(elementToRemove.lhs, elementToRemove.rhs))        
      }
      
      //The rest of the while loop is a series of complicated rewrites, implemented
      //in these helper methods (lines 29-32):
      R = line29rewrite(R)
      R = line30rewrite(R)
      H = line31rewrite(H,R,initialR)
    }
    
    //Temporary: show what we have after the algorithm completes..
    log("Exiting the algorithm:")
    logSets(H,R,S)
    
    //Line 32: return the right hand side of S_alpha||beta
    R.filterNot(_.rhs.equals(alphaParallelbeta)).last.rhs
  }

  //////////////////////////////////////////////////////////////////////////////
  // Section: STD OUT logging.
  //////////////////////////////////////////////////////////////////////////////
  val LOGGING_ENABLED = true
  def log(s:String) = if(LOGGING_ENABLED) println(s) else null
  def logSets(H:List[Element], R:List[Element], S:List[Element]):Unit = {
    log(H.map(_.toString).foldLeft("H=")((a,b) => a + b.toString +", "))
    log(R.map(_.toString).foldLeft("R=")((a,b) => a + b.toString+", "))
    log(S.map(_.toString).foldLeft("S=")((a,b) => a + b.toString+", "))
  }
    
  
  //////////////////////////////////////////////////////////////////////////////
  // Section: Helper methods for join.
  //////////////////////////////////////////////////////////////////////////////
  /**
   * @returns All elements of R whose LHS is S(a||b)
   */
  private def candidatesForTransform(R:List[Element], initialR:Element) = {
    R.filter(!_.lhs.equals(initialR.lhs))
  }
  
  private def line26filter(R:List[Element], alphaParallelbeta:Program):List[Element] = {
    R.filter(r => {
      log(r.lhs + "\t" + r.rhs)
      !r.lhs.equals(alphaParallelbeta) && !r.rhs.contains(r.lhs)
    })
  }
  
  /**
   * Implements the rewrite on line 29 of the join algorithm in the PDL paper.
   * 
   * Applies the rewriting following to **both sides** of each equation in R:
   *   left_l;s_n U right_l;s_n |--> (left_l U right_l); s_n
   */
  private def line29rewrite(R:List[Element]):List[Element] = {
    /**
     * The rewrite implementation for a single program.
     * Below, we apply this to both sides of each equation in R.
     */
    def rewrite(p:Program) = p match{
      case Choice(left,right) => {
        //Extract the s_n component of each side, as well as any prefix.
        val (left_l:Option[Program], s_left:Program) = left match {
          case Sequence(ll, lr) => (Some(ll), lr)
          case _                => (None, left)
        }
        val (right_l:Option[Program], s_right:Program) = right match {
          case Sequence(rl,rr) => (Some(rl), rr)
          case _               => (None, right)
        }
        
        //If the rewrite applies, construct the new left-hand side.
        if(s_left.equals(s_right)) {
          //construct the left hand side (might be nothing)
          val newLhsOpt:Option[Program] = left_l match {
            case Some(ll) => right_l match {
              case Some(rl) => Some(Sequence(ll,rl))
              case None     => Some(ll)
            }
            case None => right_l match {
              case Some(rl) => Some(rl)
              case None     => None
            }
          }
          
          //Return the final result.
          newLhsOpt match {
            case Some(newLhs) => Sequence(newLhs, s_left) //or s_right, doesn't matter.
            case None         => s_left
          }
        }
        else {
          p //the S_n's on the left and right don't match, so do not rewrite.
        }
      }
      case _                  => p //The program is not a choice at the top-level, so do not rewrite.
    }
    
    //Apply the rewrite to **both sides** of each element in R
    R.map(r => new Element(rewrite(r.lhs), rewrite(r.rhs)))
  }
  
  /**
   * Rewrite equations containing terms of the form a;a* U \eps into a* U \eps
   * and collapse a* U eps into a* where no other terms B;B* remain.
   */
  private def line30rewrite(R:List[Element]) = {
    //We break the rewrite into two passes -- one to roll up the loop and another
    //to remove the epsilons.
    def reroll(p:Program) = p match {
      case Choice(Sequence(alpha, STClosure(alsoAlpha)), Epsilon()) => {
        if(alpha.equals(alsoAlpha)) {
          Choice(STClosure(alpha), Epsilon())
        }
        else {
          p
        }
      }
      case _                   => p
    }
    
    def ignoreEpsilonChoices(p:Program) = p match {
      case Choice(STClosure(alpha), Epsilon()) => {
        //TODO-MarcusQuestion: only when no other B;B* exist...?
        STClosure(alpha)
      }
      case _                                   => p
    }
    
    //TODO-MarcusQuestion should we iterate ``reroll" until a fixed point?
    //TODO-MarcusQuestion Same question for ``ignoreEpsilonChoices"
    def rewrite(p:Program) = ignoreEpsilonChoices(reroll(p))
    
    //Apply the rewrite
    R.map(r => new Element(rewrite(r.lhs), rewrite(r.rhs)))
  }
  
  /**
   * If an equation S_m != S_a||b of the form S_m==a_m;S_m U gamma'
   */
  private def line31rewrite(H:List[Element],R:List[Element],initialR:Element):List[Element]= {
    /**
     * used in rewrite.
     */
    def checkGammaForm(gammaPrime:Program, S_m:Program):Boolean = gammaPrime match {
      case Choice(left,right) => checkGammaForm(left,S_m) && !right.equals(S_m)
      case Sequence(a_i,s_i)  => !s_i.equals(S_m)
      case _                  => !gammaPrime.equals(S_m)
    }
    
    /**
     * Rewrites a single element.
     */
    def rewrite(eqn:Element):Option[Element] = {
      val S_m = eqn.lhs
      
      eqn.rhs match {
        case Choice(rhs_left, gamma)         => {
          //Ensure that gamma has the expected form, and then recurse on the left.
          if(checkGammaForm(gamma, S_m)) {
            rewrite(new Element(eqn.lhs, rhs_left))
          }
          else {
            None //Rewrite does not apply
          }
        }
        case Sequence(a_m, s_m_candidate) => {
          if(S_m.equals(s_m_candidate)) {
            Some(new Element(eqn.lhs, STClosure(a_m)))
          }
          else {
            //rewrite does not apply.
            None
          }
        }
        case _                            => {
          if(eqn.rhs.equals(S_m)) {
            None //This should not be allowed TODO-MarcusQuestion correct?
            //We return instead of throwing an exn because we simply don't apply
            //the rewrite where it does not apply. This way we can pass stuff in
            //from R at will. TODO not sure if that's really OK.
          }
          else {
            //rewrite does not apply.
            None
          }
        }
      }
    }
    
    var HResult = H
    
    //Rewrite relevant elements of H
    for(r <- R) {
      val resultOpt = rewrite(r)
      
      resultOpt match {
        case Some(result) => {
          HResult = HResult.map(h => if(h.lhs.equals(result.lhs)) result else h)
        }
        case None => //okay
      }
    }
    
    HResult
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Section: Data structures for join.
  //////////////////////////////////////////////////////////////////////////////
    
  /**
   * An element of the H, R or S sets.
   */
  private class Element(val lhs:Program, val rhs:Program) {
    override def toString = lhs.prettyString + Symbols.EQUIV + rhs.prettyString
    
    def replace(oldProgram:Program, newProgram:Program) = {
      val newLhs = lhs.apply(p=>if(p.equals(oldProgram)) newProgram else p)
      val newRhs = rhs.apply(p=>if(p.equals(oldProgram)) newProgram else p)
      new Element(newLhs, newRhs)
    }
  }
  
  /**
   * An element of the set ``P" constructed in lines 6-21 of the join algorithm.
   * Programs, Tildes and untions of the two are allowed.
   */
  private sealed trait PElement {
    def removeDeadlocks():PElement = this match {
      case PProgram(p)         => PProgram(p match {
        case Choice(l,r) => {
          if(l.equals(Deadlock()))       r
          else if(r.equals(Deadlock()))  l
          else                           p
        }
        case _            => p
      })
      case PUnion(left,right) => PUnion(left.removeDeadlocks,right.removeDeadlocks)
      case PTilde(_,_)        => this
    }
    
    /**
     * @returns true iff this element is a remainder
     */
    def isRemainder() = this match {
      case PProgram(p) => p.isInstanceOf[Remainder]
      case _           => false
    }
    
    /**
     * @returns projected remainder.
     */
    def getRemainder() = this match {
      case PProgram(Remainder(r)) => r
      case _                      => throw new Exception("Isn't a remainder.")
    }
    
    /**
     * @returns this with all occurences of remainder replaces with label.
     */
    def replace(remainder:Program, label:Label):PElement = {
      def replaceFn(program:Program):Program = 
        if(program.equals(remainder)) label else program
      
      this match {
        case PProgram(p) => 
          PProgram(replaceFn(p))
        case PUnion(left, right) => 
          PUnion(left.replace(remainder,label), right.replace(remainder,label))
        case PTilde(left, right) =>
          PTilde(left.apply(replaceFn(_)), right.apply(replaceFn(_)))
      }
    }
    
    /**
     * @returns A program
     * @throws Exception if this is a PTilde.
     */
    def asProgram:Program = this match {
      case PProgram(p) => p
      case PUnion(l,r) => Choice(l.asProgram, r.asProgram)
      case PTilde(_,_) => throw new Exception
    }
    
    override def toString = this match {
      case PProgram(p)        => p.prettyString
      case PTilde(left,right) => left.prettyString + "~" + right.prettyString
      case PUnion(left,right) => left + " PUNION " + right
    }
  }
  
  private  case class PProgram(p:Program)                       extends PElement
  private  case class PTilde(left:LinearForm, right:LinearForm) extends PElement
  private  case class PUnion(left:PElement, right:PElement)     extends PElement 
//  {
//    //Ensure that the union was constructed properly.
//    if(left.isInstanceOf[PUnion])
//      throw new Exception("PUnion should have form C(1, C(2, C(3, ...)))")
//  }
  
  /**
   * Returns a unique label.
   */
  private object LabelFactory {
    var currentLabel = 0
    def consume = {
      val label = currentLabel
      currentLabel = currentLabel + 1
      label
    }
    def current = currentLabel-1
  } 
}