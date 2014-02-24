package pdl.core

import scala.xml.transform.RewriteRule

object PdlRewrite {
  def rewrite(p:Program):Program = {
    if(p.isCursorFree) {
      CursorRewrite.rewriteWithJoin(CursorBefore(p), Set[Channel]())
    }
    else {
      CursorRewrite.rewriteWithJoin(p, Set[Channel]())
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Begin join algorithm implementation.
  //////////////////////////////////////////////////////////////////////////////
  
  /*
   * The R, S and H sets can contain elements of many different types throughout
   * the execution of the algorithm. These are captured in terms of label and 
   * value types below.
   * 
   * The paper's implementation of the algorithm uses something like Set[Any,Any].
   * Hypothetically that works here, but explicit pattern  matching is no less 
   * readable than implicit casts and is quite useful for debugging.
   */
  
  /**
   * A member of the R set - allow programs with remainders and labels in them
   */
  sealed class RMember(val key:RValue, val value:RValue)
  sealed trait RValue
  case class RProgram(p:Program)           extends RValue
  case class RNothing()                      extends RValue
  case class RPSet(val P:Set[PMember])     extends RValue
  
  /**
   * A member of the S set
   */
  sealed class SMember(val label:Int, val program:Program)
  
  /**
   * A member of the P set -- either a ~ b or a program.
   */
  sealed trait PMember {
    private def replaceInProgram(remainder:Remainder, label:Int, program:Program) = {
      program.applyToSubprograms(p => {
        if(p.equals(remainder)) Label(label)
        else                    p
      })
    }
    private def replaceInLF(remainder:Remainder, label:Int, lf:LinearForm) = {
      val uOpt = lf.u match {
        case Some(u) => Some(replaceInProgram(remainder,label,u))
        case None    => None
      }
      val syncOpt = lf.sync match {
        case Some(sync) => Some(replaceInProgram(remainder,label,sync))
        case None    => None
      }
      val vOpt = lf.v match {
        case Some(v) => Some(replaceInProgram(remainder,label,v))
        case None    => None
      }
      val gammaOpt = lf.gamma match {
        case Some(gamma) => Some(replaceInProgram(remainder,label,gamma))
        case None    => None
      }
      new LinearForm(uOpt,syncOpt,vOpt,gammaOpt)
    }
    
    def replaceRemainderWithLabel(remainder:Remainder, label:Int):PMember = this match {
      case PProgram(p) => {
        val new_p = 
          p.applyToSubprograms(program => {
            if(program.equals(remainder)) Label(label)
            else                          p
          })
        PProgram(new_p)
      }
      case PTilde(left,right) => new PTilde(replaceInLF(remainder,label,left), replaceInLF(remainder,label,right))
    }
  }
  case class PTilde(val left:LinearForm, val right:LinearForm) extends PMember
  case class PProgram(val p:Program) extends PMember
  
  
  /**
   * A member of the H set
   */
  sealed class HMember(val label:Program, val program:Program) {
    /**
     * Replaces all instances of sub-programs in program with label.
     */
    def replaceLabel(labelToReplace:Program, newKey:Program) = 
      if(labelToReplace.equals(label)) {
         new HMember(newKey, program)
      }
      else {
        this
      }
  }
  sealed trait HKey
  case class HProgram(program:Program) extends HKey
  

  /**
   * Gives unique labels.
   */
  object LabelFactory {
    private var count = 0
    def getNext():Int = {
      count = count + 1
      count
    }
  }

  
  def join(a:Program, b:Program):Program = {
    val Ca = a.communicationType; val Cb = b.communicationType
    val (u,aPrime) = CursorRewrite.rewrite(a, Cb).splitAtCursor
    val (v,bPrime) = CursorRewrite.rewrite(b, Ca).splitAtCursor
    
    //Line 5
    val firstLabel = LabelFactory.getNext; 
    var H = Set[HMember](); 
    var R = initializeR(u,v,aPrime,bPrime, firstLabel)
    var S = initializeS(aPrime, bPrime, firstLabel)
    val initialRMember = R.last
    
    //Line 6..26
    while(!S.isEmpty) {
      //Line 7
      val e = S.last
      val m = e.label
      val (l,r) = e.program match {
        case JoinedParallel(l,r) => (l,r)
        case _ => throw new Exception("Only expected joined parallels in S.")
      }
      
      //Line 9
      var P = Set[PMember]()
      
      //Line 8,9
      val Ll = LFRewrite.rewrite(l, Cb)
      val Lr = LFRewrite.rewrite(r, Ca)
      
      /* create pairs containing all e- and non-e-transitions */
      //non-e-transitions lines 8-10
      for(left <- Ll.toSet) 
        for(right <- Lr.toSet) 
          if(!left.sync.get.isInstanceOf[Epsilon] && !right.sync.get.isInstanceOf[Epsilon])
            P = P + PTilde(left,right)
      //left e-transitions lines 11-12
      for(left <- Ll.toSet) 
        for(right <- Lr.toSet) 
          if(left.sync.get.isInstanceOf[Epsilon]) {
            val parLeft = Sequence(left.u.get, left.gamma.get) //safe?
            PProgram(Remainder(JoinedParallel(parLeft, r)))
          }
      //right e-transitions line 13
      for(right <- Lr.toSet) 
        for(left <- Ll.toSet) 
          if(left.sync.get.isInstanceOf[Epsilon]) {
            val parRight = Sequence(right.u.get, right.gamma.get) //safe?
            PProgram(Remainder(JoinedParallel(l, parRight)))
          }
      
      /* merging */
      P = P.map(p => p match {
        case PTilde(left,right) => PProgram(MergeRewrite.rewrite(left, right, Cb, Ca))
        case PProgram(r)        => PProgram(r)
      })
      
      /* recursion */
      //16-21.
      for(remainderCandidate <- P) remainderCandidate match {
        case PProgram(Remainder(remainingProgram)) => {
          val inH = !H.filter(p => p.program.equals(remainingProgram) && p.label.isInstanceOf[Label]).isEmpty
          val inS = !S.filter(p => p.program.equals(remainingProgram)).isEmpty
          //Find or create label required for replacement (lines 16, 19)
          val label:Int = 
            if(inH)      H.filter(p => p.program.equals(remainingProgram)).last.label match {
              case Label(l) => l
              case _         => throw new Exception("should've filtered this out in inH")
            }
            else if(inS) S.filter(p => p.program.equals(remainingProgram)).last.label
            else {
              val label = LabelFactory.getNext
              S = S + (new SMember(label, remainingProgram))
              label
            }
          //line 21
          P = P.map(p =>  p.replaceRemainderWithLabel(Remainder(remainingProgram), label))
        }
        case _ => //skip
      }

      //lines 22-24
      H = H + new HMember(Label(e.label), e.program)
      R = R + new RMember(RProgram(Label(m)),new RPSet(P))
      S = S.filter(!_.equals(e))
    }
    
    /* transformation back into loop form */
    while(!R.filter(!_.key.equals(initialRMember.key)).isEmpty) {
      val nonTerminalRMembers = R.filter(!_.key.equals(initialRMember.key))
      
      //26-28
      while(!R.filter(line26Filter).isEmpty) {
        val member = R.filter(line26Filter).last
        val key = member.key match {
          case RProgram(k) => k
          case _           => throw new Exception("Thought all replacements into H keys would be programs. May bnot be correct.")
        }
        
        try {
          for(choice <- member.value.asInstanceOf[RPSet].P) {
            choice match {
              case PProgram(Sequence(a_i, Choice(s_i, gamma))) => {
                //Line 27
                H = H.map(h => h.replaceLabel(key, Sequence(a_i, Choice(s_i, gamma))))
                //Line 28
                R = R.filter(!_.equals(member))
              }
              case _ => throw new Exception("Expected line26Filter to filter out this instance.")
            }
          }
          } 
        catch {
          case e:ClassCastException => throw new Exception("Expected line26Filter to filter out any case exception")
        }
      }
      
      //from here on out interpreting paper's biding so that a;b++c;d = (a;b)++(c;d); 
      //or, a++b;c=a++(b;c) which is different than but seems to be the author's intent.
      
      //Line 29
      R = R.map(r => 
        r.value match {
          case RProgram(Choice(Sequence(a,s_n), Sequence(b,s_n2))) => {
            if(s_n.equals(s_n2)) 
              new RMember(r.key, RProgram(Sequence(Choice(a,b), s_n)))
            else 
              r 
          }
          case _ => r
      })
    
      //Line 30 part 1 (before the "and")
      R = R.map(r =>
        r.value match {
          case RProgram(program) => new RMember(r.key, RProgram(program.applyToSubprograms(line30Transformamtion1)))
          case _ => r
        }
      );
    
      //Line 30 part 2 (after the "and")
      //Determine if and B;B* exist; if they do, count > 0.
      var count = 0
      R.map(r => r.value match {
        case RProgram(program) => {
          program.applyToSubprograms(p => p match {
            case Sequence(b, STClosure(alsoB)) => {
              if(b.equals(alsoB)) count = count + 1;
              p
            }
            case _ => p})
        }
      })
      //If we didn't find an intance of B;B*, do the second line 30 transformation.
      if(count == 0) {
        R = R.map(r => {
          r.value match {
            case RProgram(Choice(STClosure(a), Epsilon())) => 
              new RMember(r.key, RProgram(STClosure(a)))
            case _ => 
              r
          }
        })
      }
    
      //Line 31 and 32 all in one go:
      for(r <- R) {
        if(!r.key.equals(initialRMember.key)) {
          //Find out if the form matches. If it does, do the rewriting.
          r.value match {
            case RProgram(Choice(Sequence(a_m, s_m), gammaPrime)) => {
              if(line31GammaTest(gammaPrime, s_m)) { //check form of gammaPrime
                val gamma = line31GetGamma(gammaPrime).get
                H = H.map(h => h.program match {
                  case Choice(Sequence(candidate_a_m,candidate_s_m), candidate_gamma) => {
                    //Note sure if this conditional is correct.
                    if(s_m.equals(candidate_s_m) && candidate_a_m.equals(a_m) && gamma.equals(candidate_gamma)) {
                      //Do the replacement.
                      new HMember(h.label, Sequence(STClosure(candidate_a_m), candidate_gamma))
                    }
                    else h
                  }
                  case _ => h
                });
              }
            }
            case _ => //ok
          }
        }
      }
    }
    
    //Line 33
    R.filter(_.equals(initialRMember)).last.value.asInstanceOf[RProgram].p
  }
  
  //Linr 31 gamma structure match.
  private def line31GammaTest(program:Program, s_m:Program):Boolean = program match {
    case Choice(a,b) => {
      a match {
        case Choice(al,ar) => {
          if(line31GetGamma(a).isDefined)
            line31GammaTest(a, s_m) && line31GetGamma(a).get.equals(b)
          else
            false
        }
        case Sequence(a_i, s_i) => !s_i.equals(s_m)
        case _ => false
      }
    }
    case _ => false
  }
  private def line31GetGamma(program:Program):Option[Program] = program match {
    case Choice(l,r) => l match {
      case Choice(ll,lr) => line31GetGamma(l)
      case _ => Some(r)
    } 
    case _ => None
  }
  
  //Line 30 part 1
  private def line30Transformamtion1(program:Program):Program = program match {
    case Choice(Sequence(a, STClosure(alsoA)), Epsilon()) => {
      if(a.equals(alsoA))
        Choice(STClosure(a), Epsilon())
      else
        program
    }
    case _ => program
  }
    
  def line26Filter(r : RMember) = r.value match {
    case RPSet(programsInChoice) => {
      val formsAreCorrect = programsInChoice.map(choice => choice match {
        case PProgram(Sequence(choice_l, Choice(choice_r_l, choice_r_r))) => true
        case _ => false
      })
      formsAreCorrect.foldLeft(true)((a,b) => a && b)
    }
    case _ => false
  }
      
        
        
  /**
   * Inserts u||v => a||b into R.
   * @returns non-null.
   */
  private def initializeR(u:Option[Program], v:Option[Program], a:Option[Program], b:Option[Program], firstLabel:Int):Set[RMember] = {
    val key:RValue = u match {
      case Some(uPrime) => v match {
        case Some(vPrime) => RProgram(JoinedParallel(uPrime,vPrime))
        case None         => RProgram(uPrime)
      }
      case None => v match {
        case Some(vPrime) => RProgram(vPrime)
        case None         => RNothing()
      }
    }
    
    val value:RValue = a match {
      case Some(aPrime) => b match {
        case Some(bPrime) => RProgram(JoinedParallel(aPrime,bPrime))
        case None         => RProgram(aPrime)
      }
      case None => b match {
        case Some(bPrime) => RProgram(bPrime)
        case None         => RNothing()
      }
    }
    
    value match {
      case RNothing() => Set(new RMember(key, RProgram(Label(firstLabel))))
      case RProgram(v)=> Set(new RMember(key, RProgram(Sequence(v, Label(firstLabel)))))
    }
  }
  
  private def initializeS(a:Option[Program], b:Option[Program], firstLabel:Int):Set[SMember] = {
    val value = a match {
      case Some(aPrime) => b match{
        case Some(bPrime) => Some(JoinedParallel(aPrime,bPrime))
        case None         => Some(aPrime)
      }
      case None => b match {
        case Some(bPrime) => Some(bPrime)
        case None         => None
      }
    }
    
    value match {
      case Some(valuePrime) => Set[SMember](new SMember(firstLabel, valuePrime))
      case None             => Set[SMember]()
    }
  }
}

