package pdl.core

class MRDoesNotApply extends Exception
/**
 * MRDoesNotApply is truly exceptional and unexpected, whereas DeadlockOnMerge
 * is an expected error.
 * TODO this is bad name. Basically it expressed a result where the merge
 * rules do not apply.
 */
class DeadlockOnMerge extends Exception

class EncounteredVInMergeRewrite extends Exception


@throws(classOf[DeadlockOnMerge])
object MergeRewrite {
//  def log(s:String) = println(s)
  def log(s:String) = null
  
  def rewrite(left:LinearForm, right:LinearForm, left_ctx:Set[Channel], right_ctx:Set[Channel]) : Program = {
    if(left.v.isDefined || right.v.isDefined)
      throw new EncounteredVInMergeRewrite
      
    //Don't even know if context matters? TODO-nrf if so, use the correct one.
    val ctx = left_ctx

    if(M1.applies(left, right, ctx)) {
      log("Applying M1");
      M1.apply(left,right,ctx)
    }
    else if(M2.applies(left,right,ctx)) {
      log("Applying M2");
      M2.apply(left,right,ctx)
    }
    else if(M3().applies(left,right,ctx)) {
      log("Applying M3");
      M3().apply(left,right,ctx)
    }
    else if(M4.applies(left,right,ctx)) {
      log("Applying M4");
      M4.apply(left,right,ctx)
    }
    else if(M5.applies(left,right,ctx)) {
      log("Applying M5")
      M5.apply(left,right,ctx)
    }
    else {
      throw new DeadlockOnMerge
    }
  }
}

/**
 * TODO-nrf all of these rules, as stated in the paper, indicate that the 'v'
 * component of the linear form should be undefined. We relax this constraint
 * below. Is that a real constraint? Why would it hold?
 * 
 * Question 2: What about the dotted potions of the rules?
 */
sealed trait MergeRule {
  def apply(pl:LinearForm, pr:LinearForm, ctx:Set[Channel]) : Program
  def applies(p:LinearForm, pr:LinearForm, ctx:Set[Channel]) : Boolean
  
  def parallelCompose(leftOpt:Option[Program], rightOpt:Option[Program]) = {
    leftOpt match {
      case Some(left) => rightOpt match {
        case Some(right) => Some(Parallel(left,right))
        case None        => Some(left)
      }
      case None => rightOpt match {
        case Some(right) => Some(right)
        case None        => None 
      }
    }
  }
  def parallelComposeRemainder(leftOpt:Option[Program], rightOpt:Option[Program]) = {
    parallelCompose(leftOpt,rightOpt) match {
      case Some(p) => Some(Remainder(p))
      case None    => None
    }
  }
}

object M1 extends MergeRule {
  def apply(pl:LinearForm, pr:LinearForm, ctx:Set[Channel]) = {
    val send = pl.sync match {
      case Some(Send(c,v)) => Send(c,v)
      case _                  => throw new MRDoesNotApply
    }
    
    val receive = pr.sync match {
      case Some(Receive(c,v)) => Receive(c,v)
      case _                  => throw new MRDoesNotApply
    }
    
    val commProgram = new Forward(send.channel, receive.vars, send.term)
    
    val sequence =  parallelCompose(pl.u, pr.u)  ::
                    Some(commProgram)            ::
                    parallelCompose(pl.v, pr.v)  ::
                    parallelComposeRemainder(pl.gamma, pr.gamma) :: Nil
    val filteredSequence = sequence.filter(p => p.isDefined).map(p => p match {
      case Some(p) => p
      case None    => throw new Exception("unreacable.")
    })
    filteredSequence.reduceRight((a,b) => Sequence(a,b))
  }
  
  def applies(pl:LinearForm, pr:LinearForm, ctx:Set[Channel]) = {
    val sendOpt = pl.sync match {
      case Some(Send(c,v)) => Some(Send(c,v))
      case _                  => None
    }
    
    val receiveOpt = pr.sync match {
      case Some(Receive(c,v)) => Some(Receive(c,v))
      case _                  => None
    }
    
    sendOpt match {
      case None       => false
      case Some(send) => receiveOpt match {
        case Some(receive) => send.channel.equals(receive.channel)
        case None          => false
      }
    }
  }
}


object M2 extends MergeRule {
  def apply(pl:LinearForm, pr:LinearForm, ctx:Set[Channel]) = {
    val rcvLeft = pl.sync match {
      case Some(Receive(c,v)) => Receive(c,v)
      case _                  => throw new MRDoesNotApply
    }
    
    val rcvRight = pr.sync match {
      case Some(Receive(c,v)) => Receive(c,v)
      case _                  => throw new MRDoesNotApply
    }
    
    val commProgram = new Receive(rcvLeft.channel, rcvLeft.vars.union(rcvRight.vars))
    
    val sequence =  parallelCompose(pl.u, pr.u)  ::
                    Some(commProgram)            ::
                    parallelCompose(pl.v, pr.v)  ::
                    parallelComposeRemainder(pl.gamma, pr.gamma) :: Nil
    val filteredSequence = sequence.filter(p => p.isDefined).map(p => p match {
      case Some(p) => p
      case None    => throw new Exception("Scala's filter function is broken if we get here.")
    })
    filteredSequence.reduceRight((a,b) => Sequence(a,b))
  }
  
  def applies(pl:LinearForm, pr:LinearForm, ctx:Set[Channel]) = {
    val rcvLeftOpt = pl.sync match {
      case Some(Receive(c,vs)) => Some(Receive(c,vs))
      case _                  => None
    }
    
    val rcvRightOpt = pr.sync match {
      case Some(Receive(c,v)) => Some(Receive(c,v))
      case _                  => None
    }
    
    rcvLeftOpt match {
      case None             => false
      case Some(rcvLeft)    => rcvRightOpt match {
        case Some(rcvRight)   => rcvLeft.channel.equals(rcvRight.channel)
        case None             => false
      }
    }
  }
}

case class M3 extends MergeRule {
  def applies(left:LinearForm, right:LinearForm, ctx:Set[Channel]) = {
    left.sync match {
      case Some(Forward(c,vs,f)) => right.sync match {
        case Some(Receive(c2,vs2)) => c.equals(c2)
        case _                     => false
      }
      case _ => false
    }
  }
  
  def apply(left:LinearForm, right:LinearForm, ctx:Set[Channel]) = {
    val leftSync = left.sync match {
      case Some(Forward(c,vs,f)) => Forward(c,vs,f)
      case None                  => throw new MRDoesNotApply
      case Some(_)               => throw new MRDoesNotApply
    }
    
    val rightSync = right.sync match {
      case Some(Receive(c,vs)) => Receive(c,vs)
      case None                => throw new MRDoesNotApply
      case Some(_)             => throw new MRDoesNotApply
    }
    
    if(!leftSync.channel.equals(rightSync.channel))
      throw new MRDoesNotApply
      
    val newSync = Forward(leftSync.channel, leftSync.vars.union(rightSync.vars), leftSync.value)
    
    val sequence =  parallelCompose(left.u, right.u)  ::
                    Some(newSync)            ::
                    parallelCompose(left.v, right.v)  ::
                    parallelComposeRemainder(left.gamma, right.gamma) :: Nil
    val filteredSequence = sequence.filter(p => p.isDefined).map(p => p match {
      case Some(p) => p
      case None    => throw new Exception("Scala's filter function is broken if we get here.")
    })
    filteredSequence.reduceRight((a,b) => Sequence(a,b))
  }
}
  
object M4 extends MergeRule {
  def applies(left:LinearForm, right:LinearForm, ctx:Set[Channel]) = {
    val leftIsBottom = left.sync match {
      case Some(Bottom()) => true
      case _          => false
    }
    
    val rightIsBottom = right.sync match {
      case Some(Bottom()) => true
      case _          => false
    }
    
    leftIsBottom && rightIsBottom
  }
  
  def apply(left:LinearForm, right:LinearForm, ctx:Set[Channel]) = {
    val leftSync = left.sync match {
      case Some(Bottom()) => Bottom()
      case _          => throw new MRDoesNotApply
    }
    
    val rightSync = right.sync match {
      case Some(Bottom()) => Bottom()
      case _          => throw new MRDoesNotApply
    }
    
    val uOpt = parallelCompose(left.u, right.u)
    
    uOpt match {
      case Some(u) => Sequence(u, Bottom())
      case None    => Bottom()
    }
  }
}

object M5 extends MergeRule {
  def apply(left:LinearForm, right:LinearForm, ctx:Set[Channel]) = {
    val leftSystem = left.sync match {
      case Some(Evolution(a,b)) => Evolution(a,b)
      case None                 => throw new MRDoesNotApply 
      case _                    => throw new MRDoesNotApply
    }
    
    val rightSystem = right.sync match {
      case Some(Evolution(a,b)) => Evolution(a,b)
      case None                 => throw new MRDoesNotApply 
      case _                    => throw new MRDoesNotApply
    }
    
    val composedSystem = Evolution(leftSystem.diffEq.union(rightSystem.diffEq), And(leftSystem.domain, rightSystem.domain))
    
    val sequence = parallelCompose(left.u, right.u) ::
                   Some(composedSystem)             ::
                   parallelCompose(left.v, right.v) ::
                   parallelComposeRemainder(left.gamma, right.gamma) :: Nil

    val filteredSequence = sequence.filter(p => p.isDefined).map(p => p match {
      case Some(p) => p
      case None    => throw new Exception("Scala's filter function is broken if we get here.")
    })
    filteredSequence.reduceRight((a,b) => Sequence(a,b))
  }

  def applies(left:LinearForm, right:LinearForm, ctx:Set[Channel]) = {
    val leftSystem = left.sync match {
      case Some(Evolution(a,b)) => true
      case None                 => false 
      case _                    => false
    }
    
    val rightSystem = right.sync match {
      case Some(Evolution(a,b)) => true
      case None                 => false 
      case _                    => false
    }

    leftSystem && rightSystem
  }
}
