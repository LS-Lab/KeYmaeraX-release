package pdl.core

class CleanupDoesNotApply extends Exception

/**
 * These are rewrite rules which don't appear in the paper, but probably should
 * (unless I'm missing something.)
 */
object ExtraRewrites {
  def cleanup(p:Program):Program = {
    if(ForwardCleanup.applies(p)) {
      val result = ForwardCleanup.apply(p)
      cleanup(result)
    }
    else if(CursorCleanup.applies(p)) {
      val result = CursorCleanup.apply(p)
      cleanup(result)
    }
    
    else {
      p
    }
  }
  /**
   * Replaces forwards with a sequence of assignments.
   */
  object ForwardCleanup {
    def applies(program:Program) = program.contains(_.isInstanceOf[Forward])
    
    def apply(program:Program) = program.apply(p=>p match {
      case Forward(c, variables, value) => {
        val assignments:Set[Program] = variables.map(v => Assignment(v,value))
        assignments.reduceRight(Sequence(_,_))
      }
      case _ => p
    })
  }
//  object ForwardCleanup {
//    /**
//     * Rewrites forwards into a sequence of assignments.
//    */
//    def apply(program:Program):Program = program.applyToSubprograms(_ match {
//      case Forward(c, vars, value) => {
//        val assignments:Set[Program] = vars.map(v => Assignment(v, value))
//        assignments.reduceRight((l,r) => Sequence(l,r))
//      }
//      case _ => throw new CleanupDoesNotApply
//    })
//  
//    def appliesToSubprogram(p:Program) = p match {
//      case Forward(_,_,_) => true
//      case _ => false
//    }
//    
//    def applies(p:Program) = p.map(
//        appliesToSubprogram(_), 
//        pair => appliesToSubprogram(pair._1) && appliesToSubprogram(pair._2))
//  }
  
  object CursorCleanup {
    def apply(program:Program) = program match {
      case CursorBefore(p) => p
      case CursorAfter(p) => p
      case _ => throw new CleanupDoesNotApply
    }
    
    def applies(program:Program) = program match {
      case CursorBefore(p) => true
      case CursorAfter(p) => true
      case _ => false
    }
  }
}

