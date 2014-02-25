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
    else {
      p
    }
  }
  /**
   * Replaces forwards with a sequence of assignments.
   */
  object ForwardCleanup {
    /**
     * Rewrites forwards into a sequence of assignments.
    */
    def apply(program:Program):Program = program.applyToSubprograms(_ match {
      case Forward(c, vars, value) => {
        val assignments:Set[Program] = vars.map(v => Assignment(v, value))
        assignments.reduceRight((l,r) => Sequence(l,r))
      }
      case _ => throw new CleanupDoesNotApply
    })
  
    def appliesToSubprogram(p:Program) = p match {
      case Forward(_,_,_) => true
      case _ => false
    }
    
    def applies(p:Program) = p.map(
        appliesToSubprogram(_), 
        pair => appliesToSubprogram(pair._1) && appliesToSubprogram(pair._2))
  }
}

