package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

import edu.cmu.cs.ls.keymaerax.core.Variable

/**
  * Created by bbohrer on 4/24/16.
  */
object UniqueVariable {
  private var theIndex = 0
  private val theName = "secretvariable"
  def make = {
    theIndex = theIndex + 1
    Variable(theName + theIndex + "_")
  }
}
