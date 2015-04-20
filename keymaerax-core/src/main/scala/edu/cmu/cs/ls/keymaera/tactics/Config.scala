package edu.cmu.cs.ls.keymaera.tactics

object Config {

  /**
   * number of CPUs and hence threads to execute in parallel
   */
  var maxCPUs = 4

  var mathlicenses = 4

  /**
   * apply expensive check whenever this threshold is exceeded
   */
  val timeThres   = 2   // seconds
  val branchThres = 100 // branches
  val ruleThres   = 200 // rules
  val tacThres    = 42  // tactics


}
