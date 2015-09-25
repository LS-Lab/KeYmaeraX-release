/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

/**
 * List of commonly used names of branch labels.
 * Created by Jan-David Quesel on 5/19/14.
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.Tactics.LabelBranch]]
 */
object BranchLabels {
  val cutShowLbl = "Show cut"
  val cutUseLbl = "Use cut"
  val indInitLbl = "base case"  //@todo rename to "base case" for paper consistency. Used to be "Invariant initially valid"
  val indUseCaseLbl = "use case"  //@todo maybe renamed from "Use case" for paper consistency
  val indStepLbl = "induction step"  //@todo maybe renamed from "Induction step" for paper consistency

  val equivLeftLbl = "Positive equiv case"
  val equivRightLbl = "Negative equiv case"

  val axiomShowLbl = "Show axiom"
  val axiomUseLbl = "Use axiom"

  val knowledgeSubclassContinue = "Knowledge subclass continue"
}
