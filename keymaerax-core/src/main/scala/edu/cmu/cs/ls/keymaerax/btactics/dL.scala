package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import scala.collection.immutable.IndexedSeq

/**
 * The classical dL Sequent Calculus.
 * @author Nathan Fulton
 */
object dL {
  // All of the proof rules in the core are part of the dL sequent calculus.
  import ProofRuleTactics.{NotL, NotR, ImplyL, ImplyR, AndL, AndR, Close, CloseTrue, CloseFalse}

  // Proof Rules about Hybrid Programs.

//  def BoxChoice = {
//    //@todo write a helper method that constructs a USubstPatternTactic from a rewriting direction and an axiom
//    val matchingSequent = Sequent(Nil, IndexedSeq(), IndexedSeq("[a ++ b;]p(??)"))
//    def tactic = USubstPatternTactic(
//      (SequentType())
//    )
//  }

}
