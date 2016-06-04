package edu.cmu.cs.ls.keymaerax.btactics.dRL

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._

/**
  * Implements the Loos sequent calculus for Differential Refinement Logic based upon
  *
  * @see Sarah Loos. [[http://reports-archive.adm.cs.cmu.edu/anon/2015/CMU-CS-15-144.pdf Differential Refinement Logic]]. Carnegie Mellon Technical Report CMU-CS-15-144.
  *      (Especially section 3.6.2)
  * @author Nathan Fulton
  */
object RefinementSequentCalculus {

  /** alpha ++ (beta ++ gamma) == (alpha ++ beta) ++ gamma */
  val choiceAssoc = new NamedTactic("dRL.choiceAssoc", {
    ???
  })

  private val boxChoiceAssoc = HilbertCalculus.choiceb & HilbertCalculus.choiceb & SequentCalculus.andR

  /** Returns true if formula encodes a refinement relation. */
  private def isRefinement(formula : Formula) = formula match {
    case Equiv(Box(alpha, phi), Box(beta, psi)) if(phi == psi) => true //alpha ~ beta
    case Imply(Box(alpha, phi), Box(beta, psi)) if(phi == psi) => true //alpha <= beta
    case _ => false
  }
}
