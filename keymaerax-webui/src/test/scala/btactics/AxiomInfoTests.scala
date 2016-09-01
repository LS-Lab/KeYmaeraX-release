package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

/**
  * Created by bbohrer on 12/28/15.
  */
@SummaryTest
@UsualTest
class AxiomInfoTests extends FlatSpec with Matchers with BeforeAndAfterEach {
 "Axiom Info" should "exist for all axioms" in {
   try {
     Provable.axiom.keys.forall({ case axiomName => AxiomInfo(axiomName); true }) shouldBe true
   } catch {
     case e:AxiomNotFoundException =>
       println("Test failed: Axiom not implemented: " + e.axiomName)
       throw e
   }
 }
}
