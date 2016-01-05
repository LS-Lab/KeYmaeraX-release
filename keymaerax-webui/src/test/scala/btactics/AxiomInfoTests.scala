package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.AxiomInfo
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.core.Axiom
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms
import edu.cmu.cs.ls.keymaerax.tags.{UsualTest, SummaryTest}
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
  * Created by bbohrer on 12/28/15.
  */
@SummaryTest
@UsualTest
class AxiomInfoTests extends FlatSpec with Matchers with BeforeAndAfterEach {
 "Axiom Info" should "exist for all axioms" in {
   try {
     Axiom.axioms.keys.forall({ case axiomName => AxiomInfo(axiomName); true }) shouldBe true
   } catch {
     case e:AxiomNotFoundException =>
       println("Test failed: Axiom not implemented: " + e.axiomName)
       throw e
   }
 }
}
