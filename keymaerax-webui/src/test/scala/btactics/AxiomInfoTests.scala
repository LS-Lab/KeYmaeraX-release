package btactics

import edu.cmu.cs.ls.keymaerax.btactics.AxiomInfo
import edu.cmu.cs.ls.keymaerax.btactics.RunnableInfo.AxiomNotFoundException
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

 it should "exist for all derived axioms" in {
  val allDerivedAxioms = DerivedAxioms.unpopulatedAxioms ++ DerivedAxioms.derivedAxiomMap.keys
  try {
    allDerivedAxioms.forall({case axiomName => AxiomInfo(axiomName); true}) shouldBe true
  } catch {
    case e:AxiomNotFoundException =>
      println("Test failed: Derived axiom not implemented" + e.axiomName)
      throw e
  }
 }
}
