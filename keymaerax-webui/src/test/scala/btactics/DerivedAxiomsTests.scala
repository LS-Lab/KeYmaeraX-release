package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleProvable
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.core.{Lemma, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest, UsualTest}
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags.OptimisticTest
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
  * @see [[CodeNameChecker]]
 */
@CheckinTest
@SummaryTest
@UsualTest
class DerivedAxiomsTests extends edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase {

  private def check(lemma: Lemma): Sequent = {
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact shouldBe 'proved
    useToClose(lemma)
    lemma.fact.conclusion
  }

  private def useToClose(lemma: Lemma): Unit = {
    Provable.startProof(lemma.fact.conclusion)(lemma.fact, 0) shouldBe 'proved
    //@note same test as previous line, just to make sure the lemma can be used by substitution
    theInterpreter(TactixLibrary.byUS(lemma), BelleProvable(Provable.startProof(lemma.fact.conclusion))) match {
      case BelleProvable(provable, _) => provable shouldBe 'proved
      case _ => fail()
    }
  }

  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in withMathematica { qeTool =>
    DerivedAxioms.prepopulateDerivedLemmaDatabase()
  }

  "Derived Axioms" should "prove <-> reflexive" in {check(equivReflexiveAxiom)}

  ignore should "prove all distribute" in {check(allDistributeAxiom)}

  it should "prove & commute" in {check(andCommute)}
  it should "prove & assoc" in {check(andAssoc)}
  it should "prove !& deMorgan" in {check(notAnd)}
  it should "prove !| deMorgan" in {check(notOr)}
  it should "prove PC1" in {check(PC1)}
  it should "prove PC2" in {check(PC2)}
  it should "prove PC3" in {check(PC3)}
  it should "prove -> tautology" in {check{implyTautology}}

  it should "prove &-> down" in withMathematica { qeTool => check(andImplies)}

  "Derived Axiom Tactics" should "tactically prove <-> reflexive" in {check(equivReflexiveAxiom)}
  it should "tactically prove all distribute" in {check(allDistributeAxiom)}

}
