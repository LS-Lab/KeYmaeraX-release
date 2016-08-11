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
 */
@CheckinTest
@SummaryTest
@UsualTest
class DerivedAxiomsTests extends edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase {

  //@todo add a test case that runs through AxiomInfo.allInfos checking all its axioms

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

  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in withMathematica { implicit qeTool =>
    //@note rather an invasive test
    LemmaDBFactory.lemmaDB.deleteDatabase() //necessary. Perhaps we should add optional copy-and-recover.
    DerivedAxioms.prepopulateDerivedLemmaDatabase()
  }


  "Derived Axioms" should "prove <-> reflexive" in {check(equivReflexiveAxiom)}
  it should "prove !!" in {check(doubleNegationAxiom)}
  it should "prove exists dual" in {check(existsDualAxiom)}
  ignore should "prove all eliminate" taggedAs OptimisticTest in {check(allEliminateAxiom)}
  ignore should "prove exists eliminate" taggedAs OptimisticTest in {check(existsEliminate)}
  it should "prove !exists" in {check(notExists)}
  it should "prove !all" in {check(notAll)}
//  it should "prove !all2" in {check(notAll2)}
  it should "prove ![]" in {check(notBox)}
  it should "prove !<>" in {check(notDiamond)}
  ignore should "prove all distribute" in {check(allDistributeAxiom)}
  it should "prove box dual" in {check(boxAxiom)}
//  it should "prove K1" in {check(K1)}
//  it should "prove K2" in {check(K2)}
  //@todo nrf it should "prove box split" in {check(boxAnd)}
//  it should "prove box split left" in {check(boxSplitLeft)}
//  it should "prove box split right" in {check(boxSplitRight)}
  it should "prove [] split" in {check(boxAnd)}
  it should "prove [] conditional split" in {check(boxImpliesAnd)}
  it should "prove <> split" in {check(diamondOr)}
  it should "prove []~><> propagation" in {check{boxDiamondPropagation}}
  it should "prove <:=> assign" in {check(assigndAxiom)}
//  it should "prove <:=> assign v" in {check(dummyassigndVvariant)}
  it should "prove := assign dual" in {check(assignDualAxiom)}
  it should "prove all substitute" in withMathematica { implicit qeTool => check(allSubstitute)}
  it should "prove [:=] equational" in withMathematica { implicit qeTool => check(assignbEquationalAxiom)}
//  it should "prove [:=] assign equality exists" in {check(assignbExistsAxiom)}
  it should "prove exists and" in {check(existsAndAxiom)}
  it should "prove [:=] assign exists" in {check(assignbImpliesExistsAxiom)}
  it should "prove <:=> assign equality" in {check(assigndEqualityAxiom)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignbAxiom)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssigndAxiom)}
  it should "prove <':=> differential assign" in {check(assignDAxiom)}
  it should "prove <:*> assign nondet" in {check(nondetassigndAxiom)}
  it should "prove <?> test" in {check(testdAxiom)}
  it should "prove <++> choice" in {check(choicedAxiom)}
  it should "prove <;> compose" in {check(composedAxiom)}
  it should "prove <*> iterate" in {check(iteratedAxiom)}
  it should "prove <*> approx" in {check(loopApproxd)}
  it should "prove [*] approx" in {check(loopApproxb)}
  it should "prove exists generalize" in {check(existsGeneralize)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom)}
  it should "prove & commute" in {check(andCommute)}
  it should "prove & assoc" in {check(andAssoc)}
  it should "prove !& deMorgan" in {check(notAnd)}
  it should "prove !| deMorgan" in {check(notOr)}
  it should "prove !-> deMorgan" in {check(notImply)}
  it should "prove !<-> deMorgan" in {check(notEquiv)}
  it should "prove domain commute" in {check(domainCommute)}
  it should "prove -> expand" in {check(implyExpand)}
  it should "prove PC1" in {check(PC1)}
  it should "prove PC2" in {check(PC2)}
  it should "prove PC3" in {check(PC3)}
  it should "prove -> tautology" in {check{implyTautology}}
  it should "prove ->'" in {check(Dimply)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom)}
  //it should "prove DI differential invariance from DI" in {check(DIinvariance)}
  it should "prove DI differential invariant from DI" in {check(DIinvariant)}
  it should "prove DIo open differential invariance >" in {check(DIOpeninvariantLess)}
  it should "prove DW differential weakening" in {check(DWeakening)}
  it should "prove DS no domain" in {check(DSnodomain)}
  it should "prove Dsol& differential equation solution" in {check(DSddomain)}
  //  it should "prove x' derive var" in {check(Dvar)}
  it should "prove x' derive variable" in {check(Dvariable)}
  it should "prove x' derive var commuted" in withMathematica { implicit qetool => check(DvariableCommuted)}
  it should "prove 'linear" in withMathematica { implicit qetool => check(Dlinear)}
  it should "prove 'linear right" in withMathematica { implicit qeTool => check(DlinearRight)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DX diamond differential skip" in {check(Dskipd)}
  it should "prove 0*" in withMathematica { implicit qeTool => check(zeroTimes)}
  it should "prove 0+" in withMathematica { implicit qeTool => check(zeroPlus)}
  it should "prove +0" in withMathematica { implicit qeTool => check(plusZero)}
  it should "prove *0" in withMathematica { implicit qeTool => check(timesZero)}
  it should "prove = reflexive" in withMathematica {implicit qetool =>check(equalReflex)}
  it should "prove = commute" in withMathematica { implicit qetool =>check(equalCommute)}
  it should "prove <=" in withMathematica { implicit qetool =>check(lessEqual)}
  it should "prove ! !=" in withMathematica { implicit qetool =>check(notNotEqual)}
  it should "prove < negate" in withMathematica { implicit qetool =>check(notGreaterEqual)}
  it should "prove >= flip" in withMathematica { implicit qetool =>check(flipGreaterEqual)}
  it should "prove > flip" in withMathematica { implicit qetool =>check(flipGreater)}
  it should "prove <= flip" in withMathematica { implicit qetool =>check(flipLessEqual)}
  it should "prove < flip" in withMathematica { implicit qetool =>check(flipLess)}
  it should "prove + associative" in withMathematica { implicit qeTool => check(plusAssociative)}
  it should "prove * associative" in withMathematica { implicit qeTool => check(timesAssociative)}
  it should "prove + commute" in withMathematica { implicit qeTool => check(plusCommutative)}
  it should "prove * commute" in withMathematica { implicit qeTool => check(timesCommutative)}
  it should "prove distributive" in withMathematica { implicit qeTool => check(distributive)}
  it should "prove + identity" in withMathematica { implicit qeTool => check(plusIdentity)}
  it should "prove * identity" in withMathematica { implicit qeTool => check(timesIdentity)}
  it should "prove + inverse" in withMathematica { implicit qeTool => check(plusInverse)}
  it should "prove * inverse" in withMathematica { implicit qeTool => check(timesInverse)}
  it should "prove positivity" in withMathematica { implicit qeTool => check(positivity)}
  it should "prove + closed" in withMathematica { implicit qeTool => check(plusClosed)}
  it should "prove * closed" in withMathematica { implicit qeTool => check(timesClosed)}
  it should "prove <" in withMathematica { implicit qeTool => check(less)}
  it should "prove ! <" in withMathematica { implicit qeTool => check(notLess)}
  it should "prove ! <=" in withMathematica { implicit qeTool => check(notLessEqual)}
  it should "prove >" in withMathematica { implicit qeTool => check(greater)}
  it should "prove ! >" in withMathematica { implicit qeTool => check(notGreater)}
  it should "prove ! >=" in withMathematica { implicit qeTool => check(notGreaterEqual)}

  it should "prove != elimination" in withMathematica { implicit qeTool => check(notEqualElim)}
  it should "prove >= elimination" in withMathematica { implicit qeTool => check(greaterEqualElim)}
  it should "prove > elimination" in withMathematica { implicit qeTool => check(greaterElim)}
  it should "prove 1>0" in withMathematica { implicit qeTool => check(oneGreaterZero)}
  it should "prove nonnegative squares" in withMathematica { implicit qeTool => check(nonnegativeSquares)}
  it should "prove >2!=" in withMathematica { implicit qeTool => check(greaterImpliesNotEqual)}
  it should "prove > monotone" in withMathematica { implicit qeTool => check(greaterMonotone)}

  it should "prove abs" in withMathematica { implicit qeTool => check(absDef)}
  it should "prove min" in withMathematica { implicit qeTool => check(minDef)}
  it should "prove max" in withMathematica { implicit qeTool => check(maxDef)}
  it should "prove +<= up" in withMathematica { implicit qeTool => check(intervalUpPlus)}
  it should "prove -<= up" in withMathematica { implicit qeTool => check(intervalUpMinus)}
  it should "prove *<= up" in withMathematica { implicit qeTool => check(intervalUpTimes)}
  it should "prove 1Div<= up" in withMathematica { implicit qeTool => check(intervalUp1Divide)}
  it should "prove Div<= up" in withMathematica { implicit qeTool => check(intervalUpDivide)}
  it should "prove <=+ down" in withMathematica { implicit qeTool => check(intervalDownPlus)}
  it should "prove <=- down" in withMathematica { implicit qeTool => check(intervalDownMinus)}
  it should "prove <=* down" in withMathematica { implicit qeTool => check(intervalDownTimes)}
  it should "prove <=1Div down" in withMathematica { implicit qeTool => check(intervalDown1Divide)}
  it should "prove <=Div down" in withMathematica { implicit qeTool => check(intervalDownDivide)}
  it should "prove K& down" in withMathematica { implicit qeTool => check(Kand)}
  it should "prove &-> down" in withMathematica { implicit qeTool => check(andImplies)}

  "Derived Axiom Tactics" should "prove <-> reflexive" in {check(equivReflexiveAxiom)}
  it should "prove !!" in {check(doubleNegationAxiom)}
  it should "prove exists dual" in {check(existsDualAxiom)}
  ignore should "prove all eliminate" taggedAs OptimisticTest in {check(allEliminateAxiom)}
  ignore should "prove exists eliminate" taggedAs OptimisticTest in {check(existsEliminate)}
  it should "prove all distribute" in {check(allDistributeAxiom)}
  it should "prove box dual" in {check(boxAxiom)}
  it should "prove <:=> assign" in {check(assigndAxiom)}
  it should "prove [:=] equational" in {check(assignbEquationalAxiom)}
//  it should "prove [:=] equational exists" in {check(assignbExistsAxiom, assignbEquationalT)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignbAxiom)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssigndAxiom)}
  it should "prove <':=> differential assign" in {check(assignDAxiom)}
  it should "prove <++> choice" in {check(choicedAxiom)}
  it should "prove <;> compose" in {check(composedAxiom)}
  it should "prove <*> iterate" in {check(iteratedAxiom)}
  it should "prove exists generalize" in {check(existsGeneralize)}
  it should "prove = reflexive" in withMathematica { implicit qeTool => check(equalReflex)}
  it should "prove = commute" in withMathematica { implicit qeTool => check(equalCommute)}
  it should "prove <=" in withMathematica { implicit qeTool => check(lessEqual)}
  it should "prove ! !=" in withMathematica { implicit qeTool => check(notNotEqual)}
  it should "prove < negate" in withMathematica { implicit qeTool => check(notGreaterEqual)}
  it should "prove >= flip" in withMathematica { implicit qeTool => check(flipGreaterEqual)}
  it should "prove > flip" in withMathematica { implicit qeTool => check(flipGreater)}
  it should "prove all substitute" in {check(allSubstitute)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom)}
  //it should "prove DI differential invariance" in {check(DIinvariance)}
  it should "prove DI differential invariant" in {check(DIinvariant)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DW differential weakening" in {check(DWeakening)}
  it should "prove abs" in withMathematica { implicit qeTool => check(absDef)}
  it should "prove min" in withMathematica { implicit qeTool => check(minDef)}
  it should "prove max" in withMathematica { implicit qeTool => check(maxDef)}

  "Derived Rule" should "prove allG" in withMathematica { implicit qeTool => allGeneralize.fact.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("p_(||)".asFormula))
  ) }

  it should "prove CT" in withMathematica { implicit qeTool => CTtermCongruence.fact.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("f_(||) = g_(||)".asFormula))
  ) }

  it should "prove [] monotone" in withMathematica { implicit qeTool => boxMonotone.fact.subgoals shouldBe List(
      Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula))
  ) }

  it should "prove [] monotone 2" in withMathematica { implicit qeTool => boxMonotone2.fact.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq("q_(||)".asFormula), immutable.IndexedSeq("p_(||)".asFormula))
  ) }
}
