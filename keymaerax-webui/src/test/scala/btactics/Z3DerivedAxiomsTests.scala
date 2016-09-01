package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleProvable
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.core.{Lemma, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest, UsualTest}
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags.OptimisticTest

import scala.collection.immutable

/**
  * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
  * @see [[CodeNameChecker]]
  * @see [[DerivedAxiomsTests]]
  * @note Must be separate test suite from same tests withZ3, otherwise lazy vals in DerivedAxioms corrupt tests.
  */
@CheckinTest
@SummaryTest
@UsualTest
class Z3DerivedAxiomsTests extends edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase {

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

  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in withZ3 { qeTool =>
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
  it should "prove all substitute" in withZ3 { qeTool => check(allSubstitute)}
  it should "prove [:=] equational" in withZ3 { qeTool => check(assignbEquationalAxiom)}
//  it should "prove [:=] assign equality exists" in {check(assignbExistsAxiom)}
  it should "prove exists and" in {check(existsAndAxiom)}
  it should "prove [:=] assign exists" in {check(assignbImpliesExistsAxiom)}
  it should "prove <:=> assign equality" in {check(assigndEqualityAxiom)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignbAxiom)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssigndAxiom)}
  //@todo it should "prove [':=] differential assign" in {check(assignDAxiomb)}
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
  it should "prove x' derive var commuted" in withZ3 { qetool => check(DvariableCommuted)}
  it should "prove 'linear" in withZ3 { qetool => check(Dlinear)}
  it should "prove 'linear right" in withZ3 { qeTool => check(DlinearRight)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DX diamond differential skip" in {check(Dskipd)}
  it should "prove 0*" in withZ3 { qeTool => check(zeroTimes)}
  it should "prove 0+" in withZ3 { qeTool => check(zeroPlus)}
  it should "prove +0" in withZ3 { qeTool => check(plusZero)}
  it should "prove *0" in withZ3 { qeTool => check(timesZero)}
  it should "prove = reflexive" in withZ3 {qetool =>check(equalReflex)}
  it should "prove = commute" in withZ3 { qetool =>check(equalCommute)}
  it should "prove <=" in withZ3 { qetool =>check(lessEqual)}
  it should "prove ! !=" in withZ3 { qetool =>check(notNotEqual)}
  it should "prove < negate" in withZ3 { qetool =>check(notGreaterEqual)}
  it should "prove >= flip" in withZ3 { qetool =>check(flipGreaterEqual)}
  it should "prove > flip" in withZ3 { qetool =>check(flipGreater)}
  it should "prove <= flip" in withZ3 { qetool =>check(flipLessEqual)}
  it should "prove < flip" in withZ3 { qetool =>check(flipLess)}
  it should "prove + associative" in withZ3 { qeTool => check(plusAssociative)}
  it should "prove * associative" in withZ3 { qeTool => check(timesAssociative)}
  it should "prove + commute" in withZ3 { qeTool => check(plusCommutative)}
  it should "prove * commute" in withZ3 { qeTool => check(timesCommutative)}
  it should "prove distributive" in withZ3 { qeTool => check(distributive)}
  it should "prove + identity" in withZ3 { qeTool => check(plusIdentity)}
  it should "prove * identity" in withZ3 { qeTool => check(timesIdentity)}
  it should "prove + inverse" in withZ3 { qeTool => check(plusInverse)}
  it should "prove * inverse" in withZ3 { qeTool => check(timesInverse)}
  it should "prove positivity" in withZ3 { qeTool => check(positivity)}
  it should "prove + closed" in withZ3 { qeTool => check(plusClosed)}
  it should "prove * closed" in withZ3 { qeTool => check(timesClosed)}
  it should "prove <" in withZ3 { qeTool => check(less)}
  it should "prove ! <" in withZ3 { qeTool => check(notLess)}
  it should "prove ! <=" in withZ3 { qeTool => check(notLessEqual)}
  it should "prove >" in withZ3 { qeTool => check(greater)}
  it should "prove ! >" in withZ3 { qeTool => check(notGreater)}
  it should "prove ! >=" in withZ3 { qeTool => check(notGreaterEqual)}

  /** Axioms for arithmetic in core (some not yet provable with Z3) */
//  it should "prove != elimination" ignore withZ3 { qeTool => check(notEqualElim)}
//  it should "prove >= elimination" ignore withZ3 { qeTool => check(greaterEqualElim)}
//  it should "prove > elimination" ignore withZ3 { qeTool => check(greaterElim)}
  it should "prove 1>0" in withZ3 { qeTool => check(oneGreaterZero)}
  it should "prove nonnegative squares" in withZ3 { qeTool => check(nonnegativeSquares)}
  it should "prove >2!=" in withZ3 { qeTool => check(greaterImpliesNotEqual)}
  it should "prove > monotone" in withZ3 { qeTool => check(greaterMonotone)}

  it should "prove abs" in withZ3 { qeTool => check(absDef)}
  it should "prove min" in withZ3 { qeTool => check(minDef)}
  it should "prove max" in withZ3 { qeTool => check(maxDef)}
  it should "prove +<= up" in withZ3 { qeTool => check(intervalUpPlus)}
  it should "prove -<= up" in withZ3 { qeTool => check(intervalUpMinus)}
  it should "prove *<= up" in withZ3 { qeTool => check(intervalUpTimes)}
  it should "prove 1Div<= up" in withZ3 { qeTool => check(intervalUp1Divide)}
  it should "prove Div<= up" in withZ3 { qeTool => check(intervalUpDivide)}
  it should "prove <=+ down" in withZ3 { qeTool => check(intervalDownPlus)}
  it should "prove <=- down" in withZ3 { qeTool => check(intervalDownMinus)}
  it should "prove <=* down" in withZ3 { qeTool => check(intervalDownTimes)}
  it should "prove <=1Div down" in withZ3 { qeTool => check(intervalDown1Divide)}
  it should "prove <=Div down" in withZ3 { qeTool => check(intervalDownDivide)}
  it should "prove K& down" in withZ3 { qeTool => check(Kand)}
  it should "prove &-> down" in withZ3 { qeTool => check(andImplies)}

  "Derived Axiom Tactics" should "tactically prove <-> reflexive" in {check(equivReflexiveAxiom)}
  it should "tactically prove !!" in {check(doubleNegationAxiom)}
  it should "tactically prove exists dual" in {check(existsDualAxiom)}
  ignore should "tactically prove all eliminate" taggedAs OptimisticTest in {check(allEliminateAxiom)}
  ignore should "tactically prove exists eliminate" taggedAs OptimisticTest in {check(existsEliminate)}
  it should "tactically prove all distribute" in {check(allDistributeAxiom)}
  it should "tactically prove box dual" in {check(boxAxiom)}
  it should "tactically prove <:=> assign" in {check(assigndAxiom)}
  it should "tactically prove [:=] equational" in withZ3 { qeTool => check(assignbEquationalAxiom)}
//  it should "tactically prove [:=] equational exists" in {check(assignbExistsAxiom, assignbEquationalT)}
  it should "tactically prove [:=] vacuous assign" in {check(vacuousAssignbAxiom)}
  it should "tactically prove <:=> vacuous assign" in {check(vacuousAssigndAxiom)}
  it should "tactically prove <':=> differential assign" in {check(assignDAxiom)}
  it should "tactically prove <++> choice" in {check(choicedAxiom)}
  it should "tactically prove <;> compose" in {check(composedAxiom)}
  it should "tactically prove <*> iterate" in {check(iteratedAxiom)}
  it should "tactically prove exists generalize" in {check(existsGeneralize)}
  it should "tactically prove = reflexive" in withZ3 { qeTool => check(equalReflex)}
  it should "tactically prove = commute" in withZ3 { qeTool => check(equalCommute)}
  it should "tactically prove <=" in withZ3 { qeTool => check(lessEqual)}
  it should "tactically prove ! !=" in withZ3 { qeTool => check(notNotEqual)}
  it should "tactically prove < negate" in withZ3 { qeTool => check(notGreaterEqual)}
  it should "tactically prove >= flip" in withZ3 { qeTool => check(flipGreaterEqual)}
  it should "tactically prove > flip" in withZ3 { qeTool => check(flipGreater)}
  it should "tactically prove all substitute" in {check(allSubstitute)}
  it should "tactically prove vacuous exists" in {check(vacuousExistsAxiom)}
  it should "tactically prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom)}
  it should "tactically prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom)}
  it should "tactically prove \\forall->\\exists" in {check(forallThenExistsAxiom)}
  //it should "tactically prove DI differential invariance" in {check(DIinvariance)}
  it should "tactically prove DI differential invariant" in {check(DIinvariant)}
  it should "tactically prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "tactically prove DW differential weakening" in {check(DWeakening)}
  it should "tactically prove abs" in withZ3 { qeTool => check(absDef)}
  it should "tactically prove min" in withZ3 { qeTool => check(minDef)}
  it should "tactically prove max" in withZ3 { qeTool => check(maxDef)}

  "Derived Rule" should "prove allG" in withZ3 { qeTool => allGeneralize.fact.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("p_(||)".asFormula))
  ) }

  it should "prove CT" in withZ3 { qeTool => CTtermCongruence.fact.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("f_(||) = g_(||)".asFormula))
  ) }

  it should "prove [] monotone" in withZ3 { qeTool => boxMonotone.fact.subgoals shouldBe List(
      Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula))
  ) }

  it should "prove [] monotone 2" in withZ3 { qeTool => boxMonotone2.fact.subgoals shouldBe List(
    Sequent(immutable.IndexedSeq("q_(||)".asFormula), immutable.IndexedSeq("p_(||)".asFormula))
  ) }
}
