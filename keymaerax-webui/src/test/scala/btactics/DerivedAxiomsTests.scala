package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleExpr}
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.core.{Provable, Lemma, Sequent}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.tools.Mathematica
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags.OptimisticTest

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
 */
class DerivedAxiomsTests extends TacticTestBase {

  private def check(lemma: Lemma): Sequent = {
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact shouldBe 'proved
    useToClose(lemma)
    lemma.fact.conclusion
  }

  private def check(lemma: Lemma, lemT: BelleExpr): Sequent = {
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact shouldBe 'proved
    theInterpreter(lemT, BelleProvable(Provable.startProof(lemma.fact.conclusion))) match {
      case BelleProvable(provable) =>
        provable shouldBe 'proved
        provable.conclusion
      case _ => fail()
    }
  }

  private def useToClose(lemma: Lemma): Unit = {
    Provable.startProof(lemma.fact.conclusion)(lemma.fact, 0) shouldBe 'proved
  }

  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in withMathematica { implicit qeTool =>
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
  it should "prove ![]" in {check(notBox)}
  it should "prove !<>" in {check(notDiamond)}
  it should "prove all distribute" in {check(allDistributeAxiom)}
  it should "prove box dual" in {check(boxDualAxiom)}
  it should "prove K1" in {check(K1)}
  it should "prove K2" in {check(K2)}
  it should "prove box split" in {check(boxSplit)}
  it should "prove box split left" in {check(boxSplitLeft)}
  it should "prove box split right" in {check(boxSplitRight)}
  it should "prove <> split" in {check(diamondSplit)}
  it should "prove diamond split left" in {check(diamondSplitLeft)}
  it should "prove []~><> propagation" in {check{boxDiamondPropagation}}
  it should "prove <:=> assign" in {check(assigndAxiom)}
//  it should "prove <:=> assign v" in {check(dummyassigndVvariant)}
  it should "prove := assign dual" in {check(assignDualAxiom)}
  it should "prove all substitute" in {check(allSubstitute)}
  it should "prove [:=] equational" in {check(assignbEquationalAxiom)}
  ignore should "prove [:=] assign equality exists" in {check(assignbExistsAxiom)}
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
  it should "prove DW differential weakening" in {check(DWeakening)}
  it should "prove DS no domain" in {check(DSnodomain)}
  it should "prove DSol no domain" in {check(DSdnodomain)}
  it should "prove Dsol& differential equation solution" in {check(DSddomain)}
  //  it should "prove x' derive var" in {check(Dvar)}
  it should "prove x' derive variable" in {check(Dvariable)}
  it should "prove 'linear" in {check(Dlinear)}
  //@todo fails with substitution clash
  ignore should "prove 'linear right" in withMathematica { implicit qeTool => check(DlinearRight)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DX diamond differential skip" in {check(Dskipd)}
  it should "prove = reflexive" in {check(equalReflex)}
  it should "prove = commute" in {check(equalCommute)}
  it should "prove <=" in {check(lessEqual)}
  it should "prove = negate" in {check(notNotEqual)}
  it should "prove < negate" in {check(notGreaterEqual)}
  it should "prove >= flip" in {check(flipGreaterEqual)}
  it should "prove > flip" in {check(flipGreater)}
  it should "prove + associative" in withMathematica { implicit qeTool => check(plusAssociative)}
  it should "prove * associative" in withMathematica { implicit qeTool => check(timesAssociative)}
  it should "prove + commutative" in withMathematica { implicit qeTool => check(plusCommutative)}
  it should "prove * commutative" in withMathematica { implicit qeTool => check(timesCommutative)}
  it should "prove distributive" in withMathematica { implicit qeTool => check(distributive)}
  it should "prove + identity" in withMathematica { implicit qeTool => check(plusIdentity)}
  it should "prove * identity" in withMathematica { implicit qeTool => check(timesIdentity)}
  it should "prove + inverse" in withMathematica { implicit qeTool => check(plusInverse)}
  it should "prove * inverse" in withMathematica { implicit qeTool => check(timesInverse)}
  it should "prove positivity" in withMathematica { implicit qeTool => check(positivity)}
  it should "prove + closed" in withMathematica { implicit qeTool => check(plusClosed)}
  it should "prove * closed" in withMathematica { implicit qeTool => check(timesClosed)}
  it should "prove <" in withMathematica { implicit qeTool => check(less)}
  it should "prove >" in withMathematica { implicit qeTool => check(greater)}
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

  "Derived Axiom Tactics" should "prove <-> reflexive" in {check(equivReflexiveAxiom, equivReflexiveT)}
  it should "prove !!" in {check(doubleNegationAxiom, doubleNegationT)}
  it should "prove exists dual" in {check(existsDualAxiom, existsDualT)}
  ignore should "prove all eliminate" taggedAs OptimisticTest in {check(allEliminateAxiom, allEliminateT)}
  ignore should "prove exists eliminate" taggedAs OptimisticTest in {check(existsEliminate, existsEliminateT)}
  it should "prove all distribute" in {check(allDistributeAxiom, allDistributeT)}
  it should "prove box dual" in {check(boxDualAxiom, boxDualT)}
  it should "prove <:=> assign" in {check(assigndAxiom, assigndT)}
  it should "prove [:=] equational" in {check(assignbEquationalAxiom, assignbEquationalT)}
//  it should "prove [:=] equational exists" in {check(assignbExistsAxiom, assignbEquationalT)}
  it should "prove [:=] vacuous assign" in {check(vacuousAssignbAxiom, vacuousAssignbT)}
  it should "prove <:=> vacuous assign" in {check(vacuousAssigndAxiom, vacuousAssigndT)}
  it should "prove <':=> differential assign" in {check(assignDAxiom, assignDT)}
  it should "prove <++> choice" in {check(choicedAxiom, choicedT)}
  it should "prove <;> compose" in {check(composedAxiom, composedT)}
  it should "prove <*> iterate" in {check(iteratedAxiom, iteratedT)}
  it should "prove exists generalize" in {check(existsGeneralize, existsGeneralizeT)}
  it should "prove = reflexive" in withMathematica { implicit qeTool => check(equalReflex, equalReflexiveT)}
  it should "prove = commute" in withMathematica { implicit qeTool => check(equalCommute, equalCommuteT)}
  it should "prove <=" in withMathematica { implicit qeTool => check(lessEqual, lessEqualT)}
  it should "prove = negate" in withMathematica { implicit qeTool => check(notNotEqual, notNotEqualT)}
  it should "prove < negate" in withMathematica { implicit qeTool => check(notGreaterEqual, notGreaterEqualT)}
  it should "prove >= flip" in withMathematica { implicit qeTool => check(flipGreaterEqual, flipGreaterEqualT)}
  it should "prove > flip" in withMathematica { implicit qeTool => check(flipGreater, flipGreaterT)}
  it should "prove all substitute" in {check(allSubstitute, allSubstituteT)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom, vacuousExistsT)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom, vacuousBoxAssignNondetT)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom, vacuousDiamondAssignNondetT)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom, forallThenExistsT)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost, DGpreghostT)}
  it should "prove DW differential weakening" in {check(DWeakening, DWeakeningT)}
  it should "prove abs" in withMathematica { implicit qeTool => check(absDef, absT)}
  it should "prove min" in withMathematica { implicit qeTool => check(minDef, minT)}
  it should "prove max" in withMathematica { implicit qeTool => check(maxDef, maxT)}
}
