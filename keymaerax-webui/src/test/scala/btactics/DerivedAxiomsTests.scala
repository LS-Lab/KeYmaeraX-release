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

  /** Initializer for those tests where deriving the axioms actually requires Mathematica; keeps non-Mathematica tests fast */
  trait DerivedAxiomsMathematicaInitializer {
    val mathematica = new Mathematica()
    mathematica.init(DefaultConfiguration.defaultMathematicaConfig)
    mathematica shouldBe 'initialized
    DerivedAxioms.qeTool = mathematica
  }

  override def afterEach() = {
    if (DerivedAxioms.qeTool != null) {
      DerivedAxioms.qeTool match { case m: Mathematica => m.shutdown() }
      DerivedAxioms.qeTool = null
    }
    super.afterEach()
  }

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

  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in new DerivedAxiomsMathematicaInitializer {
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
  it should "prove DG differential pre-ghost" in {check(DGpreghost)}
  it should "prove DX diamond differential skip" in {check(Dskipd)}
  it should "prove = reflexive" in {check(equalReflex)}
  it should "prove = commute" in {check(equalCommute)}
  it should "prove <=" in {check(lessEqual)}
  it should "prove = negate" in {check(notNotEqual)}
  it should "prove < negate" in {check(notGreaterEqual)}
  it should "prove >= flip" in {check(flipGreaterEqual)}
  it should "prove > flip" in {check(flipGreater)}
  it should "prove + associative" in new DerivedAxiomsMathematicaInitializer {check(plusAssociative)}
  it should "prove * associative" in new DerivedAxiomsMathematicaInitializer {check(timesAssociative)}
  it should "prove + commutative" in new DerivedAxiomsMathematicaInitializer {check(plusCommutative)}
  it should "prove * commutative" in new DerivedAxiomsMathematicaInitializer {check(timesCommutative)}
  it should "prove distributive" in new DerivedAxiomsMathematicaInitializer {check(distributive)}
  it should "prove + identity" in new DerivedAxiomsMathematicaInitializer {check(plusIdentity)}
  it should "prove * identity" in new DerivedAxiomsMathematicaInitializer {check(timesIdentity)}
  it should "prove + inverse" in new DerivedAxiomsMathematicaInitializer {check(plusInverse)}
  it should "prove * inverse" in new DerivedAxiomsMathematicaInitializer {check(timesInverse)}
  it should "prove positivity" in new DerivedAxiomsMathematicaInitializer {check(positivity)}
  it should "prove + closed" in new DerivedAxiomsMathematicaInitializer {check(plusClosed)}
  it should "prove * closed" in new DerivedAxiomsMathematicaInitializer {check(timesClosed)}
  it should "prove <" in new DerivedAxiomsMathematicaInitializer {check(less)}
  it should "prove >" in new DerivedAxiomsMathematicaInitializer {check(greater)}
  it should "prove abs" in new DerivedAxiomsMathematicaInitializer {check(absDef)}
  it should "prove min" in new DerivedAxiomsMathematicaInitializer {check(minDef)}
  it should "prove max" in new DerivedAxiomsMathematicaInitializer {check(maxDef)}
  it should "prove +<= up" in new DerivedAxiomsMathematicaInitializer {check(intervalUpPlus)}
  it should "prove -<= up" in new DerivedAxiomsMathematicaInitializer {check(intervalUpMinus)}
  ignore should "prove *<= up" in new DerivedAxiomsMathematicaInitializer {check(intervalUpTimes)} //@todo QE fails???
  it should "prove 1Div<= up" in new DerivedAxiomsMathematicaInitializer {check(intervalUp1Divide)}
  it should "prove Div<= up" in new DerivedAxiomsMathematicaInitializer {check(intervalUpDivide)}
  it should "prove <=+ down" in new DerivedAxiomsMathematicaInitializer {check(intervalDownPlus)}
  it should "prove <=- down" in new DerivedAxiomsMathematicaInitializer {check(intervalDownMinus)}
  ignore should "prove <=* down" in new DerivedAxiomsMathematicaInitializer {check(intervalDownTimes)} //@todo QE fails???
  it should "prove <=1Div down" in new DerivedAxiomsMathematicaInitializer {check(intervalDown1Divide)}
  it should "prove <=Div down" in new DerivedAxiomsMathematicaInitializer {check(intervalDownDivide)}

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
  it should "prove = reflexive" in new DerivedAxiomsMathematicaInitializer {check(equalReflex, equalReflexiveT)}
  it should "prove = commute" in new DerivedAxiomsMathematicaInitializer {check(equalCommute, equalCommuteT)}
  it should "prove <=" in new DerivedAxiomsMathematicaInitializer {check(lessEqual, lessEqualT)}
  it should "prove = negate" in new DerivedAxiomsMathematicaInitializer {check(notNotEqual, notNotEqualT)}
  it should "prove < negate" in new DerivedAxiomsMathematicaInitializer {check(notGreaterEqual, notGreaterEqualT)}
  it should "prove >= flip" in new DerivedAxiomsMathematicaInitializer {check(flipGreaterEqual, flipGreaterEqualT)}
  it should "prove > flip" in new DerivedAxiomsMathematicaInitializer {check(flipGreater, flipGreaterT)}
  it should "prove all substitute" in {check(allSubstitute, allSubstituteT)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom, vacuousExistsT)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom, vacuousBoxAssignNondetT)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom, vacuousDiamondAssignNondetT)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom, forallThenExistsT)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost, DGpreghostT)}
  it should "prove DW differential weakening" in {check(DWeakening, DWeakeningT)}
  it should "prove abs" in new DerivedAxiomsMathematicaInitializer {check(absDef, absT)}
  it should "prove min" in new DerivedAxiomsMathematicaInitializer {check(minDef, minT)}
  it should "prove max" in new DerivedAxiomsMathematicaInitializer {check(maxDef, maxT)}
}
