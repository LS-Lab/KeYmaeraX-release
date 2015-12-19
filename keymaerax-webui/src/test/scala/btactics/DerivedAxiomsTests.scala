package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleExpr}
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.core.{Provable, Lemma, Sequent}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.tactics.Interpreter
import edu.cmu.cs.ls.keymaerax.tools.Mathematica
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags.OptimisticTest

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
 */
class DerivedAxiomsTests extends TacticTestBase {

  override def beforeEach() = {
    super.beforeEach()
    //@todo fix when QE fixed; right now, QE fetches from there
    edu.cmu.cs.ls.keymaerax.tactics.Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    edu.cmu.cs.ls.keymaerax.tactics.Tactics.MathematicaScheduler.init(DefaultConfiguration.defaultMathematicaConfig)
  }

  override def afterEach() = {
    edu.cmu.cs.ls.keymaerax.tactics.Tactics.MathematicaScheduler.shutdown()
    edu.cmu.cs.ls.keymaerax.tactics.Tactics.MathematicaScheduler = null
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

  "The DerivedAxioms prepopulation procedure" should "not crash" taggedAs KeYmaeraXTestTags.CheckinTest in {
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
  it should "prove + associative" in {check(plusAssociative)}
  it should "prove * associative" in {check(timesAssociative)}
  it should "prove + commutative" in {check(plusCommutative)}
  it should "prove * commutative" in {check(timesCommutative)}
  it should "prove distributive" in {check(distributive)}
  it should "prove + identity" in {check(plusIdentity)}
  it should "prove * identity" in {check(timesIdentity)}
  it should "prove + inverse" in {check(plusInverse)}
  it should "prove * inverse" in {check(timesInverse)}
  it should "prove positivity" in {check(positivity)}
  it should "prove + closed" in {check(plusClosed)}
  it should "prove * closed" in {check(timesClosed)}
  it should "prove <" in {check(less)}
  it should "prove >" in {check(greater)}
  it should "prove abs" in {check(absDef)}
  it should "prove min" in {check(minDef)}
  it should "prove max" in {check(maxDef)}

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
  it should "prove = reflexive" in {check(equalReflex, equalReflexiveT)}
  it should "prove = commute" in {check(equalCommute, equalCommuteT)}
  it should "prove <=" in {check(lessEqual, lessEqualT)}
  it should "prove = negate" in {check(notNotEqual, notNotEqualT)}
  it should "prove < negate" in {check(notGreaterEqual, notGreaterEqualT)}
  it should "prove >= flip" in {check(flipGreaterEqual, flipGreaterEqualT)}
  it should "prove > flip" in {check(flipGreater, flipGreaterT)}
  it should "prove all substitute" in {check(allSubstitute, allSubstituteT)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom, vacuousExistsT)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom, vacuousBoxAssignNondetT)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom, vacuousDiamondAssignNondetT)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom, forallThenExistsT)}
  it should "prove DG differential pre-ghost" in {check(DGpreghost, DGpreghostT)}
  it should "prove DW differential weakening" in {check(DWeakening, DWeakeningT)}
  it should "prove abs" in {check(absDef, absT)}
  it should "prove min" in {check(minDef, minT)}
  it should "prove max" in {check(maxDef, maxT)}
}
