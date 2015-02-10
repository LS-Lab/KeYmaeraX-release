import edu.cmu.cs.ls.keymaera.core.{Variable, Real, RootNode}
import edu.cmu.cs.ls.keymaera.tactics.{Config, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{locateSucc,locateAnte}
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.{uniquify,instantiateT,existentialGenT,
  vacuousExistentialQuanT,vacuousUniversalQuanT,decomposeQuanT}

import scala.collection.immutable.Map

/**
 * Created by smitsch on 1/31/15.
 * @author Stefan Mitsch
 */
class FOQuantifierTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  // TODO mathematica is only necessary because of ProofFactory -> make ProofFactory configurable
  Config.mathlicenses = 1
  Config.maxCPUs = 1

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

  override def beforeEach() = {
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
  }

  "Uniquify" should "rename assignments" in {
    val tactic = locateSucc(uniquify)
    getProofSequent(tactic, new RootNode(sucSequent("[y:=1;]y>0".asFormula))) should be (
      sucSequent("[y_0:=1;]y_0>0".asFormula))
  }

  it should "rename nondeterministic assignments" in {
    val tactic = locateSucc(uniquify)
    getProofSequent(tactic, new RootNode(sucSequent("[y:=*;]y>0".asFormula))) should be (
      sucSequent("[y_0:=*;]y_0>0".asFormula))
  }

  it should "rename universally quantified variables" in {
    val tactic = locateSucc(uniquify)
    getProofSequent(tactic, new RootNode(sucSequent("\\forall y. y>0".asFormula))) should be (
      sucSequent("\\forall y_0. y_0>0".asFormula))
  }

  it should "select a fresh variable when renaming universally quantified variables" in {
    val tactic = locateSucc(uniquify)
    getProofSequent(tactic, new RootNode(sucSequent("\\forall y. [y_0:=y;]y_0>0".asFormula))) should be (
      sucSequent("\\forall y_1. [y_0:=y_1;]y_0>0".asFormula))
  }

  it should "select a fresh variable when renaming assignments" in {
    val tactic = locateSucc(uniquify)
    getProofSequent(tactic, new RootNode(sucSequent("[y:=1;][y_0:=y;]y_0>0".asFormula))) should be (
      sucSequent("[y_1:=1;][y_0:=y_1;]y_0>0".asFormula))
  }

  it should "select a fresh variable when renaming nondeterministic assignments" in {
    val tactic = locateSucc(uniquify)
    getProofSequent(tactic, new RootNode(sucSequent("[y:=*;][y_0:=y;]y_0>0".asFormula))) should be (
      sucSequent("[y_1:=*;][y_0:=y_1;]y_0>0".asFormula))
  }

  "Quantifier instantiation" should "instantiate simple predicate" in {
    val tactic = locateAnte(instantiateT(Variable("x", None, Real), "z".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "\\forall x. x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "z>0".asFormula :: Nil, Nil))
  }

  it should "instantiate assignment modality" in {
    val tactic = locateAnte(instantiateT(Variable("x", None, Real), "z".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "\\forall x. [y:=x;][y:=2;]y>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "[y:=z;][y:=2;]y>0".asFormula :: Nil, Nil))
  }

  it should "instantiate ODE modality" in {
    val tactic = locateAnte(instantiateT(Variable("x", None, Real), "z".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "\\forall x. [y'=x;]y>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "[y'=z;]y>0".asFormula :: Nil, Nil))
  }

  it should "instantiate assignment irrespective of what follows" in {
    val tactic = locateAnte(instantiateT(Variable("x", None, Real), "z".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "\\forall x. [y:=x;][y'=1;]y>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "[y:=z;][y'=1;]y>0".asFormula :: Nil, Nil))
  }

  "Existential generalization p(t) -> \\exists x. p(x)" should "introduce existential quantifier in antecedent" in {
    val tactic = locateAnte(existentialGenT(Variable("y", None, Real), "x".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "\\exists y. y>0".asFormula :: Nil, Nil))
  }

  it should "introduce existential quantifier in antecedent when applied to succedent" in {
    val tactic = locateSucc(existentialGenT(Variable("y", None, Real), "x".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("x>0".asFormula))) should be (
      List(sequent(Nil, "\\exists y. y>0".asFormula :: Nil, "x>0".asFormula :: Nil), sucSequent("x>0".asFormula)))
  }

  it should "replace free occurrences of t with x" in {
    val tactic = locateAnte(existentialGenT(Variable("y", None, Real), "x".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "[x:=x+1;]x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "\\exists y. [x:=y+1;]x>0".asFormula :: Nil, Nil))
  }

  // TODO AlphaConversionHelper replaces variable bound by quantifier -> might be needed by some tactics (check before fixing)
  ignore should "not replace bound occurrences of t with x" in {
    val tactic = locateAnte(existentialGenT(Variable("y", None, Real), "x".asTerm))
    getProofSequent(tactic, new RootNode(sequent(Nil, "\\forall x. x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "\\exists y. \\forall x. x>0".asFormula :: Nil, Nil))
  }

  "Vacuous universal quantification" should "introduce universal quantifier" in {
    val tactic = vacuousUniversalQuanT(Some(Variable("y", None, Real)))
    getProofSequent(locateSucc(tactic), new RootNode(sucSequent("x>0".asFormula))) should be (
      sucSequent("\\forall y. x>0".asFormula))
    getProofSequent(locateAnte(tactic), new RootNode(sequent(Nil, "x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "\\forall y. x>0".asFormula :: Nil, Nil))
  }

  it should "not introduce universal quantifier if variable occurs in p" in {
    val tactic = locateSucc(vacuousUniversalQuanT(Some(Variable("x", None, Real))))
    tactic.applicable(new RootNode(sucSequent("x>0".asFormula))) shouldBe false
  }

  it should "remove vacuous universal quantifier" in {
    val tactic = vacuousUniversalQuanT(None)
    getProofSequent(locateSucc(tactic), new RootNode(sucSequent("\\forall y. x>0".asFormula))) should be (
      sucSequent("x>0".asFormula))
    getProofSequent(locateAnte(tactic), new RootNode(sequent(Nil, "\\forall y. x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "x>0".asFormula :: Nil, Nil))
  }

  it should "not be applicable if more than one quantified variable occurs" in {
    val tactic = locateSucc(vacuousUniversalQuanT(None))
    tactic.applicable(new RootNode(sucSequent("\\forall x,y,z. x>0".asFormula))) shouldBe false
  }

  it should "be preceded by quantifier decomposition if more than one quantified variable occurs" in {
    val tactic = Tactics.repeatT(locateSucc(decomposeQuanT) ~ locateSucc(vacuousUniversalQuanT(None)))
    getProofSequent(tactic, new RootNode(sucSequent("\\forall x,y,z. a>0".asFormula))) should be (
      sucSequent("a>0".asFormula))
  }

  "Vacuous existential quantification" should "introduce existential quantifier" in {
    val tactic = vacuousExistentialQuanT(Some(Variable("y", None, Real)))
    getProofSequent(locateSucc(tactic), new RootNode(sucSequent("x>0".asFormula))) should be (
      sucSequent("\\exists y. x>0".asFormula))
    getProofSequent(locateAnte(tactic), new RootNode(sequent(Nil, "x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "\\exists y. x>0".asFormula :: Nil, Nil))
  }

  it should "not introduce universal quantifier if variable occurs in p" in {
    val tactic = locateSucc(vacuousExistentialQuanT(Some(Variable("x", None, Real))))
    tactic.applicable(new RootNode(sucSequent("x>0".asFormula))) shouldBe false
  }

  it should "remove vacuous universal quantifier" in {
    val tactic = vacuousExistentialQuanT(None)
    getProofSequent(locateSucc(tactic), new RootNode(sucSequent("\\exists y. x>0".asFormula))) should be (
      sucSequent("x>0".asFormula))
    getProofSequent(locateAnte(tactic), new RootNode(sequent(Nil, "\\exists y. x>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "x>0".asFormula :: Nil, Nil))
  }

  it should "not be applicable if more than one quantified variable occurs" in {
    val tactic = locateSucc(vacuousExistentialQuanT(None))
    tactic.applicable(new RootNode(sucSequent("\\exists x,y,z. x>0".asFormula))) shouldBe false
  }

  it should "be preceded by quantifier decomposition if more than one quantified variable occurs" in {
    val tactic = Tactics.repeatT(locateSucc(decomposeQuanT) ~ locateSucc(vacuousExistentialQuanT(None)))
    getProofSequent(tactic, new RootNode(sucSequent("\\exists x,y,z. a>0".asFormula))) should be (
      sucSequent("a>0".asFormula))
  }

  "Quantifier skolemization" should "not introduce a new name if the quantified names are unique already" in {
    import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.skolemizeT
    val tactic = locateSucc(skolemizeT)
    getProofSequent(tactic, new RootNode(sucSequent("\\forall x. x>0".asFormula))) should be (
      sequent("x".asNamedSymbol :: Nil, Nil, "x>0".asFormula :: Nil))
  }

  it should "introduce a new name if the quantified name is not unique" in {
    import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.skolemizeT
    val tactic = locateSucc(skolemizeT)
    getProofSequent(tactic, new RootNode(sequent(Nil, "x>2".asFormula :: Nil, "\\forall x. x>0".asFormula :: Nil))) should be (
      sequent("x_0".asNamedSymbol :: Nil, "x>2".asFormula :: Nil, "x_0>0".asFormula :: Nil))
  }

  it should "introduce a new name even if the quantified names are unique already, if forced to do so" in {
    import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.skolemizeT
    val tactic = locateSucc(skolemizeT(forceUniquify = true))
    getProofSequent(tactic, new RootNode(sucSequent("\\forall x. x>0".asFormula))) should be (
      sequent("x_0".asNamedSymbol :: Nil, Nil, "x_0>0".asFormula :: Nil))
  }
}
