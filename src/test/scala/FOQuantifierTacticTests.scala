import edu.cmu.cs.ls.keymaera.core.{Variable, Real, RootNode}
import edu.cmu.cs.ls.keymaera.tactics.{Config, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{locateSucc,locateAnte}
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.{uniquify,instantiateT,existentialGenT}

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
}
