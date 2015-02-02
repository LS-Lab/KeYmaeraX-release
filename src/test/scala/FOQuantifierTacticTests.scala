import edu.cmu.cs.ls.keymaera.core.RootNode
import edu.cmu.cs.ls.keymaera.tactics.Tactics
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.locateSucc
import edu.cmu.cs.ls.keymaera.tactics.FOQuantifierTacticsImpl.uniquify

/**
 * Created by smitsch on 1/31/15.
 * @author Stefan Mitsch
 */
class FOQuantifierTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
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
}
