import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{TacticLibrary, Config, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

import scala.collection.immutable.Map

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 */
class HybridProgramTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach  {
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

  "Box assignment tactic" should "introduce universal quantifier and rename free variables" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y0 = Variable("y", Some(0), Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(
          // \forall y_0. y_0=1 -> y_0>0
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)), GreaterThan(Real, y0, Number(0))))))))
  }

  it should "rename free variables in modality predicates" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][z:=2;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y0 = Variable("y", Some(0), Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(
          // \forall y_0. y_0=1 -> [z:=2]y_0>0
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(Assign(Variable("z", None, Real), Number(2)), GreaterThan(Real, y0, Number(0)))))))))
  }

  it should "rename free variables but not bound variables" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][y:=2;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y = Variable("y", None, Real)
    val y0 = Variable("y", Some(0), Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [y:=2;]y>0
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(Assign(y, Number(2)), GreaterThan(Real, y, Number(0)))))))))
  }

  it should "rename free variables but not bound variables in modality predicates" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][y:=2+y;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y = Variable("y", None, Real)
    val y0 = Variable("y", Some(0), Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [y:=2+y_0;]y>0
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(Assign(y, Add(Real, Number(2), y0)), GreaterThan(Real, y, Number(0)))))))))
  }

  it should "rename only free names in modality predicates" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=y+1;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y = Variable("y", None, Real)
    val y0 = Variable("y", Some(0), Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=y+1 -> y_0>0
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Add(Real, y, Number(1))),
            GreaterThan(Real, y0, Number(0))))))))
  }
}
