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
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
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
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][z:=2;](y>0 & z>0)"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y0 = Variable("y", Some(0), Real)
    val z = Variable("z", None, Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(
          // \forall y_0. y_0=1 -> [z:=2](y_0>0 & z>0)
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(Assign(z, Number(2)),
              And(GreaterThan(Real, y0, Number(0)), GreaterThan(Real, z, Number(0))))))))))
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
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [y:=2;]y>0
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(Assign(y, Number(2)), GreaterThan(Real, y, Number(0)))))))))
  }

  it should "rename free variables but not variables bound by assignment in modality predicates" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][y:=2+y;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y = Variable("y", None, Real)
    val y0 = Variable("y", Some(0), Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [y:=2+y_0;]y>0
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(Assign(y, Add(Real, Number(2), y0)), GreaterThan(Real, y, Number(0)))))))))
  }

  it should "rename free variables but not variables bound by ODEs in modality predicates" in {
    import TacticLibrary.boxAssignT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][z'=2+y;](y>0 & z>0)"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT)
    val y0 = Variable("y", Some(0), Real)
    val z = Variable("z", None, Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [z'=2+y_0;](y_0>0 & z>0)
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Number(1)),
            BoxModality(ContEvolveProduct(NFContEvolve(Nil, Derivative(Real, z), Add(Real, Number(2), y0), True), EmptyContEvolveProgram()),
              And(GreaterThan(Real, y0, Number(0)), GreaterThan(Real, z, Number(0))))))))))
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
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=y+1 -> y_0>0
        scala.collection.immutable.IndexedSeq(
          Forall(y0 :: Nil, Imply(Equals(Real, y0, Add(Real, y, Number(1))),
            GreaterThan(Real, y0, Number(0))))))))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import TacticLibrary.{boxAssignT, skolemizeT, ImplyRightT}
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=y+1;][y:=2;][?y>1;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT) &
      helper.positionTacticToTactic(skolemizeT) & helper.positionTacticToTactic(ImplyRightT)
    val y = Variable("y", None, Real)
    val y1 = Variable("y", Some(1), Real)
    val afterFirst = helper.runTactic(assignT, new RootNode(sequent))
    afterFirst.openGoals().foreach(_.sequent should be (
      new Sequent(y1 :: Nil,
        scala.collection.immutable.IndexedSeq(Equals(Real, y1, Add(Real, y, Number(1)))),
        // [y:=2;][?y>1;]y>0
        scala.collection.immutable.IndexedSeq(BoxModality(Assign(y, Number(2)),
          BoxModality(Test(GreaterThan(Real, y, Number(1))),
            GreaterThan(Real, y, Number(0))))))))

    val afterSecond = helper.runTactic(assignT, afterFirst.openGoals().head)
    val y2 = Variable("y", Some(2), Real)
    afterSecond.openGoals().foreach(_.sequent should be (
      new Sequent(y1 :: y2 :: Nil,
        scala.collection.immutable.IndexedSeq(Equals(Real, y1, Add(Real, y, Number(1))), Equals(Real, y2, Number(2))),
        // [?y_2>1;]y_2>0
        scala.collection.immutable.IndexedSeq(
          BoxModality(Test(GreaterThan(Real, y2, Number(1))),
            GreaterThan(Real, y2, Number(0)))))))
  }

  ignore should "work in front of a continuous program" in {
    import TacticLibrary.{boxAssignT, skolemizeT, ImplyRightT}
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][y'=2;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT) &
      helper.positionTacticToTactic(skolemizeT) & helper.positionTacticToTactic(ImplyRightT)
    val y = Variable("y", None, Real)
    val y1 = Variable("y", Some(1), Real)
    val afterFirst = helper.runTactic(assignT, new RootNode(sequent))
    afterFirst.openGoals().foreach(_.sequent should be (
      new Sequent(y1 :: Nil,
        scala.collection.immutable.IndexedSeq(Equals(Real, y1, Number(1))),
        // [y'=2;]y>0
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[y'=2;]y>0")))))
  }

//  it should "substitute with additional assignment if followed by a differential equation" in {
//    import TacticLibrary.boxAssignT
//    val sequent = new Sequent(Nil,
//      scala.collection.immutable.IndexedSeq(),
//      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x:=1;][x'=2+x;]true"))
//    )
//    val assignT = helper.positionTacticToTactic(boxAssignT)
//    val x = Variable("x", None, Real)
//    val x0 = Variable("x", Some(0), Real)
//    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
//      new Sequent(Nil,
//        scala.collection.immutable.IndexedSeq(),
//        // \forall x_0. x_0=1 -> [x:=\cdot;][x'=2+x_0;]true
//        scala.collection.immutable.IndexedSeq(
//          Forall(x0 :: Nil, Imply(Equals(Real, x0, Number(1)),
//            BoxModality(Assign(x, CDot),
//              BoxModality(NFContEvolve(Nil, Derivative(Real, x), Add(Real, Number(2), x0), True), True))))))))
//  }
//
//  it should "substitute with additional assignment if followed by a loop" in {
//    import TacticLibrary.boxAssignT
//    val sequent = new Sequent(Nil,
//      scala.collection.immutable.IndexedSeq(),
//      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][{y:=2+y;}*;]true"))
//    )
//    val assignT = helper.positionTacticToTactic(boxAssignT)
//    val y = Variable("y", None, Real)
//    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
//      new Sequent(Nil,
//        scala.collection.immutable.IndexedSeq(),
//        // \forall y. y=1 -> [y'=2+y;]y>0
//        scala.collection.immutable.IndexedSeq(
//          Forall(y :: Nil, Imply(Equals(Real, y, Number(1)),
//            BoxModality(NFContEvolve(Nil, Derivative(Real, y), Add(Real, Number(2), y), True), True)))))))
//  }

  "Box test tactic" should "use axiom [?H;]p <-> (H->p)" in {
    import TacticLibrary.boxTestT
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[?y>2;]y>0"))
    )
    val tactic = helper.positionTacticToTactic(boxTestT)
    val y = Variable("y", None, Real)
    helper.runTactic(tactic, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=y+1 -> y_0>0
        scala.collection.immutable.IndexedSeq(
          Imply(GreaterThan(Real, y, Number(2)), GreaterThan(Real, y, Number(0)))
          ))))
  }

  "Box nondeterministic assignment tactic" should "introduce universal quantifier and rename free variables" in {
    import TacticLibrary.boxNDetAssign
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;]y>0"))
    )
    val tactic = helper.positionTacticToTactic(boxNDetAssign)
    val y = Variable("y", None, Real)
    helper.runTactic(tactic, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(
          // \forall y. y>0
          Forall(y :: Nil, GreaterThan(Real, y, Number(0)))))))
  }

  it should "rename free variables in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][z:=2;](y>0 & z>0)"))
    )
    val assignT = helper.positionTacticToTactic(boxNDetAssign)
    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(
          // \forall y. [z:=2](y>0 & z>0)
          Forall(y :: Nil, BoxModality(Assign(z, Number(2)),
              And(GreaterThan(Real, y, Number(0)), GreaterThan(Real, z, Number(0)))))))))
  }

  it should "rename free variables but not bound variables" in {
    import TacticLibrary.boxNDetAssign
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][y:=2;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxNDetAssign)
    val y = Variable("y", None, Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y. [y:=2;]y>0
        scala.collection.immutable.IndexedSeq(
          Forall(y :: Nil, BoxModality(Assign(y, Number(2)), GreaterThan(Real, y, Number(0))))))))
  }

  it should "rename free variables but not variables bound by assignment in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][y:=2+y;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxNDetAssign)
    val y = Variable("y", None, Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [y:=2+y_0;]y>0
        scala.collection.immutable.IndexedSeq(
          Forall(y :: Nil, BoxModality(Assign(y, Add(Real, Number(2), y)), GreaterThan(Real, y, Number(0))))))))
  }

  it should "rename free variables but not variables bound by ODEs in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][z'=2+y;](y>0 & z>0)"))
    )
    val assignT = helper.positionTacticToTactic(boxNDetAssign)
    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)
    helper.runTactic(assignT, new RootNode(sequent)).openGoals().foreach(_.sequent should be (
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        // \forall y_0. y_0=1 -> [z'=2+y_0;](y_0>0 & z>0)
        scala.collection.immutable.IndexedSeq(
          Forall(y :: Nil,
            BoxModality(ContEvolveProduct(NFContEvolve(Nil, Derivative(Real, z), Add(Real, Number(2), y), True), EmptyContEvolveProgram()),
              And(GreaterThan(Real, y, Number(0)), GreaterThan(Real, z, Number(0)))))))))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import TacticLibrary.{boxNDetAssign, skolemizeT, ImplyRightT}
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][y:=*;][?y>1;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxNDetAssign) &
      helper.positionTacticToTactic(skolemizeT) & helper.positionTacticToTactic(ImplyRightT)
    val y = Variable("y", None, Real)
    val y0 = Variable("y", Some(0), Real)
    val afterFirst = helper.runTactic(assignT, new RootNode(sequent))
    afterFirst.openGoals().foreach(_.sequent should be (
      new Sequent(y0 :: Nil,
        scala.collection.immutable.IndexedSeq(),
        // [y:=2;][?y>1;]y>0
        scala.collection.immutable.IndexedSeq(BoxModality(NDetAssign(y0),
          BoxModality(Test(GreaterThan(Real, y0, Number(1))),
            GreaterThan(Real, y0, Number(0))))))))

    val afterSecond = helper.runTactic(assignT, afterFirst.openGoals().head)
    val y1 = Variable("y", Some(1), Real)
    afterSecond.openGoals().foreach(_.sequent should be (
      new Sequent(y0 :: y1 :: Nil,
        scala.collection.immutable.IndexedSeq(),
        // [?y_1>1;]y_1>0
        scala.collection.immutable.IndexedSeq(
          BoxModality(Test(GreaterThan(Real, y1, Number(1))),
            GreaterThan(Real, y1, Number(0)))))))
  }

  ignore should "work in front of a continuous program" in {
    import TacticLibrary.{boxAssignT, skolemizeT, ImplyRightT}
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=1;][y'=2;]y>0"))
    )
    val assignT = helper.positionTacticToTactic(boxAssignT) &
      helper.positionTacticToTactic(skolemizeT) & helper.positionTacticToTactic(ImplyRightT)
    val y = Variable("y", None, Real)
    val y1 = Variable("y", Some(1), Real)
    val afterFirst = helper.runTactic(assignT, new RootNode(sequent))
    afterFirst.openGoals().foreach(_.sequent should be (
      new Sequent(y1 :: Nil,
        scala.collection.immutable.IndexedSeq(Equals(Real, y1, Number(1))),
        // [y'=2;]y>0
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[y'=2;]y>0")))))
  }
}
