import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import ODETactics.{diffWeakenT, diffWeakenNormalFormT, diffWeakenSystemIntroT, diffWeakenSystemHeadT,
  diffWeakenSystemFinalHeadT, diffWeakenSystemNilT, diffSolution}

import scala.collection.immutable.Map


/**
 * Created by nfulton on 12/1/14.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class DifferentialTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))

  //Mathematica
  val mathematicaConfig: Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
  }

  "differential weaken" should "nondeterministically assign to primed variable and test the evolution domain constraint" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=1 & x>2;]x>0"))
    )

    val diffWeakenNF = helper.positionTacticToTactic(diffWeakenNormalFormT)
    helper.runTactic(diffWeakenNF, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x:=*;][?x>2;]x>0")))))
  }

  it should "turn nondeterministic assignments and tests of the evolution domain into facts in the antecedent" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=1 & x>2;]x>0"))
    )

    val diffWeaken = helper.positionTacticToTactic(diffWeakenT)
    helper.runTactic(diffWeaken, new RootNode(sequent)).openGoals().foreach(_.sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x", Some(0), Real)),
        scala.collection.immutable.IndexedSeq(GreaterThan(Real, Variable("x", Some(0), Real), Number(2))),
        scala.collection.immutable.IndexedSeq(GreaterThan(Real, Variable("x", Some(0), Real), Number(0))))))
  }

  it should "perform alpha renaming if necessary" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[y'=y & y>2 & z<0;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenNormalFormT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals() should have size 2
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][?y>2&z<0;]y>0")))
    ))
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=1;]x>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenNormalFormT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x:=*;][?true;]x>0")))
    ))
  }

  "differential weaken of system of ODEs" should "replace system of ODEs with nondeterministic assignments and tests" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=x & x>3, y'=1 & y>2 & z<0;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x", Some(0), Real), Variable("y", Some(0), Real)),
        scala.collection.immutable.IndexedSeq(
          // y_0>2 & z<0, x_0>3
          And(
            GreaterThan(Real, Variable("y", Some(0), Real), Number(2)),
            LessThan(Real, Variable("z", None, Real), Number(0))),
          GreaterThan(Real, Variable("x", Some(0), Real), Number(3))
        ),
        scala.collection.immutable.IndexedSeq(
          // y_0>0 but cannot use helper because of indices
          GreaterThan(Real, Variable("y", Some(0), Real), Number(0))))
    ))
  }

  it should "replace system of ODEs with nondeterministic assignments and tests and skolemize correctly" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=x & x>3, y'=1 & y>2 & z<0, z'=2;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x", Some(0), Real),
        Variable("y", Some(0), Real), Variable("z", Some(0), Real)),
        scala.collection.immutable.IndexedSeq(
          True,
          // y_0>2 & z_0<0, x_0>3
          And(
            GreaterThan(Real, Variable("y", Some(0), Real), Number(2)),
            LessThan(Real, Variable("z", Some(0), Real), Number(0))),
          GreaterThan(Real, Variable("x", Some(0), Real), Number(3))
        ),
        scala.collection.immutable.IndexedSeq(
          // y_0>0 but cannot use helper because of indices
          GreaterThan(Real, Variable("y", Some(0), Real), Number(0)))
      )))
  }

  it should "introduce marker when started" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=x & x>3, y'=1 & y>2 & z<0;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemIntroT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$x'=x & x>3, y'=1 & y>2&z<0$$;]y>0")))
    ))
  }

  it should "pull out first ODE from marked system" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$x'=x & x>3, y'=1 & y>2 & z<0$$;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x:=*;][$$y'=1 & y>2&z<0$$;][?x>3;]y>0")))
    ))
  }

  it should "pull out first ODE from marked system and sort in correctly" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$x'=1 & x>2 & z<0, z'=2$$;][?x>3;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x:=*;][$$z'=2$$;][?x>2&z<0;][?x>3;]y>0")))
    ))
  }

  it should "alpha rename if necessary" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$y'=1 & y>2 & z<0, z'=2$$;][?x>3;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][$$z'=2$$;][?y>2&z<0;][?x>3;]y>0")))
    ))
  }

  it should "pull out sole ODE from marked system and sort in correctly" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$x'=1 & x>2$$;][?x>3;]x>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemFinalHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x:=*;][$$$$;][?x>2;][?x>3;]x>0")))
    ))
  }

  it should "alpha rename in sole ODE correctly" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$y'=1 & y>2$$;][?x>3;]x>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemFinalHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[y:=*;][$$$$;][?y>2;][?x>3;]x>0")))
    ))
  }

  it should "remove empty marker" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[$$$$;][?x>3;]y>0"))
    )
    val diffWeaken = helper.positionTacticToTactic(diffWeakenSystemNilT)
    val node = helper.runTactic(diffWeaken, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[?x>3;]y>0")))
    ))
  }

  // TODO tests that tactics don't pull out without marker

  "differential cut" should "cut formula into NFContEvolve" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=2;]x>0"))
    )
    val tactic = helper.positionTacticToTactic(diffCutT(helper.parseFormula("x>1")))
    val node = helper.runTactic(tactic, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=2;]x>1 & [x'=2 & (true&x>1);]x>0"))))
    )
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ContEvolveProduct" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=2, y'=3 & y>4;]x>0"))
    )
    val tactic = helper.positionTacticToTactic(diffCutT(helper.parseFormula("x>1")))
    val node = helper.runTactic(tactic, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=2,y'=3&y>4;]x>1 & [x'=2,y'=3 & (y>4&x>1);]x>0"))))
    )
  }

  it should "cut formula into rightmost ODE in ContEvolveProduct, even if constraint empty" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=2, y'=3;]x>0"))
    )
    val tactic = helper.positionTacticToTactic(diffCutT(helper.parseFormula("x>1")))
    val node = helper.runTactic(tactic, new RootNode(sequent))
    node.openGoals().foreach(_.sequent should be(
      new Sequent(Nil,
        scala.collection.immutable.IndexedSeq(),
        scala.collection.immutable.IndexedSeq(helper.parseFormula("[x'=2,y'=3;]x>1 & [x'=2,y'=3 & (true&x>1);]x>0"))))
    )
  }

  "differential solution tactic" should "use provided solution correctly" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x0:=x; t:=0; x'=2, t'=1;]x>0"))
    )

    val diffNode = helper.runTactic(default, new RootNode(sequent)).openGoals().head
    val tactic = helper.positionTacticToTactic(diffSolution(Some(helper.parseFormula("x = x0 + 2*t"))))
    val node = helper.runTactic(tactic, diffNode)
    node.openGoals()(0).sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x0", Some(0), Real),
        Variable("t", Some(0), Real), Variable("x", Some(0), Real), Variable("t", Some(1), Real)),
        scala.collection.immutable.IndexedSeq(
          // t_0 = 0
          Equals(Real, Variable("t", Some(0), Real), Number(0)), True, True),
        scala.collection.immutable.IndexedSeq(
          // x_0 = x0 + 2*t, see provided solution
          Equals(Real,
            Variable("x", Some(0), Real),
            Add(Real, Variable("x0", None, Real), Multiply(Real, Number(2),
              Variable("t", None, Real))))
        )
      )
    )
    node.openGoals()(1).sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x0", Some(0), Real),
        Variable("t", Some(0), Real), Variable("x", Some(0), Real), Variable("t", Some(1), Real)),
        // TODO could simplify all those true &
        scala.collection.immutable.IndexedSeq(
          // t_0 = 0
          Equals(Real, Variable("t", Some(0), Real), Number(0)),
          // true & x_0 = x0 + 2*t
          And(True,
            Equals(Real,
              Variable("x", Some(0), Real),
              Add(Real, Variable("x0", None, Real), Multiply(Real, Number(2),
                Variable("t", None, Real))))),
          True),
        scala.collection.immutable.IndexedSeq(
          // x_0 > 0
          GreaterThan(Real, Variable("x", Some(0), Real), Number(0))
        )
      )
    )
  }

  it should "use Mathematica to find solution if None is provided" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x0:=x; t:=0; x'=2, t'=1;]x>0"))
    )

    val diffNode = helper.runTactic(default, new RootNode(sequent)).openGoals().head
    // solution = None -> Mathematica
    val tactic = helper.positionTacticToTactic(diffSolution(None))
    val node = helper.runTactic(tactic, diffNode)
    node.openGoals()(0).sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x0", Some(0), Real),
        Variable("t", Some(0), Real), Variable("x", Some(0), Real), Variable("t", Some(1), Real)),
        scala.collection.immutable.IndexedSeq(
          // t_0 = 0
          Equals(Real, Variable("t", Some(0), Real), Number(0)), True, True),
        scala.collection.immutable.IndexedSeq(
          // x_0 = 2*t + x0 & t_1 = 1*t + t0_0
          // TODO not robust if Mathematica reports equivalent formula but differently formatted
          And(
            Equals(Real,
              Variable("x", Some(0), Real),
              Add(Real, Multiply(Real, Number(2),
                                 Variable("t", None, Real)),
                Variable("x0", None, Real)
              )),
            Equals(Real,
              Variable("t", Some(1), Real),
              Add(Real, Multiply(Real, Number(1), Variable("t", None, Real)),
                Variable("t0", Some(0), Real))
            )
          )
        )
      )
    )
    node.openGoals()(1).sequent should be(
      new Sequent(scala.collection.immutable.IndexedSeq(Variable("x0", Some(0), Real),
        Variable("t", Some(0), Real), Variable("x", Some(0), Real), Variable("t", Some(1), Real)),
        // TODO could simplify all those true &
        scala.collection.immutable.IndexedSeq(
          // t_0 = 0
          Equals(Real, Variable("t", Some(0), Real), Number(0)),
          // true & x_0 = 2*t + x0 & t_1 = 1*t + t0_0
          And(True,
            And(
              Equals(Real,
                Variable("x", Some(0), Real),
                Add(Real, Multiply(Real, Number(2),
                  Variable("t", None, Real)),
                  Variable("x0", None, Real)
                )),
              Equals(Real,
                Variable("t", Some(1), Real),
                Add(Real, Multiply(Real, Number(1), Variable("t", None, Real)),
                  Variable("t0", Some(0), Real))
              )
            )
          ),
          True),
        scala.collection.immutable.IndexedSeq(
          // x_0 > 0
          GreaterThan(Real, Variable("x", Some(0), Real), Number(0))
        )
      )
    )
  }

  ignore should "prove with differential solution tactic" in {
    import scala.language.postfixOps
    import TacticLibrary.{boxAssignT, skolemizeT, boxSeqT}
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(helper.parseFormula("x>0")),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x0:=x; t:=0; t0:=t; x'=2, t'=1 & t>=0;]x>0"))
      )
    // TODO t:=0 leads to a SubstitutionClashException (because subsequently t'=1)
    val diffNode = helper.runTactic((locateSucc(boxSeqT) ~ locateSucc(boxAssignT) ~ locateSucc(skolemizeT) ~
      locateSucc(ImplyRightT))*, new RootNode(sequent)).openGoals().head
    // TODO when alpha renaming finally works it should be head instead of tail.tail.head
    val postDiffSolNode = helper.runTactic(locateSucc(diffSolution(None)), diffNode).openGoals().tail.tail.head
    helper.runTactic(default, postDiffSolNode) shouldBe 'closed
  }

}
