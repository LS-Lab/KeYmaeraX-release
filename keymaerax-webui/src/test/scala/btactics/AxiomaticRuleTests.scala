package btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
 * Tests
 * [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.monb]],
 * [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.mond]],
 * [[edu.cmu.cs.ls.keymaerax.btactics.DLBySubst.G]]
 */
class AxiomaticRuleTests extends TacticTestBase {

  "[] monotone" should "work" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("[x:=1;]x>0".asFormula), immutable.IndexedSeq("[x:=1;]x>-1".asFormula)),
      TactixLibrary.monb)

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>-1".asFormula
  }

  "<> monotone" should "work" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("<x:=1;>x>0".asFormula), immutable.IndexedSeq("<x:=1;>x>-1".asFormula)),
      TactixLibrary.mond)

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>-1".asFormula
  }

  "G" should "work" in {
    val result = proveBy("[x:=1;]x>0".asFormula, TactixLibrary.G)

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0".asFormula
  }
}
