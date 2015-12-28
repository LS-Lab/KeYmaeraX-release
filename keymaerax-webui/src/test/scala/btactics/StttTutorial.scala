/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.TheType
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Imply, Box}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ConfigurableGenerate
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
 * Tutorial test cases.
 * @author Stefan Mitsch
 */
@SlowTest
class StttTutorial extends TacticTestBase {

  "Example 1" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    val tactic = implyR('_) & andL('_) & DC("v>=0".asFormula)(1) <(
      /* use */ diffWeaken(1) & prop,
      /* show */ diffInd(qeTool)(1)
      )
    proveBy(s, tactic) shouldBe 'proved
  }

  //@todo DiffSolve
  ignore should "be provable with master" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 1a" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key"))
    val tactic = implyR('_) & andL('_)*@TheType() & diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1) &
        diffWeaken(1) & exhaustiveEqL2R(-3) & exhaustiveEqL2R(-4) & prop

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 2" should "be provable with master and custom loop invariant" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    val Imply(_, Box(loop, _)) = s.succ.head

    val result = proveBy(s, master(new ConfigurableGenerate(Map((loop, "v>=0".asFormula)))))
    result.subgoals should have size 3
    result.subgoals.head.succ should contain only "[{x'=v,v'=A&v>=0}]v>=0".asFormula
    result.subgoals(1).succ should contain only "[{x'=v,v'=0&v>=0}]v>=0".asFormula
    result.subgoals(2).succ should contain only "[{x'=v,v'=-B&v>=0}]v>=0".asFormula

    //@todo when DiffSolve is available
    //proveBy(s, master(new ConfigurableGenerate(Map((loop, "v>=0".asFormula))))) shouldBe 'proved
  }

}
