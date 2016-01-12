/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{DoAll, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.ConfigurableGenerate
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Imply, Box}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
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

  it should "be provable with diffSolve" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    val tactic = implyR('_) & andL('_) & diffSolve(None)(1) & QE
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable with master" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 1a" should "be provable" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.key"))
    val tactic = implyR('_) & andL('_)*@TheType() & diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1) &
        diffWeaken(1) & exhaustiveEqL2R(-3) & exhaustiveEqL2R(-4) & prop

    proveBy(s, tactic) shouldBe 'proved
  }

  "Example 2" should "be provable with master and custom loop invariant" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    val Imply(_, Box(loop, _)) = s.succ.head
    proveBy(s, master(new ConfigurableGenerate(Map((loop, "v>=0".asFormula))))) shouldBe 'proved
  }

  it should "be provable with master and loop invariant from file" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 5 with simple control" should "be provable" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))

    val plant = debug("plant") & composeb('R) & assignb('R) &
      diffSolve(None)('R) & implyR('R)

    val tactic = implyR('R) & (andL('L)*@TheType()) &
      loop("v >= 0 & x+v^2/(2*B) <= S".asFormula)('R) <(
      debug("Use Case") & QE,
      debug("Base Case") & andR('R) & DoAll(closeId),
      debug("Step") & andL('L) & composeb('R) & assignb('R) & plant & QE
    )

    proveBy(s, tactic) shouldBe 'proved
  }

  it should "be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.key"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Example 5" should "be provable automatically with Mathematica" in withMathematica { implicit qeTool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example5.key"))
    proveBy(s, master()) shouldBe 'proved
  }

}
